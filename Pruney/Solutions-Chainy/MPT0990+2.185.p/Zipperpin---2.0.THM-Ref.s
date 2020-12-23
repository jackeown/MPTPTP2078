%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.baKagkDFy7

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:27 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :  238 ( 610 expanded)
%              Number of leaves         :   48 ( 202 expanded)
%              Depth                    :   21
%              Number of atoms          : 2354 (13947 expanded)
%              Number of equality atoms :  158 ( 955 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('5',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','5','6','7'])).

thf('9',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
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

thf('14',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('21',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( X19 = X22 )
      | ~ ( r2_relset_1 @ X20 @ X21 @ X19 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','22'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('24',plain,(
    ! [X23: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('25',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('26',plain,(
    ! [X23: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,(
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

thf('29',plain,(
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

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['27','33'])).

thf('35',plain,(
    ! [X23: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('36',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( r2_relset_1 @ X20 @ X21 @ X19 @ X22 )
      | ( X19 != X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('37',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_relset_1 @ X20 @ X21 @ X22 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['34','38','39','40','41','42'])).

thf('44',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','43'])).

thf('45',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','26'])).

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
    ! [X13: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('55',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('56',plain,(
    ! [X13: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X13 ) ) ),
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
    ! [X43: $i,X44: $i] :
      ( ( X43 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X43 @ X44 ) ) ),
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
    ! [X41: $i,X42: $i] :
      ( ( v2_funct_1 @ X42 )
      | ~ ( zip_tseitin_0 @ X42 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('68',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['45','68'])).

thf(t58_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('70',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X15 @ ( k2_funct_1 @ X15 ) ) )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('71',plain,
    ( ( ( k2_relat_1 @ ( k6_partfun1 @ sk_B ) )
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('72',plain,(
    ! [X8: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X8 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('73',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('74',plain,(
    ! [X8: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X8 ) )
      = X8 ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('77',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('78',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('79',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['66','67'])).

thf('82',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['71','74','79','80','81'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('83',plain,(
    ! [X9: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X9 ) ) @ X9 )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('84',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('85',plain,(
    ! [X9: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X9 ) ) @ X9 )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['82','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
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

thf('89',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( ( k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33 )
        = ( k5_relat_1 @ X30 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['87','92'])).

thf('94',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('96',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('97',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('98',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
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

thf('100',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['100','101','102','103','104'])).

thf('106',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['106','107'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('109',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X5 @ X4 ) @ X6 )
        = ( k5_relat_1 @ X5 @ ( k5_relat_1 @ X4 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('113',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('115',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['110','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['97','116'])).

thf('118',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['113','114'])).

thf('119',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['96','120'])).

thf('122',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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

thf('123',plain,(
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k1_relat_1 @ X14 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('124',plain,(
    ! [X10: $i] :
      ( ( ( k5_relat_1 @ X10 @ ( k6_relat_1 @ ( k2_relat_1 @ X10 ) ) )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('125',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('126',plain,(
    ! [X10: $i] :
      ( ( ( k5_relat_1 @ X10 @ ( k6_partfun1 @ ( k2_relat_1 @ X10 ) ) )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['123','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['122','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('131',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('133',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('137',plain,(
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k2_relat_1 @ X14 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('138',plain,(
    ! [X9: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X9 ) ) @ X9 )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['136','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['135','141'])).

thf('143',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['113','114'])).

thf('144',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['142','143','144','145'])).

thf('147',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X5 @ X4 ) @ X6 )
        = ( k5_relat_1 @ X5 @ ( k5_relat_1 @ X4 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('150',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('151',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X12 ) ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['148','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['130','152'])).

thf('154',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['113','114'])).

thf('155',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['153','154','155'])).

thf('157',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['129','156'])).

thf('158',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['142','143','144','145'])).

thf('159',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['113','114'])).

thf('160',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X12 ) ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('163',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['157','158','159','160','161','162'])).

thf('164',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
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

thf('166',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['166','167','168','169','170'])).

thf('172',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['171'])).

thf('173',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X15 @ ( k2_funct_1 @ X15 ) ) )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('176',plain,
    ( ( ( k2_relat_1 @ ( k6_partfun1 @ sk_A ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X8: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X8 ) )
      = X8 ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('178',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['113','114'])).

thf('179',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['176','177','178','179','180'])).

thf('182',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['163','181'])).

thf('183',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['77','78'])).

thf('184',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['121','182','183'])).

thf('185',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['77','78'])).

thf('186',plain,
    ( ( k2_funct_1 @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['86','184','185'])).

thf('187',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['186','187'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.baKagkDFy7
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:26:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.35/1.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.35/1.57  % Solved by: fo/fo7.sh
% 1.35/1.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.35/1.57  % done 1182 iterations in 1.114s
% 1.35/1.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.35/1.57  % SZS output start Refutation
% 1.35/1.57  thf(sk_C_type, type, sk_C: $i).
% 1.35/1.57  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 1.35/1.57  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.35/1.57  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.35/1.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.35/1.57  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.35/1.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.35/1.57  thf(sk_A_type, type, sk_A: $i).
% 1.35/1.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.35/1.57  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.35/1.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.35/1.57  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.35/1.57  thf(sk_B_type, type, sk_B: $i).
% 1.35/1.57  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.35/1.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.35/1.57  thf(sk_D_type, type, sk_D: $i).
% 1.35/1.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.35/1.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.35/1.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.35/1.57  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.35/1.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.35/1.57  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.35/1.57  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.35/1.57  thf(t36_funct_2, conjecture,
% 1.35/1.57    (![A:$i,B:$i,C:$i]:
% 1.35/1.57     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.35/1.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.35/1.57       ( ![D:$i]:
% 1.35/1.57         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.35/1.57             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.35/1.57           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.35/1.57               ( r2_relset_1 @
% 1.35/1.57                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.35/1.57                 ( k6_partfun1 @ A ) ) & 
% 1.35/1.57               ( v2_funct_1 @ C ) ) =>
% 1.35/1.57             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.35/1.57               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.35/1.57  thf(zf_stmt_0, negated_conjecture,
% 1.35/1.57    (~( ![A:$i,B:$i,C:$i]:
% 1.35/1.57        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.35/1.57            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.35/1.57          ( ![D:$i]:
% 1.35/1.57            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.35/1.57                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.35/1.57              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.35/1.57                  ( r2_relset_1 @
% 1.35/1.57                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.35/1.57                    ( k6_partfun1 @ A ) ) & 
% 1.35/1.57                  ( v2_funct_1 @ C ) ) =>
% 1.35/1.57                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.35/1.57                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.35/1.57    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.35/1.57  thf('0', plain,
% 1.35/1.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf(t35_funct_2, axiom,
% 1.35/1.57    (![A:$i,B:$i,C:$i]:
% 1.35/1.57     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.35/1.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.35/1.57       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.35/1.57         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.35/1.57           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 1.35/1.57             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 1.35/1.57  thf('1', plain,
% 1.35/1.57      (![X50 : $i, X51 : $i, X52 : $i]:
% 1.35/1.57         (((X50) = (k1_xboole_0))
% 1.35/1.57          | ~ (v1_funct_1 @ X51)
% 1.35/1.57          | ~ (v1_funct_2 @ X51 @ X52 @ X50)
% 1.35/1.57          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X50)))
% 1.35/1.57          | ((k5_relat_1 @ X51 @ (k2_funct_1 @ X51)) = (k6_partfun1 @ X52))
% 1.35/1.57          | ~ (v2_funct_1 @ X51)
% 1.35/1.57          | ((k2_relset_1 @ X52 @ X50 @ X51) != (X50)))),
% 1.35/1.57      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.35/1.57  thf('2', plain,
% 1.35/1.57      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 1.35/1.57        | ~ (v2_funct_1 @ sk_D)
% 1.35/1.57        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.35/1.57        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.35/1.57        | ~ (v1_funct_1 @ sk_D)
% 1.35/1.57        | ((sk_A) = (k1_xboole_0)))),
% 1.35/1.57      inference('sup-', [status(thm)], ['0', '1'])).
% 1.35/1.57  thf('3', plain,
% 1.35/1.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf(redefinition_k2_relset_1, axiom,
% 1.35/1.57    (![A:$i,B:$i,C:$i]:
% 1.35/1.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.35/1.57       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.35/1.57  thf('4', plain,
% 1.35/1.57      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.35/1.57         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 1.35/1.57          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.35/1.57      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.35/1.57  thf('5', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.35/1.57      inference('sup-', [status(thm)], ['3', '4'])).
% 1.35/1.57  thf('6', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('8', plain,
% 1.35/1.57      ((((k2_relat_1 @ sk_D) != (sk_A))
% 1.35/1.57        | ~ (v2_funct_1 @ sk_D)
% 1.35/1.57        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.35/1.57        | ((sk_A) = (k1_xboole_0)))),
% 1.35/1.57      inference('demod', [status(thm)], ['2', '5', '6', '7'])).
% 1.35/1.57  thf('9', plain, (((sk_A) != (k1_xboole_0))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('10', plain,
% 1.35/1.57      ((((k2_relat_1 @ sk_D) != (sk_A))
% 1.35/1.57        | ~ (v2_funct_1 @ sk_D)
% 1.35/1.57        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 1.35/1.57      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 1.35/1.57  thf('11', plain,
% 1.35/1.57      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.35/1.57        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.35/1.57        (k6_partfun1 @ sk_A))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('12', plain,
% 1.35/1.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('13', plain,
% 1.35/1.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf(dt_k1_partfun1, axiom,
% 1.35/1.57    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.35/1.57     ( ( ( v1_funct_1 @ E ) & 
% 1.35/1.57         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.35/1.57         ( v1_funct_1 @ F ) & 
% 1.35/1.57         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.35/1.57       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.35/1.57         ( m1_subset_1 @
% 1.35/1.57           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.35/1.57           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.35/1.57  thf('14', plain,
% 1.35/1.57      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.35/1.57         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 1.35/1.57          | ~ (v1_funct_1 @ X24)
% 1.35/1.57          | ~ (v1_funct_1 @ X27)
% 1.35/1.57          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 1.35/1.57          | (m1_subset_1 @ (k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27) @ 
% 1.35/1.57             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X29))))),
% 1.35/1.57      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.35/1.57  thf('15', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.57         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.35/1.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.35/1.57          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.35/1.57          | ~ (v1_funct_1 @ X1)
% 1.35/1.57          | ~ (v1_funct_1 @ sk_C))),
% 1.35/1.57      inference('sup-', [status(thm)], ['13', '14'])).
% 1.35/1.57  thf('16', plain, ((v1_funct_1 @ sk_C)),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('17', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.57         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.35/1.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.35/1.57          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.35/1.57          | ~ (v1_funct_1 @ X1))),
% 1.35/1.57      inference('demod', [status(thm)], ['15', '16'])).
% 1.35/1.57  thf('18', plain,
% 1.35/1.57      ((~ (v1_funct_1 @ sk_D)
% 1.35/1.57        | (m1_subset_1 @ 
% 1.35/1.57           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.35/1.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.35/1.57      inference('sup-', [status(thm)], ['12', '17'])).
% 1.35/1.57  thf('19', plain, ((v1_funct_1 @ sk_D)),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('20', plain,
% 1.35/1.57      ((m1_subset_1 @ 
% 1.35/1.57        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.35/1.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.35/1.57      inference('demod', [status(thm)], ['18', '19'])).
% 1.35/1.57  thf(redefinition_r2_relset_1, axiom,
% 1.35/1.57    (![A:$i,B:$i,C:$i,D:$i]:
% 1.35/1.57     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.35/1.57         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.35/1.57       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.35/1.57  thf('21', plain,
% 1.35/1.57      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.35/1.57         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 1.35/1.57          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 1.35/1.57          | ((X19) = (X22))
% 1.35/1.57          | ~ (r2_relset_1 @ X20 @ X21 @ X19 @ X22))),
% 1.35/1.57      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.35/1.57  thf('22', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.35/1.57             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 1.35/1.57          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 1.35/1.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.35/1.57      inference('sup-', [status(thm)], ['20', '21'])).
% 1.35/1.57  thf('23', plain,
% 1.35/1.57      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 1.35/1.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.35/1.57        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.35/1.57            = (k6_partfun1 @ sk_A)))),
% 1.35/1.57      inference('sup-', [status(thm)], ['11', '22'])).
% 1.35/1.57  thf(t29_relset_1, axiom,
% 1.35/1.57    (![A:$i]:
% 1.35/1.57     ( m1_subset_1 @
% 1.35/1.57       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 1.35/1.57  thf('24', plain,
% 1.35/1.57      (![X23 : $i]:
% 1.35/1.57         (m1_subset_1 @ (k6_relat_1 @ X23) @ 
% 1.35/1.57          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X23)))),
% 1.35/1.57      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.35/1.57  thf(redefinition_k6_partfun1, axiom,
% 1.35/1.57    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.35/1.57  thf('25', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 1.35/1.57      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.35/1.57  thf('26', plain,
% 1.35/1.57      (![X23 : $i]:
% 1.35/1.57         (m1_subset_1 @ (k6_partfun1 @ X23) @ 
% 1.35/1.57          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X23)))),
% 1.35/1.57      inference('demod', [status(thm)], ['24', '25'])).
% 1.35/1.57  thf('27', plain,
% 1.35/1.57      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.35/1.57         = (k6_partfun1 @ sk_A))),
% 1.35/1.57      inference('demod', [status(thm)], ['23', '26'])).
% 1.35/1.57  thf('28', plain,
% 1.35/1.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf(t24_funct_2, axiom,
% 1.35/1.57    (![A:$i,B:$i,C:$i]:
% 1.35/1.57     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.35/1.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.35/1.57       ( ![D:$i]:
% 1.35/1.57         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.35/1.57             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.35/1.57           ( ( r2_relset_1 @
% 1.35/1.57               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 1.35/1.57               ( k6_partfun1 @ B ) ) =>
% 1.35/1.57             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 1.35/1.57  thf('29', plain,
% 1.35/1.57      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 1.35/1.57         (~ (v1_funct_1 @ X37)
% 1.35/1.57          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 1.35/1.57          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 1.35/1.57          | ~ (r2_relset_1 @ X38 @ X38 @ 
% 1.35/1.57               (k1_partfun1 @ X38 @ X39 @ X39 @ X38 @ X37 @ X40) @ 
% 1.35/1.57               (k6_partfun1 @ X38))
% 1.35/1.57          | ((k2_relset_1 @ X39 @ X38 @ X40) = (X38))
% 1.35/1.57          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38)))
% 1.35/1.57          | ~ (v1_funct_2 @ X40 @ X39 @ X38)
% 1.35/1.57          | ~ (v1_funct_1 @ X40))),
% 1.35/1.57      inference('cnf', [status(esa)], [t24_funct_2])).
% 1.35/1.57  thf('30', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (~ (v1_funct_1 @ X0)
% 1.35/1.57          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.35/1.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.35/1.57          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.35/1.57          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.35/1.57               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.35/1.57               (k6_partfun1 @ sk_A))
% 1.35/1.57          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.35/1.57          | ~ (v1_funct_1 @ sk_C))),
% 1.35/1.57      inference('sup-', [status(thm)], ['28', '29'])).
% 1.35/1.57  thf('31', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('32', plain, ((v1_funct_1 @ sk_C)),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('33', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (~ (v1_funct_1 @ X0)
% 1.35/1.57          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.35/1.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.35/1.57          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.35/1.57          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.35/1.57               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.35/1.57               (k6_partfun1 @ sk_A)))),
% 1.35/1.57      inference('demod', [status(thm)], ['30', '31', '32'])).
% 1.35/1.57  thf('34', plain,
% 1.35/1.57      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 1.35/1.57           (k6_partfun1 @ sk_A))
% 1.35/1.57        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 1.35/1.57        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.35/1.57        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.35/1.57        | ~ (v1_funct_1 @ sk_D))),
% 1.35/1.57      inference('sup-', [status(thm)], ['27', '33'])).
% 1.35/1.57  thf('35', plain,
% 1.35/1.57      (![X23 : $i]:
% 1.35/1.57         (m1_subset_1 @ (k6_partfun1 @ X23) @ 
% 1.35/1.57          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X23)))),
% 1.35/1.57      inference('demod', [status(thm)], ['24', '25'])).
% 1.35/1.57  thf('36', plain,
% 1.35/1.57      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.35/1.57         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 1.35/1.57          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 1.35/1.57          | (r2_relset_1 @ X20 @ X21 @ X19 @ X22)
% 1.35/1.57          | ((X19) != (X22)))),
% 1.35/1.57      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.35/1.57  thf('37', plain,
% 1.35/1.57      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.35/1.57         ((r2_relset_1 @ X20 @ X21 @ X22 @ X22)
% 1.35/1.57          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 1.35/1.57      inference('simplify', [status(thm)], ['36'])).
% 1.35/1.57  thf('38', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 1.35/1.57      inference('sup-', [status(thm)], ['35', '37'])).
% 1.35/1.57  thf('39', plain,
% 1.35/1.57      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.35/1.57      inference('sup-', [status(thm)], ['3', '4'])).
% 1.35/1.57  thf('40', plain,
% 1.35/1.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('41', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('42', plain, ((v1_funct_1 @ sk_D)),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('43', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.35/1.57      inference('demod', [status(thm)], ['34', '38', '39', '40', '41', '42'])).
% 1.35/1.57  thf('44', plain,
% 1.35/1.57      ((((sk_A) != (sk_A))
% 1.35/1.57        | ~ (v2_funct_1 @ sk_D)
% 1.35/1.57        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 1.35/1.57      inference('demod', [status(thm)], ['10', '43'])).
% 1.35/1.57  thf('45', plain,
% 1.35/1.57      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.35/1.57        | ~ (v2_funct_1 @ sk_D))),
% 1.35/1.57      inference('simplify', [status(thm)], ['44'])).
% 1.35/1.57  thf('46', plain,
% 1.35/1.57      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.35/1.57         = (k6_partfun1 @ sk_A))),
% 1.35/1.57      inference('demod', [status(thm)], ['23', '26'])).
% 1.35/1.57  thf('47', plain,
% 1.35/1.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf(t30_funct_2, axiom,
% 1.35/1.57    (![A:$i,B:$i,C:$i,D:$i]:
% 1.35/1.57     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.35/1.57         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 1.35/1.57       ( ![E:$i]:
% 1.35/1.57         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 1.35/1.57             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 1.35/1.57           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 1.35/1.57               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 1.35/1.57             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 1.35/1.57               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 1.35/1.57  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 1.35/1.57  thf(zf_stmt_2, axiom,
% 1.35/1.57    (![C:$i,B:$i]:
% 1.35/1.57     ( ( zip_tseitin_1 @ C @ B ) =>
% 1.35/1.57       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 1.35/1.57  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.35/1.57  thf(zf_stmt_4, axiom,
% 1.35/1.57    (![E:$i,D:$i]:
% 1.35/1.57     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 1.35/1.57  thf(zf_stmt_5, axiom,
% 1.35/1.57    (![A:$i,B:$i,C:$i,D:$i]:
% 1.35/1.57     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.35/1.57         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.35/1.57       ( ![E:$i]:
% 1.35/1.57         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.35/1.57             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.35/1.57           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 1.35/1.57               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 1.35/1.57             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 1.35/1.57  thf('48', plain,
% 1.35/1.57      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 1.35/1.57         (~ (v1_funct_1 @ X45)
% 1.35/1.57          | ~ (v1_funct_2 @ X45 @ X46 @ X47)
% 1.35/1.57          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 1.35/1.57          | (zip_tseitin_0 @ X45 @ X48)
% 1.35/1.57          | ~ (v2_funct_1 @ (k1_partfun1 @ X49 @ X46 @ X46 @ X47 @ X48 @ X45))
% 1.35/1.57          | (zip_tseitin_1 @ X47 @ X46)
% 1.35/1.57          | ((k2_relset_1 @ X49 @ X46 @ X48) != (X46))
% 1.35/1.57          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X46)))
% 1.35/1.57          | ~ (v1_funct_2 @ X48 @ X49 @ X46)
% 1.35/1.57          | ~ (v1_funct_1 @ X48))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.35/1.57  thf('49', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i]:
% 1.35/1.57         (~ (v1_funct_1 @ X0)
% 1.35/1.57          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.35/1.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.35/1.57          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 1.35/1.57          | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.35/1.57          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.35/1.57          | (zip_tseitin_0 @ sk_D @ X0)
% 1.35/1.57          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.35/1.57          | ~ (v1_funct_1 @ sk_D))),
% 1.35/1.57      inference('sup-', [status(thm)], ['47', '48'])).
% 1.35/1.57  thf('50', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('51', plain, ((v1_funct_1 @ sk_D)),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('52', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i]:
% 1.35/1.57         (~ (v1_funct_1 @ X0)
% 1.35/1.57          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.35/1.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.35/1.57          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 1.35/1.57          | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.35/1.57          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.35/1.57          | (zip_tseitin_0 @ sk_D @ X0))),
% 1.35/1.57      inference('demod', [status(thm)], ['49', '50', '51'])).
% 1.35/1.57  thf('53', plain,
% 1.35/1.57      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 1.35/1.57        | (zip_tseitin_0 @ sk_D @ sk_C)
% 1.35/1.57        | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.35/1.57        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.35/1.57        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 1.35/1.57        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.35/1.57        | ~ (v1_funct_1 @ sk_C))),
% 1.35/1.57      inference('sup-', [status(thm)], ['46', '52'])).
% 1.35/1.57  thf(fc4_funct_1, axiom,
% 1.35/1.57    (![A:$i]:
% 1.35/1.57     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.35/1.57       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.35/1.57  thf('54', plain, (![X13 : $i]: (v2_funct_1 @ (k6_relat_1 @ X13))),
% 1.35/1.57      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.35/1.57  thf('55', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 1.35/1.57      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.35/1.57  thf('56', plain, (![X13 : $i]: (v2_funct_1 @ (k6_partfun1 @ X13))),
% 1.35/1.57      inference('demod', [status(thm)], ['54', '55'])).
% 1.35/1.57  thf('57', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('58', plain,
% 1.35/1.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('59', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('60', plain, ((v1_funct_1 @ sk_C)),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('61', plain,
% 1.35/1.57      (((zip_tseitin_0 @ sk_D @ sk_C)
% 1.35/1.57        | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.35/1.57        | ((sk_B) != (sk_B)))),
% 1.35/1.57      inference('demod', [status(thm)], ['53', '56', '57', '58', '59', '60'])).
% 1.35/1.57  thf('62', plain,
% 1.35/1.57      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 1.35/1.57      inference('simplify', [status(thm)], ['61'])).
% 1.35/1.57  thf('63', plain,
% 1.35/1.57      (![X43 : $i, X44 : $i]:
% 1.35/1.57         (((X43) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X43 @ X44))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.35/1.57  thf('64', plain,
% 1.35/1.57      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 1.35/1.57      inference('sup-', [status(thm)], ['62', '63'])).
% 1.35/1.57  thf('65', plain, (((sk_A) != (k1_xboole_0))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('66', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 1.35/1.57      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 1.35/1.57  thf('67', plain,
% 1.35/1.57      (![X41 : $i, X42 : $i]:
% 1.35/1.57         ((v2_funct_1 @ X42) | ~ (zip_tseitin_0 @ X42 @ X41))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.35/1.57  thf('68', plain, ((v2_funct_1 @ sk_D)),
% 1.35/1.57      inference('sup-', [status(thm)], ['66', '67'])).
% 1.35/1.57  thf('69', plain,
% 1.35/1.57      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 1.35/1.57      inference('demod', [status(thm)], ['45', '68'])).
% 1.35/1.57  thf(t58_funct_1, axiom,
% 1.35/1.57    (![A:$i]:
% 1.35/1.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.35/1.57       ( ( v2_funct_1 @ A ) =>
% 1.35/1.57         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 1.35/1.57             ( k1_relat_1 @ A ) ) & 
% 1.35/1.57           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 1.35/1.57             ( k1_relat_1 @ A ) ) ) ) ))).
% 1.35/1.57  thf('70', plain,
% 1.35/1.57      (![X15 : $i]:
% 1.35/1.57         (~ (v2_funct_1 @ X15)
% 1.35/1.57          | ((k2_relat_1 @ (k5_relat_1 @ X15 @ (k2_funct_1 @ X15)))
% 1.35/1.57              = (k1_relat_1 @ X15))
% 1.35/1.57          | ~ (v1_funct_1 @ X15)
% 1.35/1.57          | ~ (v1_relat_1 @ X15))),
% 1.35/1.57      inference('cnf', [status(esa)], [t58_funct_1])).
% 1.35/1.57  thf('71', plain,
% 1.35/1.57      ((((k2_relat_1 @ (k6_partfun1 @ sk_B)) = (k1_relat_1 @ sk_D))
% 1.35/1.57        | ~ (v1_relat_1 @ sk_D)
% 1.35/1.57        | ~ (v1_funct_1 @ sk_D)
% 1.35/1.57        | ~ (v2_funct_1 @ sk_D))),
% 1.35/1.57      inference('sup+', [status(thm)], ['69', '70'])).
% 1.35/1.57  thf(t71_relat_1, axiom,
% 1.35/1.57    (![A:$i]:
% 1.35/1.57     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.35/1.57       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.35/1.57  thf('72', plain, (![X8 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X8)) = (X8))),
% 1.35/1.57      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.35/1.57  thf('73', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 1.35/1.57      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.35/1.57  thf('74', plain, (![X8 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X8)) = (X8))),
% 1.35/1.57      inference('demod', [status(thm)], ['72', '73'])).
% 1.35/1.57  thf('75', plain,
% 1.35/1.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf(cc2_relat_1, axiom,
% 1.35/1.57    (![A:$i]:
% 1.35/1.57     ( ( v1_relat_1 @ A ) =>
% 1.35/1.57       ( ![B:$i]:
% 1.35/1.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.35/1.57  thf('76', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i]:
% 1.35/1.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.35/1.57          | (v1_relat_1 @ X0)
% 1.35/1.57          | ~ (v1_relat_1 @ X1))),
% 1.35/1.57      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.35/1.57  thf('77', plain,
% 1.35/1.57      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 1.35/1.57      inference('sup-', [status(thm)], ['75', '76'])).
% 1.35/1.57  thf(fc6_relat_1, axiom,
% 1.35/1.57    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.35/1.57  thf('78', plain,
% 1.35/1.57      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.35/1.57      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.35/1.57  thf('79', plain, ((v1_relat_1 @ sk_D)),
% 1.35/1.57      inference('demod', [status(thm)], ['77', '78'])).
% 1.35/1.57  thf('80', plain, ((v1_funct_1 @ sk_D)),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('81', plain, ((v2_funct_1 @ sk_D)),
% 1.35/1.57      inference('sup-', [status(thm)], ['66', '67'])).
% 1.35/1.57  thf('82', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.35/1.57      inference('demod', [status(thm)], ['71', '74', '79', '80', '81'])).
% 1.35/1.57  thf(t78_relat_1, axiom,
% 1.35/1.57    (![A:$i]:
% 1.35/1.57     ( ( v1_relat_1 @ A ) =>
% 1.35/1.57       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 1.35/1.57  thf('83', plain,
% 1.35/1.57      (![X9 : $i]:
% 1.35/1.57         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X9)) @ X9) = (X9))
% 1.35/1.57          | ~ (v1_relat_1 @ X9))),
% 1.35/1.57      inference('cnf', [status(esa)], [t78_relat_1])).
% 1.35/1.57  thf('84', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 1.35/1.57      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.35/1.57  thf('85', plain,
% 1.35/1.57      (![X9 : $i]:
% 1.35/1.57         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X9)) @ X9) = (X9))
% 1.35/1.57          | ~ (v1_relat_1 @ X9))),
% 1.35/1.57      inference('demod', [status(thm)], ['83', '84'])).
% 1.35/1.57  thf('86', plain,
% 1.35/1.57      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))
% 1.35/1.57        | ~ (v1_relat_1 @ sk_D))),
% 1.35/1.57      inference('sup+', [status(thm)], ['82', '85'])).
% 1.35/1.57  thf('87', plain,
% 1.35/1.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('88', plain,
% 1.35/1.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf(redefinition_k1_partfun1, axiom,
% 1.35/1.57    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.35/1.57     ( ( ( v1_funct_1 @ E ) & 
% 1.35/1.57         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.35/1.57         ( v1_funct_1 @ F ) & 
% 1.35/1.57         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.35/1.57       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.35/1.57  thf('89', plain,
% 1.35/1.57      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 1.35/1.57         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 1.35/1.57          | ~ (v1_funct_1 @ X30)
% 1.35/1.57          | ~ (v1_funct_1 @ X33)
% 1.35/1.57          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 1.35/1.57          | ((k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33)
% 1.35/1.57              = (k5_relat_1 @ X30 @ X33)))),
% 1.35/1.57      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.35/1.57  thf('90', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.57         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.35/1.57            = (k5_relat_1 @ sk_C @ X0))
% 1.35/1.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.35/1.57          | ~ (v1_funct_1 @ X0)
% 1.35/1.57          | ~ (v1_funct_1 @ sk_C))),
% 1.35/1.57      inference('sup-', [status(thm)], ['88', '89'])).
% 1.35/1.57  thf('91', plain, ((v1_funct_1 @ sk_C)),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('92', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.57         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.35/1.57            = (k5_relat_1 @ sk_C @ X0))
% 1.35/1.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.35/1.57          | ~ (v1_funct_1 @ X0))),
% 1.35/1.57      inference('demod', [status(thm)], ['90', '91'])).
% 1.35/1.57  thf('93', plain,
% 1.35/1.57      ((~ (v1_funct_1 @ sk_D)
% 1.35/1.57        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.35/1.57            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.35/1.57      inference('sup-', [status(thm)], ['87', '92'])).
% 1.35/1.57  thf('94', plain, ((v1_funct_1 @ sk_D)),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('95', plain,
% 1.35/1.57      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.35/1.57         = (k6_partfun1 @ sk_A))),
% 1.35/1.57      inference('demod', [status(thm)], ['23', '26'])).
% 1.35/1.57  thf('96', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 1.35/1.57      inference('demod', [status(thm)], ['93', '94', '95'])).
% 1.35/1.57  thf(dt_k2_funct_1, axiom,
% 1.35/1.57    (![A:$i]:
% 1.35/1.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.35/1.57       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.35/1.57         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.35/1.57  thf('97', plain,
% 1.35/1.57      (![X11 : $i]:
% 1.35/1.57         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 1.35/1.57          | ~ (v1_funct_1 @ X11)
% 1.35/1.57          | ~ (v1_relat_1 @ X11))),
% 1.35/1.57      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.35/1.57  thf('98', plain,
% 1.35/1.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('99', plain,
% 1.35/1.57      (![X50 : $i, X51 : $i, X52 : $i]:
% 1.35/1.57         (((X50) = (k1_xboole_0))
% 1.35/1.57          | ~ (v1_funct_1 @ X51)
% 1.35/1.57          | ~ (v1_funct_2 @ X51 @ X52 @ X50)
% 1.35/1.57          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X50)))
% 1.35/1.57          | ((k5_relat_1 @ (k2_funct_1 @ X51) @ X51) = (k6_partfun1 @ X50))
% 1.35/1.57          | ~ (v2_funct_1 @ X51)
% 1.35/1.57          | ((k2_relset_1 @ X52 @ X50 @ X51) != (X50)))),
% 1.35/1.57      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.35/1.57  thf('100', plain,
% 1.35/1.57      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.35/1.57        | ~ (v2_funct_1 @ sk_C)
% 1.35/1.57        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 1.35/1.57        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.35/1.57        | ~ (v1_funct_1 @ sk_C)
% 1.35/1.57        | ((sk_B) = (k1_xboole_0)))),
% 1.35/1.57      inference('sup-', [status(thm)], ['98', '99'])).
% 1.35/1.57  thf('101', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('102', plain, ((v2_funct_1 @ sk_C)),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('103', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('104', plain, ((v1_funct_1 @ sk_C)),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('105', plain,
% 1.35/1.57      ((((sk_B) != (sk_B))
% 1.35/1.57        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 1.35/1.57        | ((sk_B) = (k1_xboole_0)))),
% 1.35/1.57      inference('demod', [status(thm)], ['100', '101', '102', '103', '104'])).
% 1.35/1.57  thf('106', plain,
% 1.35/1.57      ((((sk_B) = (k1_xboole_0))
% 1.35/1.57        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B)))),
% 1.35/1.57      inference('simplify', [status(thm)], ['105'])).
% 1.35/1.57  thf('107', plain, (((sk_B) != (k1_xboole_0))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('108', plain,
% 1.35/1.57      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 1.35/1.57      inference('simplify_reflect-', [status(thm)], ['106', '107'])).
% 1.35/1.57  thf(t55_relat_1, axiom,
% 1.35/1.57    (![A:$i]:
% 1.35/1.57     ( ( v1_relat_1 @ A ) =>
% 1.35/1.57       ( ![B:$i]:
% 1.35/1.57         ( ( v1_relat_1 @ B ) =>
% 1.35/1.57           ( ![C:$i]:
% 1.35/1.57             ( ( v1_relat_1 @ C ) =>
% 1.35/1.57               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 1.35/1.57                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 1.35/1.57  thf('109', plain,
% 1.35/1.57      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.35/1.57         (~ (v1_relat_1 @ X4)
% 1.35/1.57          | ((k5_relat_1 @ (k5_relat_1 @ X5 @ X4) @ X6)
% 1.35/1.57              = (k5_relat_1 @ X5 @ (k5_relat_1 @ X4 @ X6)))
% 1.35/1.57          | ~ (v1_relat_1 @ X6)
% 1.35/1.57          | ~ (v1_relat_1 @ X5))),
% 1.35/1.57      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.35/1.57  thf('110', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.35/1.57            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 1.35/1.57          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.35/1.57          | ~ (v1_relat_1 @ X0)
% 1.35/1.57          | ~ (v1_relat_1 @ sk_C))),
% 1.35/1.57      inference('sup+', [status(thm)], ['108', '109'])).
% 1.35/1.57  thf('111', plain,
% 1.35/1.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('112', plain,
% 1.35/1.57      (![X0 : $i, X1 : $i]:
% 1.35/1.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.35/1.57          | (v1_relat_1 @ X0)
% 1.35/1.57          | ~ (v1_relat_1 @ X1))),
% 1.35/1.57      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.35/1.57  thf('113', plain,
% 1.35/1.57      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 1.35/1.57      inference('sup-', [status(thm)], ['111', '112'])).
% 1.35/1.57  thf('114', plain,
% 1.35/1.57      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.35/1.57      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.35/1.57  thf('115', plain, ((v1_relat_1 @ sk_C)),
% 1.35/1.57      inference('demod', [status(thm)], ['113', '114'])).
% 1.35/1.57  thf('116', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.35/1.57            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 1.35/1.57          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.35/1.57          | ~ (v1_relat_1 @ X0))),
% 1.35/1.57      inference('demod', [status(thm)], ['110', '115'])).
% 1.35/1.57  thf('117', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (~ (v1_relat_1 @ sk_C)
% 1.35/1.57          | ~ (v1_funct_1 @ sk_C)
% 1.35/1.57          | ~ (v1_relat_1 @ X0)
% 1.35/1.57          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.35/1.57              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 1.35/1.57      inference('sup-', [status(thm)], ['97', '116'])).
% 1.35/1.57  thf('118', plain, ((v1_relat_1 @ sk_C)),
% 1.35/1.57      inference('demod', [status(thm)], ['113', '114'])).
% 1.35/1.57  thf('119', plain, ((v1_funct_1 @ sk_C)),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('120', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (~ (v1_relat_1 @ X0)
% 1.35/1.57          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.35/1.57              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 1.35/1.57      inference('demod', [status(thm)], ['117', '118', '119'])).
% 1.35/1.57  thf('121', plain,
% 1.35/1.57      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 1.35/1.57          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 1.35/1.57        | ~ (v1_relat_1 @ sk_D))),
% 1.35/1.57      inference('sup+', [status(thm)], ['96', '120'])).
% 1.35/1.57  thf('122', plain,
% 1.35/1.57      (![X11 : $i]:
% 1.35/1.57         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 1.35/1.57          | ~ (v1_funct_1 @ X11)
% 1.35/1.57          | ~ (v1_relat_1 @ X11))),
% 1.35/1.57      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.35/1.57  thf(t55_funct_1, axiom,
% 1.35/1.57    (![A:$i]:
% 1.35/1.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.35/1.57       ( ( v2_funct_1 @ A ) =>
% 1.35/1.57         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.35/1.57           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.35/1.57  thf('123', plain,
% 1.35/1.57      (![X14 : $i]:
% 1.35/1.57         (~ (v2_funct_1 @ X14)
% 1.35/1.57          | ((k1_relat_1 @ X14) = (k2_relat_1 @ (k2_funct_1 @ X14)))
% 1.35/1.57          | ~ (v1_funct_1 @ X14)
% 1.35/1.57          | ~ (v1_relat_1 @ X14))),
% 1.35/1.57      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.35/1.57  thf(t80_relat_1, axiom,
% 1.35/1.57    (![A:$i]:
% 1.35/1.57     ( ( v1_relat_1 @ A ) =>
% 1.35/1.57       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 1.35/1.57  thf('124', plain,
% 1.35/1.57      (![X10 : $i]:
% 1.35/1.57         (((k5_relat_1 @ X10 @ (k6_relat_1 @ (k2_relat_1 @ X10))) = (X10))
% 1.35/1.57          | ~ (v1_relat_1 @ X10))),
% 1.35/1.57      inference('cnf', [status(esa)], [t80_relat_1])).
% 1.35/1.57  thf('125', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 1.35/1.57      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.35/1.57  thf('126', plain,
% 1.35/1.57      (![X10 : $i]:
% 1.35/1.57         (((k5_relat_1 @ X10 @ (k6_partfun1 @ (k2_relat_1 @ X10))) = (X10))
% 1.35/1.57          | ~ (v1_relat_1 @ X10))),
% 1.35/1.57      inference('demod', [status(thm)], ['124', '125'])).
% 1.35/1.57  thf('127', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 1.35/1.57            = (k2_funct_1 @ X0))
% 1.35/1.57          | ~ (v1_relat_1 @ X0)
% 1.35/1.57          | ~ (v1_funct_1 @ X0)
% 1.35/1.57          | ~ (v2_funct_1 @ X0)
% 1.35/1.57          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.35/1.57      inference('sup+', [status(thm)], ['123', '126'])).
% 1.35/1.57  thf('128', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (~ (v1_relat_1 @ X0)
% 1.35/1.57          | ~ (v1_funct_1 @ X0)
% 1.35/1.57          | ~ (v2_funct_1 @ X0)
% 1.35/1.57          | ~ (v1_funct_1 @ X0)
% 1.35/1.57          | ~ (v1_relat_1 @ X0)
% 1.35/1.57          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 1.35/1.57              (k6_partfun1 @ (k1_relat_1 @ X0))) = (k2_funct_1 @ X0)))),
% 1.35/1.57      inference('sup-', [status(thm)], ['122', '127'])).
% 1.35/1.57  thf('129', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 1.35/1.57            = (k2_funct_1 @ X0))
% 1.35/1.57          | ~ (v2_funct_1 @ X0)
% 1.35/1.57          | ~ (v1_funct_1 @ X0)
% 1.35/1.57          | ~ (v1_relat_1 @ X0))),
% 1.35/1.57      inference('simplify', [status(thm)], ['128'])).
% 1.35/1.57  thf('130', plain,
% 1.35/1.57      (![X11 : $i]:
% 1.35/1.57         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 1.35/1.57          | ~ (v1_funct_1 @ X11)
% 1.35/1.57          | ~ (v1_relat_1 @ X11))),
% 1.35/1.57      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.35/1.57  thf('131', plain,
% 1.35/1.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('132', plain,
% 1.35/1.57      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.35/1.57         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 1.35/1.57          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.35/1.57      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.35/1.57  thf('133', plain,
% 1.35/1.57      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.35/1.57      inference('sup-', [status(thm)], ['131', '132'])).
% 1.35/1.57  thf('134', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('135', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.35/1.57      inference('sup+', [status(thm)], ['133', '134'])).
% 1.35/1.57  thf('136', plain,
% 1.35/1.57      (![X11 : $i]:
% 1.35/1.57         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 1.35/1.57          | ~ (v1_funct_1 @ X11)
% 1.35/1.57          | ~ (v1_relat_1 @ X11))),
% 1.35/1.57      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.35/1.57  thf('137', plain,
% 1.35/1.57      (![X14 : $i]:
% 1.35/1.57         (~ (v2_funct_1 @ X14)
% 1.35/1.57          | ((k2_relat_1 @ X14) = (k1_relat_1 @ (k2_funct_1 @ X14)))
% 1.35/1.57          | ~ (v1_funct_1 @ X14)
% 1.35/1.57          | ~ (v1_relat_1 @ X14))),
% 1.35/1.57      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.35/1.57  thf('138', plain,
% 1.35/1.57      (![X9 : $i]:
% 1.35/1.57         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X9)) @ X9) = (X9))
% 1.35/1.57          | ~ (v1_relat_1 @ X9))),
% 1.35/1.57      inference('demod', [status(thm)], ['83', '84'])).
% 1.35/1.57  thf('139', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 1.35/1.57            = (k2_funct_1 @ X0))
% 1.35/1.57          | ~ (v1_relat_1 @ X0)
% 1.35/1.57          | ~ (v1_funct_1 @ X0)
% 1.35/1.57          | ~ (v2_funct_1 @ X0)
% 1.35/1.57          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.35/1.57      inference('sup+', [status(thm)], ['137', '138'])).
% 1.35/1.57  thf('140', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (~ (v1_relat_1 @ X0)
% 1.35/1.57          | ~ (v1_funct_1 @ X0)
% 1.35/1.57          | ~ (v2_funct_1 @ X0)
% 1.35/1.57          | ~ (v1_funct_1 @ X0)
% 1.35/1.57          | ~ (v1_relat_1 @ X0)
% 1.35/1.57          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 1.35/1.57              (k2_funct_1 @ X0)) = (k2_funct_1 @ X0)))),
% 1.35/1.57      inference('sup-', [status(thm)], ['136', '139'])).
% 1.35/1.57  thf('141', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 1.35/1.57            = (k2_funct_1 @ X0))
% 1.35/1.57          | ~ (v2_funct_1 @ X0)
% 1.35/1.57          | ~ (v1_funct_1 @ X0)
% 1.35/1.57          | ~ (v1_relat_1 @ X0))),
% 1.35/1.57      inference('simplify', [status(thm)], ['140'])).
% 1.35/1.57  thf('142', plain,
% 1.35/1.57      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.35/1.57          = (k2_funct_1 @ sk_C))
% 1.35/1.57        | ~ (v1_relat_1 @ sk_C)
% 1.35/1.57        | ~ (v1_funct_1 @ sk_C)
% 1.35/1.57        | ~ (v2_funct_1 @ sk_C))),
% 1.35/1.57      inference('sup+', [status(thm)], ['135', '141'])).
% 1.35/1.57  thf('143', plain, ((v1_relat_1 @ sk_C)),
% 1.35/1.57      inference('demod', [status(thm)], ['113', '114'])).
% 1.35/1.57  thf('144', plain, ((v1_funct_1 @ sk_C)),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('145', plain, ((v2_funct_1 @ sk_C)),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('146', plain,
% 1.35/1.57      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.35/1.57         = (k2_funct_1 @ sk_C))),
% 1.35/1.57      inference('demod', [status(thm)], ['142', '143', '144', '145'])).
% 1.35/1.57  thf('147', plain,
% 1.35/1.57      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.35/1.57         (~ (v1_relat_1 @ X4)
% 1.35/1.57          | ((k5_relat_1 @ (k5_relat_1 @ X5 @ X4) @ X6)
% 1.35/1.57              = (k5_relat_1 @ X5 @ (k5_relat_1 @ X4 @ X6)))
% 1.35/1.57          | ~ (v1_relat_1 @ X6)
% 1.35/1.57          | ~ (v1_relat_1 @ X5))),
% 1.35/1.57      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.35/1.57  thf('148', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 1.35/1.57            = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.35/1.57               (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)))
% 1.35/1.57          | ~ (v1_relat_1 @ (k6_partfun1 @ sk_B))
% 1.35/1.57          | ~ (v1_relat_1 @ X0)
% 1.35/1.57          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.35/1.57      inference('sup+', [status(thm)], ['146', '147'])).
% 1.35/1.57  thf('149', plain, (![X12 : $i]: (v1_relat_1 @ (k6_relat_1 @ X12))),
% 1.35/1.57      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.35/1.57  thf('150', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 1.35/1.57      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.35/1.57  thf('151', plain, (![X12 : $i]: (v1_relat_1 @ (k6_partfun1 @ X12))),
% 1.35/1.57      inference('demod', [status(thm)], ['149', '150'])).
% 1.35/1.57  thf('152', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 1.35/1.57            = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.35/1.57               (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)))
% 1.35/1.57          | ~ (v1_relat_1 @ X0)
% 1.35/1.57          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.35/1.57      inference('demod', [status(thm)], ['148', '151'])).
% 1.35/1.57  thf('153', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (~ (v1_relat_1 @ sk_C)
% 1.35/1.57          | ~ (v1_funct_1 @ sk_C)
% 1.35/1.57          | ~ (v1_relat_1 @ X0)
% 1.35/1.57          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 1.35/1.57              = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.35/1.57                 (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))))),
% 1.35/1.57      inference('sup-', [status(thm)], ['130', '152'])).
% 1.35/1.57  thf('154', plain, ((v1_relat_1 @ sk_C)),
% 1.35/1.57      inference('demod', [status(thm)], ['113', '114'])).
% 1.35/1.57  thf('155', plain, ((v1_funct_1 @ sk_C)),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('156', plain,
% 1.35/1.57      (![X0 : $i]:
% 1.35/1.57         (~ (v1_relat_1 @ X0)
% 1.35/1.57          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 1.35/1.57              = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.35/1.57                 (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))))),
% 1.35/1.57      inference('demod', [status(thm)], ['153', '154', '155'])).
% 1.35/1.57  thf('157', plain,
% 1.35/1.57      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 1.35/1.57          (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 1.35/1.57          = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C)))
% 1.35/1.57        | ~ (v1_relat_1 @ sk_C)
% 1.35/1.57        | ~ (v1_funct_1 @ sk_C)
% 1.35/1.57        | ~ (v2_funct_1 @ sk_C)
% 1.35/1.57        | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C))))),
% 1.35/1.57      inference('sup+', [status(thm)], ['129', '156'])).
% 1.35/1.57  thf('158', plain,
% 1.35/1.57      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.35/1.57         = (k2_funct_1 @ sk_C))),
% 1.35/1.57      inference('demod', [status(thm)], ['142', '143', '144', '145'])).
% 1.35/1.57  thf('159', plain, ((v1_relat_1 @ sk_C)),
% 1.35/1.57      inference('demod', [status(thm)], ['113', '114'])).
% 1.35/1.57  thf('160', plain, ((v1_funct_1 @ sk_C)),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('161', plain, ((v2_funct_1 @ sk_C)),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('162', plain, (![X12 : $i]: (v1_relat_1 @ (k6_partfun1 @ X12))),
% 1.35/1.57      inference('demod', [status(thm)], ['149', '150'])).
% 1.35/1.57  thf('163', plain,
% 1.35/1.57      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 1.35/1.57         = (k2_funct_1 @ sk_C))),
% 1.35/1.57      inference('demod', [status(thm)],
% 1.35/1.57                ['157', '158', '159', '160', '161', '162'])).
% 1.35/1.57  thf('164', plain,
% 1.35/1.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('165', plain,
% 1.35/1.57      (![X50 : $i, X51 : $i, X52 : $i]:
% 1.35/1.57         (((X50) = (k1_xboole_0))
% 1.35/1.57          | ~ (v1_funct_1 @ X51)
% 1.35/1.57          | ~ (v1_funct_2 @ X51 @ X52 @ X50)
% 1.35/1.57          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X50)))
% 1.35/1.57          | ((k5_relat_1 @ X51 @ (k2_funct_1 @ X51)) = (k6_partfun1 @ X52))
% 1.35/1.57          | ~ (v2_funct_1 @ X51)
% 1.35/1.57          | ((k2_relset_1 @ X52 @ X50 @ X51) != (X50)))),
% 1.35/1.57      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.35/1.57  thf('166', plain,
% 1.35/1.57      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.35/1.57        | ~ (v2_funct_1 @ sk_C)
% 1.35/1.57        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 1.35/1.57        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.35/1.57        | ~ (v1_funct_1 @ sk_C)
% 1.35/1.57        | ((sk_B) = (k1_xboole_0)))),
% 1.35/1.57      inference('sup-', [status(thm)], ['164', '165'])).
% 1.35/1.57  thf('167', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('168', plain, ((v2_funct_1 @ sk_C)),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('169', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('170', plain, ((v1_funct_1 @ sk_C)),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('171', plain,
% 1.35/1.57      ((((sk_B) != (sk_B))
% 1.35/1.57        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 1.35/1.57        | ((sk_B) = (k1_xboole_0)))),
% 1.35/1.57      inference('demod', [status(thm)], ['166', '167', '168', '169', '170'])).
% 1.35/1.57  thf('172', plain,
% 1.35/1.57      ((((sk_B) = (k1_xboole_0))
% 1.35/1.57        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 1.35/1.57      inference('simplify', [status(thm)], ['171'])).
% 1.35/1.57  thf('173', plain, (((sk_B) != (k1_xboole_0))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('174', plain,
% 1.35/1.57      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 1.35/1.57      inference('simplify_reflect-', [status(thm)], ['172', '173'])).
% 1.35/1.57  thf('175', plain,
% 1.35/1.57      (![X15 : $i]:
% 1.35/1.57         (~ (v2_funct_1 @ X15)
% 1.35/1.57          | ((k2_relat_1 @ (k5_relat_1 @ X15 @ (k2_funct_1 @ X15)))
% 1.35/1.57              = (k1_relat_1 @ X15))
% 1.35/1.57          | ~ (v1_funct_1 @ X15)
% 1.35/1.57          | ~ (v1_relat_1 @ X15))),
% 1.35/1.57      inference('cnf', [status(esa)], [t58_funct_1])).
% 1.35/1.57  thf('176', plain,
% 1.35/1.57      ((((k2_relat_1 @ (k6_partfun1 @ sk_A)) = (k1_relat_1 @ sk_C))
% 1.35/1.57        | ~ (v1_relat_1 @ sk_C)
% 1.35/1.57        | ~ (v1_funct_1 @ sk_C)
% 1.35/1.57        | ~ (v2_funct_1 @ sk_C))),
% 1.35/1.57      inference('sup+', [status(thm)], ['174', '175'])).
% 1.35/1.57  thf('177', plain, (![X8 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X8)) = (X8))),
% 1.35/1.57      inference('demod', [status(thm)], ['72', '73'])).
% 1.35/1.57  thf('178', plain, ((v1_relat_1 @ sk_C)),
% 1.35/1.57      inference('demod', [status(thm)], ['113', '114'])).
% 1.35/1.57  thf('179', plain, ((v1_funct_1 @ sk_C)),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('180', plain, ((v2_funct_1 @ sk_C)),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('181', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 1.35/1.57      inference('demod', [status(thm)], ['176', '177', '178', '179', '180'])).
% 1.35/1.57  thf('182', plain,
% 1.35/1.57      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 1.35/1.57         = (k2_funct_1 @ sk_C))),
% 1.35/1.57      inference('demod', [status(thm)], ['163', '181'])).
% 1.35/1.57  thf('183', plain, ((v1_relat_1 @ sk_D)),
% 1.35/1.57      inference('demod', [status(thm)], ['77', '78'])).
% 1.35/1.57  thf('184', plain,
% 1.35/1.57      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (k2_funct_1 @ sk_C))),
% 1.35/1.57      inference('demod', [status(thm)], ['121', '182', '183'])).
% 1.35/1.57  thf('185', plain, ((v1_relat_1 @ sk_D)),
% 1.35/1.57      inference('demod', [status(thm)], ['77', '78'])).
% 1.35/1.57  thf('186', plain, (((k2_funct_1 @ sk_C) = (sk_D))),
% 1.35/1.57      inference('demod', [status(thm)], ['86', '184', '185'])).
% 1.35/1.57  thf('187', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.35/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.57  thf('188', plain, ($false),
% 1.35/1.57      inference('simplify_reflect-', [status(thm)], ['186', '187'])).
% 1.35/1.57  
% 1.35/1.57  % SZS output end Refutation
% 1.35/1.57  
% 1.35/1.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

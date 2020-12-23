%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KDotbfHWgL

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:08 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :  226 (1078 expanded)
%              Number of leaves         :   48 ( 340 expanded)
%              Depth                    :   29
%              Number of atoms          : 2140 (27638 expanded)
%              Number of equality atoms :  165 (1831 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

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
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( X49 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_funct_2 @ X50 @ X51 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X49 ) ) )
      | ( ( k5_relat_1 @ X50 @ ( k2_funct_1 @ X50 ) )
        = ( k6_partfun1 @ X51 ) )
      | ~ ( v2_funct_1 @ X50 )
      | ( ( k2_relset_1 @ X51 @ X49 @ X50 )
       != X49 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X28 ) ) ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( X18 = X21 )
      | ~ ( r2_relset_1 @ X19 @ X20 @ X18 @ X21 ) ) ),
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
    ! [X22: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('25',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('26',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ),
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
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( r2_relset_1 @ X37 @ X37 @ ( k1_partfun1 @ X37 @ X38 @ X38 @ X37 @ X36 @ X39 ) @ ( k6_partfun1 @ X37 ) )
      | ( ( k2_relset_1 @ X38 @ X37 @ X39 )
        = X37 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X38 @ X37 )
      | ~ ( v1_funct_1 @ X39 ) ) ),
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
    ! [X22: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('36',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( r2_relset_1 @ X19 @ X20 @ X18 @ X21 )
      | ( X18 != X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('37',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r2_relset_1 @ X19 @ X20 @ X21 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
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
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ( zip_tseitin_0 @ X44 @ X47 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X48 @ X45 @ X45 @ X46 @ X47 @ X44 ) )
      | ( zip_tseitin_1 @ X46 @ X45 )
      | ( ( k2_relset_1 @ X48 @ X45 @ X47 )
       != X45 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X45 ) ) )
      | ~ ( v1_funct_2 @ X47 @ X48 @ X45 )
      | ~ ( v1_funct_1 @ X47 ) ) ),
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
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('55',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('56',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X7 ) ) ),
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
    ! [X42: $i,X43: $i] :
      ( ( X42 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X42 @ X43 ) ) ),
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
    ! [X40: $i,X41: $i] :
      ( ( v2_funct_1 @ X41 )
      | ~ ( zip_tseitin_0 @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('68',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['45','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
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

thf('72',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32 )
        = ( k5_relat_1 @ X29 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['70','75'])).

thf('77',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('79',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['76','77','78'])).

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

thf('80',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( X10
        = ( k2_funct_1 @ X11 ) )
      | ( ( k5_relat_1 @ X10 @ X11 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X11 ) ) )
      | ( ( k2_relat_1 @ X10 )
       != ( k1_relat_1 @ X11 ) )
      | ~ ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('81',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('82',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( X10
        = ( k2_funct_1 @ X11 ) )
      | ( ( k5_relat_1 @ X10 @ X11 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X11 ) ) )
      | ( ( k2_relat_1 @ X10 )
       != ( k1_relat_1 @ X11 ) )
      | ~ ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
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
    inference('sup-',[status(thm)],['79','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('85',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('86',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('90',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('96',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['83','86','87','92','93','96'])).

thf('98',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['34','38','39','40','41','42'])).

thf('99',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['66','67'])).

thf('102',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('103',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k10_relat_1 @ X8 @ X9 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X8 ) @ X9 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('104',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('105',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['45','68'])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k9_relat_1 @ X0 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('107',plain,
    ( ( ( k2_relat_1 @ ( k6_partfun1 @ sk_B ) )
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('108',plain,(
    ! [X4: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('109',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('110',plain,(
    ! [X4: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['34','38','39','40','41','42'])).

thf('112',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['84','85'])).

thf('113',plain,
    ( ( sk_B
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_D ) @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['107','110','111','112'])).

thf('114',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_B
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_D ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['104','113'])).

thf('115',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['84','85'])).

thf('116',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( sk_B
    = ( k9_relat_1 @ ( k2_funct_1 @ sk_D ) @ sk_A ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,
    ( ( sk_B
      = ( k10_relat_1 @ sk_D @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['103','117'])).

thf('119',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['34','38','39','40','41','42'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('120',plain,(
    ! [X2: $i] :
      ( ( ( k10_relat_1 @ X2 @ ( k2_relat_1 @ X2 ) )
        = ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('121',plain,
    ( ( ( k10_relat_1 @ sk_D @ sk_A )
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['84','85'])).

thf('123',plain,
    ( ( k10_relat_1 @ sk_D @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['84','85'])).

thf('125',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['66','67'])).

thf('127',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['118','123','124','125','126'])).

thf('128',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['102','127'])).

thf('129',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,
    ( ( k5_relat_1 @ sk_D @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['69','129'])).

thf('131',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( X10
        = ( k2_funct_1 @ X11 ) )
      | ( ( k5_relat_1 @ X10 @ X11 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X11 ) ) )
      | ( ( k2_relat_1 @ X10 )
       != ( k1_relat_1 @ X11 ) )
      | ~ ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('132',plain,
    ( ( ( k6_partfun1 @ sk_B )
     != ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_D )
     != ( k1_relat_1 @ sk_C ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['90','91'])).

thf('134',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['94','95'])).

thf('135',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['34','38','39','40','41','42'])).

thf('138',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k10_relat_1 @ X8 @ X9 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X8 ) @ X9 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('139',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('140',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( X49 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_funct_2 @ X50 @ X51 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X49 ) ) )
      | ( ( k5_relat_1 @ X50 @ ( k2_funct_1 @ X50 ) )
        = ( k6_partfun1 @ X51 ) )
      | ~ ( v2_funct_1 @ X50 )
      | ( ( k2_relset_1 @ X51 @ X49 @ X50 )
       != X49 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('142',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['142','143','144','145','146'])).

thf('148',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k9_relat_1 @ X0 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('152',plain,
    ( ( ( k2_relat_1 @ ( k6_partfun1 @ sk_A ) )
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X4: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('154',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['90','91'])).

thf('155',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['94','95'])).

thf('156',plain,
    ( ( sk_A
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['152','153','154','155'])).

thf('157',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_A
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['139','156'])).

thf('158',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['94','95'])).

thf('159',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( sk_A
    = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['157','158','159'])).

thf('161',plain,
    ( ( sk_A
      = ( k10_relat_1 @ sk_C @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['138','160'])).

thf('162',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['90','91'])).

thf('163',plain,(
    ! [X2: $i] :
      ( ( ( k10_relat_1 @ X2 @ ( k2_relat_1 @ X2 ) )
        = ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('164',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_B )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['162','163'])).

thf('165',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['94','95'])).

thf('166',plain,
    ( ( k10_relat_1 @ sk_C @ sk_B )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['94','95'])).

thf('168',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['161','166','167','168','169'])).

thf('171',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['84','85'])).

thf('173',plain,
    ( ( ( k6_partfun1 @ sk_B )
     != ( k6_partfun1 @ sk_B ) )
    | ( sk_A != sk_A )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['132','133','134','135','136','137','170','171','172'])).

thf('174',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['174','175'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KDotbfHWgL
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:02:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.27/1.44  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.27/1.44  % Solved by: fo/fo7.sh
% 1.27/1.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.27/1.44  % done 837 iterations in 1.015s
% 1.27/1.44  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.27/1.44  % SZS output start Refutation
% 1.27/1.44  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.27/1.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.27/1.44  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.27/1.44  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.27/1.44  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.27/1.44  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.27/1.44  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.27/1.44  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.27/1.44  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.27/1.44  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.27/1.44  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.27/1.44  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.27/1.44  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.27/1.44  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.27/1.44  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.27/1.44  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.27/1.44  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.27/1.44  thf(sk_C_type, type, sk_C: $i).
% 1.27/1.44  thf(sk_D_type, type, sk_D: $i).
% 1.27/1.44  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.27/1.44  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.27/1.44  thf(sk_B_type, type, sk_B: $i).
% 1.27/1.44  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 1.27/1.44  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.27/1.44  thf(sk_A_type, type, sk_A: $i).
% 1.27/1.44  thf(t36_funct_2, conjecture,
% 1.27/1.44    (![A:$i,B:$i,C:$i]:
% 1.27/1.44     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.27/1.44         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.27/1.44       ( ![D:$i]:
% 1.27/1.44         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.27/1.44             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.27/1.44           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.27/1.44               ( r2_relset_1 @
% 1.27/1.44                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.27/1.44                 ( k6_partfun1 @ A ) ) & 
% 1.27/1.44               ( v2_funct_1 @ C ) ) =>
% 1.27/1.44             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.27/1.44               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.27/1.44  thf(zf_stmt_0, negated_conjecture,
% 1.27/1.44    (~( ![A:$i,B:$i,C:$i]:
% 1.27/1.44        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.27/1.44            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.27/1.44          ( ![D:$i]:
% 1.27/1.44            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.27/1.44                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.27/1.44              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.27/1.44                  ( r2_relset_1 @
% 1.27/1.44                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.27/1.44                    ( k6_partfun1 @ A ) ) & 
% 1.27/1.44                  ( v2_funct_1 @ C ) ) =>
% 1.27/1.44                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.27/1.44                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.27/1.44    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.27/1.44  thf('0', plain,
% 1.27/1.44      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.27/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.44  thf(t35_funct_2, axiom,
% 1.27/1.44    (![A:$i,B:$i,C:$i]:
% 1.27/1.44     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.27/1.44         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.27/1.44       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.27/1.44         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.27/1.44           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 1.27/1.44             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 1.27/1.44  thf('1', plain,
% 1.27/1.44      (![X49 : $i, X50 : $i, X51 : $i]:
% 1.27/1.44         (((X49) = (k1_xboole_0))
% 1.27/1.44          | ~ (v1_funct_1 @ X50)
% 1.27/1.44          | ~ (v1_funct_2 @ X50 @ X51 @ X49)
% 1.27/1.44          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X49)))
% 1.27/1.44          | ((k5_relat_1 @ X50 @ (k2_funct_1 @ X50)) = (k6_partfun1 @ X51))
% 1.27/1.44          | ~ (v2_funct_1 @ X50)
% 1.27/1.44          | ((k2_relset_1 @ X51 @ X49 @ X50) != (X49)))),
% 1.27/1.44      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.27/1.44  thf('2', plain,
% 1.27/1.44      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 1.27/1.44        | ~ (v2_funct_1 @ sk_D)
% 1.27/1.44        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.27/1.44        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.27/1.44        | ~ (v1_funct_1 @ sk_D)
% 1.27/1.44        | ((sk_A) = (k1_xboole_0)))),
% 1.27/1.44      inference('sup-', [status(thm)], ['0', '1'])).
% 1.27/1.44  thf('3', plain,
% 1.27/1.44      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.27/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.44  thf(redefinition_k2_relset_1, axiom,
% 1.27/1.44    (![A:$i,B:$i,C:$i]:
% 1.27/1.44     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.27/1.44       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.27/1.44  thf('4', plain,
% 1.27/1.44      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.27/1.44         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 1.27/1.44          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 1.27/1.44      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.27/1.44  thf('5', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.27/1.44      inference('sup-', [status(thm)], ['3', '4'])).
% 1.27/1.44  thf('6', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.27/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.44  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 1.27/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.44  thf('8', plain,
% 1.27/1.44      ((((k2_relat_1 @ sk_D) != (sk_A))
% 1.27/1.44        | ~ (v2_funct_1 @ sk_D)
% 1.27/1.44        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.27/1.44        | ((sk_A) = (k1_xboole_0)))),
% 1.27/1.44      inference('demod', [status(thm)], ['2', '5', '6', '7'])).
% 1.27/1.44  thf('9', plain, (((sk_A) != (k1_xboole_0))),
% 1.27/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.44  thf('10', plain,
% 1.27/1.44      ((((k2_relat_1 @ sk_D) != (sk_A))
% 1.27/1.44        | ~ (v2_funct_1 @ sk_D)
% 1.27/1.44        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 1.27/1.44      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 1.27/1.44  thf('11', plain,
% 1.27/1.44      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.27/1.44        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.27/1.44        (k6_partfun1 @ sk_A))),
% 1.27/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.44  thf('12', plain,
% 1.27/1.44      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.27/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.44  thf('13', plain,
% 1.27/1.44      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.27/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.44  thf(dt_k1_partfun1, axiom,
% 1.27/1.44    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.27/1.44     ( ( ( v1_funct_1 @ E ) & 
% 1.27/1.44         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.27/1.44         ( v1_funct_1 @ F ) & 
% 1.27/1.44         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.27/1.44       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.27/1.44         ( m1_subset_1 @
% 1.27/1.44           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.27/1.44           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.27/1.44  thf('14', plain,
% 1.27/1.44      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.27/1.44         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 1.27/1.44          | ~ (v1_funct_1 @ X23)
% 1.27/1.44          | ~ (v1_funct_1 @ X26)
% 1.27/1.44          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 1.27/1.44          | (m1_subset_1 @ (k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26) @ 
% 1.27/1.44             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X28))))),
% 1.27/1.44      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.27/1.44  thf('15', plain,
% 1.27/1.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.27/1.44         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.27/1.44           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.27/1.44          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.27/1.44          | ~ (v1_funct_1 @ X1)
% 1.27/1.44          | ~ (v1_funct_1 @ sk_C))),
% 1.27/1.44      inference('sup-', [status(thm)], ['13', '14'])).
% 1.27/1.44  thf('16', plain, ((v1_funct_1 @ sk_C)),
% 1.27/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.44  thf('17', plain,
% 1.27/1.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.27/1.44         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.27/1.44           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.27/1.44          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.27/1.44          | ~ (v1_funct_1 @ X1))),
% 1.27/1.44      inference('demod', [status(thm)], ['15', '16'])).
% 1.27/1.44  thf('18', plain,
% 1.27/1.44      ((~ (v1_funct_1 @ sk_D)
% 1.27/1.44        | (m1_subset_1 @ 
% 1.27/1.44           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.27/1.44           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.27/1.44      inference('sup-', [status(thm)], ['12', '17'])).
% 1.27/1.44  thf('19', plain, ((v1_funct_1 @ sk_D)),
% 1.27/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.44  thf('20', plain,
% 1.27/1.44      ((m1_subset_1 @ 
% 1.27/1.44        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.27/1.44        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.27/1.44      inference('demod', [status(thm)], ['18', '19'])).
% 1.27/1.44  thf(redefinition_r2_relset_1, axiom,
% 1.27/1.44    (![A:$i,B:$i,C:$i,D:$i]:
% 1.27/1.44     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.27/1.44         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.27/1.44       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.27/1.44  thf('21', plain,
% 1.27/1.44      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.27/1.44         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 1.27/1.44          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 1.27/1.44          | ((X18) = (X21))
% 1.27/1.44          | ~ (r2_relset_1 @ X19 @ X20 @ X18 @ X21))),
% 1.27/1.44      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.27/1.44  thf('22', plain,
% 1.27/1.44      (![X0 : $i]:
% 1.27/1.44         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.27/1.44             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 1.27/1.44          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 1.27/1.44          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.27/1.44      inference('sup-', [status(thm)], ['20', '21'])).
% 1.27/1.44  thf('23', plain,
% 1.27/1.44      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 1.27/1.44           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.27/1.44        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.27/1.44            = (k6_partfun1 @ sk_A)))),
% 1.27/1.44      inference('sup-', [status(thm)], ['11', '22'])).
% 1.27/1.44  thf(t29_relset_1, axiom,
% 1.27/1.44    (![A:$i]:
% 1.27/1.44     ( m1_subset_1 @
% 1.27/1.44       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 1.27/1.44  thf('24', plain,
% 1.27/1.44      (![X22 : $i]:
% 1.27/1.44         (m1_subset_1 @ (k6_relat_1 @ X22) @ 
% 1.27/1.44          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))),
% 1.27/1.44      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.27/1.44  thf(redefinition_k6_partfun1, axiom,
% 1.27/1.44    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.27/1.44  thf('25', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 1.27/1.44      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.27/1.44  thf('26', plain,
% 1.27/1.44      (![X22 : $i]:
% 1.27/1.44         (m1_subset_1 @ (k6_partfun1 @ X22) @ 
% 1.27/1.44          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))),
% 1.27/1.44      inference('demod', [status(thm)], ['24', '25'])).
% 1.27/1.44  thf('27', plain,
% 1.27/1.44      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.27/1.44         = (k6_partfun1 @ sk_A))),
% 1.27/1.44      inference('demod', [status(thm)], ['23', '26'])).
% 1.27/1.44  thf('28', plain,
% 1.27/1.44      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.27/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.44  thf(t24_funct_2, axiom,
% 1.27/1.44    (![A:$i,B:$i,C:$i]:
% 1.27/1.44     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.27/1.44         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.27/1.44       ( ![D:$i]:
% 1.27/1.44         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.27/1.44             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.27/1.44           ( ( r2_relset_1 @
% 1.27/1.44               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 1.27/1.44               ( k6_partfun1 @ B ) ) =>
% 1.27/1.44             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 1.27/1.44  thf('29', plain,
% 1.27/1.44      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 1.27/1.44         (~ (v1_funct_1 @ X36)
% 1.27/1.44          | ~ (v1_funct_2 @ X36 @ X37 @ X38)
% 1.27/1.44          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 1.27/1.44          | ~ (r2_relset_1 @ X37 @ X37 @ 
% 1.27/1.44               (k1_partfun1 @ X37 @ X38 @ X38 @ X37 @ X36 @ X39) @ 
% 1.27/1.44               (k6_partfun1 @ X37))
% 1.27/1.44          | ((k2_relset_1 @ X38 @ X37 @ X39) = (X37))
% 1.27/1.44          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 1.27/1.44          | ~ (v1_funct_2 @ X39 @ X38 @ X37)
% 1.27/1.44          | ~ (v1_funct_1 @ X39))),
% 1.27/1.44      inference('cnf', [status(esa)], [t24_funct_2])).
% 1.27/1.44  thf('30', plain,
% 1.27/1.44      (![X0 : $i]:
% 1.27/1.44         (~ (v1_funct_1 @ X0)
% 1.27/1.44          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.27/1.44          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.27/1.44          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.27/1.44          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.27/1.44               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.27/1.44               (k6_partfun1 @ sk_A))
% 1.27/1.44          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.27/1.44          | ~ (v1_funct_1 @ sk_C))),
% 1.27/1.44      inference('sup-', [status(thm)], ['28', '29'])).
% 1.27/1.44  thf('31', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.27/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.44  thf('32', plain, ((v1_funct_1 @ sk_C)),
% 1.27/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.44  thf('33', plain,
% 1.27/1.44      (![X0 : $i]:
% 1.27/1.44         (~ (v1_funct_1 @ X0)
% 1.27/1.44          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.27/1.44          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.27/1.44          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.27/1.44          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.27/1.44               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.27/1.44               (k6_partfun1 @ sk_A)))),
% 1.27/1.44      inference('demod', [status(thm)], ['30', '31', '32'])).
% 1.27/1.44  thf('34', plain,
% 1.27/1.44      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 1.27/1.44           (k6_partfun1 @ sk_A))
% 1.27/1.44        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 1.27/1.44        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.27/1.44        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.27/1.44        | ~ (v1_funct_1 @ sk_D))),
% 1.27/1.44      inference('sup-', [status(thm)], ['27', '33'])).
% 1.27/1.44  thf('35', plain,
% 1.27/1.44      (![X22 : $i]:
% 1.27/1.44         (m1_subset_1 @ (k6_partfun1 @ X22) @ 
% 1.27/1.44          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))),
% 1.27/1.44      inference('demod', [status(thm)], ['24', '25'])).
% 1.27/1.44  thf('36', plain,
% 1.27/1.44      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.27/1.44         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 1.27/1.44          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 1.27/1.44          | (r2_relset_1 @ X19 @ X20 @ X18 @ X21)
% 1.27/1.44          | ((X18) != (X21)))),
% 1.27/1.44      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.27/1.44  thf('37', plain,
% 1.27/1.44      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.27/1.45         ((r2_relset_1 @ X19 @ X20 @ X21 @ X21)
% 1.27/1.45          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 1.27/1.45      inference('simplify', [status(thm)], ['36'])).
% 1.27/1.45  thf('38', plain,
% 1.27/1.45      (![X0 : $i]:
% 1.27/1.45         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 1.27/1.45      inference('sup-', [status(thm)], ['35', '37'])).
% 1.27/1.45  thf('39', plain,
% 1.27/1.45      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.27/1.45      inference('sup-', [status(thm)], ['3', '4'])).
% 1.27/1.45  thf('40', plain,
% 1.27/1.45      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.27/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.45  thf('41', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.27/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.45  thf('42', plain, ((v1_funct_1 @ sk_D)),
% 1.27/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.45  thf('43', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.27/1.45      inference('demod', [status(thm)], ['34', '38', '39', '40', '41', '42'])).
% 1.27/1.45  thf('44', plain,
% 1.27/1.45      ((((sk_A) != (sk_A))
% 1.27/1.45        | ~ (v2_funct_1 @ sk_D)
% 1.27/1.45        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 1.27/1.45      inference('demod', [status(thm)], ['10', '43'])).
% 1.27/1.45  thf('45', plain,
% 1.27/1.45      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 1.27/1.45        | ~ (v2_funct_1 @ sk_D))),
% 1.27/1.45      inference('simplify', [status(thm)], ['44'])).
% 1.27/1.45  thf('46', plain,
% 1.27/1.45      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.27/1.45         = (k6_partfun1 @ sk_A))),
% 1.27/1.45      inference('demod', [status(thm)], ['23', '26'])).
% 1.27/1.45  thf('47', plain,
% 1.27/1.45      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.27/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.45  thf(t30_funct_2, axiom,
% 1.27/1.45    (![A:$i,B:$i,C:$i,D:$i]:
% 1.27/1.45     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.27/1.45         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 1.27/1.45       ( ![E:$i]:
% 1.27/1.45         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 1.27/1.45             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 1.27/1.45           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 1.27/1.45               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 1.27/1.45             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 1.27/1.45               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 1.27/1.45  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 1.27/1.45  thf(zf_stmt_2, axiom,
% 1.27/1.45    (![C:$i,B:$i]:
% 1.27/1.45     ( ( zip_tseitin_1 @ C @ B ) =>
% 1.27/1.45       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 1.27/1.45  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.27/1.45  thf(zf_stmt_4, axiom,
% 1.27/1.45    (![E:$i,D:$i]:
% 1.27/1.45     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 1.27/1.45  thf(zf_stmt_5, axiom,
% 1.27/1.45    (![A:$i,B:$i,C:$i,D:$i]:
% 1.27/1.45     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.27/1.45         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.27/1.45       ( ![E:$i]:
% 1.27/1.45         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.27/1.45             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.27/1.45           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 1.27/1.45               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 1.27/1.45             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 1.27/1.45  thf('48', plain,
% 1.27/1.45      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 1.27/1.45         (~ (v1_funct_1 @ X44)
% 1.27/1.45          | ~ (v1_funct_2 @ X44 @ X45 @ X46)
% 1.27/1.45          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 1.27/1.45          | (zip_tseitin_0 @ X44 @ X47)
% 1.27/1.45          | ~ (v2_funct_1 @ (k1_partfun1 @ X48 @ X45 @ X45 @ X46 @ X47 @ X44))
% 1.27/1.45          | (zip_tseitin_1 @ X46 @ X45)
% 1.27/1.45          | ((k2_relset_1 @ X48 @ X45 @ X47) != (X45))
% 1.27/1.45          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X45)))
% 1.27/1.45          | ~ (v1_funct_2 @ X47 @ X48 @ X45)
% 1.27/1.45          | ~ (v1_funct_1 @ X47))),
% 1.27/1.45      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.27/1.45  thf('49', plain,
% 1.27/1.45      (![X0 : $i, X1 : $i]:
% 1.27/1.45         (~ (v1_funct_1 @ X0)
% 1.27/1.45          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.27/1.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.27/1.45          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 1.27/1.45          | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.27/1.45          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.27/1.45          | (zip_tseitin_0 @ sk_D @ X0)
% 1.27/1.45          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.27/1.45          | ~ (v1_funct_1 @ sk_D))),
% 1.27/1.45      inference('sup-', [status(thm)], ['47', '48'])).
% 1.27/1.45  thf('50', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.27/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.45  thf('51', plain, ((v1_funct_1 @ sk_D)),
% 1.27/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.45  thf('52', plain,
% 1.27/1.45      (![X0 : $i, X1 : $i]:
% 1.27/1.45         (~ (v1_funct_1 @ X0)
% 1.27/1.45          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.27/1.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.27/1.45          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 1.27/1.45          | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.27/1.45          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.27/1.45          | (zip_tseitin_0 @ sk_D @ X0))),
% 1.27/1.45      inference('demod', [status(thm)], ['49', '50', '51'])).
% 1.27/1.45  thf('53', plain,
% 1.27/1.45      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 1.27/1.45        | (zip_tseitin_0 @ sk_D @ sk_C)
% 1.27/1.45        | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.27/1.45        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.27/1.45        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 1.27/1.45        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.27/1.45        | ~ (v1_funct_1 @ sk_C))),
% 1.27/1.45      inference('sup-', [status(thm)], ['46', '52'])).
% 1.27/1.45  thf(fc4_funct_1, axiom,
% 1.27/1.45    (![A:$i]:
% 1.27/1.45     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.27/1.45       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.27/1.45  thf('54', plain, (![X7 : $i]: (v2_funct_1 @ (k6_relat_1 @ X7))),
% 1.27/1.45      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.27/1.45  thf('55', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 1.27/1.45      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.27/1.45  thf('56', plain, (![X7 : $i]: (v2_funct_1 @ (k6_partfun1 @ X7))),
% 1.27/1.45      inference('demod', [status(thm)], ['54', '55'])).
% 1.27/1.45  thf('57', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.27/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.45  thf('58', plain,
% 1.27/1.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.27/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.45  thf('59', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.27/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.45  thf('60', plain, ((v1_funct_1 @ sk_C)),
% 1.27/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.45  thf('61', plain,
% 1.27/1.45      (((zip_tseitin_0 @ sk_D @ sk_C)
% 1.27/1.45        | (zip_tseitin_1 @ sk_A @ sk_B)
% 1.27/1.45        | ((sk_B) != (sk_B)))),
% 1.27/1.45      inference('demod', [status(thm)], ['53', '56', '57', '58', '59', '60'])).
% 1.27/1.45  thf('62', plain,
% 1.27/1.45      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 1.27/1.45      inference('simplify', [status(thm)], ['61'])).
% 1.27/1.45  thf('63', plain,
% 1.27/1.45      (![X42 : $i, X43 : $i]:
% 1.27/1.45         (((X42) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X42 @ X43))),
% 1.27/1.45      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.27/1.45  thf('64', plain,
% 1.27/1.45      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 1.27/1.45      inference('sup-', [status(thm)], ['62', '63'])).
% 1.27/1.45  thf('65', plain, (((sk_A) != (k1_xboole_0))),
% 1.27/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.45  thf('66', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 1.27/1.45      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 1.27/1.45  thf('67', plain,
% 1.27/1.45      (![X40 : $i, X41 : $i]:
% 1.27/1.45         ((v2_funct_1 @ X41) | ~ (zip_tseitin_0 @ X41 @ X40))),
% 1.27/1.45      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.27/1.45  thf('68', plain, ((v2_funct_1 @ sk_D)),
% 1.27/1.45      inference('sup-', [status(thm)], ['66', '67'])).
% 1.27/1.45  thf('69', plain,
% 1.27/1.45      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 1.27/1.45      inference('demod', [status(thm)], ['45', '68'])).
% 1.27/1.45  thf('70', plain,
% 1.27/1.45      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.27/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.45  thf('71', plain,
% 1.27/1.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.27/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.45  thf(redefinition_k1_partfun1, axiom,
% 1.27/1.45    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.27/1.45     ( ( ( v1_funct_1 @ E ) & 
% 1.27/1.45         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.27/1.45         ( v1_funct_1 @ F ) & 
% 1.27/1.45         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.27/1.45       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.27/1.45  thf('72', plain,
% 1.27/1.45      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.27/1.45         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 1.27/1.45          | ~ (v1_funct_1 @ X29)
% 1.27/1.45          | ~ (v1_funct_1 @ X32)
% 1.27/1.45          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 1.27/1.45          | ((k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32)
% 1.27/1.45              = (k5_relat_1 @ X29 @ X32)))),
% 1.27/1.45      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.27/1.45  thf('73', plain,
% 1.27/1.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.27/1.45         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.27/1.45            = (k5_relat_1 @ sk_C @ X0))
% 1.27/1.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.27/1.45          | ~ (v1_funct_1 @ X0)
% 1.27/1.45          | ~ (v1_funct_1 @ sk_C))),
% 1.27/1.45      inference('sup-', [status(thm)], ['71', '72'])).
% 1.27/1.45  thf('74', plain, ((v1_funct_1 @ sk_C)),
% 1.27/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.45  thf('75', plain,
% 1.27/1.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.27/1.45         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.27/1.45            = (k5_relat_1 @ sk_C @ X0))
% 1.27/1.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.27/1.45          | ~ (v1_funct_1 @ X0))),
% 1.27/1.45      inference('demod', [status(thm)], ['73', '74'])).
% 1.27/1.45  thf('76', plain,
% 1.27/1.45      ((~ (v1_funct_1 @ sk_D)
% 1.27/1.45        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.27/1.45            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.27/1.45      inference('sup-', [status(thm)], ['70', '75'])).
% 1.27/1.45  thf('77', plain, ((v1_funct_1 @ sk_D)),
% 1.27/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.45  thf('78', plain,
% 1.27/1.45      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.27/1.45         = (k6_partfun1 @ sk_A))),
% 1.27/1.45      inference('demod', [status(thm)], ['23', '26'])).
% 1.27/1.45  thf('79', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 1.27/1.45      inference('demod', [status(thm)], ['76', '77', '78'])).
% 1.27/1.45  thf(t64_funct_1, axiom,
% 1.27/1.45    (![A:$i]:
% 1.27/1.45     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.27/1.45       ( ![B:$i]:
% 1.27/1.45         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.27/1.45           ( ( ( v2_funct_1 @ A ) & 
% 1.27/1.45               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 1.27/1.45               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 1.27/1.45             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.27/1.45  thf('80', plain,
% 1.27/1.45      (![X10 : $i, X11 : $i]:
% 1.27/1.45         (~ (v1_relat_1 @ X10)
% 1.27/1.45          | ~ (v1_funct_1 @ X10)
% 1.27/1.45          | ((X10) = (k2_funct_1 @ X11))
% 1.27/1.45          | ((k5_relat_1 @ X10 @ X11) != (k6_relat_1 @ (k2_relat_1 @ X11)))
% 1.27/1.45          | ((k2_relat_1 @ X10) != (k1_relat_1 @ X11))
% 1.27/1.45          | ~ (v2_funct_1 @ X11)
% 1.27/1.45          | ~ (v1_funct_1 @ X11)
% 1.27/1.45          | ~ (v1_relat_1 @ X11))),
% 1.27/1.45      inference('cnf', [status(esa)], [t64_funct_1])).
% 1.27/1.45  thf('81', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 1.27/1.45      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.27/1.45  thf('82', plain,
% 1.27/1.45      (![X10 : $i, X11 : $i]:
% 1.27/1.45         (~ (v1_relat_1 @ X10)
% 1.27/1.45          | ~ (v1_funct_1 @ X10)
% 1.27/1.45          | ((X10) = (k2_funct_1 @ X11))
% 1.27/1.45          | ((k5_relat_1 @ X10 @ X11) != (k6_partfun1 @ (k2_relat_1 @ X11)))
% 1.27/1.45          | ((k2_relat_1 @ X10) != (k1_relat_1 @ X11))
% 1.27/1.45          | ~ (v2_funct_1 @ X11)
% 1.27/1.45          | ~ (v1_funct_1 @ X11)
% 1.27/1.45          | ~ (v1_relat_1 @ X11))),
% 1.27/1.45      inference('demod', [status(thm)], ['80', '81'])).
% 1.27/1.45  thf('83', plain,
% 1.27/1.45      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 1.27/1.45        | ~ (v1_relat_1 @ sk_D)
% 1.27/1.45        | ~ (v1_funct_1 @ sk_D)
% 1.27/1.45        | ~ (v2_funct_1 @ sk_D)
% 1.27/1.45        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 1.27/1.45        | ((sk_C) = (k2_funct_1 @ sk_D))
% 1.27/1.45        | ~ (v1_funct_1 @ sk_C)
% 1.27/1.45        | ~ (v1_relat_1 @ sk_C))),
% 1.27/1.45      inference('sup-', [status(thm)], ['79', '82'])).
% 1.27/1.45  thf('84', plain,
% 1.27/1.45      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.27/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.45  thf(cc1_relset_1, axiom,
% 1.27/1.45    (![A:$i,B:$i,C:$i]:
% 1.27/1.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.27/1.45       ( v1_relat_1 @ C ) ))).
% 1.27/1.45  thf('85', plain,
% 1.27/1.45      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.27/1.45         ((v1_relat_1 @ X12)
% 1.27/1.45          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 1.27/1.45      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.27/1.45  thf('86', plain, ((v1_relat_1 @ sk_D)),
% 1.27/1.45      inference('sup-', [status(thm)], ['84', '85'])).
% 1.27/1.45  thf('87', plain, ((v1_funct_1 @ sk_D)),
% 1.27/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.45  thf('88', plain,
% 1.27/1.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.27/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.45  thf('89', plain,
% 1.27/1.45      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.27/1.45         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 1.27/1.45          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 1.27/1.45      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.27/1.45  thf('90', plain,
% 1.27/1.45      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.27/1.45      inference('sup-', [status(thm)], ['88', '89'])).
% 1.27/1.45  thf('91', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.27/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.45  thf('92', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.27/1.45      inference('sup+', [status(thm)], ['90', '91'])).
% 1.27/1.45  thf('93', plain, ((v1_funct_1 @ sk_C)),
% 1.27/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.45  thf('94', plain,
% 1.27/1.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.27/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.45  thf('95', plain,
% 1.27/1.45      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.27/1.45         ((v1_relat_1 @ X12)
% 1.27/1.45          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 1.27/1.45      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.27/1.45  thf('96', plain, ((v1_relat_1 @ sk_C)),
% 1.27/1.45      inference('sup-', [status(thm)], ['94', '95'])).
% 1.27/1.45  thf('97', plain,
% 1.27/1.45      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 1.27/1.45        | ~ (v2_funct_1 @ sk_D)
% 1.27/1.45        | ((sk_B) != (k1_relat_1 @ sk_D))
% 1.27/1.45        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 1.27/1.45      inference('demod', [status(thm)], ['83', '86', '87', '92', '93', '96'])).
% 1.27/1.45  thf('98', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.27/1.45      inference('demod', [status(thm)], ['34', '38', '39', '40', '41', '42'])).
% 1.27/1.45  thf('99', plain,
% 1.27/1.45      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 1.27/1.45        | ~ (v2_funct_1 @ sk_D)
% 1.27/1.45        | ((sk_B) != (k1_relat_1 @ sk_D))
% 1.27/1.45        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 1.27/1.45      inference('demod', [status(thm)], ['97', '98'])).
% 1.27/1.45  thf('100', plain,
% 1.27/1.45      ((((sk_C) = (k2_funct_1 @ sk_D))
% 1.27/1.45        | ((sk_B) != (k1_relat_1 @ sk_D))
% 1.27/1.45        | ~ (v2_funct_1 @ sk_D))),
% 1.27/1.45      inference('simplify', [status(thm)], ['99'])).
% 1.27/1.45  thf('101', plain, ((v2_funct_1 @ sk_D)),
% 1.27/1.45      inference('sup-', [status(thm)], ['66', '67'])).
% 1.27/1.45  thf('102', plain,
% 1.27/1.45      ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (k1_relat_1 @ sk_D)))),
% 1.27/1.45      inference('demod', [status(thm)], ['100', '101'])).
% 1.27/1.45  thf(t155_funct_1, axiom,
% 1.27/1.45    (![A:$i,B:$i]:
% 1.27/1.45     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.27/1.45       ( ( v2_funct_1 @ B ) =>
% 1.27/1.45         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 1.27/1.45  thf('103', plain,
% 1.27/1.45      (![X8 : $i, X9 : $i]:
% 1.27/1.45         (~ (v2_funct_1 @ X8)
% 1.27/1.45          | ((k10_relat_1 @ X8 @ X9) = (k9_relat_1 @ (k2_funct_1 @ X8) @ X9))
% 1.27/1.45          | ~ (v1_funct_1 @ X8)
% 1.27/1.45          | ~ (v1_relat_1 @ X8))),
% 1.27/1.45      inference('cnf', [status(esa)], [t155_funct_1])).
% 1.27/1.45  thf(dt_k2_funct_1, axiom,
% 1.27/1.45    (![A:$i]:
% 1.27/1.45     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.27/1.45       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.27/1.45         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.27/1.45  thf('104', plain,
% 1.27/1.45      (![X5 : $i]:
% 1.27/1.45         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 1.27/1.45          | ~ (v1_funct_1 @ X5)
% 1.27/1.45          | ~ (v1_relat_1 @ X5))),
% 1.27/1.45      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.27/1.45  thf('105', plain,
% 1.27/1.45      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 1.27/1.45      inference('demod', [status(thm)], ['45', '68'])).
% 1.27/1.45  thf(t160_relat_1, axiom,
% 1.27/1.45    (![A:$i]:
% 1.27/1.45     ( ( v1_relat_1 @ A ) =>
% 1.27/1.45       ( ![B:$i]:
% 1.27/1.45         ( ( v1_relat_1 @ B ) =>
% 1.27/1.45           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 1.27/1.45             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.27/1.45  thf('106', plain,
% 1.27/1.45      (![X0 : $i, X1 : $i]:
% 1.27/1.45         (~ (v1_relat_1 @ X0)
% 1.27/1.45          | ((k2_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 1.27/1.45              = (k9_relat_1 @ X0 @ (k2_relat_1 @ X1)))
% 1.27/1.45          | ~ (v1_relat_1 @ X1))),
% 1.27/1.45      inference('cnf', [status(esa)], [t160_relat_1])).
% 1.27/1.45  thf('107', plain,
% 1.27/1.45      ((((k2_relat_1 @ (k6_partfun1 @ sk_B))
% 1.27/1.45          = (k9_relat_1 @ (k2_funct_1 @ sk_D) @ (k2_relat_1 @ sk_D)))
% 1.27/1.45        | ~ (v1_relat_1 @ sk_D)
% 1.27/1.45        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D)))),
% 1.27/1.45      inference('sup+', [status(thm)], ['105', '106'])).
% 1.27/1.45  thf(t71_relat_1, axiom,
% 1.27/1.45    (![A:$i]:
% 1.27/1.45     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.27/1.45       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.27/1.45  thf('108', plain, (![X4 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X4)) = (X4))),
% 1.27/1.45      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.27/1.45  thf('109', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 1.27/1.45      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.27/1.45  thf('110', plain, (![X4 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 1.27/1.45      inference('demod', [status(thm)], ['108', '109'])).
% 1.27/1.45  thf('111', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.27/1.45      inference('demod', [status(thm)], ['34', '38', '39', '40', '41', '42'])).
% 1.27/1.45  thf('112', plain, ((v1_relat_1 @ sk_D)),
% 1.27/1.45      inference('sup-', [status(thm)], ['84', '85'])).
% 1.27/1.45  thf('113', plain,
% 1.27/1.45      ((((sk_B) = (k9_relat_1 @ (k2_funct_1 @ sk_D) @ sk_A))
% 1.27/1.45        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D)))),
% 1.27/1.45      inference('demod', [status(thm)], ['107', '110', '111', '112'])).
% 1.27/1.45  thf('114', plain,
% 1.27/1.45      ((~ (v1_relat_1 @ sk_D)
% 1.27/1.45        | ~ (v1_funct_1 @ sk_D)
% 1.27/1.45        | ((sk_B) = (k9_relat_1 @ (k2_funct_1 @ sk_D) @ sk_A)))),
% 1.27/1.45      inference('sup-', [status(thm)], ['104', '113'])).
% 1.27/1.45  thf('115', plain, ((v1_relat_1 @ sk_D)),
% 1.27/1.45      inference('sup-', [status(thm)], ['84', '85'])).
% 1.27/1.45  thf('116', plain, ((v1_funct_1 @ sk_D)),
% 1.27/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.45  thf('117', plain, (((sk_B) = (k9_relat_1 @ (k2_funct_1 @ sk_D) @ sk_A))),
% 1.27/1.45      inference('demod', [status(thm)], ['114', '115', '116'])).
% 1.27/1.45  thf('118', plain,
% 1.27/1.45      ((((sk_B) = (k10_relat_1 @ sk_D @ sk_A))
% 1.27/1.45        | ~ (v1_relat_1 @ sk_D)
% 1.27/1.45        | ~ (v1_funct_1 @ sk_D)
% 1.27/1.45        | ~ (v2_funct_1 @ sk_D))),
% 1.27/1.45      inference('sup+', [status(thm)], ['103', '117'])).
% 1.27/1.45  thf('119', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.27/1.45      inference('demod', [status(thm)], ['34', '38', '39', '40', '41', '42'])).
% 1.27/1.45  thf(t169_relat_1, axiom,
% 1.27/1.45    (![A:$i]:
% 1.27/1.45     ( ( v1_relat_1 @ A ) =>
% 1.27/1.45       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 1.27/1.45  thf('120', plain,
% 1.27/1.45      (![X2 : $i]:
% 1.27/1.45         (((k10_relat_1 @ X2 @ (k2_relat_1 @ X2)) = (k1_relat_1 @ X2))
% 1.27/1.45          | ~ (v1_relat_1 @ X2))),
% 1.27/1.45      inference('cnf', [status(esa)], [t169_relat_1])).
% 1.27/1.45  thf('121', plain,
% 1.27/1.45      ((((k10_relat_1 @ sk_D @ sk_A) = (k1_relat_1 @ sk_D))
% 1.27/1.45        | ~ (v1_relat_1 @ sk_D))),
% 1.27/1.45      inference('sup+', [status(thm)], ['119', '120'])).
% 1.27/1.45  thf('122', plain, ((v1_relat_1 @ sk_D)),
% 1.27/1.45      inference('sup-', [status(thm)], ['84', '85'])).
% 1.27/1.45  thf('123', plain, (((k10_relat_1 @ sk_D @ sk_A) = (k1_relat_1 @ sk_D))),
% 1.27/1.45      inference('demod', [status(thm)], ['121', '122'])).
% 1.27/1.45  thf('124', plain, ((v1_relat_1 @ sk_D)),
% 1.27/1.45      inference('sup-', [status(thm)], ['84', '85'])).
% 1.27/1.45  thf('125', plain, ((v1_funct_1 @ sk_D)),
% 1.27/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.45  thf('126', plain, ((v2_funct_1 @ sk_D)),
% 1.27/1.45      inference('sup-', [status(thm)], ['66', '67'])).
% 1.27/1.45  thf('127', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.27/1.45      inference('demod', [status(thm)], ['118', '123', '124', '125', '126'])).
% 1.27/1.45  thf('128', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (sk_B)))),
% 1.27/1.45      inference('demod', [status(thm)], ['102', '127'])).
% 1.27/1.45  thf('129', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.27/1.45      inference('simplify', [status(thm)], ['128'])).
% 1.27/1.45  thf('130', plain, (((k5_relat_1 @ sk_D @ sk_C) = (k6_partfun1 @ sk_B))),
% 1.27/1.45      inference('demod', [status(thm)], ['69', '129'])).
% 1.27/1.45  thf('131', plain,
% 1.27/1.45      (![X10 : $i, X11 : $i]:
% 1.27/1.45         (~ (v1_relat_1 @ X10)
% 1.27/1.45          | ~ (v1_funct_1 @ X10)
% 1.27/1.45          | ((X10) = (k2_funct_1 @ X11))
% 1.27/1.45          | ((k5_relat_1 @ X10 @ X11) != (k6_partfun1 @ (k2_relat_1 @ X11)))
% 1.27/1.45          | ((k2_relat_1 @ X10) != (k1_relat_1 @ X11))
% 1.27/1.45          | ~ (v2_funct_1 @ X11)
% 1.27/1.45          | ~ (v1_funct_1 @ X11)
% 1.27/1.45          | ~ (v1_relat_1 @ X11))),
% 1.27/1.45      inference('demod', [status(thm)], ['80', '81'])).
% 1.27/1.45  thf('132', plain,
% 1.27/1.45      ((((k6_partfun1 @ sk_B) != (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 1.27/1.45        | ~ (v1_relat_1 @ sk_C)
% 1.27/1.45        | ~ (v1_funct_1 @ sk_C)
% 1.27/1.45        | ~ (v2_funct_1 @ sk_C)
% 1.27/1.45        | ((k2_relat_1 @ sk_D) != (k1_relat_1 @ sk_C))
% 1.27/1.45        | ((sk_D) = (k2_funct_1 @ sk_C))
% 1.27/1.45        | ~ (v1_funct_1 @ sk_D)
% 1.27/1.45        | ~ (v1_relat_1 @ sk_D))),
% 1.27/1.45      inference('sup-', [status(thm)], ['130', '131'])).
% 1.27/1.45  thf('133', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.27/1.45      inference('sup+', [status(thm)], ['90', '91'])).
% 1.27/1.45  thf('134', plain, ((v1_relat_1 @ sk_C)),
% 1.27/1.45      inference('sup-', [status(thm)], ['94', '95'])).
% 1.27/1.45  thf('135', plain, ((v1_funct_1 @ sk_C)),
% 1.27/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.45  thf('136', plain, ((v2_funct_1 @ sk_C)),
% 1.27/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.45  thf('137', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.27/1.45      inference('demod', [status(thm)], ['34', '38', '39', '40', '41', '42'])).
% 1.27/1.45  thf('138', plain,
% 1.27/1.45      (![X8 : $i, X9 : $i]:
% 1.27/1.45         (~ (v2_funct_1 @ X8)
% 1.27/1.45          | ((k10_relat_1 @ X8 @ X9) = (k9_relat_1 @ (k2_funct_1 @ X8) @ X9))
% 1.27/1.45          | ~ (v1_funct_1 @ X8)
% 1.27/1.45          | ~ (v1_relat_1 @ X8))),
% 1.27/1.45      inference('cnf', [status(esa)], [t155_funct_1])).
% 1.27/1.45  thf('139', plain,
% 1.27/1.45      (![X5 : $i]:
% 1.27/1.45         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 1.27/1.45          | ~ (v1_funct_1 @ X5)
% 1.27/1.45          | ~ (v1_relat_1 @ X5))),
% 1.27/1.45      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.27/1.45  thf('140', plain,
% 1.27/1.45      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.27/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.45  thf('141', plain,
% 1.27/1.45      (![X49 : $i, X50 : $i, X51 : $i]:
% 1.27/1.45         (((X49) = (k1_xboole_0))
% 1.27/1.45          | ~ (v1_funct_1 @ X50)
% 1.27/1.45          | ~ (v1_funct_2 @ X50 @ X51 @ X49)
% 1.27/1.45          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X49)))
% 1.27/1.45          | ((k5_relat_1 @ X50 @ (k2_funct_1 @ X50)) = (k6_partfun1 @ X51))
% 1.27/1.45          | ~ (v2_funct_1 @ X50)
% 1.27/1.45          | ((k2_relset_1 @ X51 @ X49 @ X50) != (X49)))),
% 1.27/1.45      inference('cnf', [status(esa)], [t35_funct_2])).
% 1.27/1.45  thf('142', plain,
% 1.27/1.45      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 1.27/1.45        | ~ (v2_funct_1 @ sk_C)
% 1.27/1.45        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 1.27/1.45        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.27/1.45        | ~ (v1_funct_1 @ sk_C)
% 1.27/1.45        | ((sk_B) = (k1_xboole_0)))),
% 1.27/1.45      inference('sup-', [status(thm)], ['140', '141'])).
% 1.27/1.45  thf('143', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.27/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.45  thf('144', plain, ((v2_funct_1 @ sk_C)),
% 1.27/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.45  thf('145', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.27/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.45  thf('146', plain, ((v1_funct_1 @ sk_C)),
% 1.27/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.45  thf('147', plain,
% 1.27/1.45      ((((sk_B) != (sk_B))
% 1.27/1.45        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 1.27/1.45        | ((sk_B) = (k1_xboole_0)))),
% 1.27/1.45      inference('demod', [status(thm)], ['142', '143', '144', '145', '146'])).
% 1.27/1.45  thf('148', plain,
% 1.27/1.45      ((((sk_B) = (k1_xboole_0))
% 1.27/1.45        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 1.27/1.45      inference('simplify', [status(thm)], ['147'])).
% 1.27/1.45  thf('149', plain, (((sk_B) != (k1_xboole_0))),
% 1.27/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.45  thf('150', plain,
% 1.27/1.45      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 1.27/1.45      inference('simplify_reflect-', [status(thm)], ['148', '149'])).
% 1.27/1.45  thf('151', plain,
% 1.27/1.45      (![X0 : $i, X1 : $i]:
% 1.27/1.45         (~ (v1_relat_1 @ X0)
% 1.27/1.45          | ((k2_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 1.27/1.45              = (k9_relat_1 @ X0 @ (k2_relat_1 @ X1)))
% 1.27/1.45          | ~ (v1_relat_1 @ X1))),
% 1.27/1.45      inference('cnf', [status(esa)], [t160_relat_1])).
% 1.27/1.45  thf('152', plain,
% 1.27/1.45      ((((k2_relat_1 @ (k6_partfun1 @ sk_A))
% 1.27/1.45          = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C)))
% 1.27/1.45        | ~ (v1_relat_1 @ sk_C)
% 1.27/1.45        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.27/1.45      inference('sup+', [status(thm)], ['150', '151'])).
% 1.27/1.45  thf('153', plain, (![X4 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 1.27/1.45      inference('demod', [status(thm)], ['108', '109'])).
% 1.27/1.45  thf('154', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.27/1.45      inference('sup+', [status(thm)], ['90', '91'])).
% 1.27/1.45  thf('155', plain, ((v1_relat_1 @ sk_C)),
% 1.27/1.45      inference('sup-', [status(thm)], ['94', '95'])).
% 1.27/1.45  thf('156', plain,
% 1.27/1.45      ((((sk_A) = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B))
% 1.27/1.45        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.27/1.45      inference('demod', [status(thm)], ['152', '153', '154', '155'])).
% 1.27/1.45  thf('157', plain,
% 1.27/1.45      ((~ (v1_relat_1 @ sk_C)
% 1.27/1.45        | ~ (v1_funct_1 @ sk_C)
% 1.27/1.45        | ((sk_A) = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)))),
% 1.27/1.45      inference('sup-', [status(thm)], ['139', '156'])).
% 1.27/1.45  thf('158', plain, ((v1_relat_1 @ sk_C)),
% 1.27/1.45      inference('sup-', [status(thm)], ['94', '95'])).
% 1.27/1.45  thf('159', plain, ((v1_funct_1 @ sk_C)),
% 1.27/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.45  thf('160', plain, (((sk_A) = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B))),
% 1.27/1.45      inference('demod', [status(thm)], ['157', '158', '159'])).
% 1.27/1.45  thf('161', plain,
% 1.27/1.45      ((((sk_A) = (k10_relat_1 @ sk_C @ sk_B))
% 1.27/1.45        | ~ (v1_relat_1 @ sk_C)
% 1.27/1.45        | ~ (v1_funct_1 @ sk_C)
% 1.27/1.45        | ~ (v2_funct_1 @ sk_C))),
% 1.27/1.45      inference('sup+', [status(thm)], ['138', '160'])).
% 1.27/1.45  thf('162', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.27/1.45      inference('sup+', [status(thm)], ['90', '91'])).
% 1.27/1.45  thf('163', plain,
% 1.27/1.45      (![X2 : $i]:
% 1.27/1.45         (((k10_relat_1 @ X2 @ (k2_relat_1 @ X2)) = (k1_relat_1 @ X2))
% 1.27/1.45          | ~ (v1_relat_1 @ X2))),
% 1.27/1.45      inference('cnf', [status(esa)], [t169_relat_1])).
% 1.27/1.45  thf('164', plain,
% 1.27/1.45      ((((k10_relat_1 @ sk_C @ sk_B) = (k1_relat_1 @ sk_C))
% 1.27/1.45        | ~ (v1_relat_1 @ sk_C))),
% 1.27/1.45      inference('sup+', [status(thm)], ['162', '163'])).
% 1.27/1.45  thf('165', plain, ((v1_relat_1 @ sk_C)),
% 1.27/1.45      inference('sup-', [status(thm)], ['94', '95'])).
% 1.27/1.45  thf('166', plain, (((k10_relat_1 @ sk_C @ sk_B) = (k1_relat_1 @ sk_C))),
% 1.27/1.45      inference('demod', [status(thm)], ['164', '165'])).
% 1.27/1.45  thf('167', plain, ((v1_relat_1 @ sk_C)),
% 1.27/1.45      inference('sup-', [status(thm)], ['94', '95'])).
% 1.27/1.45  thf('168', plain, ((v1_funct_1 @ sk_C)),
% 1.27/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.45  thf('169', plain, ((v2_funct_1 @ sk_C)),
% 1.27/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.45  thf('170', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 1.27/1.45      inference('demod', [status(thm)], ['161', '166', '167', '168', '169'])).
% 1.27/1.45  thf('171', plain, ((v1_funct_1 @ sk_D)),
% 1.27/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.45  thf('172', plain, ((v1_relat_1 @ sk_D)),
% 1.27/1.45      inference('sup-', [status(thm)], ['84', '85'])).
% 1.27/1.45  thf('173', plain,
% 1.27/1.45      ((((k6_partfun1 @ sk_B) != (k6_partfun1 @ sk_B))
% 1.27/1.45        | ((sk_A) != (sk_A))
% 1.27/1.45        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 1.27/1.45      inference('demod', [status(thm)],
% 1.27/1.45                ['132', '133', '134', '135', '136', '137', '170', '171', '172'])).
% 1.27/1.45  thf('174', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 1.27/1.45      inference('simplify', [status(thm)], ['173'])).
% 1.27/1.45  thf('175', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.27/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.45  thf('176', plain, ($false),
% 1.27/1.45      inference('simplify_reflect-', [status(thm)], ['174', '175'])).
% 1.27/1.45  
% 1.27/1.45  % SZS output end Refutation
% 1.27/1.45  
% 1.27/1.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

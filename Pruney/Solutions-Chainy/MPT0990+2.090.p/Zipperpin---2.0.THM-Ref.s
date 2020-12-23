%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RUcxCsAsmV

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:09 EST 2020

% Result     : Theorem 0.92s
% Output     : Refutation 0.92s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 432 expanded)
%              Number of leaves         :   44 ( 147 expanded)
%              Depth                    :   21
%              Number of atoms          : 1830 (10775 expanded)
%              Number of equality atoms :  129 ( 747 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k5_relat_1 @ X6 @ ( k2_funct_1 @ X6 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('2',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k5_relat_1 @ X6 @ ( k2_funct_1 @ X6 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

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

thf('3',plain,(
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

thf('4',plain,(
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

thf('5',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('8',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','8','9','10'])).

thf('12',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf('14',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
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

thf('17',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X20 @ X21 @ X23 @ X24 @ X19 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('24',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( X15 = X18 )
      | ~ ( r2_relset_1 @ X16 @ X17 @ X15 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','25'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('27',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('28',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
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

thf('30',plain,(
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

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['28','34'])).

thf('36',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('37',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( r2_relset_1 @ X16 @ X17 @ X15 @ X18 )
      | ( X15 != X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('38',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_relset_1 @ X16 @ X17 @ X18 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('41',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['35','39','40','41','42','43'])).

thf('45',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','44'])).

thf('46',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('48',plain,(
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

thf('49',plain,(
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

thf('50',plain,(
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
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['47','53'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('55',plain,(
    ! [X3: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('56',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('57',plain,(
    ! [X3: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X3 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['54','57','58','59','60','61'])).

thf('63',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X40: $i,X41: $i] :
      ( ( X40 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('65',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X38: $i,X39: $i] :
      ( ( v2_funct_1 @ X39 )
      | ~ ( zip_tseitin_0 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('69',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['46','69'])).

thf('71',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['2','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('73',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('74',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['67','68'])).

thf('77',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['71','74','75','76'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('79',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['77','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('83',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
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

thf('86',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( ( k1_partfun1 @ X28 @ X29 @ X31 @ X32 @ X27 @ X30 )
        = ( k5_relat_1 @ X27 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['84','89'])).

thf('91',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('93',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['90','91','92'])).

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

thf('94',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( X7
        = ( k2_funct_1 @ X8 ) )
      | ( ( k5_relat_1 @ X8 @ X7 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X8 ) ) )
      | ( ( k2_relat_1 @ X8 )
       != ( k1_relat_1 @ X7 ) )
      | ~ ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t63_funct_1])).

thf('95',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('96',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( X7
        = ( k2_funct_1 @ X8 ) )
      | ( ( k5_relat_1 @ X8 @ X7 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X8 ) ) )
      | ( ( k2_relat_1 @ X8 )
       != ( k1_relat_1 @ X7 ) )
      | ~ ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
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
    inference('sup-',[status(thm)],['93','96'])).

thf('98',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k5_relat_1 @ X6 @ ( k2_funct_1 @ X6 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('99',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
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

thf('101',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['101','102','103','104','105'])).

thf('107',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['98','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('113',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['110','113','114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('118',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('120',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['111','112'])).

thf('122',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('126',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['72','73'])).

thf('131',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['97','120','121','122','123','128','129','130'])).

thf('132',plain,
    ( ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    sk_B
 != ( k1_relat_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['132','133'])).

thf('135',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['83','134'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RUcxCsAsmV
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:40:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.92/1.17  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.92/1.17  % Solved by: fo/fo7.sh
% 0.92/1.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.92/1.17  % done 986 iterations in 0.704s
% 0.92/1.17  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.92/1.17  % SZS output start Refutation
% 0.92/1.17  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.92/1.17  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.92/1.17  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.92/1.17  thf(sk_D_type, type, sk_D: $i).
% 0.92/1.17  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.92/1.17  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.92/1.17  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.92/1.17  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.92/1.17  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.92/1.17  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.92/1.17  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.92/1.17  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.92/1.17  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.92/1.17  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.92/1.17  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.92/1.17  thf(sk_B_type, type, sk_B: $i).
% 0.92/1.17  thf(sk_C_type, type, sk_C: $i).
% 0.92/1.17  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.92/1.17  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.92/1.17  thf(sk_A_type, type, sk_A: $i).
% 0.92/1.17  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.92/1.17  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.92/1.17  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.92/1.17  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.92/1.17  thf(t61_funct_1, axiom,
% 0.92/1.17    (![A:$i]:
% 0.92/1.17     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.92/1.17       ( ( v2_funct_1 @ A ) =>
% 0.92/1.17         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.92/1.17             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.92/1.17           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.92/1.17             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.92/1.17  thf('0', plain,
% 0.92/1.17      (![X6 : $i]:
% 0.92/1.17         (~ (v2_funct_1 @ X6)
% 0.92/1.17          | ((k5_relat_1 @ X6 @ (k2_funct_1 @ X6))
% 0.92/1.17              = (k6_relat_1 @ (k1_relat_1 @ X6)))
% 0.92/1.17          | ~ (v1_funct_1 @ X6)
% 0.92/1.17          | ~ (v1_relat_1 @ X6))),
% 0.92/1.17      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.92/1.17  thf(redefinition_k6_partfun1, axiom,
% 0.92/1.17    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.92/1.17  thf('1', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.92/1.17      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.92/1.17  thf('2', plain,
% 0.92/1.17      (![X6 : $i]:
% 0.92/1.17         (~ (v2_funct_1 @ X6)
% 0.92/1.17          | ((k5_relat_1 @ X6 @ (k2_funct_1 @ X6))
% 0.92/1.17              = (k6_partfun1 @ (k1_relat_1 @ X6)))
% 0.92/1.17          | ~ (v1_funct_1 @ X6)
% 0.92/1.17          | ~ (v1_relat_1 @ X6))),
% 0.92/1.17      inference('demod', [status(thm)], ['0', '1'])).
% 0.92/1.17  thf(t36_funct_2, conjecture,
% 0.92/1.17    (![A:$i,B:$i,C:$i]:
% 0.92/1.17     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.92/1.17         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.92/1.17       ( ![D:$i]:
% 0.92/1.17         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.92/1.17             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.92/1.17           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.92/1.17               ( r2_relset_1 @
% 0.92/1.17                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.92/1.17                 ( k6_partfun1 @ A ) ) & 
% 0.92/1.17               ( v2_funct_1 @ C ) ) =>
% 0.92/1.17             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.92/1.17               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.92/1.17  thf(zf_stmt_0, negated_conjecture,
% 0.92/1.17    (~( ![A:$i,B:$i,C:$i]:
% 0.92/1.17        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.92/1.17            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.92/1.17          ( ![D:$i]:
% 0.92/1.17            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.92/1.17                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.92/1.17              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.92/1.17                  ( r2_relset_1 @
% 0.92/1.17                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.92/1.17                    ( k6_partfun1 @ A ) ) & 
% 0.92/1.17                  ( v2_funct_1 @ C ) ) =>
% 0.92/1.17                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.92/1.17                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.92/1.17    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.92/1.17  thf('3', plain,
% 0.92/1.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.17  thf(t35_funct_2, axiom,
% 0.92/1.17    (![A:$i,B:$i,C:$i]:
% 0.92/1.17     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.92/1.17         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.92/1.17       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.92/1.17         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.92/1.17           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 0.92/1.17             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 0.92/1.17  thf('4', plain,
% 0.92/1.17      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.92/1.17         (((X47) = (k1_xboole_0))
% 0.92/1.17          | ~ (v1_funct_1 @ X48)
% 0.92/1.17          | ~ (v1_funct_2 @ X48 @ X49 @ X47)
% 0.92/1.17          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X47)))
% 0.92/1.17          | ((k5_relat_1 @ X48 @ (k2_funct_1 @ X48)) = (k6_partfun1 @ X49))
% 0.92/1.17          | ~ (v2_funct_1 @ X48)
% 0.92/1.17          | ((k2_relset_1 @ X49 @ X47 @ X48) != (X47)))),
% 0.92/1.17      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.92/1.17  thf('5', plain,
% 0.92/1.17      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 0.92/1.17        | ~ (v2_funct_1 @ sk_D)
% 0.92/1.17        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.92/1.17        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.92/1.17        | ~ (v1_funct_1 @ sk_D)
% 0.92/1.17        | ((sk_A) = (k1_xboole_0)))),
% 0.92/1.17      inference('sup-', [status(thm)], ['3', '4'])).
% 0.92/1.17  thf('6', plain,
% 0.92/1.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.17  thf(redefinition_k2_relset_1, axiom,
% 0.92/1.17    (![A:$i,B:$i,C:$i]:
% 0.92/1.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.92/1.17       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.92/1.17  thf('7', plain,
% 0.92/1.17      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.92/1.17         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.92/1.17          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.92/1.17      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.92/1.17  thf('8', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.92/1.17      inference('sup-', [status(thm)], ['6', '7'])).
% 0.92/1.17  thf('9', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.17  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.17  thf('11', plain,
% 0.92/1.17      ((((k2_relat_1 @ sk_D) != (sk_A))
% 0.92/1.17        | ~ (v2_funct_1 @ sk_D)
% 0.92/1.17        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.92/1.17        | ((sk_A) = (k1_xboole_0)))),
% 0.92/1.17      inference('demod', [status(thm)], ['5', '8', '9', '10'])).
% 0.92/1.17  thf('12', plain, (((sk_A) != (k1_xboole_0))),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.17  thf('13', plain,
% 0.92/1.17      ((((k2_relat_1 @ sk_D) != (sk_A))
% 0.92/1.17        | ~ (v2_funct_1 @ sk_D)
% 0.92/1.17        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 0.92/1.17      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 0.92/1.17  thf('14', plain,
% 0.92/1.17      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.92/1.17        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.92/1.17        (k6_partfun1 @ sk_A))),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.17  thf('15', plain,
% 0.92/1.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.17  thf('16', plain,
% 0.92/1.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.17  thf(dt_k1_partfun1, axiom,
% 0.92/1.17    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.92/1.17     ( ( ( v1_funct_1 @ E ) & 
% 0.92/1.17         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.92/1.17         ( v1_funct_1 @ F ) & 
% 0.92/1.17         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.92/1.17       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.92/1.17         ( m1_subset_1 @
% 0.92/1.17           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.92/1.17           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.92/1.17  thf('17', plain,
% 0.92/1.17      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.92/1.17         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.92/1.17          | ~ (v1_funct_1 @ X19)
% 0.92/1.17          | ~ (v1_funct_1 @ X22)
% 0.92/1.17          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.92/1.17          | (m1_subset_1 @ (k1_partfun1 @ X20 @ X21 @ X23 @ X24 @ X19 @ X22) @ 
% 0.92/1.17             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X24))))),
% 0.92/1.17      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.92/1.17  thf('18', plain,
% 0.92/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.92/1.17         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.92/1.17           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.92/1.17          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.92/1.17          | ~ (v1_funct_1 @ X1)
% 0.92/1.17          | ~ (v1_funct_1 @ sk_C))),
% 0.92/1.17      inference('sup-', [status(thm)], ['16', '17'])).
% 0.92/1.17  thf('19', plain, ((v1_funct_1 @ sk_C)),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.17  thf('20', plain,
% 0.92/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.92/1.17         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.92/1.17           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.92/1.17          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.92/1.17          | ~ (v1_funct_1 @ X1))),
% 0.92/1.17      inference('demod', [status(thm)], ['18', '19'])).
% 0.92/1.17  thf('21', plain,
% 0.92/1.17      ((~ (v1_funct_1 @ sk_D)
% 0.92/1.17        | (m1_subset_1 @ 
% 0.92/1.17           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.92/1.17           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.92/1.17      inference('sup-', [status(thm)], ['15', '20'])).
% 0.92/1.17  thf('22', plain, ((v1_funct_1 @ sk_D)),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.17  thf('23', plain,
% 0.92/1.17      ((m1_subset_1 @ 
% 0.92/1.17        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.92/1.17        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.92/1.17      inference('demod', [status(thm)], ['21', '22'])).
% 0.92/1.17  thf(redefinition_r2_relset_1, axiom,
% 0.92/1.17    (![A:$i,B:$i,C:$i,D:$i]:
% 0.92/1.17     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.92/1.17         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.92/1.17       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.92/1.17  thf('24', plain,
% 0.92/1.17      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.92/1.17         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.92/1.17          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.92/1.17          | ((X15) = (X18))
% 0.92/1.17          | ~ (r2_relset_1 @ X16 @ X17 @ X15 @ X18))),
% 0.92/1.17      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.92/1.17  thf('25', plain,
% 0.92/1.17      (![X0 : $i]:
% 0.92/1.17         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.92/1.17             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 0.92/1.17          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 0.92/1.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.92/1.17      inference('sup-', [status(thm)], ['23', '24'])).
% 0.92/1.17  thf('26', plain,
% 0.92/1.17      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.92/1.17           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.92/1.17        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.92/1.17            = (k6_partfun1 @ sk_A)))),
% 0.92/1.17      inference('sup-', [status(thm)], ['14', '25'])).
% 0.92/1.17  thf(dt_k6_partfun1, axiom,
% 0.92/1.17    (![A:$i]:
% 0.92/1.17     ( ( m1_subset_1 @
% 0.92/1.17         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.92/1.17       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.92/1.17  thf('27', plain,
% 0.92/1.17      (![X26 : $i]:
% 0.92/1.17         (m1_subset_1 @ (k6_partfun1 @ X26) @ 
% 0.92/1.17          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X26)))),
% 0.92/1.17      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.92/1.17  thf('28', plain,
% 0.92/1.17      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.92/1.17         = (k6_partfun1 @ sk_A))),
% 0.92/1.17      inference('demod', [status(thm)], ['26', '27'])).
% 0.92/1.17  thf('29', plain,
% 0.92/1.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.17  thf(t24_funct_2, axiom,
% 0.92/1.17    (![A:$i,B:$i,C:$i]:
% 0.92/1.17     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.92/1.17         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.92/1.17       ( ![D:$i]:
% 0.92/1.17         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.92/1.17             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.92/1.17           ( ( r2_relset_1 @
% 0.92/1.17               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.92/1.17               ( k6_partfun1 @ B ) ) =>
% 0.92/1.17             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.92/1.17  thf('30', plain,
% 0.92/1.17      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.92/1.17         (~ (v1_funct_1 @ X34)
% 0.92/1.17          | ~ (v1_funct_2 @ X34 @ X35 @ X36)
% 0.92/1.17          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.92/1.17          | ~ (r2_relset_1 @ X35 @ X35 @ 
% 0.92/1.17               (k1_partfun1 @ X35 @ X36 @ X36 @ X35 @ X34 @ X37) @ 
% 0.92/1.17               (k6_partfun1 @ X35))
% 0.92/1.17          | ((k2_relset_1 @ X36 @ X35 @ X37) = (X35))
% 0.92/1.17          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 0.92/1.17          | ~ (v1_funct_2 @ X37 @ X36 @ X35)
% 0.92/1.17          | ~ (v1_funct_1 @ X37))),
% 0.92/1.17      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.92/1.17  thf('31', plain,
% 0.92/1.17      (![X0 : $i]:
% 0.92/1.17         (~ (v1_funct_1 @ X0)
% 0.92/1.17          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.92/1.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.92/1.17          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.92/1.17          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.92/1.17               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.92/1.17               (k6_partfun1 @ sk_A))
% 0.92/1.17          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.92/1.17          | ~ (v1_funct_1 @ sk_C))),
% 0.92/1.17      inference('sup-', [status(thm)], ['29', '30'])).
% 0.92/1.17  thf('32', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.17  thf('33', plain, ((v1_funct_1 @ sk_C)),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.17  thf('34', plain,
% 0.92/1.17      (![X0 : $i]:
% 0.92/1.17         (~ (v1_funct_1 @ X0)
% 0.92/1.17          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.92/1.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.92/1.17          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.92/1.17          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.92/1.17               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.92/1.17               (k6_partfun1 @ sk_A)))),
% 0.92/1.17      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.92/1.17  thf('35', plain,
% 0.92/1.17      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 0.92/1.17           (k6_partfun1 @ sk_A))
% 0.92/1.17        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 0.92/1.17        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.92/1.17        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.92/1.17        | ~ (v1_funct_1 @ sk_D))),
% 0.92/1.17      inference('sup-', [status(thm)], ['28', '34'])).
% 0.92/1.17  thf('36', plain,
% 0.92/1.17      (![X26 : $i]:
% 0.92/1.17         (m1_subset_1 @ (k6_partfun1 @ X26) @ 
% 0.92/1.17          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X26)))),
% 0.92/1.17      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.92/1.17  thf('37', plain,
% 0.92/1.17      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.92/1.17         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.92/1.17          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.92/1.17          | (r2_relset_1 @ X16 @ X17 @ X15 @ X18)
% 0.92/1.17          | ((X15) != (X18)))),
% 0.92/1.17      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.92/1.17  thf('38', plain,
% 0.92/1.17      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.92/1.17         ((r2_relset_1 @ X16 @ X17 @ X18 @ X18)
% 0.92/1.17          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.92/1.17      inference('simplify', [status(thm)], ['37'])).
% 0.92/1.17  thf('39', plain,
% 0.92/1.17      (![X0 : $i]:
% 0.92/1.17         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 0.92/1.17      inference('sup-', [status(thm)], ['36', '38'])).
% 0.92/1.17  thf('40', plain,
% 0.92/1.17      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.92/1.17      inference('sup-', [status(thm)], ['6', '7'])).
% 0.92/1.17  thf('41', plain,
% 0.92/1.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.17  thf('42', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.17  thf('43', plain, ((v1_funct_1 @ sk_D)),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.17  thf('44', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.92/1.17      inference('demod', [status(thm)], ['35', '39', '40', '41', '42', '43'])).
% 0.92/1.17  thf('45', plain,
% 0.92/1.17      ((((sk_A) != (sk_A))
% 0.92/1.17        | ~ (v2_funct_1 @ sk_D)
% 0.92/1.17        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 0.92/1.17      inference('demod', [status(thm)], ['13', '44'])).
% 0.92/1.17  thf('46', plain,
% 0.92/1.17      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.92/1.17        | ~ (v2_funct_1 @ sk_D))),
% 0.92/1.17      inference('simplify', [status(thm)], ['45'])).
% 0.92/1.17  thf('47', plain,
% 0.92/1.17      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.92/1.17         = (k6_partfun1 @ sk_A))),
% 0.92/1.17      inference('demod', [status(thm)], ['26', '27'])).
% 0.92/1.17  thf('48', plain,
% 0.92/1.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.17  thf(t30_funct_2, axiom,
% 0.92/1.17    (![A:$i,B:$i,C:$i,D:$i]:
% 0.92/1.17     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.92/1.17         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 0.92/1.17       ( ![E:$i]:
% 0.92/1.17         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 0.92/1.17             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 0.92/1.17           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 0.92/1.17               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 0.92/1.17             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 0.92/1.17               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 0.92/1.17  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 0.92/1.17  thf(zf_stmt_2, axiom,
% 0.92/1.17    (![C:$i,B:$i]:
% 0.92/1.17     ( ( zip_tseitin_1 @ C @ B ) =>
% 0.92/1.17       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 0.92/1.17  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.92/1.17  thf(zf_stmt_4, axiom,
% 0.92/1.17    (![E:$i,D:$i]:
% 0.92/1.17     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 0.92/1.17  thf(zf_stmt_5, axiom,
% 0.92/1.17    (![A:$i,B:$i,C:$i,D:$i]:
% 0.92/1.17     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.92/1.17         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.92/1.17       ( ![E:$i]:
% 0.92/1.17         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.92/1.17             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.92/1.17           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 0.92/1.17               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 0.92/1.17             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 0.92/1.17  thf('49', plain,
% 0.92/1.17      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.92/1.17         (~ (v1_funct_1 @ X42)
% 0.92/1.17          | ~ (v1_funct_2 @ X42 @ X43 @ X44)
% 0.92/1.17          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 0.92/1.17          | (zip_tseitin_0 @ X42 @ X45)
% 0.92/1.17          | ~ (v2_funct_1 @ (k1_partfun1 @ X46 @ X43 @ X43 @ X44 @ X45 @ X42))
% 0.92/1.17          | (zip_tseitin_1 @ X44 @ X43)
% 0.92/1.17          | ((k2_relset_1 @ X46 @ X43 @ X45) != (X43))
% 0.92/1.17          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X43)))
% 0.92/1.17          | ~ (v1_funct_2 @ X45 @ X46 @ X43)
% 0.92/1.17          | ~ (v1_funct_1 @ X45))),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.92/1.17  thf('50', plain,
% 0.92/1.17      (![X0 : $i, X1 : $i]:
% 0.92/1.17         (~ (v1_funct_1 @ X0)
% 0.92/1.17          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.92/1.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.92/1.17          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 0.92/1.17          | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.92/1.17          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.92/1.17          | (zip_tseitin_0 @ sk_D @ X0)
% 0.92/1.17          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.92/1.17          | ~ (v1_funct_1 @ sk_D))),
% 0.92/1.17      inference('sup-', [status(thm)], ['48', '49'])).
% 0.92/1.17  thf('51', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.17  thf('52', plain, ((v1_funct_1 @ sk_D)),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.17  thf('53', plain,
% 0.92/1.17      (![X0 : $i, X1 : $i]:
% 0.92/1.17         (~ (v1_funct_1 @ X0)
% 0.92/1.17          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.92/1.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.92/1.17          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 0.92/1.17          | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.92/1.17          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.92/1.17          | (zip_tseitin_0 @ sk_D @ X0))),
% 0.92/1.17      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.92/1.17  thf('54', plain,
% 0.92/1.17      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 0.92/1.17        | (zip_tseitin_0 @ sk_D @ sk_C)
% 0.92/1.17        | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.92/1.17        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.92/1.17        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.92/1.17        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.92/1.17        | ~ (v1_funct_1 @ sk_C))),
% 0.92/1.17      inference('sup-', [status(thm)], ['47', '53'])).
% 0.92/1.17  thf(fc4_funct_1, axiom,
% 0.92/1.17    (![A:$i]:
% 0.92/1.17     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.92/1.17       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.92/1.17  thf('55', plain, (![X3 : $i]: (v2_funct_1 @ (k6_relat_1 @ X3))),
% 0.92/1.17      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.92/1.17  thf('56', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.92/1.17      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.92/1.17  thf('57', plain, (![X3 : $i]: (v2_funct_1 @ (k6_partfun1 @ X3))),
% 0.92/1.17      inference('demod', [status(thm)], ['55', '56'])).
% 0.92/1.17  thf('58', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.17  thf('59', plain,
% 0.92/1.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.17  thf('60', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.17  thf('61', plain, ((v1_funct_1 @ sk_C)),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.17  thf('62', plain,
% 0.92/1.17      (((zip_tseitin_0 @ sk_D @ sk_C)
% 0.92/1.17        | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.92/1.17        | ((sk_B) != (sk_B)))),
% 0.92/1.17      inference('demod', [status(thm)], ['54', '57', '58', '59', '60', '61'])).
% 0.92/1.17  thf('63', plain,
% 0.92/1.17      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 0.92/1.17      inference('simplify', [status(thm)], ['62'])).
% 0.92/1.17  thf('64', plain,
% 0.92/1.17      (![X40 : $i, X41 : $i]:
% 0.92/1.17         (((X40) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X40 @ X41))),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.92/1.17  thf('65', plain,
% 0.92/1.17      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.92/1.17      inference('sup-', [status(thm)], ['63', '64'])).
% 0.92/1.17  thf('66', plain, (((sk_A) != (k1_xboole_0))),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.17  thf('67', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 0.92/1.17      inference('simplify_reflect-', [status(thm)], ['65', '66'])).
% 0.92/1.17  thf('68', plain,
% 0.92/1.17      (![X38 : $i, X39 : $i]:
% 0.92/1.17         ((v2_funct_1 @ X39) | ~ (zip_tseitin_0 @ X39 @ X38))),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.92/1.17  thf('69', plain, ((v2_funct_1 @ sk_D)),
% 0.92/1.17      inference('sup-', [status(thm)], ['67', '68'])).
% 0.92/1.17  thf('70', plain,
% 0.92/1.17      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 0.92/1.17      inference('demod', [status(thm)], ['46', '69'])).
% 0.92/1.17  thf('71', plain,
% 0.92/1.17      ((((k6_partfun1 @ (k1_relat_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.92/1.17        | ~ (v1_relat_1 @ sk_D)
% 0.92/1.17        | ~ (v1_funct_1 @ sk_D)
% 0.92/1.17        | ~ (v2_funct_1 @ sk_D))),
% 0.92/1.17      inference('sup+', [status(thm)], ['2', '70'])).
% 0.92/1.17  thf('72', plain,
% 0.92/1.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.17  thf(cc1_relset_1, axiom,
% 0.92/1.17    (![A:$i,B:$i,C:$i]:
% 0.92/1.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.92/1.17       ( v1_relat_1 @ C ) ))).
% 0.92/1.17  thf('73', plain,
% 0.92/1.17      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.92/1.17         ((v1_relat_1 @ X9)
% 0.92/1.17          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.92/1.17      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.92/1.17  thf('74', plain, ((v1_relat_1 @ sk_D)),
% 0.92/1.17      inference('sup-', [status(thm)], ['72', '73'])).
% 0.92/1.17  thf('75', plain, ((v1_funct_1 @ sk_D)),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.17  thf('76', plain, ((v2_funct_1 @ sk_D)),
% 0.92/1.17      inference('sup-', [status(thm)], ['67', '68'])).
% 0.92/1.17  thf('77', plain,
% 0.92/1.17      (((k6_partfun1 @ (k1_relat_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 0.92/1.17      inference('demod', [status(thm)], ['71', '74', '75', '76'])).
% 0.92/1.17  thf(t71_relat_1, axiom,
% 0.92/1.17    (![A:$i]:
% 0.92/1.17     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.92/1.17       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.92/1.17  thf('78', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X0)) = (X0))),
% 0.92/1.17      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.92/1.17  thf('79', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.92/1.17      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.92/1.17  thf('80', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0))),
% 0.92/1.17      inference('demod', [status(thm)], ['78', '79'])).
% 0.92/1.17  thf('81', plain,
% 0.92/1.17      (((k1_relat_1 @ (k6_partfun1 @ sk_B)) = (k1_relat_1 @ sk_D))),
% 0.92/1.17      inference('sup+', [status(thm)], ['77', '80'])).
% 0.92/1.17  thf('82', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0))),
% 0.92/1.17      inference('demod', [status(thm)], ['78', '79'])).
% 0.92/1.17  thf('83', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.92/1.17      inference('demod', [status(thm)], ['81', '82'])).
% 0.92/1.17  thf('84', plain,
% 0.92/1.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.17  thf('85', plain,
% 0.92/1.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.17  thf(redefinition_k1_partfun1, axiom,
% 0.92/1.17    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.92/1.17     ( ( ( v1_funct_1 @ E ) & 
% 0.92/1.17         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.92/1.17         ( v1_funct_1 @ F ) & 
% 0.92/1.17         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.92/1.17       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.92/1.17  thf('86', plain,
% 0.92/1.17      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.92/1.17         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.92/1.17          | ~ (v1_funct_1 @ X27)
% 0.92/1.17          | ~ (v1_funct_1 @ X30)
% 0.92/1.17          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.92/1.17          | ((k1_partfun1 @ X28 @ X29 @ X31 @ X32 @ X27 @ X30)
% 0.92/1.17              = (k5_relat_1 @ X27 @ X30)))),
% 0.92/1.17      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.92/1.17  thf('87', plain,
% 0.92/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.92/1.17         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.92/1.17            = (k5_relat_1 @ sk_C @ X0))
% 0.92/1.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.92/1.17          | ~ (v1_funct_1 @ X0)
% 0.92/1.17          | ~ (v1_funct_1 @ sk_C))),
% 0.92/1.17      inference('sup-', [status(thm)], ['85', '86'])).
% 0.92/1.17  thf('88', plain, ((v1_funct_1 @ sk_C)),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.17  thf('89', plain,
% 0.92/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.92/1.17         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.92/1.17            = (k5_relat_1 @ sk_C @ X0))
% 0.92/1.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.92/1.17          | ~ (v1_funct_1 @ X0))),
% 0.92/1.17      inference('demod', [status(thm)], ['87', '88'])).
% 0.92/1.17  thf('90', plain,
% 0.92/1.17      ((~ (v1_funct_1 @ sk_D)
% 0.92/1.17        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.92/1.17            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.92/1.17      inference('sup-', [status(thm)], ['84', '89'])).
% 0.92/1.17  thf('91', plain, ((v1_funct_1 @ sk_D)),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.17  thf('92', plain,
% 0.92/1.17      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.92/1.17         = (k6_partfun1 @ sk_A))),
% 0.92/1.17      inference('demod', [status(thm)], ['26', '27'])).
% 0.92/1.17  thf('93', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 0.92/1.17      inference('demod', [status(thm)], ['90', '91', '92'])).
% 0.92/1.17  thf(t63_funct_1, axiom,
% 0.92/1.17    (![A:$i]:
% 0.92/1.17     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.92/1.17       ( ![B:$i]:
% 0.92/1.17         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.92/1.17           ( ( ( v2_funct_1 @ A ) & 
% 0.92/1.17               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.92/1.17               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.92/1.17             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.92/1.17  thf('94', plain,
% 0.92/1.17      (![X7 : $i, X8 : $i]:
% 0.92/1.17         (~ (v1_relat_1 @ X7)
% 0.92/1.17          | ~ (v1_funct_1 @ X7)
% 0.92/1.17          | ((X7) = (k2_funct_1 @ X8))
% 0.92/1.17          | ((k5_relat_1 @ X8 @ X7) != (k6_relat_1 @ (k1_relat_1 @ X8)))
% 0.92/1.17          | ((k2_relat_1 @ X8) != (k1_relat_1 @ X7))
% 0.92/1.17          | ~ (v2_funct_1 @ X8)
% 0.92/1.17          | ~ (v1_funct_1 @ X8)
% 0.92/1.17          | ~ (v1_relat_1 @ X8))),
% 0.92/1.17      inference('cnf', [status(esa)], [t63_funct_1])).
% 0.92/1.17  thf('95', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.92/1.17      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.92/1.17  thf('96', plain,
% 0.92/1.17      (![X7 : $i, X8 : $i]:
% 0.92/1.17         (~ (v1_relat_1 @ X7)
% 0.92/1.17          | ~ (v1_funct_1 @ X7)
% 0.92/1.17          | ((X7) = (k2_funct_1 @ X8))
% 0.92/1.17          | ((k5_relat_1 @ X8 @ X7) != (k6_partfun1 @ (k1_relat_1 @ X8)))
% 0.92/1.17          | ((k2_relat_1 @ X8) != (k1_relat_1 @ X7))
% 0.92/1.17          | ~ (v2_funct_1 @ X8)
% 0.92/1.17          | ~ (v1_funct_1 @ X8)
% 0.92/1.17          | ~ (v1_relat_1 @ X8))),
% 0.92/1.17      inference('demod', [status(thm)], ['94', '95'])).
% 0.92/1.17  thf('97', plain,
% 0.92/1.17      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 0.92/1.17        | ~ (v1_relat_1 @ sk_C)
% 0.92/1.17        | ~ (v1_funct_1 @ sk_C)
% 0.92/1.17        | ~ (v2_funct_1 @ sk_C)
% 0.92/1.17        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.92/1.17        | ((sk_D) = (k2_funct_1 @ sk_C))
% 0.92/1.17        | ~ (v1_funct_1 @ sk_D)
% 0.92/1.17        | ~ (v1_relat_1 @ sk_D))),
% 0.92/1.17      inference('sup-', [status(thm)], ['93', '96'])).
% 0.92/1.17  thf('98', plain,
% 0.92/1.17      (![X6 : $i]:
% 0.92/1.17         (~ (v2_funct_1 @ X6)
% 0.92/1.17          | ((k5_relat_1 @ X6 @ (k2_funct_1 @ X6))
% 0.92/1.17              = (k6_partfun1 @ (k1_relat_1 @ X6)))
% 0.92/1.17          | ~ (v1_funct_1 @ X6)
% 0.92/1.17          | ~ (v1_relat_1 @ X6))),
% 0.92/1.17      inference('demod', [status(thm)], ['0', '1'])).
% 0.92/1.17  thf('99', plain,
% 0.92/1.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.17  thf('100', plain,
% 0.92/1.17      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.92/1.17         (((X47) = (k1_xboole_0))
% 0.92/1.17          | ~ (v1_funct_1 @ X48)
% 0.92/1.17          | ~ (v1_funct_2 @ X48 @ X49 @ X47)
% 0.92/1.17          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X47)))
% 0.92/1.17          | ((k5_relat_1 @ X48 @ (k2_funct_1 @ X48)) = (k6_partfun1 @ X49))
% 0.92/1.17          | ~ (v2_funct_1 @ X48)
% 0.92/1.17          | ((k2_relset_1 @ X49 @ X47 @ X48) != (X47)))),
% 0.92/1.17      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.92/1.17  thf('101', plain,
% 0.92/1.17      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.92/1.17        | ~ (v2_funct_1 @ sk_C)
% 0.92/1.17        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.92/1.17        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.92/1.17        | ~ (v1_funct_1 @ sk_C)
% 0.92/1.17        | ((sk_B) = (k1_xboole_0)))),
% 0.92/1.17      inference('sup-', [status(thm)], ['99', '100'])).
% 0.92/1.17  thf('102', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.17  thf('103', plain, ((v2_funct_1 @ sk_C)),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.17  thf('104', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.17  thf('105', plain, ((v1_funct_1 @ sk_C)),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.17  thf('106', plain,
% 0.92/1.17      ((((sk_B) != (sk_B))
% 0.92/1.17        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.92/1.17        | ((sk_B) = (k1_xboole_0)))),
% 0.92/1.17      inference('demod', [status(thm)], ['101', '102', '103', '104', '105'])).
% 0.92/1.17  thf('107', plain,
% 0.92/1.17      ((((sk_B) = (k1_xboole_0))
% 0.92/1.17        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 0.92/1.17      inference('simplify', [status(thm)], ['106'])).
% 0.92/1.17  thf('108', plain, (((sk_B) != (k1_xboole_0))),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.17  thf('109', plain,
% 0.92/1.17      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 0.92/1.17      inference('simplify_reflect-', [status(thm)], ['107', '108'])).
% 0.92/1.17  thf('110', plain,
% 0.92/1.17      ((((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.92/1.17        | ~ (v1_relat_1 @ sk_C)
% 0.92/1.17        | ~ (v1_funct_1 @ sk_C)
% 0.92/1.17        | ~ (v2_funct_1 @ sk_C))),
% 0.92/1.17      inference('sup+', [status(thm)], ['98', '109'])).
% 0.92/1.17  thf('111', plain,
% 0.92/1.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.17  thf('112', plain,
% 0.92/1.17      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.92/1.17         ((v1_relat_1 @ X9)
% 0.92/1.17          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.92/1.17      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.92/1.17  thf('113', plain, ((v1_relat_1 @ sk_C)),
% 0.92/1.17      inference('sup-', [status(thm)], ['111', '112'])).
% 0.92/1.17  thf('114', plain, ((v1_funct_1 @ sk_C)),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.17  thf('115', plain, ((v2_funct_1 @ sk_C)),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.17  thf('116', plain,
% 0.92/1.17      (((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 0.92/1.17      inference('demod', [status(thm)], ['110', '113', '114', '115'])).
% 0.92/1.17  thf('117', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0))),
% 0.92/1.17      inference('demod', [status(thm)], ['78', '79'])).
% 0.92/1.17  thf('118', plain,
% 0.92/1.17      (((k1_relat_1 @ (k6_partfun1 @ sk_A)) = (k1_relat_1 @ sk_C))),
% 0.92/1.17      inference('sup+', [status(thm)], ['116', '117'])).
% 0.92/1.17  thf('119', plain, (![X0 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X0)) = (X0))),
% 0.92/1.17      inference('demod', [status(thm)], ['78', '79'])).
% 0.92/1.17  thf('120', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.92/1.17      inference('demod', [status(thm)], ['118', '119'])).
% 0.92/1.17  thf('121', plain, ((v1_relat_1 @ sk_C)),
% 0.92/1.17      inference('sup-', [status(thm)], ['111', '112'])).
% 0.92/1.17  thf('122', plain, ((v1_funct_1 @ sk_C)),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.17  thf('123', plain, ((v2_funct_1 @ sk_C)),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.17  thf('124', plain,
% 0.92/1.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.17  thf('125', plain,
% 0.92/1.17      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.92/1.17         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.92/1.17          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.92/1.17      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.92/1.17  thf('126', plain,
% 0.92/1.17      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.92/1.17      inference('sup-', [status(thm)], ['124', '125'])).
% 0.92/1.17  thf('127', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.17  thf('128', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.92/1.17      inference('sup+', [status(thm)], ['126', '127'])).
% 0.92/1.17  thf('129', plain, ((v1_funct_1 @ sk_D)),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.17  thf('130', plain, ((v1_relat_1 @ sk_D)),
% 0.92/1.17      inference('sup-', [status(thm)], ['72', '73'])).
% 0.92/1.17  thf('131', plain,
% 0.92/1.17      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 0.92/1.17        | ((sk_B) != (k1_relat_1 @ sk_D))
% 0.92/1.17        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 0.92/1.17      inference('demod', [status(thm)],
% 0.92/1.17                ['97', '120', '121', '122', '123', '128', '129', '130'])).
% 0.92/1.17  thf('132', plain,
% 0.92/1.17      ((((sk_D) = (k2_funct_1 @ sk_C)) | ((sk_B) != (k1_relat_1 @ sk_D)))),
% 0.92/1.17      inference('simplify', [status(thm)], ['131'])).
% 0.92/1.17  thf('133', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.92/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.17  thf('134', plain, (((sk_B) != (k1_relat_1 @ sk_D))),
% 0.92/1.17      inference('simplify_reflect-', [status(thm)], ['132', '133'])).
% 0.92/1.17  thf('135', plain, ($false),
% 0.92/1.17      inference('simplify_reflect-', [status(thm)], ['83', '134'])).
% 0.92/1.17  
% 0.92/1.17  % SZS output end Refutation
% 0.92/1.17  
% 1.01/1.17  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

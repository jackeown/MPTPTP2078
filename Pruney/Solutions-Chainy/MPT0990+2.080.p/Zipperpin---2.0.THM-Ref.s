%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.z4V1hqWNBx

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:07 EST 2020

% Result     : Theorem 37.01s
% Output     : Refutation 37.01s
% Verified   : 
% Statistics : Number of formulae       :  291 (1566 expanded)
%              Number of leaves         :   46 ( 484 expanded)
%              Depth                    :   27
%              Number of atoms          : 3172 (37078 expanded)
%              Number of equality atoms :  197 (2380 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

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

thf('1',plain,(
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

thf('2',plain,(
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

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('4',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( X47 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_funct_2 @ X48 @ X49 @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X47 ) ) )
      | ( ( k5_relat_1 @ X48 @ ( k2_funct_1 @ X48 ) )
        = ( k6_relat_1 @ X49 ) )
      | ~ ( v2_funct_1 @ X48 )
      | ( ( k2_relset_1 @ X49 @ X47 @ X48 )
       != X47 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','4'])).

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
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('11',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

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
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X20 @ X21 @ X23 @ X24 @ X19 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X24 ) ) ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( X15 = X18 )
      | ~ ( r2_relset_1 @ X16 @ X17 @ X15 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','22'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('24',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('25',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('26',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X26 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
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

thf('30',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('31',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( r2_relset_1 @ X35 @ X35 @ ( k1_partfun1 @ X35 @ X36 @ X36 @ X35 @ X34 @ X37 ) @ ( k6_relat_1 @ X35 ) )
      | ( ( k2_relset_1 @ X36 @ X35 @ X37 )
        = X35 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) )
      | ~ ( v1_funct_2 @ X37 @ X36 @ X35 )
      | ~ ( v1_funct_1 @ X37 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['27','35'])).

thf('37',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X26 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('38',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( r2_relset_1 @ X16 @ X17 @ X15 @ X18 )
      | ( X15 != X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('39',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_relset_1 @ X16 @ X17 @ X18 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['6','7'])).

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
    inference(demod,[status(thm)],['36','40','41','42','43','44'])).

thf('46',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['8','45'])).

thf('47',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','46','47','48'])).

thf('50',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('54',plain,(
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

thf('55',plain,(
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

thf('56',plain,(
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
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['53','59'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('61',plain,(
    ! [X6: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('62',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['60','61','62','63','64','65'])).

thf('67',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X40: $i,X41: $i] :
      ( ( X40 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('69',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X38: $i,X39: $i] :
      ( ( v2_funct_1 @ X39 )
      | ~ ( zip_tseitin_0 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('73',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['52','73'])).

thf('75',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['36','40','41','42','43','44'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('76',plain,(
    ! [X4: $i] :
      ( ( ( k5_relat_1 @ X4 @ ( k6_relat_1 @ ( k2_relat_1 @ X4 ) ) )
        = X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('77',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k6_relat_1 @ sk_A ) )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('79',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('80',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k5_relat_1 @ sk_D @ ( k6_relat_1 @ sk_A ) )
    = sk_D ),
    inference(demod,[status(thm)],['77','80'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('82',plain,(
    ! [X3: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X3 ) ) @ X3 )
        = X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X26 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('87',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['85','88'])).

thf('90',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k6_relat_1 @ sk_A ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_D ) ) @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['81','89'])).

thf('91',plain,
    ( ( k5_relat_1 @ sk_D @ ( k6_relat_1 @ sk_A ) )
    = sk_D ),
    inference(demod,[status(thm)],['77','80'])).

thf('92',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['78','79'])).

thf('93',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('94',plain,
    ( sk_D
    = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_D ) ) @ sk_D ) ),
    inference(demod,[status(thm)],['90','91','92','93'])).

thf('95',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
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

thf('97',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( ( k1_partfun1 @ X28 @ X29 @ X31 @ X32 @ X27 @ X30 )
        = ( k5_relat_1 @ X27 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['95','100'])).

thf('102',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('104',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['85','88'])).

thf('106',plain,(
    ! [X3: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X3 ) ) @ X3 )
        = X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X3 )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ ( k5_relat_1 @ X0 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) @ X3 )
        = ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ ( k5_relat_1 @ X0 @ X3 ) ) ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X2 ) ) @ X1 )
        = ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) @ ( k5_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['106','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X2 ) ) @ X1 )
        = ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) @ ( k5_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X2 ) ) @ X1 )
        = ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) @ ( k5_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) @ X1 ) @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['105','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) @ X1 ) @ ( k5_relat_1 @ X0 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X0 @ sk_C ) @ sk_D )
        = ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) @ ( k6_relat_1 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['104','116'])).

thf('118',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('120',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['78','79'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X0 @ sk_C ) @ sk_D )
        = ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) @ ( k6_relat_1 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['117','120','121'])).

thf('123',plain,
    ( ( ( k5_relat_1 @ ( k5_relat_1 @ sk_D @ sk_C ) @ sk_D )
      = ( k5_relat_1 @ sk_D @ ( k6_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['94','122'])).

thf('124',plain,
    ( ( k5_relat_1 @ sk_D @ ( k6_relat_1 @ sk_A ) )
    = sk_D ),
    inference(demod,[status(thm)],['77','80'])).

thf('125',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['78','79'])).

thf('126',plain,
    ( ( k5_relat_1 @ ( k5_relat_1 @ sk_D @ sk_C ) @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_D @ X0 )
        = ( k5_relat_1 @ ( k5_relat_1 @ sk_D @ sk_C ) @ ( k5_relat_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_D @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['78','79'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_D @ X0 )
        = ( k5_relat_1 @ ( k5_relat_1 @ sk_D @ sk_C ) @ ( k5_relat_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_D @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X20 @ X21 @ X23 @ X24 @ X19 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('134',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['131','136'])).

thf('138',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( ( k1_partfun1 @ X28 @ X29 @ X31 @ X32 @ X27 @ X30 )
        = ( k5_relat_1 @ X27 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('142',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C )
      = ( k5_relat_1 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['139','144'])).

thf('146',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C )
    = ( k5_relat_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['137','138','147'])).

thf('149',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('150',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_D @ X0 )
        = ( k5_relat_1 @ ( k5_relat_1 @ sk_D @ sk_C ) @ ( k5_relat_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['130','150'])).

thf('152',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k5_relat_1 @ ( k5_relat_1 @ sk_D @ sk_C ) @ ( k6_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['74','151'])).

thf('153',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['52','73'])).

thf('154',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('156',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['156','157'])).

thf('159',plain,
    ( sk_D
    = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_D ) ) @ sk_D ) ),
    inference(demod,[status(thm)],['90','91','92','93'])).

thf('160',plain,(
    ! [X4: $i] :
      ( ( ( k5_relat_1 @ X4 @ ( k6_relat_1 @ ( k2_relat_1 @ X4 ) ) )
        = X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('161',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) @ X1 ) @ ( k5_relat_1 @ X0 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['164'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ sk_D @ X0 ) @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['159','165'])).

thf('167',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['78','79'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ sk_D @ X0 ) @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,
    ( ( ( k5_relat_1 @ ( k5_relat_1 @ sk_D @ sk_C ) @ ( k6_relat_1 @ sk_B ) )
      = ( k5_relat_1 @ sk_D @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['158','168'])).

thf('170',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['118','119'])).

thf('171',plain,
    ( ( k5_relat_1 @ ( k5_relat_1 @ sk_D @ sk_C ) @ ( k6_relat_1 @ sk_B ) )
    = ( k5_relat_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['169','170'])).

thf('172',plain,
    ( ( ( k6_relat_1 @ sk_B )
      = ( k5_relat_1 @ sk_D @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['152','153','171'])).

thf('173',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k6_relat_1 @ sk_B )
      = ( k5_relat_1 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','172'])).

thf('174',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['78','79'])).

thf('175',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( k6_relat_1 @ sk_B )
    = ( k5_relat_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['173','174','175'])).

thf('177',plain,(
    ! [X3: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X3 ) ) @ X3 )
        = X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('178',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X0 @ sk_C ) @ sk_D )
        = ( k5_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) @ ( k6_relat_1 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['117','120','121'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X0 @ sk_C ) @ sk_D )
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X0 @ sk_C ) @ sk_D )
        = ( k5_relat_1 @ X0 @ ( k6_relat_1 @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['179'])).

thf('181',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ sk_D @ ( k6_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['176','180'])).

thf('182',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('183',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('184',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( X47 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_funct_2 @ X48 @ X49 @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X47 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X48 ) @ X48 )
        = ( k6_partfun1 @ X47 ) )
      | ~ ( v2_funct_1 @ X48 )
      | ( ( k2_relset_1 @ X49 @ X47 @ X48 )
       != X47 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('186',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('187',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( X47 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_funct_2 @ X48 @ X49 @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X47 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X48 ) @ X48 )
        = ( k6_relat_1 @ X47 ) )
      | ~ ( v2_funct_1 @ X48 )
      | ( ( k2_relset_1 @ X49 @ X47 @ X48 )
       != X47 ) ) ),
    inference(demod,[status(thm)],['185','186'])).

thf('188',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['184','187'])).

thf('189',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['188','189','190','191','192'])).

thf('194',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['193'])).

thf('195',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['194','195'])).

thf('197',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('198',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['196','197'])).

thf('199',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['118','119'])).

thf('200',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['198','199'])).

thf('201',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['183','200'])).

thf('202',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['118','119'])).

thf('203',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['201','202','203'])).

thf('205',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['182','204'])).

thf('206',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('207',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( X47 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_funct_2 @ X48 @ X49 @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X47 ) ) )
      | ( ( k5_relat_1 @ X48 @ ( k2_funct_1 @ X48 ) )
        = ( k6_relat_1 @ X49 ) )
      | ~ ( v2_funct_1 @ X48 )
      | ( ( k2_relset_1 @ X49 @ X47 @ X48 )
       != X47 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('209',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['207','208'])).

thf('210',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['209','210','211','212','213'])).

thf('215',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['214'])).

thf('216',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['215','216'])).

thf('218',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['201','202','203'])).

thf('219',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['217','218'])).

thf('220',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['156','157'])).

thf('221',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
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

thf('222',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_relat_1 @ X7 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('223',plain,(
    ! [X3: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X3 ) ) @ X3 )
        = X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('224',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['222','223'])).

thf('225',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['221','224'])).

thf('226',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['225'])).

thf('227',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['220','226'])).

thf('228',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['118','119'])).

thf('229',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['227','228','229','230'])).

thf('232',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['219','231'])).

thf('233',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['206','232'])).

thf('234',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['118','119'])).

thf('235',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['233','234','235'])).

thf('237',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['78','79'])).

thf('238',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_D )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['205','236','237'])).

thf('239',plain,
    ( ( k5_relat_1 @ sk_D @ ( k6_relat_1 @ sk_A ) )
    = sk_D ),
    inference(demod,[status(thm)],['77','80'])).

thf('240',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['78','79'])).

thf('241',plain,
    ( ( k2_funct_1 @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['181','238','239','240'])).

thf('242',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['241','242'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.z4V1hqWNBx
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:24:17 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 37.01/37.21  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 37.01/37.21  % Solved by: fo/fo7.sh
% 37.01/37.21  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 37.01/37.21  % done 4795 iterations in 36.742s
% 37.01/37.21  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 37.01/37.21  % SZS output start Refutation
% 37.01/37.21  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 37.01/37.21  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 37.01/37.21  thf(sk_B_type, type, sk_B: $i).
% 37.01/37.21  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 37.01/37.21  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 37.01/37.21  thf(sk_D_type, type, sk_D: $i).
% 37.01/37.21  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 37.01/37.21  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 37.01/37.21  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 37.01/37.21  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 37.01/37.21  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 37.01/37.21  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 37.01/37.21  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 37.01/37.21  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 37.01/37.21  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 37.01/37.21  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 37.01/37.21  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 37.01/37.21  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 37.01/37.21  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 37.01/37.21  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 37.01/37.21  thf(sk_A_type, type, sk_A: $i).
% 37.01/37.21  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 37.01/37.21  thf(sk_C_type, type, sk_C: $i).
% 37.01/37.21  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 37.01/37.21  thf(dt_k2_funct_1, axiom,
% 37.01/37.21    (![A:$i]:
% 37.01/37.21     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 37.01/37.21       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 37.01/37.21         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 37.01/37.21  thf('0', plain,
% 37.01/37.21      (![X5 : $i]:
% 37.01/37.21         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 37.01/37.21          | ~ (v1_funct_1 @ X5)
% 37.01/37.21          | ~ (v1_relat_1 @ X5))),
% 37.01/37.21      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 37.01/37.21  thf(t36_funct_2, conjecture,
% 37.01/37.21    (![A:$i,B:$i,C:$i]:
% 37.01/37.21     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 37.01/37.21         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 37.01/37.21       ( ![D:$i]:
% 37.01/37.21         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 37.01/37.21             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 37.01/37.21           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 37.01/37.21               ( r2_relset_1 @
% 37.01/37.21                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 37.01/37.21                 ( k6_partfun1 @ A ) ) & 
% 37.01/37.21               ( v2_funct_1 @ C ) ) =>
% 37.01/37.21             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 37.01/37.21               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 37.01/37.21  thf(zf_stmt_0, negated_conjecture,
% 37.01/37.21    (~( ![A:$i,B:$i,C:$i]:
% 37.01/37.21        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 37.01/37.21            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 37.01/37.21          ( ![D:$i]:
% 37.01/37.21            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 37.01/37.21                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 37.01/37.21              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 37.01/37.21                  ( r2_relset_1 @
% 37.01/37.21                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 37.01/37.21                    ( k6_partfun1 @ A ) ) & 
% 37.01/37.21                  ( v2_funct_1 @ C ) ) =>
% 37.01/37.21                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 37.01/37.21                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 37.01/37.21    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 37.01/37.21  thf('1', plain,
% 37.01/37.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf(t35_funct_2, axiom,
% 37.01/37.21    (![A:$i,B:$i,C:$i]:
% 37.01/37.21     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 37.01/37.21         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 37.01/37.21       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 37.01/37.21         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 37.01/37.21           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 37.01/37.21             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 37.01/37.21  thf('2', plain,
% 37.01/37.21      (![X47 : $i, X48 : $i, X49 : $i]:
% 37.01/37.21         (((X47) = (k1_xboole_0))
% 37.01/37.21          | ~ (v1_funct_1 @ X48)
% 37.01/37.21          | ~ (v1_funct_2 @ X48 @ X49 @ X47)
% 37.01/37.21          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X47)))
% 37.01/37.21          | ((k5_relat_1 @ X48 @ (k2_funct_1 @ X48)) = (k6_partfun1 @ X49))
% 37.01/37.21          | ~ (v2_funct_1 @ X48)
% 37.01/37.21          | ((k2_relset_1 @ X49 @ X47 @ X48) != (X47)))),
% 37.01/37.21      inference('cnf', [status(esa)], [t35_funct_2])).
% 37.01/37.21  thf(redefinition_k6_partfun1, axiom,
% 37.01/37.21    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 37.01/37.21  thf('3', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 37.01/37.21      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 37.01/37.21  thf('4', plain,
% 37.01/37.21      (![X47 : $i, X48 : $i, X49 : $i]:
% 37.01/37.21         (((X47) = (k1_xboole_0))
% 37.01/37.21          | ~ (v1_funct_1 @ X48)
% 37.01/37.21          | ~ (v1_funct_2 @ X48 @ X49 @ X47)
% 37.01/37.21          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X47)))
% 37.01/37.21          | ((k5_relat_1 @ X48 @ (k2_funct_1 @ X48)) = (k6_relat_1 @ X49))
% 37.01/37.21          | ~ (v2_funct_1 @ X48)
% 37.01/37.21          | ((k2_relset_1 @ X49 @ X47 @ X48) != (X47)))),
% 37.01/37.21      inference('demod', [status(thm)], ['2', '3'])).
% 37.01/37.21  thf('5', plain,
% 37.01/37.21      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 37.01/37.21        | ~ (v2_funct_1 @ sk_D)
% 37.01/37.21        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 37.01/37.21        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 37.01/37.21        | ~ (v1_funct_1 @ sk_D)
% 37.01/37.21        | ((sk_A) = (k1_xboole_0)))),
% 37.01/37.21      inference('sup-', [status(thm)], ['1', '4'])).
% 37.01/37.21  thf('6', plain,
% 37.01/37.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf(redefinition_k2_relset_1, axiom,
% 37.01/37.21    (![A:$i,B:$i,C:$i]:
% 37.01/37.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 37.01/37.21       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 37.01/37.21  thf('7', plain,
% 37.01/37.21      (![X12 : $i, X13 : $i, X14 : $i]:
% 37.01/37.21         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 37.01/37.21          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 37.01/37.21      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 37.01/37.21  thf('8', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 37.01/37.21      inference('sup-', [status(thm)], ['6', '7'])).
% 37.01/37.21  thf('9', plain,
% 37.01/37.21      ((r2_relset_1 @ sk_A @ sk_A @ 
% 37.01/37.21        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 37.01/37.21        (k6_partfun1 @ sk_A))),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('10', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 37.01/37.21      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 37.01/37.21  thf('11', plain,
% 37.01/37.21      ((r2_relset_1 @ sk_A @ sk_A @ 
% 37.01/37.21        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 37.01/37.21        (k6_relat_1 @ sk_A))),
% 37.01/37.21      inference('demod', [status(thm)], ['9', '10'])).
% 37.01/37.21  thf('12', plain,
% 37.01/37.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('13', plain,
% 37.01/37.21      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf(dt_k1_partfun1, axiom,
% 37.01/37.21    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 37.01/37.21     ( ( ( v1_funct_1 @ E ) & 
% 37.01/37.21         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 37.01/37.21         ( v1_funct_1 @ F ) & 
% 37.01/37.21         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 37.01/37.21       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 37.01/37.21         ( m1_subset_1 @
% 37.01/37.21           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 37.01/37.21           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 37.01/37.21  thf('14', plain,
% 37.01/37.21      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 37.01/37.21         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 37.01/37.21          | ~ (v1_funct_1 @ X19)
% 37.01/37.21          | ~ (v1_funct_1 @ X22)
% 37.01/37.21          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 37.01/37.21          | (m1_subset_1 @ (k1_partfun1 @ X20 @ X21 @ X23 @ X24 @ X19 @ X22) @ 
% 37.01/37.21             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X24))))),
% 37.01/37.21      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 37.01/37.21  thf('15', plain,
% 37.01/37.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.01/37.21         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 37.01/37.21           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 37.01/37.21          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 37.01/37.21          | ~ (v1_funct_1 @ X1)
% 37.01/37.21          | ~ (v1_funct_1 @ sk_C))),
% 37.01/37.21      inference('sup-', [status(thm)], ['13', '14'])).
% 37.01/37.21  thf('16', plain, ((v1_funct_1 @ sk_C)),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('17', plain,
% 37.01/37.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.01/37.21         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 37.01/37.21           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 37.01/37.21          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 37.01/37.21          | ~ (v1_funct_1 @ X1))),
% 37.01/37.21      inference('demod', [status(thm)], ['15', '16'])).
% 37.01/37.21  thf('18', plain,
% 37.01/37.21      ((~ (v1_funct_1 @ sk_D)
% 37.01/37.21        | (m1_subset_1 @ 
% 37.01/37.21           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 37.01/37.21           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 37.01/37.21      inference('sup-', [status(thm)], ['12', '17'])).
% 37.01/37.21  thf('19', plain, ((v1_funct_1 @ sk_D)),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('20', plain,
% 37.01/37.21      ((m1_subset_1 @ 
% 37.01/37.21        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 37.01/37.21        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 37.01/37.21      inference('demod', [status(thm)], ['18', '19'])).
% 37.01/37.21  thf(redefinition_r2_relset_1, axiom,
% 37.01/37.21    (![A:$i,B:$i,C:$i,D:$i]:
% 37.01/37.21     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 37.01/37.21         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 37.01/37.21       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 37.01/37.21  thf('21', plain,
% 37.01/37.21      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 37.01/37.21         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 37.01/37.21          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 37.01/37.21          | ((X15) = (X18))
% 37.01/37.21          | ~ (r2_relset_1 @ X16 @ X17 @ X15 @ X18))),
% 37.01/37.21      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 37.01/37.21  thf('22', plain,
% 37.01/37.21      (![X0 : $i]:
% 37.01/37.21         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 37.01/37.21             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 37.01/37.21          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 37.01/37.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 37.01/37.21      inference('sup-', [status(thm)], ['20', '21'])).
% 37.01/37.21  thf('23', plain,
% 37.01/37.21      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 37.01/37.21           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 37.01/37.21        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 37.01/37.21            = (k6_relat_1 @ sk_A)))),
% 37.01/37.21      inference('sup-', [status(thm)], ['11', '22'])).
% 37.01/37.21  thf(dt_k6_partfun1, axiom,
% 37.01/37.21    (![A:$i]:
% 37.01/37.21     ( ( m1_subset_1 @
% 37.01/37.21         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 37.01/37.21       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 37.01/37.21  thf('24', plain,
% 37.01/37.21      (![X26 : $i]:
% 37.01/37.21         (m1_subset_1 @ (k6_partfun1 @ X26) @ 
% 37.01/37.21          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X26)))),
% 37.01/37.21      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 37.01/37.21  thf('25', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 37.01/37.21      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 37.01/37.21  thf('26', plain,
% 37.01/37.21      (![X26 : $i]:
% 37.01/37.21         (m1_subset_1 @ (k6_relat_1 @ X26) @ 
% 37.01/37.21          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X26)))),
% 37.01/37.21      inference('demod', [status(thm)], ['24', '25'])).
% 37.01/37.21  thf('27', plain,
% 37.01/37.21      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 37.01/37.21         = (k6_relat_1 @ sk_A))),
% 37.01/37.21      inference('demod', [status(thm)], ['23', '26'])).
% 37.01/37.21  thf('28', plain,
% 37.01/37.21      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf(t24_funct_2, axiom,
% 37.01/37.21    (![A:$i,B:$i,C:$i]:
% 37.01/37.21     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 37.01/37.21         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 37.01/37.21       ( ![D:$i]:
% 37.01/37.21         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 37.01/37.21             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 37.01/37.21           ( ( r2_relset_1 @
% 37.01/37.21               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 37.01/37.21               ( k6_partfun1 @ B ) ) =>
% 37.01/37.21             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 37.01/37.21  thf('29', plain,
% 37.01/37.21      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 37.01/37.21         (~ (v1_funct_1 @ X34)
% 37.01/37.21          | ~ (v1_funct_2 @ X34 @ X35 @ X36)
% 37.01/37.21          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 37.01/37.21          | ~ (r2_relset_1 @ X35 @ X35 @ 
% 37.01/37.21               (k1_partfun1 @ X35 @ X36 @ X36 @ X35 @ X34 @ X37) @ 
% 37.01/37.21               (k6_partfun1 @ X35))
% 37.01/37.21          | ((k2_relset_1 @ X36 @ X35 @ X37) = (X35))
% 37.01/37.21          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 37.01/37.21          | ~ (v1_funct_2 @ X37 @ X36 @ X35)
% 37.01/37.21          | ~ (v1_funct_1 @ X37))),
% 37.01/37.21      inference('cnf', [status(esa)], [t24_funct_2])).
% 37.01/37.21  thf('30', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 37.01/37.21      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 37.01/37.21  thf('31', plain,
% 37.01/37.21      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 37.01/37.21         (~ (v1_funct_1 @ X34)
% 37.01/37.21          | ~ (v1_funct_2 @ X34 @ X35 @ X36)
% 37.01/37.21          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 37.01/37.21          | ~ (r2_relset_1 @ X35 @ X35 @ 
% 37.01/37.21               (k1_partfun1 @ X35 @ X36 @ X36 @ X35 @ X34 @ X37) @ 
% 37.01/37.21               (k6_relat_1 @ X35))
% 37.01/37.21          | ((k2_relset_1 @ X36 @ X35 @ X37) = (X35))
% 37.01/37.21          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 37.01/37.21          | ~ (v1_funct_2 @ X37 @ X36 @ X35)
% 37.01/37.21          | ~ (v1_funct_1 @ X37))),
% 37.01/37.21      inference('demod', [status(thm)], ['29', '30'])).
% 37.01/37.21  thf('32', plain,
% 37.01/37.21      (![X0 : $i]:
% 37.01/37.21         (~ (v1_funct_1 @ X0)
% 37.01/37.21          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 37.01/37.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 37.01/37.21          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 37.01/37.21          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 37.01/37.21               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 37.01/37.21               (k6_relat_1 @ sk_A))
% 37.01/37.21          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 37.01/37.21          | ~ (v1_funct_1 @ sk_C))),
% 37.01/37.21      inference('sup-', [status(thm)], ['28', '31'])).
% 37.01/37.21  thf('33', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('34', plain, ((v1_funct_1 @ sk_C)),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('35', plain,
% 37.01/37.21      (![X0 : $i]:
% 37.01/37.21         (~ (v1_funct_1 @ X0)
% 37.01/37.21          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 37.01/37.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 37.01/37.21          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 37.01/37.21          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 37.01/37.21               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 37.01/37.21               (k6_relat_1 @ sk_A)))),
% 37.01/37.21      inference('demod', [status(thm)], ['32', '33', '34'])).
% 37.01/37.21  thf('36', plain,
% 37.01/37.21      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 37.01/37.21           (k6_relat_1 @ sk_A))
% 37.01/37.21        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 37.01/37.21        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 37.01/37.21        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 37.01/37.21        | ~ (v1_funct_1 @ sk_D))),
% 37.01/37.21      inference('sup-', [status(thm)], ['27', '35'])).
% 37.01/37.21  thf('37', plain,
% 37.01/37.21      (![X26 : $i]:
% 37.01/37.21         (m1_subset_1 @ (k6_relat_1 @ X26) @ 
% 37.01/37.21          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X26)))),
% 37.01/37.21      inference('demod', [status(thm)], ['24', '25'])).
% 37.01/37.21  thf('38', plain,
% 37.01/37.21      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 37.01/37.21         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 37.01/37.21          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 37.01/37.21          | (r2_relset_1 @ X16 @ X17 @ X15 @ X18)
% 37.01/37.21          | ((X15) != (X18)))),
% 37.01/37.21      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 37.01/37.21  thf('39', plain,
% 37.01/37.21      (![X16 : $i, X17 : $i, X18 : $i]:
% 37.01/37.21         ((r2_relset_1 @ X16 @ X17 @ X18 @ X18)
% 37.01/37.21          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 37.01/37.21      inference('simplify', [status(thm)], ['38'])).
% 37.01/37.21  thf('40', plain,
% 37.01/37.21      (![X0 : $i]:
% 37.01/37.21         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 37.01/37.21      inference('sup-', [status(thm)], ['37', '39'])).
% 37.01/37.21  thf('41', plain,
% 37.01/37.21      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 37.01/37.21      inference('sup-', [status(thm)], ['6', '7'])).
% 37.01/37.21  thf('42', plain,
% 37.01/37.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('43', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('44', plain, ((v1_funct_1 @ sk_D)),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('45', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 37.01/37.21      inference('demod', [status(thm)], ['36', '40', '41', '42', '43', '44'])).
% 37.01/37.21  thf('46', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))),
% 37.01/37.21      inference('demod', [status(thm)], ['8', '45'])).
% 37.01/37.21  thf('47', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('48', plain, ((v1_funct_1 @ sk_D)),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('49', plain,
% 37.01/37.21      ((((sk_A) != (sk_A))
% 37.01/37.21        | ~ (v2_funct_1 @ sk_D)
% 37.01/37.21        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 37.01/37.21        | ((sk_A) = (k1_xboole_0)))),
% 37.01/37.21      inference('demod', [status(thm)], ['5', '46', '47', '48'])).
% 37.01/37.21  thf('50', plain,
% 37.01/37.21      ((((sk_A) = (k1_xboole_0))
% 37.01/37.21        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 37.01/37.21        | ~ (v2_funct_1 @ sk_D))),
% 37.01/37.21      inference('simplify', [status(thm)], ['49'])).
% 37.01/37.21  thf('51', plain, (((sk_A) != (k1_xboole_0))),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('52', plain,
% 37.01/37.21      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 37.01/37.21        | ~ (v2_funct_1 @ sk_D))),
% 37.01/37.21      inference('simplify_reflect-', [status(thm)], ['50', '51'])).
% 37.01/37.21  thf('53', plain,
% 37.01/37.21      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 37.01/37.21         = (k6_relat_1 @ sk_A))),
% 37.01/37.21      inference('demod', [status(thm)], ['23', '26'])).
% 37.01/37.21  thf('54', plain,
% 37.01/37.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf(t30_funct_2, axiom,
% 37.01/37.21    (![A:$i,B:$i,C:$i,D:$i]:
% 37.01/37.21     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 37.01/37.21         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 37.01/37.21       ( ![E:$i]:
% 37.01/37.21         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 37.01/37.21             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 37.01/37.21           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 37.01/37.21               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 37.01/37.21             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 37.01/37.21               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 37.01/37.21  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 37.01/37.21  thf(zf_stmt_2, axiom,
% 37.01/37.21    (![C:$i,B:$i]:
% 37.01/37.21     ( ( zip_tseitin_1 @ C @ B ) =>
% 37.01/37.21       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 37.01/37.21  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 37.01/37.21  thf(zf_stmt_4, axiom,
% 37.01/37.21    (![E:$i,D:$i]:
% 37.01/37.21     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 37.01/37.21  thf(zf_stmt_5, axiom,
% 37.01/37.21    (![A:$i,B:$i,C:$i,D:$i]:
% 37.01/37.21     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 37.01/37.21         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 37.01/37.21       ( ![E:$i]:
% 37.01/37.21         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 37.01/37.21             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 37.01/37.21           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 37.01/37.21               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 37.01/37.21             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 37.01/37.21  thf('55', plain,
% 37.01/37.21      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 37.01/37.21         (~ (v1_funct_1 @ X42)
% 37.01/37.21          | ~ (v1_funct_2 @ X42 @ X43 @ X44)
% 37.01/37.21          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 37.01/37.21          | (zip_tseitin_0 @ X42 @ X45)
% 37.01/37.21          | ~ (v2_funct_1 @ (k1_partfun1 @ X46 @ X43 @ X43 @ X44 @ X45 @ X42))
% 37.01/37.21          | (zip_tseitin_1 @ X44 @ X43)
% 37.01/37.21          | ((k2_relset_1 @ X46 @ X43 @ X45) != (X43))
% 37.01/37.21          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X43)))
% 37.01/37.21          | ~ (v1_funct_2 @ X45 @ X46 @ X43)
% 37.01/37.21          | ~ (v1_funct_1 @ X45))),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_5])).
% 37.01/37.21  thf('56', plain,
% 37.01/37.21      (![X0 : $i, X1 : $i]:
% 37.01/37.21         (~ (v1_funct_1 @ X0)
% 37.01/37.21          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 37.01/37.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 37.01/37.21          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 37.01/37.21          | (zip_tseitin_1 @ sk_A @ sk_B)
% 37.01/37.21          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 37.01/37.21          | (zip_tseitin_0 @ sk_D @ X0)
% 37.01/37.21          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 37.01/37.21          | ~ (v1_funct_1 @ sk_D))),
% 37.01/37.21      inference('sup-', [status(thm)], ['54', '55'])).
% 37.01/37.21  thf('57', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('58', plain, ((v1_funct_1 @ sk_D)),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('59', plain,
% 37.01/37.21      (![X0 : $i, X1 : $i]:
% 37.01/37.21         (~ (v1_funct_1 @ X0)
% 37.01/37.21          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 37.01/37.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 37.01/37.21          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 37.01/37.21          | (zip_tseitin_1 @ sk_A @ sk_B)
% 37.01/37.21          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 37.01/37.21          | (zip_tseitin_0 @ sk_D @ X0))),
% 37.01/37.21      inference('demod', [status(thm)], ['56', '57', '58'])).
% 37.01/37.21  thf('60', plain,
% 37.01/37.21      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 37.01/37.21        | (zip_tseitin_0 @ sk_D @ sk_C)
% 37.01/37.21        | (zip_tseitin_1 @ sk_A @ sk_B)
% 37.01/37.21        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 37.01/37.21        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 37.01/37.21        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 37.01/37.21        | ~ (v1_funct_1 @ sk_C))),
% 37.01/37.21      inference('sup-', [status(thm)], ['53', '59'])).
% 37.01/37.21  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 37.01/37.21  thf('61', plain, (![X6 : $i]: (v2_funct_1 @ (k6_relat_1 @ X6))),
% 37.01/37.21      inference('cnf', [status(esa)], [t52_funct_1])).
% 37.01/37.21  thf('62', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('63', plain,
% 37.01/37.21      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('64', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('65', plain, ((v1_funct_1 @ sk_C)),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('66', plain,
% 37.01/37.21      (((zip_tseitin_0 @ sk_D @ sk_C)
% 37.01/37.21        | (zip_tseitin_1 @ sk_A @ sk_B)
% 37.01/37.21        | ((sk_B) != (sk_B)))),
% 37.01/37.21      inference('demod', [status(thm)], ['60', '61', '62', '63', '64', '65'])).
% 37.01/37.21  thf('67', plain,
% 37.01/37.21      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 37.01/37.21      inference('simplify', [status(thm)], ['66'])).
% 37.01/37.21  thf('68', plain,
% 37.01/37.21      (![X40 : $i, X41 : $i]:
% 37.01/37.21         (((X40) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X40 @ X41))),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_2])).
% 37.01/37.21  thf('69', plain,
% 37.01/37.21      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 37.01/37.21      inference('sup-', [status(thm)], ['67', '68'])).
% 37.01/37.21  thf('70', plain, (((sk_A) != (k1_xboole_0))),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('71', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 37.01/37.21      inference('simplify_reflect-', [status(thm)], ['69', '70'])).
% 37.01/37.21  thf('72', plain,
% 37.01/37.21      (![X38 : $i, X39 : $i]:
% 37.01/37.21         ((v2_funct_1 @ X39) | ~ (zip_tseitin_0 @ X39 @ X38))),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_4])).
% 37.01/37.21  thf('73', plain, ((v2_funct_1 @ sk_D)),
% 37.01/37.21      inference('sup-', [status(thm)], ['71', '72'])).
% 37.01/37.21  thf('74', plain,
% 37.01/37.21      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 37.01/37.21      inference('demod', [status(thm)], ['52', '73'])).
% 37.01/37.21  thf('75', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 37.01/37.21      inference('demod', [status(thm)], ['36', '40', '41', '42', '43', '44'])).
% 37.01/37.21  thf(t80_relat_1, axiom,
% 37.01/37.21    (![A:$i]:
% 37.01/37.21     ( ( v1_relat_1 @ A ) =>
% 37.01/37.21       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 37.01/37.21  thf('76', plain,
% 37.01/37.21      (![X4 : $i]:
% 37.01/37.21         (((k5_relat_1 @ X4 @ (k6_relat_1 @ (k2_relat_1 @ X4))) = (X4))
% 37.01/37.21          | ~ (v1_relat_1 @ X4))),
% 37.01/37.21      inference('cnf', [status(esa)], [t80_relat_1])).
% 37.01/37.21  thf('77', plain,
% 37.01/37.21      ((((k5_relat_1 @ sk_D @ (k6_relat_1 @ sk_A)) = (sk_D))
% 37.01/37.21        | ~ (v1_relat_1 @ sk_D))),
% 37.01/37.21      inference('sup+', [status(thm)], ['75', '76'])).
% 37.01/37.21  thf('78', plain,
% 37.01/37.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf(cc1_relset_1, axiom,
% 37.01/37.21    (![A:$i,B:$i,C:$i]:
% 37.01/37.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 37.01/37.21       ( v1_relat_1 @ C ) ))).
% 37.01/37.21  thf('79', plain,
% 37.01/37.21      (![X9 : $i, X10 : $i, X11 : $i]:
% 37.01/37.21         ((v1_relat_1 @ X9)
% 37.01/37.21          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 37.01/37.21      inference('cnf', [status(esa)], [cc1_relset_1])).
% 37.01/37.21  thf('80', plain, ((v1_relat_1 @ sk_D)),
% 37.01/37.21      inference('sup-', [status(thm)], ['78', '79'])).
% 37.01/37.21  thf('81', plain, (((k5_relat_1 @ sk_D @ (k6_relat_1 @ sk_A)) = (sk_D))),
% 37.01/37.21      inference('demod', [status(thm)], ['77', '80'])).
% 37.01/37.21  thf(t78_relat_1, axiom,
% 37.01/37.21    (![A:$i]:
% 37.01/37.21     ( ( v1_relat_1 @ A ) =>
% 37.01/37.21       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 37.01/37.21  thf('82', plain,
% 37.01/37.21      (![X3 : $i]:
% 37.01/37.21         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X3)) @ X3) = (X3))
% 37.01/37.21          | ~ (v1_relat_1 @ X3))),
% 37.01/37.21      inference('cnf', [status(esa)], [t78_relat_1])).
% 37.01/37.21  thf(t55_relat_1, axiom,
% 37.01/37.21    (![A:$i]:
% 37.01/37.21     ( ( v1_relat_1 @ A ) =>
% 37.01/37.21       ( ![B:$i]:
% 37.01/37.21         ( ( v1_relat_1 @ B ) =>
% 37.01/37.21           ( ![C:$i]:
% 37.01/37.21             ( ( v1_relat_1 @ C ) =>
% 37.01/37.21               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 37.01/37.21                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 37.01/37.21  thf('83', plain,
% 37.01/37.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.01/37.21         (~ (v1_relat_1 @ X0)
% 37.01/37.21          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 37.01/37.21              = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 37.01/37.21          | ~ (v1_relat_1 @ X2)
% 37.01/37.21          | ~ (v1_relat_1 @ X1))),
% 37.01/37.21      inference('cnf', [status(esa)], [t55_relat_1])).
% 37.01/37.21  thf('84', plain,
% 37.01/37.21      (![X0 : $i, X1 : $i]:
% 37.01/37.21         (((k5_relat_1 @ X0 @ X1)
% 37.01/37.21            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 37.01/37.21               (k5_relat_1 @ X0 @ X1)))
% 37.01/37.21          | ~ (v1_relat_1 @ X0)
% 37.01/37.21          | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 37.01/37.21          | ~ (v1_relat_1 @ X1)
% 37.01/37.21          | ~ (v1_relat_1 @ X0))),
% 37.01/37.21      inference('sup+', [status(thm)], ['82', '83'])).
% 37.01/37.21  thf('85', plain,
% 37.01/37.21      (![X0 : $i, X1 : $i]:
% 37.01/37.21         (~ (v1_relat_1 @ X1)
% 37.01/37.21          | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 37.01/37.21          | ~ (v1_relat_1 @ X0)
% 37.01/37.21          | ((k5_relat_1 @ X0 @ X1)
% 37.01/37.21              = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 37.01/37.21                 (k5_relat_1 @ X0 @ X1))))),
% 37.01/37.21      inference('simplify', [status(thm)], ['84'])).
% 37.01/37.21  thf('86', plain,
% 37.01/37.21      (![X26 : $i]:
% 37.01/37.21         (m1_subset_1 @ (k6_relat_1 @ X26) @ 
% 37.01/37.21          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X26)))),
% 37.01/37.21      inference('demod', [status(thm)], ['24', '25'])).
% 37.01/37.21  thf('87', plain,
% 37.01/37.21      (![X9 : $i, X10 : $i, X11 : $i]:
% 37.01/37.21         ((v1_relat_1 @ X9)
% 37.01/37.21          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 37.01/37.21      inference('cnf', [status(esa)], [cc1_relset_1])).
% 37.01/37.21  thf('88', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 37.01/37.21      inference('sup-', [status(thm)], ['86', '87'])).
% 37.01/37.21  thf('89', plain,
% 37.01/37.21      (![X0 : $i, X1 : $i]:
% 37.01/37.21         (~ (v1_relat_1 @ X1)
% 37.01/37.21          | ~ (v1_relat_1 @ X0)
% 37.01/37.21          | ((k5_relat_1 @ X0 @ X1)
% 37.01/37.21              = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 37.01/37.21                 (k5_relat_1 @ X0 @ X1))))),
% 37.01/37.21      inference('demod', [status(thm)], ['85', '88'])).
% 37.01/37.21  thf('90', plain,
% 37.01/37.21      ((((k5_relat_1 @ sk_D @ (k6_relat_1 @ sk_A))
% 37.01/37.21          = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_D)) @ sk_D))
% 37.01/37.21        | ~ (v1_relat_1 @ sk_D)
% 37.01/37.21        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 37.01/37.21      inference('sup+', [status(thm)], ['81', '89'])).
% 37.01/37.21  thf('91', plain, (((k5_relat_1 @ sk_D @ (k6_relat_1 @ sk_A)) = (sk_D))),
% 37.01/37.21      inference('demod', [status(thm)], ['77', '80'])).
% 37.01/37.21  thf('92', plain, ((v1_relat_1 @ sk_D)),
% 37.01/37.21      inference('sup-', [status(thm)], ['78', '79'])).
% 37.01/37.21  thf('93', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 37.01/37.21      inference('sup-', [status(thm)], ['86', '87'])).
% 37.01/37.21  thf('94', plain,
% 37.01/37.21      (((sk_D) = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_D)) @ sk_D))),
% 37.01/37.21      inference('demod', [status(thm)], ['90', '91', '92', '93'])).
% 37.01/37.21  thf('95', plain,
% 37.01/37.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('96', plain,
% 37.01/37.21      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf(redefinition_k1_partfun1, axiom,
% 37.01/37.21    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 37.01/37.21     ( ( ( v1_funct_1 @ E ) & 
% 37.01/37.21         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 37.01/37.21         ( v1_funct_1 @ F ) & 
% 37.01/37.21         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 37.01/37.21       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 37.01/37.21  thf('97', plain,
% 37.01/37.21      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 37.01/37.21         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 37.01/37.21          | ~ (v1_funct_1 @ X27)
% 37.01/37.21          | ~ (v1_funct_1 @ X30)
% 37.01/37.21          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 37.01/37.21          | ((k1_partfun1 @ X28 @ X29 @ X31 @ X32 @ X27 @ X30)
% 37.01/37.21              = (k5_relat_1 @ X27 @ X30)))),
% 37.01/37.21      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 37.01/37.21  thf('98', plain,
% 37.01/37.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.01/37.21         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 37.01/37.21            = (k5_relat_1 @ sk_C @ X0))
% 37.01/37.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 37.01/37.21          | ~ (v1_funct_1 @ X0)
% 37.01/37.21          | ~ (v1_funct_1 @ sk_C))),
% 37.01/37.21      inference('sup-', [status(thm)], ['96', '97'])).
% 37.01/37.21  thf('99', plain, ((v1_funct_1 @ sk_C)),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('100', plain,
% 37.01/37.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.01/37.21         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 37.01/37.21            = (k5_relat_1 @ sk_C @ X0))
% 37.01/37.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 37.01/37.21          | ~ (v1_funct_1 @ X0))),
% 37.01/37.21      inference('demod', [status(thm)], ['98', '99'])).
% 37.01/37.21  thf('101', plain,
% 37.01/37.21      ((~ (v1_funct_1 @ sk_D)
% 37.01/37.21        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 37.01/37.21            = (k5_relat_1 @ sk_C @ sk_D)))),
% 37.01/37.21      inference('sup-', [status(thm)], ['95', '100'])).
% 37.01/37.21  thf('102', plain, ((v1_funct_1 @ sk_D)),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('103', plain,
% 37.01/37.21      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 37.01/37.21         = (k6_relat_1 @ sk_A))),
% 37.01/37.21      inference('demod', [status(thm)], ['23', '26'])).
% 37.01/37.21  thf('104', plain, (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 37.01/37.21      inference('demod', [status(thm)], ['101', '102', '103'])).
% 37.01/37.21  thf('105', plain,
% 37.01/37.21      (![X0 : $i, X1 : $i]:
% 37.01/37.21         (~ (v1_relat_1 @ X1)
% 37.01/37.21          | ~ (v1_relat_1 @ X0)
% 37.01/37.21          | ((k5_relat_1 @ X0 @ X1)
% 37.01/37.21              = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 37.01/37.21                 (k5_relat_1 @ X0 @ X1))))),
% 37.01/37.21      inference('demod', [status(thm)], ['85', '88'])).
% 37.01/37.21  thf('106', plain,
% 37.01/37.21      (![X3 : $i]:
% 37.01/37.21         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X3)) @ X3) = (X3))
% 37.01/37.21          | ~ (v1_relat_1 @ X3))),
% 37.01/37.21      inference('cnf', [status(esa)], [t78_relat_1])).
% 37.01/37.21  thf('107', plain,
% 37.01/37.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.01/37.21         (~ (v1_relat_1 @ X0)
% 37.01/37.21          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 37.01/37.21              = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 37.01/37.21          | ~ (v1_relat_1 @ X2)
% 37.01/37.21          | ~ (v1_relat_1 @ X1))),
% 37.01/37.21      inference('cnf', [status(esa)], [t55_relat_1])).
% 37.01/37.21  thf('108', plain,
% 37.01/37.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.01/37.21         (~ (v1_relat_1 @ X0)
% 37.01/37.21          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 37.01/37.21              = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 37.01/37.21          | ~ (v1_relat_1 @ X2)
% 37.01/37.21          | ~ (v1_relat_1 @ X1))),
% 37.01/37.21      inference('cnf', [status(esa)], [t55_relat_1])).
% 37.01/37.21  thf('109', plain,
% 37.01/37.21      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 37.01/37.21         (((k5_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X3)
% 37.01/37.21            = (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ (k5_relat_1 @ X0 @ X3)))
% 37.01/37.21          | ~ (v1_relat_1 @ X2)
% 37.01/37.21          | ~ (v1_relat_1 @ X0)
% 37.01/37.21          | ~ (v1_relat_1 @ X1)
% 37.01/37.21          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 37.01/37.21          | ~ (v1_relat_1 @ X3)
% 37.01/37.21          | ~ (v1_relat_1 @ X0))),
% 37.01/37.21      inference('sup+', [status(thm)], ['107', '108'])).
% 37.01/37.21  thf('110', plain,
% 37.01/37.21      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 37.01/37.21         (~ (v1_relat_1 @ X3)
% 37.01/37.21          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 37.01/37.21          | ~ (v1_relat_1 @ X1)
% 37.01/37.21          | ~ (v1_relat_1 @ X0)
% 37.01/37.21          | ~ (v1_relat_1 @ X2)
% 37.01/37.21          | ((k5_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)) @ X3)
% 37.01/37.21              = (k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ (k5_relat_1 @ X0 @ X3))))),
% 37.01/37.21      inference('simplify', [status(thm)], ['109'])).
% 37.01/37.21  thf('111', plain,
% 37.01/37.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.01/37.21         (~ (v1_relat_1 @ X0)
% 37.01/37.21          | ~ (v1_relat_1 @ X0)
% 37.01/37.21          | ((k5_relat_1 @ 
% 37.01/37.21              (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 37.01/37.21               (k5_relat_1 @ X0 @ X2)) @ 
% 37.01/37.21              X1)
% 37.01/37.21              = (k5_relat_1 @ 
% 37.01/37.21                 (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) @ 
% 37.01/37.21                 (k5_relat_1 @ X2 @ X1)))
% 37.01/37.21          | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 37.01/37.21          | ~ (v1_relat_1 @ X2)
% 37.01/37.21          | ~ (v1_relat_1 @ X0)
% 37.01/37.21          | ~ (v1_relat_1 @ X1))),
% 37.01/37.21      inference('sup-', [status(thm)], ['106', '110'])).
% 37.01/37.21  thf('112', plain,
% 37.01/37.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.01/37.21         (~ (v1_relat_1 @ X1)
% 37.01/37.21          | ~ (v1_relat_1 @ X2)
% 37.01/37.21          | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 37.01/37.21          | ((k5_relat_1 @ 
% 37.01/37.21              (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 37.01/37.21               (k5_relat_1 @ X0 @ X2)) @ 
% 37.01/37.21              X1)
% 37.01/37.21              = (k5_relat_1 @ 
% 37.01/37.21                 (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) @ 
% 37.01/37.21                 (k5_relat_1 @ X2 @ X1)))
% 37.01/37.21          | ~ (v1_relat_1 @ X0))),
% 37.01/37.21      inference('simplify', [status(thm)], ['111'])).
% 37.01/37.21  thf('113', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 37.01/37.21      inference('sup-', [status(thm)], ['86', '87'])).
% 37.01/37.21  thf('114', plain,
% 37.01/37.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.01/37.21         (~ (v1_relat_1 @ X1)
% 37.01/37.21          | ~ (v1_relat_1 @ X2)
% 37.01/37.21          | ((k5_relat_1 @ 
% 37.01/37.21              (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 37.01/37.21               (k5_relat_1 @ X0 @ X2)) @ 
% 37.01/37.21              X1)
% 37.01/37.21              = (k5_relat_1 @ 
% 37.01/37.21                 (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) @ 
% 37.01/37.21                 (k5_relat_1 @ X2 @ X1)))
% 37.01/37.21          | ~ (v1_relat_1 @ X0))),
% 37.01/37.21      inference('demod', [status(thm)], ['112', '113'])).
% 37.01/37.21  thf('115', plain,
% 37.01/37.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.01/37.21         (((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 37.01/37.21            = (k5_relat_1 @ 
% 37.01/37.21               (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X1)) @ X1) @ 
% 37.01/37.21               (k5_relat_1 @ X0 @ X2)))
% 37.01/37.21          | ~ (v1_relat_1 @ X1)
% 37.01/37.21          | ~ (v1_relat_1 @ X0)
% 37.01/37.21          | ~ (v1_relat_1 @ X1)
% 37.01/37.21          | ~ (v1_relat_1 @ X0)
% 37.01/37.21          | ~ (v1_relat_1 @ X2))),
% 37.01/37.21      inference('sup+', [status(thm)], ['105', '114'])).
% 37.01/37.21  thf('116', plain,
% 37.01/37.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.01/37.21         (~ (v1_relat_1 @ X2)
% 37.01/37.21          | ~ (v1_relat_1 @ X0)
% 37.01/37.21          | ~ (v1_relat_1 @ X1)
% 37.01/37.21          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 37.01/37.21              = (k5_relat_1 @ 
% 37.01/37.21                 (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X1)) @ X1) @ 
% 37.01/37.21                 (k5_relat_1 @ X0 @ X2))))),
% 37.01/37.21      inference('simplify', [status(thm)], ['115'])).
% 37.01/37.21  thf('117', plain,
% 37.01/37.21      (![X0 : $i]:
% 37.01/37.21         (((k5_relat_1 @ (k5_relat_1 @ X0 @ sk_C) @ sk_D)
% 37.01/37.21            = (k5_relat_1 @ 
% 37.01/37.21               (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) @ 
% 37.01/37.21               (k6_relat_1 @ sk_A)))
% 37.01/37.21          | ~ (v1_relat_1 @ X0)
% 37.01/37.21          | ~ (v1_relat_1 @ sk_C)
% 37.01/37.21          | ~ (v1_relat_1 @ sk_D))),
% 37.01/37.21      inference('sup+', [status(thm)], ['104', '116'])).
% 37.01/37.21  thf('118', plain,
% 37.01/37.21      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('119', plain,
% 37.01/37.21      (![X9 : $i, X10 : $i, X11 : $i]:
% 37.01/37.21         ((v1_relat_1 @ X9)
% 37.01/37.21          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 37.01/37.21      inference('cnf', [status(esa)], [cc1_relset_1])).
% 37.01/37.21  thf('120', plain, ((v1_relat_1 @ sk_C)),
% 37.01/37.21      inference('sup-', [status(thm)], ['118', '119'])).
% 37.01/37.21  thf('121', plain, ((v1_relat_1 @ sk_D)),
% 37.01/37.21      inference('sup-', [status(thm)], ['78', '79'])).
% 37.01/37.21  thf('122', plain,
% 37.01/37.21      (![X0 : $i]:
% 37.01/37.21         (((k5_relat_1 @ (k5_relat_1 @ X0 @ sk_C) @ sk_D)
% 37.01/37.21            = (k5_relat_1 @ 
% 37.01/37.21               (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) @ 
% 37.01/37.21               (k6_relat_1 @ sk_A)))
% 37.01/37.21          | ~ (v1_relat_1 @ X0))),
% 37.01/37.21      inference('demod', [status(thm)], ['117', '120', '121'])).
% 37.01/37.21  thf('123', plain,
% 37.01/37.21      ((((k5_relat_1 @ (k5_relat_1 @ sk_D @ sk_C) @ sk_D)
% 37.01/37.21          = (k5_relat_1 @ sk_D @ (k6_relat_1 @ sk_A)))
% 37.01/37.21        | ~ (v1_relat_1 @ sk_D))),
% 37.01/37.21      inference('sup+', [status(thm)], ['94', '122'])).
% 37.01/37.21  thf('124', plain, (((k5_relat_1 @ sk_D @ (k6_relat_1 @ sk_A)) = (sk_D))),
% 37.01/37.21      inference('demod', [status(thm)], ['77', '80'])).
% 37.01/37.21  thf('125', plain, ((v1_relat_1 @ sk_D)),
% 37.01/37.21      inference('sup-', [status(thm)], ['78', '79'])).
% 37.01/37.21  thf('126', plain,
% 37.01/37.21      (((k5_relat_1 @ (k5_relat_1 @ sk_D @ sk_C) @ sk_D) = (sk_D))),
% 37.01/37.21      inference('demod', [status(thm)], ['123', '124', '125'])).
% 37.01/37.21  thf('127', plain,
% 37.01/37.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.01/37.21         (~ (v1_relat_1 @ X0)
% 37.01/37.21          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 37.01/37.21              = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 37.01/37.21          | ~ (v1_relat_1 @ X2)
% 37.01/37.21          | ~ (v1_relat_1 @ X1))),
% 37.01/37.21      inference('cnf', [status(esa)], [t55_relat_1])).
% 37.01/37.21  thf('128', plain,
% 37.01/37.21      (![X0 : $i]:
% 37.01/37.21         (((k5_relat_1 @ sk_D @ X0)
% 37.01/37.21            = (k5_relat_1 @ (k5_relat_1 @ sk_D @ sk_C) @ 
% 37.01/37.21               (k5_relat_1 @ sk_D @ X0)))
% 37.01/37.21          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_D @ sk_C))
% 37.01/37.21          | ~ (v1_relat_1 @ X0)
% 37.01/37.21          | ~ (v1_relat_1 @ sk_D))),
% 37.01/37.21      inference('sup+', [status(thm)], ['126', '127'])).
% 37.01/37.21  thf('129', plain, ((v1_relat_1 @ sk_D)),
% 37.01/37.21      inference('sup-', [status(thm)], ['78', '79'])).
% 37.01/37.21  thf('130', plain,
% 37.01/37.21      (![X0 : $i]:
% 37.01/37.21         (((k5_relat_1 @ sk_D @ X0)
% 37.01/37.21            = (k5_relat_1 @ (k5_relat_1 @ sk_D @ sk_C) @ 
% 37.01/37.21               (k5_relat_1 @ sk_D @ X0)))
% 37.01/37.21          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_D @ sk_C))
% 37.01/37.21          | ~ (v1_relat_1 @ X0))),
% 37.01/37.21      inference('demod', [status(thm)], ['128', '129'])).
% 37.01/37.21  thf('131', plain,
% 37.01/37.21      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('132', plain,
% 37.01/37.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('133', plain,
% 37.01/37.21      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 37.01/37.21         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 37.01/37.21          | ~ (v1_funct_1 @ X19)
% 37.01/37.21          | ~ (v1_funct_1 @ X22)
% 37.01/37.21          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 37.01/37.21          | (m1_subset_1 @ (k1_partfun1 @ X20 @ X21 @ X23 @ X24 @ X19 @ X22) @ 
% 37.01/37.21             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X24))))),
% 37.01/37.21      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 37.01/37.21  thf('134', plain,
% 37.01/37.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.01/37.21         ((m1_subset_1 @ (k1_partfun1 @ sk_B @ sk_A @ X2 @ X0 @ sk_D @ X1) @ 
% 37.01/37.21           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 37.01/37.21          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 37.01/37.21          | ~ (v1_funct_1 @ X1)
% 37.01/37.21          | ~ (v1_funct_1 @ sk_D))),
% 37.01/37.21      inference('sup-', [status(thm)], ['132', '133'])).
% 37.01/37.21  thf('135', plain, ((v1_funct_1 @ sk_D)),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('136', plain,
% 37.01/37.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.01/37.21         ((m1_subset_1 @ (k1_partfun1 @ sk_B @ sk_A @ X2 @ X0 @ sk_D @ X1) @ 
% 37.01/37.21           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 37.01/37.21          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 37.01/37.21          | ~ (v1_funct_1 @ X1))),
% 37.01/37.21      inference('demod', [status(thm)], ['134', '135'])).
% 37.01/37.21  thf('137', plain,
% 37.01/37.21      ((~ (v1_funct_1 @ sk_C)
% 37.01/37.21        | (m1_subset_1 @ 
% 37.01/37.21           (k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 37.01/37.21           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B))))),
% 37.01/37.21      inference('sup-', [status(thm)], ['131', '136'])).
% 37.01/37.21  thf('138', plain, ((v1_funct_1 @ sk_C)),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('139', plain,
% 37.01/37.21      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('140', plain,
% 37.01/37.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('141', plain,
% 37.01/37.21      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 37.01/37.21         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 37.01/37.21          | ~ (v1_funct_1 @ X27)
% 37.01/37.21          | ~ (v1_funct_1 @ X30)
% 37.01/37.21          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 37.01/37.21          | ((k1_partfun1 @ X28 @ X29 @ X31 @ X32 @ X27 @ X30)
% 37.01/37.21              = (k5_relat_1 @ X27 @ X30)))),
% 37.01/37.21      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 37.01/37.21  thf('142', plain,
% 37.01/37.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.01/37.21         (((k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0)
% 37.01/37.21            = (k5_relat_1 @ sk_D @ X0))
% 37.01/37.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 37.01/37.21          | ~ (v1_funct_1 @ X0)
% 37.01/37.21          | ~ (v1_funct_1 @ sk_D))),
% 37.01/37.21      inference('sup-', [status(thm)], ['140', '141'])).
% 37.01/37.21  thf('143', plain, ((v1_funct_1 @ sk_D)),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('144', plain,
% 37.01/37.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.01/37.21         (((k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0)
% 37.01/37.21            = (k5_relat_1 @ sk_D @ X0))
% 37.01/37.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 37.01/37.21          | ~ (v1_funct_1 @ X0))),
% 37.01/37.21      inference('demod', [status(thm)], ['142', '143'])).
% 37.01/37.21  thf('145', plain,
% 37.01/37.21      ((~ (v1_funct_1 @ sk_C)
% 37.01/37.21        | ((k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C)
% 37.01/37.21            = (k5_relat_1 @ sk_D @ sk_C)))),
% 37.01/37.21      inference('sup-', [status(thm)], ['139', '144'])).
% 37.01/37.21  thf('146', plain, ((v1_funct_1 @ sk_C)),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('147', plain,
% 37.01/37.21      (((k1_partfun1 @ sk_B @ sk_A @ sk_A @ sk_B @ sk_D @ sk_C)
% 37.01/37.21         = (k5_relat_1 @ sk_D @ sk_C))),
% 37.01/37.21      inference('demod', [status(thm)], ['145', '146'])).
% 37.01/37.21  thf('148', plain,
% 37.01/37.21      ((m1_subset_1 @ (k5_relat_1 @ sk_D @ sk_C) @ 
% 37.01/37.21        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_B)))),
% 37.01/37.21      inference('demod', [status(thm)], ['137', '138', '147'])).
% 37.01/37.21  thf('149', plain,
% 37.01/37.21      (![X9 : $i, X10 : $i, X11 : $i]:
% 37.01/37.21         ((v1_relat_1 @ X9)
% 37.01/37.21          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 37.01/37.21      inference('cnf', [status(esa)], [cc1_relset_1])).
% 37.01/37.21  thf('150', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_D @ sk_C))),
% 37.01/37.21      inference('sup-', [status(thm)], ['148', '149'])).
% 37.01/37.21  thf('151', plain,
% 37.01/37.21      (![X0 : $i]:
% 37.01/37.21         (((k5_relat_1 @ sk_D @ X0)
% 37.01/37.21            = (k5_relat_1 @ (k5_relat_1 @ sk_D @ sk_C) @ 
% 37.01/37.21               (k5_relat_1 @ sk_D @ X0)))
% 37.01/37.21          | ~ (v1_relat_1 @ X0))),
% 37.01/37.21      inference('demod', [status(thm)], ['130', '150'])).
% 37.01/37.21  thf('152', plain,
% 37.01/37.21      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D))
% 37.01/37.21          = (k5_relat_1 @ (k5_relat_1 @ sk_D @ sk_C) @ (k6_relat_1 @ sk_B)))
% 37.01/37.21        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D)))),
% 37.01/37.21      inference('sup+', [status(thm)], ['74', '151'])).
% 37.01/37.21  thf('153', plain,
% 37.01/37.21      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 37.01/37.21      inference('demod', [status(thm)], ['52', '73'])).
% 37.01/37.21  thf('154', plain,
% 37.01/37.21      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('155', plain,
% 37.01/37.21      (![X12 : $i, X13 : $i, X14 : $i]:
% 37.01/37.21         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 37.01/37.21          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 37.01/37.21      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 37.01/37.21  thf('156', plain,
% 37.01/37.21      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 37.01/37.21      inference('sup-', [status(thm)], ['154', '155'])).
% 37.01/37.21  thf('157', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('158', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 37.01/37.21      inference('sup+', [status(thm)], ['156', '157'])).
% 37.01/37.21  thf('159', plain,
% 37.01/37.21      (((sk_D) = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_D)) @ sk_D))),
% 37.01/37.21      inference('demod', [status(thm)], ['90', '91', '92', '93'])).
% 37.01/37.21  thf('160', plain,
% 37.01/37.21      (![X4 : $i]:
% 37.01/37.21         (((k5_relat_1 @ X4 @ (k6_relat_1 @ (k2_relat_1 @ X4))) = (X4))
% 37.01/37.21          | ~ (v1_relat_1 @ X4))),
% 37.01/37.21      inference('cnf', [status(esa)], [t80_relat_1])).
% 37.01/37.21  thf('161', plain,
% 37.01/37.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.01/37.21         (~ (v1_relat_1 @ X2)
% 37.01/37.21          | ~ (v1_relat_1 @ X0)
% 37.01/37.21          | ~ (v1_relat_1 @ X1)
% 37.01/37.21          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 37.01/37.21              = (k5_relat_1 @ 
% 37.01/37.21                 (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X1)) @ X1) @ 
% 37.01/37.21                 (k5_relat_1 @ X0 @ X2))))),
% 37.01/37.21      inference('simplify', [status(thm)], ['115'])).
% 37.01/37.21  thf('162', plain,
% 37.01/37.21      (![X0 : $i, X1 : $i]:
% 37.01/37.21         (((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 37.01/37.21            (k6_relat_1 @ (k2_relat_1 @ X0)))
% 37.01/37.21            = (k5_relat_1 @ 
% 37.01/37.21               (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X1)) @ X1) @ X0))
% 37.01/37.21          | ~ (v1_relat_1 @ X0)
% 37.01/37.21          | ~ (v1_relat_1 @ X1)
% 37.01/37.21          | ~ (v1_relat_1 @ X0)
% 37.01/37.21          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))),
% 37.01/37.21      inference('sup+', [status(thm)], ['160', '161'])).
% 37.01/37.21  thf('163', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 37.01/37.21      inference('sup-', [status(thm)], ['86', '87'])).
% 37.01/37.21  thf('164', plain,
% 37.01/37.21      (![X0 : $i, X1 : $i]:
% 37.01/37.21         (((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 37.01/37.21            (k6_relat_1 @ (k2_relat_1 @ X0)))
% 37.01/37.21            = (k5_relat_1 @ 
% 37.01/37.21               (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X1)) @ X1) @ X0))
% 37.01/37.21          | ~ (v1_relat_1 @ X0)
% 37.01/37.21          | ~ (v1_relat_1 @ X1)
% 37.01/37.21          | ~ (v1_relat_1 @ X0))),
% 37.01/37.21      inference('demod', [status(thm)], ['162', '163'])).
% 37.01/37.21  thf('165', plain,
% 37.01/37.21      (![X0 : $i, X1 : $i]:
% 37.01/37.21         (~ (v1_relat_1 @ X1)
% 37.01/37.21          | ~ (v1_relat_1 @ X0)
% 37.01/37.21          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 37.01/37.21              (k6_relat_1 @ (k2_relat_1 @ X0)))
% 37.01/37.21              = (k5_relat_1 @ 
% 37.01/37.21                 (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X1)) @ X1) @ X0)))),
% 37.01/37.21      inference('simplify', [status(thm)], ['164'])).
% 37.01/37.21  thf('166', plain,
% 37.01/37.21      (![X0 : $i]:
% 37.01/37.21         (((k5_relat_1 @ (k5_relat_1 @ sk_D @ X0) @ 
% 37.01/37.21            (k6_relat_1 @ (k2_relat_1 @ X0))) = (k5_relat_1 @ sk_D @ X0))
% 37.01/37.21          | ~ (v1_relat_1 @ X0)
% 37.01/37.21          | ~ (v1_relat_1 @ sk_D))),
% 37.01/37.21      inference('sup+', [status(thm)], ['159', '165'])).
% 37.01/37.21  thf('167', plain, ((v1_relat_1 @ sk_D)),
% 37.01/37.21      inference('sup-', [status(thm)], ['78', '79'])).
% 37.01/37.21  thf('168', plain,
% 37.01/37.21      (![X0 : $i]:
% 37.01/37.21         (((k5_relat_1 @ (k5_relat_1 @ sk_D @ X0) @ 
% 37.01/37.21            (k6_relat_1 @ (k2_relat_1 @ X0))) = (k5_relat_1 @ sk_D @ X0))
% 37.01/37.21          | ~ (v1_relat_1 @ X0))),
% 37.01/37.21      inference('demod', [status(thm)], ['166', '167'])).
% 37.01/37.21  thf('169', plain,
% 37.01/37.21      ((((k5_relat_1 @ (k5_relat_1 @ sk_D @ sk_C) @ (k6_relat_1 @ sk_B))
% 37.01/37.21          = (k5_relat_1 @ sk_D @ sk_C))
% 37.01/37.21        | ~ (v1_relat_1 @ sk_C))),
% 37.01/37.21      inference('sup+', [status(thm)], ['158', '168'])).
% 37.01/37.21  thf('170', plain, ((v1_relat_1 @ sk_C)),
% 37.01/37.21      inference('sup-', [status(thm)], ['118', '119'])).
% 37.01/37.21  thf('171', plain,
% 37.01/37.21      (((k5_relat_1 @ (k5_relat_1 @ sk_D @ sk_C) @ (k6_relat_1 @ sk_B))
% 37.01/37.21         = (k5_relat_1 @ sk_D @ sk_C))),
% 37.01/37.21      inference('demod', [status(thm)], ['169', '170'])).
% 37.01/37.21  thf('172', plain,
% 37.01/37.21      ((((k6_relat_1 @ sk_B) = (k5_relat_1 @ sk_D @ sk_C))
% 37.01/37.21        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D)))),
% 37.01/37.21      inference('demod', [status(thm)], ['152', '153', '171'])).
% 37.01/37.21  thf('173', plain,
% 37.01/37.21      ((~ (v1_relat_1 @ sk_D)
% 37.01/37.21        | ~ (v1_funct_1 @ sk_D)
% 37.01/37.21        | ((k6_relat_1 @ sk_B) = (k5_relat_1 @ sk_D @ sk_C)))),
% 37.01/37.21      inference('sup-', [status(thm)], ['0', '172'])).
% 37.01/37.21  thf('174', plain, ((v1_relat_1 @ sk_D)),
% 37.01/37.21      inference('sup-', [status(thm)], ['78', '79'])).
% 37.01/37.21  thf('175', plain, ((v1_funct_1 @ sk_D)),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('176', plain, (((k6_relat_1 @ sk_B) = (k5_relat_1 @ sk_D @ sk_C))),
% 37.01/37.21      inference('demod', [status(thm)], ['173', '174', '175'])).
% 37.01/37.21  thf('177', plain,
% 37.01/37.21      (![X3 : $i]:
% 37.01/37.21         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X3)) @ X3) = (X3))
% 37.01/37.21          | ~ (v1_relat_1 @ X3))),
% 37.01/37.21      inference('cnf', [status(esa)], [t78_relat_1])).
% 37.01/37.21  thf('178', plain,
% 37.01/37.21      (![X0 : $i]:
% 37.01/37.21         (((k5_relat_1 @ (k5_relat_1 @ X0 @ sk_C) @ sk_D)
% 37.01/37.21            = (k5_relat_1 @ 
% 37.01/37.21               (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) @ 
% 37.01/37.21               (k6_relat_1 @ sk_A)))
% 37.01/37.21          | ~ (v1_relat_1 @ X0))),
% 37.01/37.21      inference('demod', [status(thm)], ['117', '120', '121'])).
% 37.01/37.21  thf('179', plain,
% 37.01/37.21      (![X0 : $i]:
% 37.01/37.21         (((k5_relat_1 @ (k5_relat_1 @ X0 @ sk_C) @ sk_D)
% 37.01/37.21            = (k5_relat_1 @ X0 @ (k6_relat_1 @ sk_A)))
% 37.01/37.21          | ~ (v1_relat_1 @ X0)
% 37.01/37.21          | ~ (v1_relat_1 @ X0))),
% 37.01/37.21      inference('sup+', [status(thm)], ['177', '178'])).
% 37.01/37.21  thf('180', plain,
% 37.01/37.21      (![X0 : $i]:
% 37.01/37.21         (~ (v1_relat_1 @ X0)
% 37.01/37.21          | ((k5_relat_1 @ (k5_relat_1 @ X0 @ sk_C) @ sk_D)
% 37.01/37.21              = (k5_relat_1 @ X0 @ (k6_relat_1 @ sk_A))))),
% 37.01/37.21      inference('simplify', [status(thm)], ['179'])).
% 37.01/37.21  thf('181', plain,
% 37.01/37.21      ((((k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_D)
% 37.01/37.21          = (k5_relat_1 @ sk_D @ (k6_relat_1 @ sk_A)))
% 37.01/37.21        | ~ (v1_relat_1 @ sk_D))),
% 37.01/37.21      inference('sup+', [status(thm)], ['176', '180'])).
% 37.01/37.21  thf('182', plain, (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 37.01/37.21      inference('demod', [status(thm)], ['101', '102', '103'])).
% 37.01/37.21  thf('183', plain,
% 37.01/37.21      (![X5 : $i]:
% 37.01/37.21         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 37.01/37.21          | ~ (v1_funct_1 @ X5)
% 37.01/37.21          | ~ (v1_relat_1 @ X5))),
% 37.01/37.21      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 37.01/37.21  thf('184', plain,
% 37.01/37.21      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('185', plain,
% 37.01/37.21      (![X47 : $i, X48 : $i, X49 : $i]:
% 37.01/37.21         (((X47) = (k1_xboole_0))
% 37.01/37.21          | ~ (v1_funct_1 @ X48)
% 37.01/37.21          | ~ (v1_funct_2 @ X48 @ X49 @ X47)
% 37.01/37.21          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X47)))
% 37.01/37.21          | ((k5_relat_1 @ (k2_funct_1 @ X48) @ X48) = (k6_partfun1 @ X47))
% 37.01/37.21          | ~ (v2_funct_1 @ X48)
% 37.01/37.21          | ((k2_relset_1 @ X49 @ X47 @ X48) != (X47)))),
% 37.01/37.21      inference('cnf', [status(esa)], [t35_funct_2])).
% 37.01/37.21  thf('186', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 37.01/37.21      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 37.01/37.21  thf('187', plain,
% 37.01/37.21      (![X47 : $i, X48 : $i, X49 : $i]:
% 37.01/37.21         (((X47) = (k1_xboole_0))
% 37.01/37.21          | ~ (v1_funct_1 @ X48)
% 37.01/37.21          | ~ (v1_funct_2 @ X48 @ X49 @ X47)
% 37.01/37.21          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X47)))
% 37.01/37.21          | ((k5_relat_1 @ (k2_funct_1 @ X48) @ X48) = (k6_relat_1 @ X47))
% 37.01/37.21          | ~ (v2_funct_1 @ X48)
% 37.01/37.21          | ((k2_relset_1 @ X49 @ X47 @ X48) != (X47)))),
% 37.01/37.21      inference('demod', [status(thm)], ['185', '186'])).
% 37.01/37.21  thf('188', plain,
% 37.01/37.21      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 37.01/37.21        | ~ (v2_funct_1 @ sk_C)
% 37.01/37.21        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))
% 37.01/37.21        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 37.01/37.21        | ~ (v1_funct_1 @ sk_C)
% 37.01/37.21        | ((sk_B) = (k1_xboole_0)))),
% 37.01/37.21      inference('sup-', [status(thm)], ['184', '187'])).
% 37.01/37.21  thf('189', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('190', plain, ((v2_funct_1 @ sk_C)),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('191', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('192', plain, ((v1_funct_1 @ sk_C)),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('193', plain,
% 37.01/37.21      ((((sk_B) != (sk_B))
% 37.01/37.21        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))
% 37.01/37.21        | ((sk_B) = (k1_xboole_0)))),
% 37.01/37.21      inference('demod', [status(thm)], ['188', '189', '190', '191', '192'])).
% 37.01/37.21  thf('194', plain,
% 37.01/37.21      ((((sk_B) = (k1_xboole_0))
% 37.01/37.21        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B)))),
% 37.01/37.21      inference('simplify', [status(thm)], ['193'])).
% 37.01/37.21  thf('195', plain, (((sk_B) != (k1_xboole_0))),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('196', plain,
% 37.01/37.21      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))),
% 37.01/37.21      inference('simplify_reflect-', [status(thm)], ['194', '195'])).
% 37.01/37.21  thf('197', plain,
% 37.01/37.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.01/37.21         (~ (v1_relat_1 @ X0)
% 37.01/37.21          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 37.01/37.21              = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 37.01/37.21          | ~ (v1_relat_1 @ X2)
% 37.01/37.21          | ~ (v1_relat_1 @ X1))),
% 37.01/37.21      inference('cnf', [status(esa)], [t55_relat_1])).
% 37.01/37.21  thf('198', plain,
% 37.01/37.21      (![X0 : $i]:
% 37.01/37.21         (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0)
% 37.01/37.21            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 37.01/37.21          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 37.01/37.21          | ~ (v1_relat_1 @ X0)
% 37.01/37.21          | ~ (v1_relat_1 @ sk_C))),
% 37.01/37.21      inference('sup+', [status(thm)], ['196', '197'])).
% 37.01/37.21  thf('199', plain, ((v1_relat_1 @ sk_C)),
% 37.01/37.21      inference('sup-', [status(thm)], ['118', '119'])).
% 37.01/37.21  thf('200', plain,
% 37.01/37.21      (![X0 : $i]:
% 37.01/37.21         (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0)
% 37.01/37.21            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 37.01/37.21          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 37.01/37.21          | ~ (v1_relat_1 @ X0))),
% 37.01/37.21      inference('demod', [status(thm)], ['198', '199'])).
% 37.01/37.21  thf('201', plain,
% 37.01/37.21      (![X0 : $i]:
% 37.01/37.21         (~ (v1_relat_1 @ sk_C)
% 37.01/37.21          | ~ (v1_funct_1 @ sk_C)
% 37.01/37.21          | ~ (v1_relat_1 @ X0)
% 37.01/37.21          | ((k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0)
% 37.01/37.21              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 37.01/37.21      inference('sup-', [status(thm)], ['183', '200'])).
% 37.01/37.21  thf('202', plain, ((v1_relat_1 @ sk_C)),
% 37.01/37.21      inference('sup-', [status(thm)], ['118', '119'])).
% 37.01/37.21  thf('203', plain, ((v1_funct_1 @ sk_C)),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('204', plain,
% 37.01/37.21      (![X0 : $i]:
% 37.01/37.21         (~ (v1_relat_1 @ X0)
% 37.01/37.21          | ((k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0)
% 37.01/37.21              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 37.01/37.21      inference('demod', [status(thm)], ['201', '202', '203'])).
% 37.01/37.21  thf('205', plain,
% 37.01/37.21      ((((k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_D)
% 37.01/37.21          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_relat_1 @ sk_A)))
% 37.01/37.21        | ~ (v1_relat_1 @ sk_D))),
% 37.01/37.21      inference('sup+', [status(thm)], ['182', '204'])).
% 37.01/37.21  thf('206', plain,
% 37.01/37.21      (![X5 : $i]:
% 37.01/37.21         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 37.01/37.21          | ~ (v1_funct_1 @ X5)
% 37.01/37.21          | ~ (v1_relat_1 @ X5))),
% 37.01/37.21      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 37.01/37.21  thf('207', plain,
% 37.01/37.21      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('208', plain,
% 37.01/37.21      (![X47 : $i, X48 : $i, X49 : $i]:
% 37.01/37.21         (((X47) = (k1_xboole_0))
% 37.01/37.21          | ~ (v1_funct_1 @ X48)
% 37.01/37.21          | ~ (v1_funct_2 @ X48 @ X49 @ X47)
% 37.01/37.21          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X47)))
% 37.01/37.21          | ((k5_relat_1 @ X48 @ (k2_funct_1 @ X48)) = (k6_relat_1 @ X49))
% 37.01/37.21          | ~ (v2_funct_1 @ X48)
% 37.01/37.21          | ((k2_relset_1 @ X49 @ X47 @ X48) != (X47)))),
% 37.01/37.21      inference('demod', [status(thm)], ['2', '3'])).
% 37.01/37.21  thf('209', plain,
% 37.01/37.21      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 37.01/37.21        | ~ (v2_funct_1 @ sk_C)
% 37.01/37.21        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 37.01/37.21        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 37.01/37.21        | ~ (v1_funct_1 @ sk_C)
% 37.01/37.21        | ((sk_B) = (k1_xboole_0)))),
% 37.01/37.21      inference('sup-', [status(thm)], ['207', '208'])).
% 37.01/37.21  thf('210', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('211', plain, ((v2_funct_1 @ sk_C)),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('212', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('213', plain, ((v1_funct_1 @ sk_C)),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('214', plain,
% 37.01/37.21      ((((sk_B) != (sk_B))
% 37.01/37.21        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 37.01/37.21        | ((sk_B) = (k1_xboole_0)))),
% 37.01/37.21      inference('demod', [status(thm)], ['209', '210', '211', '212', '213'])).
% 37.01/37.21  thf('215', plain,
% 37.01/37.21      ((((sk_B) = (k1_xboole_0))
% 37.01/37.21        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A)))),
% 37.01/37.21      inference('simplify', [status(thm)], ['214'])).
% 37.01/37.21  thf('216', plain, (((sk_B) != (k1_xboole_0))),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('217', plain,
% 37.01/37.21      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))),
% 37.01/37.21      inference('simplify_reflect-', [status(thm)], ['215', '216'])).
% 37.01/37.21  thf('218', plain,
% 37.01/37.21      (![X0 : $i]:
% 37.01/37.21         (~ (v1_relat_1 @ X0)
% 37.01/37.21          | ((k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0)
% 37.01/37.21              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 37.01/37.21      inference('demod', [status(thm)], ['201', '202', '203'])).
% 37.01/37.21  thf('219', plain,
% 37.01/37.21      ((((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 37.01/37.21          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_relat_1 @ sk_A)))
% 37.01/37.21        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 37.01/37.21      inference('sup+', [status(thm)], ['217', '218'])).
% 37.01/37.21  thf('220', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 37.01/37.21      inference('sup+', [status(thm)], ['156', '157'])).
% 37.01/37.21  thf('221', plain,
% 37.01/37.21      (![X5 : $i]:
% 37.01/37.21         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 37.01/37.21          | ~ (v1_funct_1 @ X5)
% 37.01/37.21          | ~ (v1_relat_1 @ X5))),
% 37.01/37.21      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 37.01/37.21  thf(t55_funct_1, axiom,
% 37.01/37.21    (![A:$i]:
% 37.01/37.21     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 37.01/37.21       ( ( v2_funct_1 @ A ) =>
% 37.01/37.21         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 37.01/37.21           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 37.01/37.21  thf('222', plain,
% 37.01/37.21      (![X7 : $i]:
% 37.01/37.21         (~ (v2_funct_1 @ X7)
% 37.01/37.21          | ((k2_relat_1 @ X7) = (k1_relat_1 @ (k2_funct_1 @ X7)))
% 37.01/37.21          | ~ (v1_funct_1 @ X7)
% 37.01/37.21          | ~ (v1_relat_1 @ X7))),
% 37.01/37.21      inference('cnf', [status(esa)], [t55_funct_1])).
% 37.01/37.21  thf('223', plain,
% 37.01/37.21      (![X3 : $i]:
% 37.01/37.21         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X3)) @ X3) = (X3))
% 37.01/37.21          | ~ (v1_relat_1 @ X3))),
% 37.01/37.21      inference('cnf', [status(esa)], [t78_relat_1])).
% 37.01/37.21  thf('224', plain,
% 37.01/37.21      (![X0 : $i]:
% 37.01/37.21         (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 37.01/37.21            = (k2_funct_1 @ X0))
% 37.01/37.21          | ~ (v1_relat_1 @ X0)
% 37.01/37.21          | ~ (v1_funct_1 @ X0)
% 37.01/37.21          | ~ (v2_funct_1 @ X0)
% 37.01/37.21          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 37.01/37.21      inference('sup+', [status(thm)], ['222', '223'])).
% 37.01/37.21  thf('225', plain,
% 37.01/37.21      (![X0 : $i]:
% 37.01/37.21         (~ (v1_relat_1 @ X0)
% 37.01/37.21          | ~ (v1_funct_1 @ X0)
% 37.01/37.21          | ~ (v2_funct_1 @ X0)
% 37.01/37.21          | ~ (v1_funct_1 @ X0)
% 37.01/37.21          | ~ (v1_relat_1 @ X0)
% 37.01/37.21          | ((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 37.01/37.21              = (k2_funct_1 @ X0)))),
% 37.01/37.21      inference('sup-', [status(thm)], ['221', '224'])).
% 37.01/37.21  thf('226', plain,
% 37.01/37.21      (![X0 : $i]:
% 37.01/37.21         (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 37.01/37.21            = (k2_funct_1 @ X0))
% 37.01/37.21          | ~ (v2_funct_1 @ X0)
% 37.01/37.21          | ~ (v1_funct_1 @ X0)
% 37.01/37.21          | ~ (v1_relat_1 @ X0))),
% 37.01/37.21      inference('simplify', [status(thm)], ['225'])).
% 37.01/37.21  thf('227', plain,
% 37.01/37.21      ((((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 37.01/37.21          = (k2_funct_1 @ sk_C))
% 37.01/37.21        | ~ (v1_relat_1 @ sk_C)
% 37.01/37.21        | ~ (v1_funct_1 @ sk_C)
% 37.01/37.21        | ~ (v2_funct_1 @ sk_C))),
% 37.01/37.21      inference('sup+', [status(thm)], ['220', '226'])).
% 37.01/37.21  thf('228', plain, ((v1_relat_1 @ sk_C)),
% 37.01/37.21      inference('sup-', [status(thm)], ['118', '119'])).
% 37.01/37.21  thf('229', plain, ((v1_funct_1 @ sk_C)),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('230', plain, ((v2_funct_1 @ sk_C)),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('231', plain,
% 37.01/37.21      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 37.01/37.21         = (k2_funct_1 @ sk_C))),
% 37.01/37.21      inference('demod', [status(thm)], ['227', '228', '229', '230'])).
% 37.01/37.21  thf('232', plain,
% 37.01/37.21      ((((k2_funct_1 @ sk_C)
% 37.01/37.21          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_relat_1 @ sk_A)))
% 37.01/37.21        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 37.01/37.21      inference('demod', [status(thm)], ['219', '231'])).
% 37.01/37.21  thf('233', plain,
% 37.01/37.21      ((~ (v1_relat_1 @ sk_C)
% 37.01/37.21        | ~ (v1_funct_1 @ sk_C)
% 37.01/37.21        | ((k2_funct_1 @ sk_C)
% 37.01/37.21            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_relat_1 @ sk_A))))),
% 37.01/37.21      inference('sup-', [status(thm)], ['206', '232'])).
% 37.01/37.21  thf('234', plain, ((v1_relat_1 @ sk_C)),
% 37.01/37.21      inference('sup-', [status(thm)], ['118', '119'])).
% 37.01/37.21  thf('235', plain, ((v1_funct_1 @ sk_C)),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('236', plain,
% 37.01/37.21      (((k2_funct_1 @ sk_C)
% 37.01/37.21         = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_relat_1 @ sk_A)))),
% 37.01/37.21      inference('demod', [status(thm)], ['233', '234', '235'])).
% 37.01/37.21  thf('237', plain, ((v1_relat_1 @ sk_D)),
% 37.01/37.21      inference('sup-', [status(thm)], ['78', '79'])).
% 37.01/37.21  thf('238', plain,
% 37.01/37.21      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_D) = (k2_funct_1 @ sk_C))),
% 37.01/37.21      inference('demod', [status(thm)], ['205', '236', '237'])).
% 37.01/37.21  thf('239', plain, (((k5_relat_1 @ sk_D @ (k6_relat_1 @ sk_A)) = (sk_D))),
% 37.01/37.21      inference('demod', [status(thm)], ['77', '80'])).
% 37.01/37.21  thf('240', plain, ((v1_relat_1 @ sk_D)),
% 37.01/37.21      inference('sup-', [status(thm)], ['78', '79'])).
% 37.01/37.21  thf('241', plain, (((k2_funct_1 @ sk_C) = (sk_D))),
% 37.01/37.21      inference('demod', [status(thm)], ['181', '238', '239', '240'])).
% 37.01/37.21  thf('242', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 37.01/37.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.01/37.21  thf('243', plain, ($false),
% 37.01/37.21      inference('simplify_reflect-', [status(thm)], ['241', '242'])).
% 37.01/37.21  
% 37.01/37.21  % SZS output end Refutation
% 37.01/37.21  
% 37.01/37.22  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

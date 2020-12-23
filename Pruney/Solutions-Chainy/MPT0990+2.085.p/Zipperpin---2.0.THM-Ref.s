%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yHD3hI9DUt

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:08 EST 2020

% Result     : Theorem 30.45s
% Output     : Refutation 30.45s
% Verified   : 
% Statistics : Number of formulae       :  214 ( 501 expanded)
%              Number of leaves         :   47 ( 168 expanded)
%              Depth                    :   21
%              Number of atoms          : 2168 (12119 expanded)
%              Number of equality atoms :  149 ( 842 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('8',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('18',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( X16 = X19 )
      | ~ ( r2_relset_1 @ X17 @ X18 @ X16 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','19'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('21',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('22',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('23',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,(
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

thf('26',plain,(
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

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('33',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( r2_relset_1 @ X17 @ X18 @ X16 @ X19 )
      | ( X16 != X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('34',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_relset_1 @ X17 @ X18 @ X19 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['31','35','36','37','38'])).

thf('40',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['7','39'])).

thf('41',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('43',plain,(
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

thf('44',plain,(
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

thf('45',plain,(
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
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['42','48'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('50',plain,(
    ! [X9: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('51',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('52',plain,(
    ! [X9: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X9 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['49','52','53','54','55','56'])).

thf('58',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X40: $i,X41: $i] :
      ( ( X40 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('60',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X38: $i,X39: $i] :
      ( ( v2_funct_1 @ X39 )
      | ~ ( zip_tseitin_0 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('64',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['41','64'])).

thf(t58_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('66',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X11 @ ( k2_funct_1 @ X11 ) ) )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('67',plain,
    ( ( ( k2_relat_1 @ ( k6_partfun1 @ sk_B ) )
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('68',plain,(
    ! [X4: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('69',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('70',plain,(
    ! [X4: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('72',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('73',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['62','63'])).

thf('76',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['67','70','73','74','75'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('77',plain,(
    ! [X5: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X5 ) ) @ X5 )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('78',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('79',plain,(
    ! [X5: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X5 ) ) @ X5 )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['76','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
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

thf('83',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( ( k1_partfun1 @ X28 @ X29 @ X31 @ X32 @ X27 @ X30 )
        = ( k5_relat_1 @ X27 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['81','86'])).

thf('88',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('90',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('91',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('92',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X12 ) @ X12 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('93',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('94',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X12 ) @ X12 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['91','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['90','99'])).

thf('101',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X12 ) @ X12 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('102',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
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

thf('104',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['104','105','106','107','108'])).

thf('110',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['101','112'])).

thf('114',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('116',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['113','116','117','118'])).

thf('120',plain,(
    ! [X3: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X3 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('121',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('122',plain,(
    ! [X3: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X3 ) )
      = X3 ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['119','122'])).

thf('124',plain,(
    ! [X3: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X3 ) )
      = X3 ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('125',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
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

thf('128',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['128','129','130','131','132'])).

thf('134',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X11 @ ( k2_funct_1 @ X11 ) ) )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('138',plain,
    ( ( ( k2_relat_1 @ ( k6_partfun1 @ sk_A ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X4: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('140',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['114','115'])).

thf('141',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['138','139','140','141','142'])).

thf('144',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
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

thf('145',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k1_relat_1 @ X10 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('146',plain,(
    ! [X6: $i] :
      ( ( ( k5_relat_1 @ X6 @ ( k6_relat_1 @ ( k2_relat_1 @ X6 ) ) )
        = X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('147',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('148',plain,(
    ! [X6: $i] :
      ( ( ( k5_relat_1 @ X6 @ ( k6_partfun1 @ ( k2_relat_1 @ X6 ) ) )
        = X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['145','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['144','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['143','151'])).

thf('153',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['114','115'])).

thf('154',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['152','153','154','155'])).

thf('157',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['114','115'])).

thf('158',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['71','72'])).

thf('161',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['100','125','156','157','158','159','160'])).

thf('162',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['71','72'])).

thf('163',plain,
    ( ( k2_funct_1 @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['80','161','162'])).

thf('164',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['163','164'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yHD3hI9DUt
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:31:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 30.45/30.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 30.45/30.69  % Solved by: fo/fo7.sh
% 30.45/30.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 30.45/30.69  % done 4165 iterations in 30.237s
% 30.45/30.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 30.45/30.69  % SZS output start Refutation
% 30.45/30.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 30.45/30.69  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 30.45/30.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 30.45/30.69  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 30.45/30.69  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 30.45/30.69  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 30.45/30.69  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 30.45/30.69  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 30.45/30.69  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 30.45/30.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 30.45/30.69  thf(sk_A_type, type, sk_A: $i).
% 30.45/30.69  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 30.45/30.69  thf(sk_D_type, type, sk_D: $i).
% 30.45/30.69  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 30.45/30.69  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 30.45/30.69  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 30.45/30.69  thf(sk_C_type, type, sk_C: $i).
% 30.45/30.69  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 30.45/30.69  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 30.45/30.69  thf(sk_B_type, type, sk_B: $i).
% 30.45/30.69  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 30.45/30.69  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 30.45/30.69  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 30.45/30.69  thf(t36_funct_2, conjecture,
% 30.45/30.69    (![A:$i,B:$i,C:$i]:
% 30.45/30.69     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 30.45/30.69         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 30.45/30.69       ( ![D:$i]:
% 30.45/30.69         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 30.45/30.69             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 30.45/30.69           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 30.45/30.69               ( r2_relset_1 @
% 30.45/30.69                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 30.45/30.69                 ( k6_partfun1 @ A ) ) & 
% 30.45/30.69               ( v2_funct_1 @ C ) ) =>
% 30.45/30.69             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 30.45/30.69               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 30.45/30.69  thf(zf_stmt_0, negated_conjecture,
% 30.45/30.69    (~( ![A:$i,B:$i,C:$i]:
% 30.45/30.69        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 30.45/30.69            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 30.45/30.69          ( ![D:$i]:
% 30.45/30.69            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 30.45/30.69                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 30.45/30.69              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 30.45/30.69                  ( r2_relset_1 @
% 30.45/30.69                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 30.45/30.69                    ( k6_partfun1 @ A ) ) & 
% 30.45/30.69                  ( v2_funct_1 @ C ) ) =>
% 30.45/30.69                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 30.45/30.69                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 30.45/30.69    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 30.45/30.69  thf('0', plain,
% 30.45/30.69      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 30.45/30.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.69  thf(t35_funct_2, axiom,
% 30.45/30.69    (![A:$i,B:$i,C:$i]:
% 30.45/30.69     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 30.45/30.69         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 30.45/30.69       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 30.45/30.69         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 30.45/30.69           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 30.45/30.69             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 30.45/30.69  thf('1', plain,
% 30.45/30.69      (![X47 : $i, X48 : $i, X49 : $i]:
% 30.45/30.69         (((X47) = (k1_xboole_0))
% 30.45/30.69          | ~ (v1_funct_1 @ X48)
% 30.45/30.69          | ~ (v1_funct_2 @ X48 @ X49 @ X47)
% 30.45/30.69          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X47)))
% 30.45/30.69          | ((k5_relat_1 @ X48 @ (k2_funct_1 @ X48)) = (k6_partfun1 @ X49))
% 30.45/30.69          | ~ (v2_funct_1 @ X48)
% 30.45/30.69          | ((k2_relset_1 @ X49 @ X47 @ X48) != (X47)))),
% 30.45/30.69      inference('cnf', [status(esa)], [t35_funct_2])).
% 30.45/30.69  thf('2', plain,
% 30.45/30.69      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 30.45/30.69        | ~ (v2_funct_1 @ sk_D)
% 30.45/30.69        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 30.45/30.69        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 30.45/30.69        | ~ (v1_funct_1 @ sk_D)
% 30.45/30.69        | ((sk_A) = (k1_xboole_0)))),
% 30.45/30.69      inference('sup-', [status(thm)], ['0', '1'])).
% 30.45/30.69  thf('3', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 30.45/30.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.69  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 30.45/30.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.69  thf('5', plain,
% 30.45/30.69      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 30.45/30.69        | ~ (v2_funct_1 @ sk_D)
% 30.45/30.69        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 30.45/30.69        | ((sk_A) = (k1_xboole_0)))),
% 30.45/30.69      inference('demod', [status(thm)], ['2', '3', '4'])).
% 30.45/30.69  thf('6', plain, (((sk_A) != (k1_xboole_0))),
% 30.45/30.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.69  thf('7', plain,
% 30.45/30.69      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 30.45/30.69        | ~ (v2_funct_1 @ sk_D)
% 30.45/30.69        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 30.45/30.69      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 30.45/30.69  thf('8', plain,
% 30.45/30.69      ((r2_relset_1 @ sk_A @ sk_A @ 
% 30.45/30.69        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 30.45/30.69        (k6_partfun1 @ sk_A))),
% 30.45/30.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.69  thf('9', plain,
% 30.45/30.69      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 30.45/30.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.69  thf('10', plain,
% 30.45/30.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 30.45/30.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.69  thf(dt_k1_partfun1, axiom,
% 30.45/30.69    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 30.45/30.69     ( ( ( v1_funct_1 @ E ) & 
% 30.45/30.69         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 30.45/30.69         ( v1_funct_1 @ F ) & 
% 30.45/30.69         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 30.45/30.69       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 30.45/30.69         ( m1_subset_1 @
% 30.45/30.69           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 30.45/30.69           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 30.45/30.69  thf('11', plain,
% 30.45/30.69      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 30.45/30.69         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 30.45/30.69          | ~ (v1_funct_1 @ X21)
% 30.45/30.69          | ~ (v1_funct_1 @ X24)
% 30.45/30.69          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 30.45/30.69          | (m1_subset_1 @ (k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24) @ 
% 30.45/30.69             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X26))))),
% 30.45/30.69      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 30.45/30.69  thf('12', plain,
% 30.45/30.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.45/30.69         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 30.45/30.69           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 30.45/30.69          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 30.45/30.69          | ~ (v1_funct_1 @ X1)
% 30.45/30.69          | ~ (v1_funct_1 @ sk_C))),
% 30.45/30.69      inference('sup-', [status(thm)], ['10', '11'])).
% 30.45/30.69  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 30.45/30.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.69  thf('14', plain,
% 30.45/30.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.45/30.69         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 30.45/30.69           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 30.45/30.69          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 30.45/30.69          | ~ (v1_funct_1 @ X1))),
% 30.45/30.69      inference('demod', [status(thm)], ['12', '13'])).
% 30.45/30.69  thf('15', plain,
% 30.45/30.69      ((~ (v1_funct_1 @ sk_D)
% 30.45/30.69        | (m1_subset_1 @ 
% 30.45/30.69           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 30.45/30.69           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 30.45/30.69      inference('sup-', [status(thm)], ['9', '14'])).
% 30.45/30.69  thf('16', plain, ((v1_funct_1 @ sk_D)),
% 30.45/30.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.69  thf('17', plain,
% 30.45/30.69      ((m1_subset_1 @ 
% 30.45/30.69        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 30.45/30.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 30.45/30.69      inference('demod', [status(thm)], ['15', '16'])).
% 30.45/30.69  thf(redefinition_r2_relset_1, axiom,
% 30.45/30.69    (![A:$i,B:$i,C:$i,D:$i]:
% 30.45/30.69     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 30.45/30.69         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 30.45/30.69       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 30.45/30.69  thf('18', plain,
% 30.45/30.69      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 30.45/30.69         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 30.45/30.69          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 30.45/30.69          | ((X16) = (X19))
% 30.45/30.69          | ~ (r2_relset_1 @ X17 @ X18 @ X16 @ X19))),
% 30.45/30.69      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 30.45/30.69  thf('19', plain,
% 30.45/30.69      (![X0 : $i]:
% 30.45/30.69         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 30.45/30.69             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 30.45/30.69          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 30.45/30.69          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 30.45/30.69      inference('sup-', [status(thm)], ['17', '18'])).
% 30.45/30.69  thf('20', plain,
% 30.45/30.69      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 30.45/30.69           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 30.45/30.69        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 30.45/30.69            = (k6_partfun1 @ sk_A)))),
% 30.45/30.69      inference('sup-', [status(thm)], ['8', '19'])).
% 30.45/30.69  thf(t29_relset_1, axiom,
% 30.45/30.69    (![A:$i]:
% 30.45/30.69     ( m1_subset_1 @
% 30.45/30.69       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 30.45/30.69  thf('21', plain,
% 30.45/30.69      (![X20 : $i]:
% 30.45/30.69         (m1_subset_1 @ (k6_relat_1 @ X20) @ 
% 30.45/30.69          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20)))),
% 30.45/30.69      inference('cnf', [status(esa)], [t29_relset_1])).
% 30.45/30.69  thf(redefinition_k6_partfun1, axiom,
% 30.45/30.69    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 30.45/30.69  thf('22', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 30.45/30.69      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 30.45/30.69  thf('23', plain,
% 30.45/30.69      (![X20 : $i]:
% 30.45/30.69         (m1_subset_1 @ (k6_partfun1 @ X20) @ 
% 30.45/30.69          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20)))),
% 30.45/30.69      inference('demod', [status(thm)], ['21', '22'])).
% 30.45/30.69  thf('24', plain,
% 30.45/30.69      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 30.45/30.69         = (k6_partfun1 @ sk_A))),
% 30.45/30.69      inference('demod', [status(thm)], ['20', '23'])).
% 30.45/30.69  thf('25', plain,
% 30.45/30.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 30.45/30.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.69  thf(t24_funct_2, axiom,
% 30.45/30.69    (![A:$i,B:$i,C:$i]:
% 30.45/30.69     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 30.45/30.69         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 30.45/30.69       ( ![D:$i]:
% 30.45/30.69         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 30.45/30.69             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 30.45/30.69           ( ( r2_relset_1 @
% 30.45/30.69               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 30.45/30.69               ( k6_partfun1 @ B ) ) =>
% 30.45/30.69             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 30.45/30.69  thf('26', plain,
% 30.45/30.69      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 30.45/30.69         (~ (v1_funct_1 @ X34)
% 30.45/30.69          | ~ (v1_funct_2 @ X34 @ X35 @ X36)
% 30.45/30.69          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 30.45/30.69          | ~ (r2_relset_1 @ X35 @ X35 @ 
% 30.45/30.69               (k1_partfun1 @ X35 @ X36 @ X36 @ X35 @ X34 @ X37) @ 
% 30.45/30.69               (k6_partfun1 @ X35))
% 30.45/30.69          | ((k2_relset_1 @ X36 @ X35 @ X37) = (X35))
% 30.45/30.69          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 30.45/30.70          | ~ (v1_funct_2 @ X37 @ X36 @ X35)
% 30.45/30.70          | ~ (v1_funct_1 @ X37))),
% 30.45/30.70      inference('cnf', [status(esa)], [t24_funct_2])).
% 30.45/30.70  thf('27', plain,
% 30.45/30.70      (![X0 : $i]:
% 30.45/30.70         (~ (v1_funct_1 @ X0)
% 30.45/30.70          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 30.45/30.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 30.45/30.70          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 30.45/30.70          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 30.45/30.70               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 30.45/30.70               (k6_partfun1 @ sk_A))
% 30.45/30.70          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 30.45/30.70          | ~ (v1_funct_1 @ sk_C))),
% 30.45/30.70      inference('sup-', [status(thm)], ['25', '26'])).
% 30.45/30.70  thf('28', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 30.45/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.70  thf('29', plain, ((v1_funct_1 @ sk_C)),
% 30.45/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.70  thf('30', plain,
% 30.45/30.70      (![X0 : $i]:
% 30.45/30.70         (~ (v1_funct_1 @ X0)
% 30.45/30.70          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 30.45/30.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 30.45/30.70          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 30.45/30.70          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 30.45/30.70               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 30.45/30.70               (k6_partfun1 @ sk_A)))),
% 30.45/30.70      inference('demod', [status(thm)], ['27', '28', '29'])).
% 30.45/30.70  thf('31', plain,
% 30.45/30.70      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 30.45/30.70           (k6_partfun1 @ sk_A))
% 30.45/30.70        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 30.45/30.70        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 30.45/30.70        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 30.45/30.70        | ~ (v1_funct_1 @ sk_D))),
% 30.45/30.70      inference('sup-', [status(thm)], ['24', '30'])).
% 30.45/30.70  thf('32', plain,
% 30.45/30.70      (![X20 : $i]:
% 30.45/30.70         (m1_subset_1 @ (k6_partfun1 @ X20) @ 
% 30.45/30.70          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20)))),
% 30.45/30.70      inference('demod', [status(thm)], ['21', '22'])).
% 30.45/30.70  thf('33', plain,
% 30.45/30.70      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 30.45/30.70         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 30.45/30.70          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 30.45/30.70          | (r2_relset_1 @ X17 @ X18 @ X16 @ X19)
% 30.45/30.70          | ((X16) != (X19)))),
% 30.45/30.70      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 30.45/30.70  thf('34', plain,
% 30.45/30.70      (![X17 : $i, X18 : $i, X19 : $i]:
% 30.45/30.70         ((r2_relset_1 @ X17 @ X18 @ X19 @ X19)
% 30.45/30.70          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 30.45/30.70      inference('simplify', [status(thm)], ['33'])).
% 30.45/30.70  thf('35', plain,
% 30.45/30.70      (![X0 : $i]:
% 30.45/30.70         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 30.45/30.70      inference('sup-', [status(thm)], ['32', '34'])).
% 30.45/30.70  thf('36', plain,
% 30.45/30.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 30.45/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.70  thf('37', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 30.45/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.70  thf('38', plain, ((v1_funct_1 @ sk_D)),
% 30.45/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.70  thf('39', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))),
% 30.45/30.70      inference('demod', [status(thm)], ['31', '35', '36', '37', '38'])).
% 30.45/30.70  thf('40', plain,
% 30.45/30.70      ((((sk_A) != (sk_A))
% 30.45/30.70        | ~ (v2_funct_1 @ sk_D)
% 30.45/30.70        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 30.45/30.70      inference('demod', [status(thm)], ['7', '39'])).
% 30.45/30.70  thf('41', plain,
% 30.45/30.70      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 30.45/30.70        | ~ (v2_funct_1 @ sk_D))),
% 30.45/30.70      inference('simplify', [status(thm)], ['40'])).
% 30.45/30.70  thf('42', plain,
% 30.45/30.70      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 30.45/30.70         = (k6_partfun1 @ sk_A))),
% 30.45/30.70      inference('demod', [status(thm)], ['20', '23'])).
% 30.45/30.70  thf('43', plain,
% 30.45/30.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 30.45/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.70  thf(t30_funct_2, axiom,
% 30.45/30.70    (![A:$i,B:$i,C:$i,D:$i]:
% 30.45/30.70     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 30.45/30.70         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 30.45/30.70       ( ![E:$i]:
% 30.45/30.70         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 30.45/30.70             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 30.45/30.70           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 30.45/30.70               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 30.45/30.70             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 30.45/30.70               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 30.45/30.70  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 30.45/30.70  thf(zf_stmt_2, axiom,
% 30.45/30.70    (![C:$i,B:$i]:
% 30.45/30.70     ( ( zip_tseitin_1 @ C @ B ) =>
% 30.45/30.70       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 30.45/30.70  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 30.45/30.70  thf(zf_stmt_4, axiom,
% 30.45/30.70    (![E:$i,D:$i]:
% 30.45/30.70     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 30.45/30.70  thf(zf_stmt_5, axiom,
% 30.45/30.70    (![A:$i,B:$i,C:$i,D:$i]:
% 30.45/30.70     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 30.45/30.70         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 30.45/30.70       ( ![E:$i]:
% 30.45/30.70         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 30.45/30.70             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 30.45/30.70           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 30.45/30.70               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 30.45/30.70             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 30.45/30.70  thf('44', plain,
% 30.45/30.70      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 30.45/30.70         (~ (v1_funct_1 @ X42)
% 30.45/30.70          | ~ (v1_funct_2 @ X42 @ X43 @ X44)
% 30.45/30.70          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 30.45/30.70          | (zip_tseitin_0 @ X42 @ X45)
% 30.45/30.70          | ~ (v2_funct_1 @ (k1_partfun1 @ X46 @ X43 @ X43 @ X44 @ X45 @ X42))
% 30.45/30.70          | (zip_tseitin_1 @ X44 @ X43)
% 30.45/30.70          | ((k2_relset_1 @ X46 @ X43 @ X45) != (X43))
% 30.45/30.70          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X43)))
% 30.45/30.70          | ~ (v1_funct_2 @ X45 @ X46 @ X43)
% 30.45/30.70          | ~ (v1_funct_1 @ X45))),
% 30.45/30.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 30.45/30.70  thf('45', plain,
% 30.45/30.70      (![X0 : $i, X1 : $i]:
% 30.45/30.70         (~ (v1_funct_1 @ X0)
% 30.45/30.70          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 30.45/30.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 30.45/30.70          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 30.45/30.70          | (zip_tseitin_1 @ sk_A @ sk_B)
% 30.45/30.70          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 30.45/30.70          | (zip_tseitin_0 @ sk_D @ X0)
% 30.45/30.70          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 30.45/30.70          | ~ (v1_funct_1 @ sk_D))),
% 30.45/30.70      inference('sup-', [status(thm)], ['43', '44'])).
% 30.45/30.70  thf('46', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 30.45/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.70  thf('47', plain, ((v1_funct_1 @ sk_D)),
% 30.45/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.70  thf('48', plain,
% 30.45/30.70      (![X0 : $i, X1 : $i]:
% 30.45/30.70         (~ (v1_funct_1 @ X0)
% 30.45/30.70          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 30.45/30.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 30.45/30.70          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 30.45/30.70          | (zip_tseitin_1 @ sk_A @ sk_B)
% 30.45/30.70          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 30.45/30.70          | (zip_tseitin_0 @ sk_D @ X0))),
% 30.45/30.70      inference('demod', [status(thm)], ['45', '46', '47'])).
% 30.45/30.70  thf('49', plain,
% 30.45/30.70      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 30.45/30.70        | (zip_tseitin_0 @ sk_D @ sk_C)
% 30.45/30.70        | (zip_tseitin_1 @ sk_A @ sk_B)
% 30.45/30.70        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 30.45/30.70        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 30.45/30.70        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 30.45/30.70        | ~ (v1_funct_1 @ sk_C))),
% 30.45/30.70      inference('sup-', [status(thm)], ['42', '48'])).
% 30.45/30.70  thf(fc4_funct_1, axiom,
% 30.45/30.70    (![A:$i]:
% 30.45/30.70     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 30.45/30.70       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 30.45/30.70  thf('50', plain, (![X9 : $i]: (v2_funct_1 @ (k6_relat_1 @ X9))),
% 30.45/30.70      inference('cnf', [status(esa)], [fc4_funct_1])).
% 30.45/30.70  thf('51', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 30.45/30.70      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 30.45/30.70  thf('52', plain, (![X9 : $i]: (v2_funct_1 @ (k6_partfun1 @ X9))),
% 30.45/30.70      inference('demod', [status(thm)], ['50', '51'])).
% 30.45/30.70  thf('53', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 30.45/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.70  thf('54', plain,
% 30.45/30.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 30.45/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.70  thf('55', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 30.45/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.70  thf('56', plain, ((v1_funct_1 @ sk_C)),
% 30.45/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.70  thf('57', plain,
% 30.45/30.70      (((zip_tseitin_0 @ sk_D @ sk_C)
% 30.45/30.70        | (zip_tseitin_1 @ sk_A @ sk_B)
% 30.45/30.70        | ((sk_B) != (sk_B)))),
% 30.45/30.70      inference('demod', [status(thm)], ['49', '52', '53', '54', '55', '56'])).
% 30.45/30.70  thf('58', plain,
% 30.45/30.70      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 30.45/30.70      inference('simplify', [status(thm)], ['57'])).
% 30.45/30.70  thf('59', plain,
% 30.45/30.70      (![X40 : $i, X41 : $i]:
% 30.45/30.70         (((X40) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X40 @ X41))),
% 30.45/30.70      inference('cnf', [status(esa)], [zf_stmt_2])).
% 30.45/30.70  thf('60', plain,
% 30.45/30.70      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 30.45/30.70      inference('sup-', [status(thm)], ['58', '59'])).
% 30.45/30.70  thf('61', plain, (((sk_A) != (k1_xboole_0))),
% 30.45/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.70  thf('62', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 30.45/30.70      inference('simplify_reflect-', [status(thm)], ['60', '61'])).
% 30.45/30.70  thf('63', plain,
% 30.45/30.70      (![X38 : $i, X39 : $i]:
% 30.45/30.70         ((v2_funct_1 @ X39) | ~ (zip_tseitin_0 @ X39 @ X38))),
% 30.45/30.70      inference('cnf', [status(esa)], [zf_stmt_4])).
% 30.45/30.70  thf('64', plain, ((v2_funct_1 @ sk_D)),
% 30.45/30.70      inference('sup-', [status(thm)], ['62', '63'])).
% 30.45/30.70  thf('65', plain,
% 30.45/30.70      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 30.45/30.70      inference('demod', [status(thm)], ['41', '64'])).
% 30.45/30.70  thf(t58_funct_1, axiom,
% 30.45/30.70    (![A:$i]:
% 30.45/30.70     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 30.45/30.70       ( ( v2_funct_1 @ A ) =>
% 30.45/30.70         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 30.45/30.70             ( k1_relat_1 @ A ) ) & 
% 30.45/30.70           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 30.45/30.70             ( k1_relat_1 @ A ) ) ) ) ))).
% 30.45/30.70  thf('66', plain,
% 30.45/30.70      (![X11 : $i]:
% 30.45/30.70         (~ (v2_funct_1 @ X11)
% 30.45/30.70          | ((k2_relat_1 @ (k5_relat_1 @ X11 @ (k2_funct_1 @ X11)))
% 30.45/30.70              = (k1_relat_1 @ X11))
% 30.45/30.70          | ~ (v1_funct_1 @ X11)
% 30.45/30.70          | ~ (v1_relat_1 @ X11))),
% 30.45/30.70      inference('cnf', [status(esa)], [t58_funct_1])).
% 30.45/30.70  thf('67', plain,
% 30.45/30.70      ((((k2_relat_1 @ (k6_partfun1 @ sk_B)) = (k1_relat_1 @ sk_D))
% 30.45/30.70        | ~ (v1_relat_1 @ sk_D)
% 30.45/30.70        | ~ (v1_funct_1 @ sk_D)
% 30.45/30.70        | ~ (v2_funct_1 @ sk_D))),
% 30.45/30.70      inference('sup+', [status(thm)], ['65', '66'])).
% 30.45/30.70  thf(t71_relat_1, axiom,
% 30.45/30.70    (![A:$i]:
% 30.45/30.70     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 30.45/30.70       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 30.45/30.70  thf('68', plain, (![X4 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X4)) = (X4))),
% 30.45/30.70      inference('cnf', [status(esa)], [t71_relat_1])).
% 30.45/30.70  thf('69', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 30.45/30.70      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 30.45/30.70  thf('70', plain, (![X4 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 30.45/30.70      inference('demod', [status(thm)], ['68', '69'])).
% 30.45/30.70  thf('71', plain,
% 30.45/30.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 30.45/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.70  thf(cc1_relset_1, axiom,
% 30.45/30.70    (![A:$i,B:$i,C:$i]:
% 30.45/30.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 30.45/30.70       ( v1_relat_1 @ C ) ))).
% 30.45/30.70  thf('72', plain,
% 30.45/30.70      (![X13 : $i, X14 : $i, X15 : $i]:
% 30.45/30.70         ((v1_relat_1 @ X13)
% 30.45/30.70          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 30.45/30.70      inference('cnf', [status(esa)], [cc1_relset_1])).
% 30.45/30.70  thf('73', plain, ((v1_relat_1 @ sk_D)),
% 30.45/30.70      inference('sup-', [status(thm)], ['71', '72'])).
% 30.45/30.70  thf('74', plain, ((v1_funct_1 @ sk_D)),
% 30.45/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.70  thf('75', plain, ((v2_funct_1 @ sk_D)),
% 30.45/30.70      inference('sup-', [status(thm)], ['62', '63'])).
% 30.45/30.70  thf('76', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 30.45/30.70      inference('demod', [status(thm)], ['67', '70', '73', '74', '75'])).
% 30.45/30.70  thf(t78_relat_1, axiom,
% 30.45/30.70    (![A:$i]:
% 30.45/30.70     ( ( v1_relat_1 @ A ) =>
% 30.45/30.70       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 30.45/30.70  thf('77', plain,
% 30.45/30.70      (![X5 : $i]:
% 30.45/30.70         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X5)) @ X5) = (X5))
% 30.45/30.70          | ~ (v1_relat_1 @ X5))),
% 30.45/30.70      inference('cnf', [status(esa)], [t78_relat_1])).
% 30.45/30.70  thf('78', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 30.45/30.70      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 30.45/30.70  thf('79', plain,
% 30.45/30.70      (![X5 : $i]:
% 30.45/30.70         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X5)) @ X5) = (X5))
% 30.45/30.70          | ~ (v1_relat_1 @ X5))),
% 30.45/30.70      inference('demod', [status(thm)], ['77', '78'])).
% 30.45/30.70  thf('80', plain,
% 30.45/30.70      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))
% 30.45/30.70        | ~ (v1_relat_1 @ sk_D))),
% 30.45/30.70      inference('sup+', [status(thm)], ['76', '79'])).
% 30.45/30.70  thf('81', plain,
% 30.45/30.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 30.45/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.70  thf('82', plain,
% 30.45/30.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 30.45/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.70  thf(redefinition_k1_partfun1, axiom,
% 30.45/30.70    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 30.45/30.70     ( ( ( v1_funct_1 @ E ) & 
% 30.45/30.70         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 30.45/30.70         ( v1_funct_1 @ F ) & 
% 30.45/30.70         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 30.45/30.70       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 30.45/30.70  thf('83', plain,
% 30.45/30.70      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 30.45/30.70         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 30.45/30.70          | ~ (v1_funct_1 @ X27)
% 30.45/30.70          | ~ (v1_funct_1 @ X30)
% 30.45/30.70          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 30.45/30.70          | ((k1_partfun1 @ X28 @ X29 @ X31 @ X32 @ X27 @ X30)
% 30.45/30.70              = (k5_relat_1 @ X27 @ X30)))),
% 30.45/30.70      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 30.45/30.70  thf('84', plain,
% 30.45/30.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.45/30.70         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 30.45/30.70            = (k5_relat_1 @ sk_C @ X0))
% 30.45/30.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 30.45/30.70          | ~ (v1_funct_1 @ X0)
% 30.45/30.70          | ~ (v1_funct_1 @ sk_C))),
% 30.45/30.70      inference('sup-', [status(thm)], ['82', '83'])).
% 30.45/30.70  thf('85', plain, ((v1_funct_1 @ sk_C)),
% 30.45/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.70  thf('86', plain,
% 30.45/30.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.45/30.70         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 30.45/30.70            = (k5_relat_1 @ sk_C @ X0))
% 30.45/30.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 30.45/30.70          | ~ (v1_funct_1 @ X0))),
% 30.45/30.70      inference('demod', [status(thm)], ['84', '85'])).
% 30.45/30.70  thf('87', plain,
% 30.45/30.70      ((~ (v1_funct_1 @ sk_D)
% 30.45/30.70        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 30.45/30.70            = (k5_relat_1 @ sk_C @ sk_D)))),
% 30.45/30.70      inference('sup-', [status(thm)], ['81', '86'])).
% 30.45/30.70  thf('88', plain, ((v1_funct_1 @ sk_D)),
% 30.45/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.70  thf('89', plain,
% 30.45/30.70      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 30.45/30.70         = (k6_partfun1 @ sk_A))),
% 30.45/30.70      inference('demod', [status(thm)], ['20', '23'])).
% 30.45/30.70  thf('90', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 30.45/30.70      inference('demod', [status(thm)], ['87', '88', '89'])).
% 30.45/30.70  thf(dt_k2_funct_1, axiom,
% 30.45/30.70    (![A:$i]:
% 30.45/30.70     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 30.45/30.70       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 30.45/30.70         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 30.45/30.70  thf('91', plain,
% 30.45/30.70      (![X7 : $i]:
% 30.45/30.70         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 30.45/30.70          | ~ (v1_funct_1 @ X7)
% 30.45/30.70          | ~ (v1_relat_1 @ X7))),
% 30.45/30.70      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 30.45/30.70  thf(t61_funct_1, axiom,
% 30.45/30.70    (![A:$i]:
% 30.45/30.70     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 30.45/30.70       ( ( v2_funct_1 @ A ) =>
% 30.45/30.70         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 30.45/30.70             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 30.45/30.70           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 30.45/30.70             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 30.45/30.70  thf('92', plain,
% 30.45/30.70      (![X12 : $i]:
% 30.45/30.70         (~ (v2_funct_1 @ X12)
% 30.45/30.70          | ((k5_relat_1 @ (k2_funct_1 @ X12) @ X12)
% 30.45/30.70              = (k6_relat_1 @ (k2_relat_1 @ X12)))
% 30.45/30.70          | ~ (v1_funct_1 @ X12)
% 30.45/30.70          | ~ (v1_relat_1 @ X12))),
% 30.45/30.70      inference('cnf', [status(esa)], [t61_funct_1])).
% 30.45/30.70  thf('93', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 30.45/30.70      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 30.45/30.70  thf('94', plain,
% 30.45/30.70      (![X12 : $i]:
% 30.45/30.70         (~ (v2_funct_1 @ X12)
% 30.45/30.70          | ((k5_relat_1 @ (k2_funct_1 @ X12) @ X12)
% 30.45/30.70              = (k6_partfun1 @ (k2_relat_1 @ X12)))
% 30.45/30.70          | ~ (v1_funct_1 @ X12)
% 30.45/30.70          | ~ (v1_relat_1 @ X12))),
% 30.45/30.70      inference('demod', [status(thm)], ['92', '93'])).
% 30.45/30.70  thf(t55_relat_1, axiom,
% 30.45/30.70    (![A:$i]:
% 30.45/30.70     ( ( v1_relat_1 @ A ) =>
% 30.45/30.70       ( ![B:$i]:
% 30.45/30.70         ( ( v1_relat_1 @ B ) =>
% 30.45/30.70           ( ![C:$i]:
% 30.45/30.70             ( ( v1_relat_1 @ C ) =>
% 30.45/30.70               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 30.45/30.70                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 30.45/30.70  thf('95', plain,
% 30.45/30.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.45/30.70         (~ (v1_relat_1 @ X0)
% 30.45/30.70          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 30.45/30.70              = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 30.45/30.70          | ~ (v1_relat_1 @ X2)
% 30.45/30.70          | ~ (v1_relat_1 @ X1))),
% 30.45/30.70      inference('cnf', [status(esa)], [t55_relat_1])).
% 30.45/30.70  thf('96', plain,
% 30.45/30.70      (![X0 : $i, X1 : $i]:
% 30.45/30.70         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 30.45/30.70            = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 30.45/30.70          | ~ (v1_relat_1 @ X0)
% 30.45/30.70          | ~ (v1_funct_1 @ X0)
% 30.45/30.70          | ~ (v2_funct_1 @ X0)
% 30.45/30.70          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 30.45/30.70          | ~ (v1_relat_1 @ X1)
% 30.45/30.70          | ~ (v1_relat_1 @ X0))),
% 30.45/30.70      inference('sup+', [status(thm)], ['94', '95'])).
% 30.45/30.70  thf('97', plain,
% 30.45/30.70      (![X0 : $i, X1 : $i]:
% 30.45/30.70         (~ (v1_relat_1 @ X1)
% 30.45/30.70          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 30.45/30.70          | ~ (v2_funct_1 @ X0)
% 30.45/30.70          | ~ (v1_funct_1 @ X0)
% 30.45/30.70          | ~ (v1_relat_1 @ X0)
% 30.45/30.70          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 30.45/30.70              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1))))),
% 30.45/30.70      inference('simplify', [status(thm)], ['96'])).
% 30.45/30.70  thf('98', plain,
% 30.45/30.70      (![X0 : $i, X1 : $i]:
% 30.45/30.70         (~ (v1_relat_1 @ X0)
% 30.45/30.70          | ~ (v1_funct_1 @ X0)
% 30.45/30.70          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 30.45/30.70              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 30.45/30.70          | ~ (v1_relat_1 @ X0)
% 30.45/30.70          | ~ (v1_funct_1 @ X0)
% 30.45/30.70          | ~ (v2_funct_1 @ X0)
% 30.45/30.70          | ~ (v1_relat_1 @ X1))),
% 30.45/30.70      inference('sup-', [status(thm)], ['91', '97'])).
% 30.45/30.70  thf('99', plain,
% 30.45/30.70      (![X0 : $i, X1 : $i]:
% 30.45/30.70         (~ (v1_relat_1 @ X1)
% 30.45/30.70          | ~ (v2_funct_1 @ X0)
% 30.45/30.70          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 30.45/30.70              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 30.45/30.70          | ~ (v1_funct_1 @ X0)
% 30.45/30.70          | ~ (v1_relat_1 @ X0))),
% 30.45/30.70      inference('simplify', [status(thm)], ['98'])).
% 30.45/30.70  thf('100', plain,
% 30.45/30.70      ((((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)) @ sk_D)
% 30.45/30.70          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 30.45/30.70        | ~ (v1_relat_1 @ sk_C)
% 30.45/30.70        | ~ (v1_funct_1 @ sk_C)
% 30.45/30.70        | ~ (v2_funct_1 @ sk_C)
% 30.45/30.70        | ~ (v1_relat_1 @ sk_D))),
% 30.45/30.70      inference('sup+', [status(thm)], ['90', '99'])).
% 30.45/30.70  thf('101', plain,
% 30.45/30.70      (![X12 : $i]:
% 30.45/30.70         (~ (v2_funct_1 @ X12)
% 30.45/30.70          | ((k5_relat_1 @ (k2_funct_1 @ X12) @ X12)
% 30.45/30.70              = (k6_partfun1 @ (k2_relat_1 @ X12)))
% 30.45/30.70          | ~ (v1_funct_1 @ X12)
% 30.45/30.70          | ~ (v1_relat_1 @ X12))),
% 30.45/30.70      inference('demod', [status(thm)], ['92', '93'])).
% 30.45/30.70  thf('102', plain,
% 30.45/30.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 30.45/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.70  thf('103', plain,
% 30.45/30.70      (![X47 : $i, X48 : $i, X49 : $i]:
% 30.45/30.70         (((X47) = (k1_xboole_0))
% 30.45/30.70          | ~ (v1_funct_1 @ X48)
% 30.45/30.70          | ~ (v1_funct_2 @ X48 @ X49 @ X47)
% 30.45/30.70          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X47)))
% 30.45/30.70          | ((k5_relat_1 @ (k2_funct_1 @ X48) @ X48) = (k6_partfun1 @ X47))
% 30.45/30.70          | ~ (v2_funct_1 @ X48)
% 30.45/30.70          | ((k2_relset_1 @ X49 @ X47 @ X48) != (X47)))),
% 30.45/30.70      inference('cnf', [status(esa)], [t35_funct_2])).
% 30.45/30.70  thf('104', plain,
% 30.45/30.70      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 30.45/30.70        | ~ (v2_funct_1 @ sk_C)
% 30.45/30.70        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 30.45/30.70        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 30.45/30.70        | ~ (v1_funct_1 @ sk_C)
% 30.45/30.70        | ((sk_B) = (k1_xboole_0)))),
% 30.45/30.70      inference('sup-', [status(thm)], ['102', '103'])).
% 30.45/30.70  thf('105', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 30.45/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.70  thf('106', plain, ((v2_funct_1 @ sk_C)),
% 30.45/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.70  thf('107', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 30.45/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.70  thf('108', plain, ((v1_funct_1 @ sk_C)),
% 30.45/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.70  thf('109', plain,
% 30.45/30.70      ((((sk_B) != (sk_B))
% 30.45/30.70        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 30.45/30.70        | ((sk_B) = (k1_xboole_0)))),
% 30.45/30.70      inference('demod', [status(thm)], ['104', '105', '106', '107', '108'])).
% 30.45/30.70  thf('110', plain,
% 30.45/30.70      ((((sk_B) = (k1_xboole_0))
% 30.45/30.70        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B)))),
% 30.45/30.70      inference('simplify', [status(thm)], ['109'])).
% 30.45/30.70  thf('111', plain, (((sk_B) != (k1_xboole_0))),
% 30.45/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.70  thf('112', plain,
% 30.45/30.70      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 30.45/30.70      inference('simplify_reflect-', [status(thm)], ['110', '111'])).
% 30.45/30.70  thf('113', plain,
% 30.45/30.70      ((((k6_partfun1 @ (k2_relat_1 @ sk_C)) = (k6_partfun1 @ sk_B))
% 30.45/30.70        | ~ (v1_relat_1 @ sk_C)
% 30.45/30.70        | ~ (v1_funct_1 @ sk_C)
% 30.45/30.70        | ~ (v2_funct_1 @ sk_C))),
% 30.45/30.70      inference('sup+', [status(thm)], ['101', '112'])).
% 30.45/30.70  thf('114', plain,
% 30.45/30.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 30.45/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.70  thf('115', plain,
% 30.45/30.70      (![X13 : $i, X14 : $i, X15 : $i]:
% 30.45/30.70         ((v1_relat_1 @ X13)
% 30.45/30.70          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 30.45/30.70      inference('cnf', [status(esa)], [cc1_relset_1])).
% 30.45/30.70  thf('116', plain, ((v1_relat_1 @ sk_C)),
% 30.45/30.70      inference('sup-', [status(thm)], ['114', '115'])).
% 30.45/30.70  thf('117', plain, ((v1_funct_1 @ sk_C)),
% 30.45/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.70  thf('118', plain, ((v2_funct_1 @ sk_C)),
% 30.45/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.70  thf('119', plain,
% 30.45/30.70      (((k6_partfun1 @ (k2_relat_1 @ sk_C)) = (k6_partfun1 @ sk_B))),
% 30.45/30.70      inference('demod', [status(thm)], ['113', '116', '117', '118'])).
% 30.45/30.70  thf('120', plain, (![X3 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X3)) = (X3))),
% 30.45/30.70      inference('cnf', [status(esa)], [t71_relat_1])).
% 30.45/30.70  thf('121', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 30.45/30.70      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 30.45/30.70  thf('122', plain, (![X3 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X3)) = (X3))),
% 30.45/30.70      inference('demod', [status(thm)], ['120', '121'])).
% 30.45/30.70  thf('123', plain,
% 30.45/30.70      (((k1_relat_1 @ (k6_partfun1 @ sk_B)) = (k2_relat_1 @ sk_C))),
% 30.45/30.70      inference('sup+', [status(thm)], ['119', '122'])).
% 30.45/30.70  thf('124', plain, (![X3 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X3)) = (X3))),
% 30.45/30.70      inference('demod', [status(thm)], ['120', '121'])).
% 30.45/30.70  thf('125', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 30.45/30.70      inference('demod', [status(thm)], ['123', '124'])).
% 30.45/30.70  thf('126', plain,
% 30.45/30.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 30.45/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.70  thf('127', plain,
% 30.45/30.70      (![X47 : $i, X48 : $i, X49 : $i]:
% 30.45/30.70         (((X47) = (k1_xboole_0))
% 30.45/30.70          | ~ (v1_funct_1 @ X48)
% 30.45/30.70          | ~ (v1_funct_2 @ X48 @ X49 @ X47)
% 30.45/30.70          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X47)))
% 30.45/30.70          | ((k5_relat_1 @ X48 @ (k2_funct_1 @ X48)) = (k6_partfun1 @ X49))
% 30.45/30.70          | ~ (v2_funct_1 @ X48)
% 30.45/30.70          | ((k2_relset_1 @ X49 @ X47 @ X48) != (X47)))),
% 30.45/30.70      inference('cnf', [status(esa)], [t35_funct_2])).
% 30.45/30.70  thf('128', plain,
% 30.45/30.70      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 30.45/30.70        | ~ (v2_funct_1 @ sk_C)
% 30.45/30.70        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 30.45/30.70        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 30.45/30.70        | ~ (v1_funct_1 @ sk_C)
% 30.45/30.70        | ((sk_B) = (k1_xboole_0)))),
% 30.45/30.70      inference('sup-', [status(thm)], ['126', '127'])).
% 30.45/30.70  thf('129', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 30.45/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.70  thf('130', plain, ((v2_funct_1 @ sk_C)),
% 30.45/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.70  thf('131', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 30.45/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.70  thf('132', plain, ((v1_funct_1 @ sk_C)),
% 30.45/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.70  thf('133', plain,
% 30.45/30.70      ((((sk_B) != (sk_B))
% 30.45/30.70        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 30.45/30.70        | ((sk_B) = (k1_xboole_0)))),
% 30.45/30.70      inference('demod', [status(thm)], ['128', '129', '130', '131', '132'])).
% 30.45/30.70  thf('134', plain,
% 30.45/30.70      ((((sk_B) = (k1_xboole_0))
% 30.45/30.70        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 30.45/30.70      inference('simplify', [status(thm)], ['133'])).
% 30.45/30.70  thf('135', plain, (((sk_B) != (k1_xboole_0))),
% 30.45/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.70  thf('136', plain,
% 30.45/30.70      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 30.45/30.70      inference('simplify_reflect-', [status(thm)], ['134', '135'])).
% 30.45/30.70  thf('137', plain,
% 30.45/30.70      (![X11 : $i]:
% 30.45/30.70         (~ (v2_funct_1 @ X11)
% 30.45/30.70          | ((k2_relat_1 @ (k5_relat_1 @ X11 @ (k2_funct_1 @ X11)))
% 30.45/30.70              = (k1_relat_1 @ X11))
% 30.45/30.70          | ~ (v1_funct_1 @ X11)
% 30.45/30.70          | ~ (v1_relat_1 @ X11))),
% 30.45/30.70      inference('cnf', [status(esa)], [t58_funct_1])).
% 30.45/30.70  thf('138', plain,
% 30.45/30.70      ((((k2_relat_1 @ (k6_partfun1 @ sk_A)) = (k1_relat_1 @ sk_C))
% 30.45/30.70        | ~ (v1_relat_1 @ sk_C)
% 30.45/30.70        | ~ (v1_funct_1 @ sk_C)
% 30.45/30.70        | ~ (v2_funct_1 @ sk_C))),
% 30.45/30.70      inference('sup+', [status(thm)], ['136', '137'])).
% 30.45/30.70  thf('139', plain, (![X4 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 30.45/30.70      inference('demod', [status(thm)], ['68', '69'])).
% 30.45/30.70  thf('140', plain, ((v1_relat_1 @ sk_C)),
% 30.45/30.70      inference('sup-', [status(thm)], ['114', '115'])).
% 30.45/30.70  thf('141', plain, ((v1_funct_1 @ sk_C)),
% 30.45/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.70  thf('142', plain, ((v2_funct_1 @ sk_C)),
% 30.45/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.70  thf('143', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 30.45/30.70      inference('demod', [status(thm)], ['138', '139', '140', '141', '142'])).
% 30.45/30.70  thf('144', plain,
% 30.45/30.70      (![X7 : $i]:
% 30.45/30.70         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 30.45/30.70          | ~ (v1_funct_1 @ X7)
% 30.45/30.70          | ~ (v1_relat_1 @ X7))),
% 30.45/30.70      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 30.45/30.70  thf(t55_funct_1, axiom,
% 30.45/30.70    (![A:$i]:
% 30.45/30.70     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 30.45/30.70       ( ( v2_funct_1 @ A ) =>
% 30.45/30.70         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 30.45/30.70           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 30.45/30.70  thf('145', plain,
% 30.45/30.70      (![X10 : $i]:
% 30.45/30.70         (~ (v2_funct_1 @ X10)
% 30.45/30.70          | ((k1_relat_1 @ X10) = (k2_relat_1 @ (k2_funct_1 @ X10)))
% 30.45/30.70          | ~ (v1_funct_1 @ X10)
% 30.45/30.70          | ~ (v1_relat_1 @ X10))),
% 30.45/30.70      inference('cnf', [status(esa)], [t55_funct_1])).
% 30.45/30.70  thf(t80_relat_1, axiom,
% 30.45/30.70    (![A:$i]:
% 30.45/30.70     ( ( v1_relat_1 @ A ) =>
% 30.45/30.70       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 30.45/30.70  thf('146', plain,
% 30.45/30.70      (![X6 : $i]:
% 30.45/30.70         (((k5_relat_1 @ X6 @ (k6_relat_1 @ (k2_relat_1 @ X6))) = (X6))
% 30.45/30.70          | ~ (v1_relat_1 @ X6))),
% 30.45/30.70      inference('cnf', [status(esa)], [t80_relat_1])).
% 30.45/30.70  thf('147', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 30.45/30.70      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 30.45/30.70  thf('148', plain,
% 30.45/30.70      (![X6 : $i]:
% 30.45/30.70         (((k5_relat_1 @ X6 @ (k6_partfun1 @ (k2_relat_1 @ X6))) = (X6))
% 30.45/30.70          | ~ (v1_relat_1 @ X6))),
% 30.45/30.70      inference('demod', [status(thm)], ['146', '147'])).
% 30.45/30.70  thf('149', plain,
% 30.45/30.70      (![X0 : $i]:
% 30.45/30.70         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 30.45/30.70            = (k2_funct_1 @ X0))
% 30.45/30.70          | ~ (v1_relat_1 @ X0)
% 30.45/30.70          | ~ (v1_funct_1 @ X0)
% 30.45/30.70          | ~ (v2_funct_1 @ X0)
% 30.45/30.70          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 30.45/30.70      inference('sup+', [status(thm)], ['145', '148'])).
% 30.45/30.70  thf('150', plain,
% 30.45/30.70      (![X0 : $i]:
% 30.45/30.70         (~ (v1_relat_1 @ X0)
% 30.45/30.70          | ~ (v1_funct_1 @ X0)
% 30.45/30.70          | ~ (v2_funct_1 @ X0)
% 30.45/30.70          | ~ (v1_funct_1 @ X0)
% 30.45/30.70          | ~ (v1_relat_1 @ X0)
% 30.45/30.70          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 30.45/30.70              (k6_partfun1 @ (k1_relat_1 @ X0))) = (k2_funct_1 @ X0)))),
% 30.45/30.70      inference('sup-', [status(thm)], ['144', '149'])).
% 30.45/30.70  thf('151', plain,
% 30.45/30.70      (![X0 : $i]:
% 30.45/30.70         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 30.45/30.70            = (k2_funct_1 @ X0))
% 30.45/30.70          | ~ (v2_funct_1 @ X0)
% 30.45/30.70          | ~ (v1_funct_1 @ X0)
% 30.45/30.70          | ~ (v1_relat_1 @ X0))),
% 30.45/30.70      inference('simplify', [status(thm)], ['150'])).
% 30.45/30.70  thf('152', plain,
% 30.45/30.70      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 30.45/30.70          = (k2_funct_1 @ sk_C))
% 30.45/30.70        | ~ (v1_relat_1 @ sk_C)
% 30.45/30.70        | ~ (v1_funct_1 @ sk_C)
% 30.45/30.70        | ~ (v2_funct_1 @ sk_C))),
% 30.45/30.70      inference('sup+', [status(thm)], ['143', '151'])).
% 30.45/30.70  thf('153', plain, ((v1_relat_1 @ sk_C)),
% 30.45/30.70      inference('sup-', [status(thm)], ['114', '115'])).
% 30.45/30.70  thf('154', plain, ((v1_funct_1 @ sk_C)),
% 30.45/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.70  thf('155', plain, ((v2_funct_1 @ sk_C)),
% 30.45/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.70  thf('156', plain,
% 30.45/30.70      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 30.45/30.70         = (k2_funct_1 @ sk_C))),
% 30.45/30.70      inference('demod', [status(thm)], ['152', '153', '154', '155'])).
% 30.45/30.70  thf('157', plain, ((v1_relat_1 @ sk_C)),
% 30.45/30.70      inference('sup-', [status(thm)], ['114', '115'])).
% 30.45/30.70  thf('158', plain, ((v1_funct_1 @ sk_C)),
% 30.45/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.70  thf('159', plain, ((v2_funct_1 @ sk_C)),
% 30.45/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.70  thf('160', plain, ((v1_relat_1 @ sk_D)),
% 30.45/30.70      inference('sup-', [status(thm)], ['71', '72'])).
% 30.45/30.70  thf('161', plain,
% 30.45/30.70      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (k2_funct_1 @ sk_C))),
% 30.45/30.70      inference('demod', [status(thm)],
% 30.45/30.70                ['100', '125', '156', '157', '158', '159', '160'])).
% 30.45/30.70  thf('162', plain, ((v1_relat_1 @ sk_D)),
% 30.45/30.70      inference('sup-', [status(thm)], ['71', '72'])).
% 30.45/30.70  thf('163', plain, (((k2_funct_1 @ sk_C) = (sk_D))),
% 30.45/30.70      inference('demod', [status(thm)], ['80', '161', '162'])).
% 30.45/30.70  thf('164', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 30.45/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.45/30.70  thf('165', plain, ($false),
% 30.45/30.70      inference('simplify_reflect-', [status(thm)], ['163', '164'])).
% 30.45/30.70  
% 30.45/30.70  % SZS output end Refutation
% 30.45/30.70  
% 30.45/30.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Cobb8Qy4F2

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:17 EST 2020

% Result     : Theorem 3.30s
% Output     : Refutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 610 expanded)
%              Number of leaves         :   53 ( 207 expanded)
%              Depth                    :   19
%              Number of atoms          : 1664 (14197 expanded)
%              Number of equality atoms :  106 ( 987 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf('1',plain,(
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

thf('2',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ( ( k1_partfun1 @ X43 @ X44 @ X46 @ X47 @ X42 @ X45 )
        = ( k5_relat_1 @ X42 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('9',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('10',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

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
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X39 ) ) ) ) ),
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

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('20',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( X20 = X23 )
      | ~ ( r2_relset_1 @ X21 @ X22 @ X20 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','21'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('23',plain,(
    ! [X41: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('24',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('25',plain,(
    ! [X41: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X41 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['6','7','26'])).

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

thf('28',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( X11
        = ( k2_funct_1 @ X12 ) )
      | ( ( k5_relat_1 @ X11 @ X12 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X12 ) ) )
      | ( ( k2_relat_1 @ X11 )
       != ( k1_relat_1 @ X12 ) )
      | ~ ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('29',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('31',plain,(
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

thf('32',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X51 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ( v2_funct_2 @ X49 @ X51 )
      | ~ ( r2_relset_1 @ X51 @ X51 @ ( k1_partfun1 @ X51 @ X50 @ X50 @ X51 @ X52 @ X49 ) @ ( k6_partfun1 @ X51 ) )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X50 ) ) )
      | ~ ( v1_funct_2 @ X52 @ X51 @ X50 )
      | ~ ( v1_funct_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t29_funct_2])).

thf('33',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('34',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X51 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ( v2_funct_2 @ X49 @ X51 )
      | ~ ( r2_relset_1 @ X51 @ X51 @ ( k1_partfun1 @ X51 @ X50 @ X50 @ X51 @ X52 @ X49 ) @ ( k6_relat_1 @ X51 ) )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X50 ) ) )
      | ~ ( v1_funct_2 @ X52 @ X51 @ X50 )
      | ~ ( v1_funct_1 @ X52 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) @ ( k6_relat_1 @ sk_A ) )
      | ( v2_funct_2 @ sk_D @ sk_A )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) @ ( k6_relat_1 @ sk_A ) )
      | ( v2_funct_2 @ sk_D @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['30','38'])).

thf('40',plain,(
    ! [X41: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X41 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('41',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( r2_relset_1 @ X21 @ X22 @ X20 @ X23 )
      | ( X20 != X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('42',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_relset_1 @ X21 @ X22 @ X23 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['39','43','44','45','46'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('48',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v2_funct_2 @ X33 @ X32 )
      | ( ( k2_relat_1 @ X33 )
        = X32 )
      | ~ ( v5_relat_1 @ X33 @ X32 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( ( k2_relat_1 @ sk_D )
      = sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('52',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('53',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('54',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('56',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v5_relat_1 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('57',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['49','54','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['52','53'])).

thf('60',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
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

thf('62',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( X53 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X54 )
      | ~ ( v1_funct_2 @ X54 @ X55 @ X53 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X53 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X54 ) @ X54 )
        = ( k6_partfun1 @ X53 ) )
      | ~ ( v2_funct_1 @ X54 )
      | ( ( k2_relset_1 @ X55 @ X53 @ X54 )
       != X53 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('63',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('64',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( X53 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X54 )
      | ~ ( v1_funct_2 @ X54 @ X55 @ X53 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X53 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X54 ) @ X54 )
        = ( k6_relat_1 @ X53 ) )
      | ~ ( v2_funct_1 @ X54 )
      | ( ( k2_relset_1 @ X55 @ X53 @ X54 )
       != X53 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','66','67','68','69'])).

thf('71',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['71','72'])).

thf(t59_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) )
            = ( k2_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) )
            = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('74',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X10 ) @ X10 ) )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t59_funct_1])).

thf('75',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ sk_B ) )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('76',plain,(
    ! [X5: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('77',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('79',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('81',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['75','76','81','82','83'])).

thf('85',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
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

thf('86',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ( X26
        = ( k1_relset_1 @ X26 @ X27 @ X28 ) )
      | ~ ( zip_tseitin_1 @ X28 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('87',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('88',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('89',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
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

thf('90',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X30 )
      | ( zip_tseitin_1 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('91',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('93',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['92','93'])).

thf('95',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('96',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('97',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['87','94','97'])).

thf('99',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['79','80'])).

thf('101',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B != sk_B )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['29','58','59','60','84','98','99','100'])).

thf('102',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['6','7','26'])).

thf(t48_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) ) )
           => ( ( v2_funct_1 @ B )
              & ( v2_funct_1 @ A ) ) ) ) ) )).

thf('104',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( v2_funct_1 @ X9 )
      | ( ( k2_relat_1 @ X8 )
       != ( k1_relat_1 @ X9 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X8 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('105',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( v2_funct_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('106',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('107',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['52','53'])).

thf('108',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['75','76','81','82','83'])).

thf('110',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['87','94','97'])).

thf('111',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['79','80'])).

thf('113',plain,
    ( ( sk_B != sk_B )
    | ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['105','106','107','108','109','110','111','112'])).

thf('114',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['102','114'])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('116',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X13 ) )
        = X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('117',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['52','53'])).

thf('119',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['113'])).

thf('121',plain,
    ( ( k2_funct_1 @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['117','118','119','120'])).

thf('122',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['121','122'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Cobb8Qy4F2
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:51:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 3.30/3.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.30/3.53  % Solved by: fo/fo7.sh
% 3.30/3.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.30/3.53  % done 876 iterations in 3.081s
% 3.30/3.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.30/3.53  % SZS output start Refutation
% 3.30/3.53  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 3.30/3.53  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.30/3.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.30/3.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.30/3.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.30/3.53  thf(sk_D_type, type, sk_D: $i).
% 3.30/3.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.30/3.53  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 3.30/3.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.30/3.53  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.30/3.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.30/3.53  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.30/3.53  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 3.30/3.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.30/3.53  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 3.30/3.53  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.30/3.53  thf(sk_B_type, type, sk_B: $i).
% 3.30/3.53  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.30/3.53  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 3.30/3.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.30/3.53  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.30/3.53  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.30/3.53  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.30/3.53  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.30/3.53  thf(sk_C_type, type, sk_C: $i).
% 3.30/3.53  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.30/3.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.30/3.53  thf(sk_A_type, type, sk_A: $i).
% 3.30/3.53  thf(t36_funct_2, conjecture,
% 3.30/3.53    (![A:$i,B:$i,C:$i]:
% 3.30/3.53     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.30/3.53         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.30/3.53       ( ![D:$i]:
% 3.30/3.53         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.30/3.53             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.30/3.53           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 3.30/3.53               ( r2_relset_1 @
% 3.30/3.53                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.30/3.53                 ( k6_partfun1 @ A ) ) & 
% 3.30/3.53               ( v2_funct_1 @ C ) ) =>
% 3.30/3.53             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 3.30/3.53               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 3.30/3.53  thf(zf_stmt_0, negated_conjecture,
% 3.30/3.53    (~( ![A:$i,B:$i,C:$i]:
% 3.30/3.53        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.30/3.53            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.30/3.53          ( ![D:$i]:
% 3.30/3.53            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.30/3.53                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.30/3.53              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 3.30/3.53                  ( r2_relset_1 @
% 3.30/3.53                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.30/3.53                    ( k6_partfun1 @ A ) ) & 
% 3.30/3.53                  ( v2_funct_1 @ C ) ) =>
% 3.30/3.53                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 3.30/3.53                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 3.30/3.53    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 3.30/3.53  thf('0', plain,
% 3.30/3.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.30/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.53  thf('1', plain,
% 3.30/3.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.30/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.53  thf(redefinition_k1_partfun1, axiom,
% 3.30/3.53    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.30/3.53     ( ( ( v1_funct_1 @ E ) & 
% 3.30/3.53         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.30/3.53         ( v1_funct_1 @ F ) & 
% 3.30/3.53         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.30/3.53       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 3.30/3.53  thf('2', plain,
% 3.30/3.53      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 3.30/3.53         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 3.30/3.53          | ~ (v1_funct_1 @ X42)
% 3.30/3.53          | ~ (v1_funct_1 @ X45)
% 3.30/3.53          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 3.30/3.53          | ((k1_partfun1 @ X43 @ X44 @ X46 @ X47 @ X42 @ X45)
% 3.30/3.53              = (k5_relat_1 @ X42 @ X45)))),
% 3.30/3.53      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 3.30/3.53  thf('3', plain,
% 3.30/3.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.30/3.53         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 3.30/3.53            = (k5_relat_1 @ sk_C @ X0))
% 3.30/3.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.30/3.53          | ~ (v1_funct_1 @ X0)
% 3.30/3.53          | ~ (v1_funct_1 @ sk_C))),
% 3.30/3.53      inference('sup-', [status(thm)], ['1', '2'])).
% 3.30/3.53  thf('4', plain, ((v1_funct_1 @ sk_C)),
% 3.30/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.53  thf('5', plain,
% 3.30/3.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.30/3.53         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 3.30/3.53            = (k5_relat_1 @ sk_C @ X0))
% 3.30/3.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.30/3.53          | ~ (v1_funct_1 @ X0))),
% 3.30/3.53      inference('demod', [status(thm)], ['3', '4'])).
% 3.30/3.53  thf('6', plain,
% 3.30/3.53      ((~ (v1_funct_1 @ sk_D)
% 3.30/3.53        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.30/3.53            = (k5_relat_1 @ sk_C @ sk_D)))),
% 3.30/3.53      inference('sup-', [status(thm)], ['0', '5'])).
% 3.30/3.53  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 3.30/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.53  thf('8', plain,
% 3.30/3.53      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.30/3.53        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.30/3.53        (k6_partfun1 @ sk_A))),
% 3.30/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.53  thf(redefinition_k6_partfun1, axiom,
% 3.30/3.53    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 3.30/3.53  thf('9', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 3.30/3.53      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.30/3.53  thf('10', plain,
% 3.30/3.53      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.30/3.53        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.30/3.53        (k6_relat_1 @ sk_A))),
% 3.30/3.53      inference('demod', [status(thm)], ['8', '9'])).
% 3.30/3.53  thf('11', plain,
% 3.30/3.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.30/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.53  thf('12', plain,
% 3.30/3.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.30/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.53  thf(dt_k1_partfun1, axiom,
% 3.30/3.53    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.30/3.53     ( ( ( v1_funct_1 @ E ) & 
% 3.30/3.53         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.30/3.53         ( v1_funct_1 @ F ) & 
% 3.30/3.53         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.30/3.53       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 3.30/3.53         ( m1_subset_1 @
% 3.30/3.53           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 3.30/3.53           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 3.30/3.53  thf('13', plain,
% 3.30/3.53      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 3.30/3.53         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 3.30/3.53          | ~ (v1_funct_1 @ X34)
% 3.30/3.53          | ~ (v1_funct_1 @ X37)
% 3.30/3.53          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 3.30/3.53          | (m1_subset_1 @ (k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37) @ 
% 3.30/3.53             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X39))))),
% 3.30/3.53      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 3.30/3.53  thf('14', plain,
% 3.30/3.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.30/3.53         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.30/3.53           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.30/3.53          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.30/3.53          | ~ (v1_funct_1 @ X1)
% 3.30/3.53          | ~ (v1_funct_1 @ sk_C))),
% 3.30/3.53      inference('sup-', [status(thm)], ['12', '13'])).
% 3.30/3.53  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 3.30/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.53  thf('16', plain,
% 3.30/3.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.30/3.53         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.30/3.53           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.30/3.53          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.30/3.53          | ~ (v1_funct_1 @ X1))),
% 3.30/3.53      inference('demod', [status(thm)], ['14', '15'])).
% 3.30/3.53  thf('17', plain,
% 3.30/3.53      ((~ (v1_funct_1 @ sk_D)
% 3.30/3.53        | (m1_subset_1 @ 
% 3.30/3.53           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.30/3.53           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.30/3.53      inference('sup-', [status(thm)], ['11', '16'])).
% 3.30/3.53  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 3.30/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.53  thf('19', plain,
% 3.30/3.53      ((m1_subset_1 @ 
% 3.30/3.53        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.30/3.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.30/3.53      inference('demod', [status(thm)], ['17', '18'])).
% 3.30/3.53  thf(redefinition_r2_relset_1, axiom,
% 3.30/3.53    (![A:$i,B:$i,C:$i,D:$i]:
% 3.30/3.53     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.30/3.53         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.30/3.53       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.30/3.53  thf('20', plain,
% 3.30/3.53      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 3.30/3.53         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 3.30/3.53          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 3.30/3.53          | ((X20) = (X23))
% 3.30/3.53          | ~ (r2_relset_1 @ X21 @ X22 @ X20 @ X23))),
% 3.30/3.53      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.30/3.53  thf('21', plain,
% 3.30/3.53      (![X0 : $i]:
% 3.30/3.53         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.30/3.53             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 3.30/3.53          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 3.30/3.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.30/3.53      inference('sup-', [status(thm)], ['19', '20'])).
% 3.30/3.53  thf('22', plain,
% 3.30/3.53      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 3.30/3.53           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.30/3.53        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.30/3.53            = (k6_relat_1 @ sk_A)))),
% 3.30/3.53      inference('sup-', [status(thm)], ['10', '21'])).
% 3.30/3.53  thf(dt_k6_partfun1, axiom,
% 3.30/3.53    (![A:$i]:
% 3.30/3.53     ( ( m1_subset_1 @
% 3.30/3.53         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 3.30/3.53       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 3.30/3.53  thf('23', plain,
% 3.30/3.53      (![X41 : $i]:
% 3.30/3.53         (m1_subset_1 @ (k6_partfun1 @ X41) @ 
% 3.30/3.53          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X41)))),
% 3.30/3.53      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 3.30/3.53  thf('24', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 3.30/3.53      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.30/3.53  thf('25', plain,
% 3.30/3.53      (![X41 : $i]:
% 3.30/3.53         (m1_subset_1 @ (k6_relat_1 @ X41) @ 
% 3.30/3.53          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X41)))),
% 3.30/3.53      inference('demod', [status(thm)], ['23', '24'])).
% 3.30/3.53  thf('26', plain,
% 3.30/3.53      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.30/3.53         = (k6_relat_1 @ sk_A))),
% 3.30/3.53      inference('demod', [status(thm)], ['22', '25'])).
% 3.30/3.53  thf('27', plain, (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 3.30/3.53      inference('demod', [status(thm)], ['6', '7', '26'])).
% 3.30/3.53  thf(t64_funct_1, axiom,
% 3.30/3.53    (![A:$i]:
% 3.30/3.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.30/3.53       ( ![B:$i]:
% 3.30/3.53         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.30/3.53           ( ( ( v2_funct_1 @ A ) & 
% 3.30/3.53               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 3.30/3.53               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 3.30/3.53             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 3.30/3.53  thf('28', plain,
% 3.30/3.53      (![X11 : $i, X12 : $i]:
% 3.30/3.53         (~ (v1_relat_1 @ X11)
% 3.30/3.53          | ~ (v1_funct_1 @ X11)
% 3.30/3.53          | ((X11) = (k2_funct_1 @ X12))
% 3.30/3.53          | ((k5_relat_1 @ X11 @ X12) != (k6_relat_1 @ (k2_relat_1 @ X12)))
% 3.30/3.53          | ((k2_relat_1 @ X11) != (k1_relat_1 @ X12))
% 3.30/3.53          | ~ (v2_funct_1 @ X12)
% 3.30/3.53          | ~ (v1_funct_1 @ X12)
% 3.30/3.53          | ~ (v1_relat_1 @ X12))),
% 3.30/3.53      inference('cnf', [status(esa)], [t64_funct_1])).
% 3.30/3.53  thf('29', plain,
% 3.30/3.53      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ (k2_relat_1 @ sk_D)))
% 3.30/3.53        | ~ (v1_relat_1 @ sk_D)
% 3.30/3.53        | ~ (v1_funct_1 @ sk_D)
% 3.30/3.53        | ~ (v2_funct_1 @ sk_D)
% 3.30/3.53        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 3.30/3.53        | ((sk_C) = (k2_funct_1 @ sk_D))
% 3.30/3.53        | ~ (v1_funct_1 @ sk_C)
% 3.30/3.53        | ~ (v1_relat_1 @ sk_C))),
% 3.30/3.53      inference('sup-', [status(thm)], ['27', '28'])).
% 3.30/3.53  thf('30', plain,
% 3.30/3.53      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.30/3.53         = (k6_relat_1 @ sk_A))),
% 3.30/3.53      inference('demod', [status(thm)], ['22', '25'])).
% 3.30/3.53  thf('31', plain,
% 3.30/3.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.30/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.53  thf(t29_funct_2, axiom,
% 3.30/3.53    (![A:$i,B:$i,C:$i]:
% 3.30/3.53     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.30/3.53         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.30/3.53       ( ![D:$i]:
% 3.30/3.53         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.30/3.53             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.30/3.53           ( ( r2_relset_1 @
% 3.30/3.53               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.30/3.53               ( k6_partfun1 @ A ) ) =>
% 3.30/3.53             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 3.30/3.53  thf('32', plain,
% 3.30/3.53      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 3.30/3.53         (~ (v1_funct_1 @ X49)
% 3.30/3.53          | ~ (v1_funct_2 @ X49 @ X50 @ X51)
% 3.30/3.53          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 3.30/3.53          | (v2_funct_2 @ X49 @ X51)
% 3.30/3.53          | ~ (r2_relset_1 @ X51 @ X51 @ 
% 3.30/3.53               (k1_partfun1 @ X51 @ X50 @ X50 @ X51 @ X52 @ X49) @ 
% 3.30/3.53               (k6_partfun1 @ X51))
% 3.30/3.53          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X50)))
% 3.30/3.53          | ~ (v1_funct_2 @ X52 @ X51 @ X50)
% 3.30/3.53          | ~ (v1_funct_1 @ X52))),
% 3.30/3.53      inference('cnf', [status(esa)], [t29_funct_2])).
% 3.30/3.53  thf('33', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 3.30/3.53      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.30/3.53  thf('34', plain,
% 3.30/3.53      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 3.30/3.53         (~ (v1_funct_1 @ X49)
% 3.30/3.53          | ~ (v1_funct_2 @ X49 @ X50 @ X51)
% 3.30/3.53          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 3.30/3.53          | (v2_funct_2 @ X49 @ X51)
% 3.30/3.53          | ~ (r2_relset_1 @ X51 @ X51 @ 
% 3.30/3.53               (k1_partfun1 @ X51 @ X50 @ X50 @ X51 @ X52 @ X49) @ 
% 3.30/3.53               (k6_relat_1 @ X51))
% 3.30/3.53          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X50)))
% 3.30/3.53          | ~ (v1_funct_2 @ X52 @ X51 @ X50)
% 3.30/3.53          | ~ (v1_funct_1 @ X52))),
% 3.30/3.53      inference('demod', [status(thm)], ['32', '33'])).
% 3.30/3.53  thf('35', plain,
% 3.30/3.53      (![X0 : $i]:
% 3.30/3.53         (~ (v1_funct_1 @ X0)
% 3.30/3.53          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_B)
% 3.30/3.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 3.30/3.53          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.30/3.53               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ X0 @ sk_D) @ 
% 3.30/3.53               (k6_relat_1 @ sk_A))
% 3.30/3.53          | (v2_funct_2 @ sk_D @ sk_A)
% 3.30/3.53          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 3.30/3.53          | ~ (v1_funct_1 @ sk_D))),
% 3.30/3.53      inference('sup-', [status(thm)], ['31', '34'])).
% 3.30/3.53  thf('36', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 3.30/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.53  thf('37', plain, ((v1_funct_1 @ sk_D)),
% 3.30/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.53  thf('38', plain,
% 3.30/3.53      (![X0 : $i]:
% 3.30/3.53         (~ (v1_funct_1 @ X0)
% 3.30/3.53          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_B)
% 3.30/3.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 3.30/3.53          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.30/3.53               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ X0 @ sk_D) @ 
% 3.30/3.53               (k6_relat_1 @ sk_A))
% 3.30/3.53          | (v2_funct_2 @ sk_D @ sk_A))),
% 3.30/3.53      inference('demod', [status(thm)], ['35', '36', '37'])).
% 3.30/3.53  thf('39', plain,
% 3.30/3.53      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 3.30/3.53           (k6_relat_1 @ sk_A))
% 3.30/3.53        | (v2_funct_2 @ sk_D @ sk_A)
% 3.30/3.53        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 3.30/3.53        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 3.30/3.53        | ~ (v1_funct_1 @ sk_C))),
% 3.30/3.53      inference('sup-', [status(thm)], ['30', '38'])).
% 3.30/3.53  thf('40', plain,
% 3.30/3.53      (![X41 : $i]:
% 3.30/3.53         (m1_subset_1 @ (k6_relat_1 @ X41) @ 
% 3.30/3.53          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X41)))),
% 3.30/3.53      inference('demod', [status(thm)], ['23', '24'])).
% 3.30/3.53  thf('41', plain,
% 3.30/3.53      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 3.30/3.53         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 3.30/3.53          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 3.30/3.53          | (r2_relset_1 @ X21 @ X22 @ X20 @ X23)
% 3.30/3.53          | ((X20) != (X23)))),
% 3.30/3.53      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.30/3.53  thf('42', plain,
% 3.30/3.53      (![X21 : $i, X22 : $i, X23 : $i]:
% 3.30/3.53         ((r2_relset_1 @ X21 @ X22 @ X23 @ X23)
% 3.30/3.53          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 3.30/3.53      inference('simplify', [status(thm)], ['41'])).
% 3.30/3.53  thf('43', plain,
% 3.30/3.53      (![X0 : $i]:
% 3.30/3.53         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 3.30/3.53      inference('sup-', [status(thm)], ['40', '42'])).
% 3.30/3.53  thf('44', plain,
% 3.30/3.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.30/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.53  thf('45', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.30/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.53  thf('46', plain, ((v1_funct_1 @ sk_C)),
% 3.30/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.53  thf('47', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 3.30/3.53      inference('demod', [status(thm)], ['39', '43', '44', '45', '46'])).
% 3.30/3.53  thf(d3_funct_2, axiom,
% 3.30/3.53    (![A:$i,B:$i]:
% 3.30/3.53     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 3.30/3.53       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 3.30/3.53  thf('48', plain,
% 3.30/3.53      (![X32 : $i, X33 : $i]:
% 3.30/3.53         (~ (v2_funct_2 @ X33 @ X32)
% 3.30/3.53          | ((k2_relat_1 @ X33) = (X32))
% 3.30/3.53          | ~ (v5_relat_1 @ X33 @ X32)
% 3.30/3.53          | ~ (v1_relat_1 @ X33))),
% 3.30/3.53      inference('cnf', [status(esa)], [d3_funct_2])).
% 3.30/3.53  thf('49', plain,
% 3.30/3.53      ((~ (v1_relat_1 @ sk_D)
% 3.30/3.53        | ~ (v5_relat_1 @ sk_D @ sk_A)
% 3.30/3.53        | ((k2_relat_1 @ sk_D) = (sk_A)))),
% 3.30/3.53      inference('sup-', [status(thm)], ['47', '48'])).
% 3.30/3.53  thf('50', plain,
% 3.30/3.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.30/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.53  thf(cc2_relat_1, axiom,
% 3.30/3.53    (![A:$i]:
% 3.30/3.53     ( ( v1_relat_1 @ A ) =>
% 3.30/3.53       ( ![B:$i]:
% 3.30/3.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 3.30/3.53  thf('51', plain,
% 3.30/3.53      (![X0 : $i, X1 : $i]:
% 3.30/3.53         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 3.30/3.53          | (v1_relat_1 @ X0)
% 3.30/3.53          | ~ (v1_relat_1 @ X1))),
% 3.30/3.53      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.30/3.53  thf('52', plain,
% 3.30/3.53      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 3.30/3.53      inference('sup-', [status(thm)], ['50', '51'])).
% 3.30/3.53  thf(fc6_relat_1, axiom,
% 3.30/3.53    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 3.30/3.53  thf('53', plain,
% 3.30/3.53      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 3.30/3.53      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.30/3.53  thf('54', plain, ((v1_relat_1 @ sk_D)),
% 3.30/3.53      inference('demod', [status(thm)], ['52', '53'])).
% 3.30/3.53  thf('55', plain,
% 3.30/3.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.30/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.53  thf(cc2_relset_1, axiom,
% 3.30/3.53    (![A:$i,B:$i,C:$i]:
% 3.30/3.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.30/3.53       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.30/3.53  thf('56', plain,
% 3.30/3.53      (![X14 : $i, X15 : $i, X16 : $i]:
% 3.30/3.53         ((v5_relat_1 @ X14 @ X16)
% 3.30/3.53          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 3.30/3.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.30/3.53  thf('57', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 3.30/3.53      inference('sup-', [status(thm)], ['55', '56'])).
% 3.30/3.53  thf('58', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.30/3.53      inference('demod', [status(thm)], ['49', '54', '57'])).
% 3.30/3.53  thf('59', plain, ((v1_relat_1 @ sk_D)),
% 3.30/3.53      inference('demod', [status(thm)], ['52', '53'])).
% 3.30/3.53  thf('60', plain, ((v1_funct_1 @ sk_D)),
% 3.30/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.53  thf('61', plain,
% 3.30/3.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.30/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.53  thf(t35_funct_2, axiom,
% 3.30/3.53    (![A:$i,B:$i,C:$i]:
% 3.30/3.53     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.30/3.53         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.30/3.53       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 3.30/3.53         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 3.30/3.53           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 3.30/3.53             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 3.30/3.53  thf('62', plain,
% 3.30/3.53      (![X53 : $i, X54 : $i, X55 : $i]:
% 3.30/3.53         (((X53) = (k1_xboole_0))
% 3.30/3.53          | ~ (v1_funct_1 @ X54)
% 3.30/3.53          | ~ (v1_funct_2 @ X54 @ X55 @ X53)
% 3.30/3.53          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X53)))
% 3.30/3.53          | ((k5_relat_1 @ (k2_funct_1 @ X54) @ X54) = (k6_partfun1 @ X53))
% 3.30/3.53          | ~ (v2_funct_1 @ X54)
% 3.30/3.53          | ((k2_relset_1 @ X55 @ X53 @ X54) != (X53)))),
% 3.30/3.53      inference('cnf', [status(esa)], [t35_funct_2])).
% 3.30/3.53  thf('63', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 3.30/3.53      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.30/3.53  thf('64', plain,
% 3.30/3.53      (![X53 : $i, X54 : $i, X55 : $i]:
% 3.30/3.53         (((X53) = (k1_xboole_0))
% 3.30/3.53          | ~ (v1_funct_1 @ X54)
% 3.30/3.53          | ~ (v1_funct_2 @ X54 @ X55 @ X53)
% 3.30/3.53          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X53)))
% 3.30/3.53          | ((k5_relat_1 @ (k2_funct_1 @ X54) @ X54) = (k6_relat_1 @ X53))
% 3.30/3.53          | ~ (v2_funct_1 @ X54)
% 3.30/3.53          | ((k2_relset_1 @ X55 @ X53 @ X54) != (X53)))),
% 3.30/3.53      inference('demod', [status(thm)], ['62', '63'])).
% 3.30/3.53  thf('65', plain,
% 3.30/3.53      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 3.30/3.53        | ~ (v2_funct_1 @ sk_C)
% 3.30/3.53        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))
% 3.30/3.53        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 3.30/3.53        | ~ (v1_funct_1 @ sk_C)
% 3.30/3.53        | ((sk_B) = (k1_xboole_0)))),
% 3.30/3.53      inference('sup-', [status(thm)], ['61', '64'])).
% 3.30/3.53  thf('66', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 3.30/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.53  thf('67', plain, ((v2_funct_1 @ sk_C)),
% 3.30/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.53  thf('68', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.30/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.53  thf('69', plain, ((v1_funct_1 @ sk_C)),
% 3.30/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.53  thf('70', plain,
% 3.30/3.53      ((((sk_B) != (sk_B))
% 3.30/3.53        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))
% 3.30/3.53        | ((sk_B) = (k1_xboole_0)))),
% 3.30/3.53      inference('demod', [status(thm)], ['65', '66', '67', '68', '69'])).
% 3.30/3.53  thf('71', plain,
% 3.30/3.53      ((((sk_B) = (k1_xboole_0))
% 3.30/3.53        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B)))),
% 3.30/3.53      inference('simplify', [status(thm)], ['70'])).
% 3.30/3.53  thf('72', plain, (((sk_B) != (k1_xboole_0))),
% 3.30/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.53  thf('73', plain,
% 3.30/3.53      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))),
% 3.30/3.53      inference('simplify_reflect-', [status(thm)], ['71', '72'])).
% 3.30/3.53  thf(t59_funct_1, axiom,
% 3.30/3.53    (![A:$i]:
% 3.30/3.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.30/3.53       ( ( v2_funct_1 @ A ) =>
% 3.30/3.53         ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 3.30/3.53             ( k2_relat_1 @ A ) ) & 
% 3.30/3.53           ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 3.30/3.53             ( k2_relat_1 @ A ) ) ) ) ))).
% 3.30/3.53  thf('74', plain,
% 3.30/3.53      (![X10 : $i]:
% 3.30/3.53         (~ (v2_funct_1 @ X10)
% 3.30/3.53          | ((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X10) @ X10))
% 3.30/3.53              = (k2_relat_1 @ X10))
% 3.30/3.53          | ~ (v1_funct_1 @ X10)
% 3.30/3.53          | ~ (v1_relat_1 @ X10))),
% 3.30/3.53      inference('cnf', [status(esa)], [t59_funct_1])).
% 3.30/3.53  thf('75', plain,
% 3.30/3.53      ((((k2_relat_1 @ (k6_relat_1 @ sk_B)) = (k2_relat_1 @ sk_C))
% 3.30/3.53        | ~ (v1_relat_1 @ sk_C)
% 3.30/3.53        | ~ (v1_funct_1 @ sk_C)
% 3.30/3.53        | ~ (v2_funct_1 @ sk_C))),
% 3.30/3.53      inference('sup+', [status(thm)], ['73', '74'])).
% 3.30/3.53  thf(t71_relat_1, axiom,
% 3.30/3.53    (![A:$i]:
% 3.30/3.53     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 3.30/3.53       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 3.30/3.53  thf('76', plain, (![X5 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X5)) = (X5))),
% 3.30/3.53      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.30/3.53  thf('77', plain,
% 3.30/3.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.30/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.53  thf('78', plain,
% 3.30/3.53      (![X0 : $i, X1 : $i]:
% 3.30/3.53         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 3.30/3.53          | (v1_relat_1 @ X0)
% 3.30/3.53          | ~ (v1_relat_1 @ X1))),
% 3.30/3.53      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.30/3.53  thf('79', plain,
% 3.30/3.53      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 3.30/3.53      inference('sup-', [status(thm)], ['77', '78'])).
% 3.30/3.53  thf('80', plain,
% 3.30/3.53      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 3.30/3.53      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.30/3.53  thf('81', plain, ((v1_relat_1 @ sk_C)),
% 3.30/3.53      inference('demod', [status(thm)], ['79', '80'])).
% 3.30/3.53  thf('82', plain, ((v1_funct_1 @ sk_C)),
% 3.30/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.53  thf('83', plain, ((v2_funct_1 @ sk_C)),
% 3.30/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.53  thf('84', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 3.30/3.53      inference('demod', [status(thm)], ['75', '76', '81', '82', '83'])).
% 3.30/3.53  thf('85', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 3.30/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.53  thf(d1_funct_2, axiom,
% 3.30/3.53    (![A:$i,B:$i,C:$i]:
% 3.30/3.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.30/3.53       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.30/3.53           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.30/3.53             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.30/3.53         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.30/3.53           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.30/3.53             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.30/3.53  thf(zf_stmt_1, axiom,
% 3.30/3.53    (![C:$i,B:$i,A:$i]:
% 3.30/3.53     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.30/3.53       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.30/3.53  thf('86', plain,
% 3.30/3.53      (![X26 : $i, X27 : $i, X28 : $i]:
% 3.30/3.53         (~ (v1_funct_2 @ X28 @ X26 @ X27)
% 3.30/3.53          | ((X26) = (k1_relset_1 @ X26 @ X27 @ X28))
% 3.30/3.53          | ~ (zip_tseitin_1 @ X28 @ X27 @ X26))),
% 3.30/3.53      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.30/3.53  thf('87', plain,
% 3.30/3.53      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 3.30/3.53        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 3.30/3.53      inference('sup-', [status(thm)], ['85', '86'])).
% 3.30/3.53  thf(zf_stmt_2, axiom,
% 3.30/3.53    (![B:$i,A:$i]:
% 3.30/3.53     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.30/3.53       ( zip_tseitin_0 @ B @ A ) ))).
% 3.30/3.53  thf('88', plain,
% 3.30/3.53      (![X24 : $i, X25 : $i]:
% 3.30/3.53         ((zip_tseitin_0 @ X24 @ X25) | ((X24) = (k1_xboole_0)))),
% 3.30/3.53      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.30/3.53  thf('89', plain,
% 3.30/3.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.30/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.53  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.30/3.53  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 3.30/3.53  thf(zf_stmt_5, axiom,
% 3.30/3.53    (![A:$i,B:$i,C:$i]:
% 3.30/3.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.30/3.53       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.30/3.53         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.30/3.53           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.30/3.53             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.30/3.53  thf('90', plain,
% 3.30/3.53      (![X29 : $i, X30 : $i, X31 : $i]:
% 3.30/3.53         (~ (zip_tseitin_0 @ X29 @ X30)
% 3.30/3.53          | (zip_tseitin_1 @ X31 @ X29 @ X30)
% 3.30/3.53          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 3.30/3.53      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.30/3.53  thf('91', plain,
% 3.30/3.53      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 3.30/3.53      inference('sup-', [status(thm)], ['89', '90'])).
% 3.30/3.53  thf('92', plain,
% 3.30/3.53      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 3.30/3.53      inference('sup-', [status(thm)], ['88', '91'])).
% 3.30/3.53  thf('93', plain, (((sk_A) != (k1_xboole_0))),
% 3.30/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.53  thf('94', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 3.30/3.53      inference('simplify_reflect-', [status(thm)], ['92', '93'])).
% 3.30/3.53  thf('95', plain,
% 3.30/3.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.30/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.53  thf(redefinition_k1_relset_1, axiom,
% 3.30/3.53    (![A:$i,B:$i,C:$i]:
% 3.30/3.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.30/3.53       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.30/3.53  thf('96', plain,
% 3.30/3.53      (![X17 : $i, X18 : $i, X19 : $i]:
% 3.30/3.53         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 3.30/3.53          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 3.30/3.53      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.30/3.53  thf('97', plain,
% 3.30/3.53      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 3.30/3.53      inference('sup-', [status(thm)], ['95', '96'])).
% 3.30/3.53  thf('98', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 3.30/3.53      inference('demod', [status(thm)], ['87', '94', '97'])).
% 3.30/3.53  thf('99', plain, ((v1_funct_1 @ sk_C)),
% 3.30/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.53  thf('100', plain, ((v1_relat_1 @ sk_C)),
% 3.30/3.53      inference('demod', [status(thm)], ['79', '80'])).
% 3.30/3.53  thf('101', plain,
% 3.30/3.53      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ sk_A))
% 3.30/3.53        | ~ (v2_funct_1 @ sk_D)
% 3.30/3.53        | ((sk_B) != (sk_B))
% 3.30/3.53        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 3.30/3.53      inference('demod', [status(thm)],
% 3.30/3.53                ['29', '58', '59', '60', '84', '98', '99', '100'])).
% 3.30/3.53  thf('102', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 3.30/3.53      inference('simplify', [status(thm)], ['101'])).
% 3.30/3.53  thf('103', plain, (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 3.30/3.53      inference('demod', [status(thm)], ['6', '7', '26'])).
% 3.30/3.53  thf(t48_funct_1, axiom,
% 3.30/3.53    (![A:$i]:
% 3.30/3.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.30/3.53       ( ![B:$i]:
% 3.30/3.53         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.30/3.53           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 3.30/3.53               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 3.30/3.53             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 3.30/3.53  thf('104', plain,
% 3.30/3.53      (![X8 : $i, X9 : $i]:
% 3.30/3.53         (~ (v1_relat_1 @ X8)
% 3.30/3.53          | ~ (v1_funct_1 @ X8)
% 3.30/3.53          | (v2_funct_1 @ X9)
% 3.30/3.53          | ((k2_relat_1 @ X8) != (k1_relat_1 @ X9))
% 3.30/3.53          | ~ (v2_funct_1 @ (k5_relat_1 @ X8 @ X9))
% 3.30/3.53          | ~ (v1_funct_1 @ X9)
% 3.30/3.53          | ~ (v1_relat_1 @ X9))),
% 3.30/3.53      inference('cnf', [status(esa)], [t48_funct_1])).
% 3.30/3.53  thf('105', plain,
% 3.30/3.53      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 3.30/3.53        | ~ (v1_relat_1 @ sk_D)
% 3.30/3.53        | ~ (v1_funct_1 @ sk_D)
% 3.30/3.53        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 3.30/3.53        | (v2_funct_1 @ sk_D)
% 3.30/3.53        | ~ (v1_funct_1 @ sk_C)
% 3.30/3.53        | ~ (v1_relat_1 @ sk_C))),
% 3.30/3.53      inference('sup-', [status(thm)], ['103', '104'])).
% 3.30/3.53  thf(fc4_funct_1, axiom,
% 3.30/3.53    (![A:$i]:
% 3.30/3.53     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 3.30/3.53       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 3.30/3.53  thf('106', plain, (![X7 : $i]: (v2_funct_1 @ (k6_relat_1 @ X7))),
% 3.30/3.53      inference('cnf', [status(esa)], [fc4_funct_1])).
% 3.30/3.53  thf('107', plain, ((v1_relat_1 @ sk_D)),
% 3.30/3.53      inference('demod', [status(thm)], ['52', '53'])).
% 3.30/3.53  thf('108', plain, ((v1_funct_1 @ sk_D)),
% 3.30/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.53  thf('109', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 3.30/3.53      inference('demod', [status(thm)], ['75', '76', '81', '82', '83'])).
% 3.30/3.53  thf('110', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 3.30/3.53      inference('demod', [status(thm)], ['87', '94', '97'])).
% 3.30/3.53  thf('111', plain, ((v1_funct_1 @ sk_C)),
% 3.30/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.53  thf('112', plain, ((v1_relat_1 @ sk_C)),
% 3.30/3.53      inference('demod', [status(thm)], ['79', '80'])).
% 3.30/3.53  thf('113', plain, ((((sk_B) != (sk_B)) | (v2_funct_1 @ sk_D))),
% 3.30/3.53      inference('demod', [status(thm)],
% 3.30/3.53                ['105', '106', '107', '108', '109', '110', '111', '112'])).
% 3.30/3.53  thf('114', plain, ((v2_funct_1 @ sk_D)),
% 3.30/3.53      inference('simplify', [status(thm)], ['113'])).
% 3.30/3.53  thf('115', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 3.30/3.53      inference('demod', [status(thm)], ['102', '114'])).
% 3.30/3.53  thf(t65_funct_1, axiom,
% 3.30/3.53    (![A:$i]:
% 3.30/3.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.30/3.53       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 3.30/3.53  thf('116', plain,
% 3.30/3.53      (![X13 : $i]:
% 3.30/3.53         (~ (v2_funct_1 @ X13)
% 3.30/3.53          | ((k2_funct_1 @ (k2_funct_1 @ X13)) = (X13))
% 3.30/3.53          | ~ (v1_funct_1 @ X13)
% 3.30/3.53          | ~ (v1_relat_1 @ X13))),
% 3.30/3.53      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.30/3.53  thf('117', plain,
% 3.30/3.53      ((((k2_funct_1 @ sk_C) = (sk_D))
% 3.30/3.53        | ~ (v1_relat_1 @ sk_D)
% 3.30/3.53        | ~ (v1_funct_1 @ sk_D)
% 3.30/3.53        | ~ (v2_funct_1 @ sk_D))),
% 3.30/3.53      inference('sup+', [status(thm)], ['115', '116'])).
% 3.30/3.53  thf('118', plain, ((v1_relat_1 @ sk_D)),
% 3.30/3.53      inference('demod', [status(thm)], ['52', '53'])).
% 3.30/3.53  thf('119', plain, ((v1_funct_1 @ sk_D)),
% 3.30/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.53  thf('120', plain, ((v2_funct_1 @ sk_D)),
% 3.30/3.53      inference('simplify', [status(thm)], ['113'])).
% 3.30/3.53  thf('121', plain, (((k2_funct_1 @ sk_C) = (sk_D))),
% 3.30/3.53      inference('demod', [status(thm)], ['117', '118', '119', '120'])).
% 3.30/3.53  thf('122', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 3.30/3.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.53  thf('123', plain, ($false),
% 3.30/3.53      inference('simplify_reflect-', [status(thm)], ['121', '122'])).
% 3.30/3.53  
% 3.30/3.53  % SZS output end Refutation
% 3.30/3.53  
% 3.30/3.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Y4QftcV975

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:13 EST 2020

% Result     : Theorem 0.79s
% Output     : Refutation 0.79s
% Verified   : 
% Statistics : Number of formulae       :  246 (1838 expanded)
%              Number of leaves         :   49 ( 580 expanded)
%              Depth                    :   34
%              Number of atoms          : 1955 (36594 expanded)
%              Number of equality atoms :  121 (2359 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

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
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ( ( k1_partfun1 @ X45 @ X46 @ X48 @ X49 @ X44 @ X47 )
        = ( k5_relat_1 @ X44 @ X47 ) ) ) ),
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
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X41 ) ) ) ) ),
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
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( X32 = X35 )
      | ~ ( r2_relset_1 @ X33 @ X34 @ X32 @ X35 ) ) ),
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

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('21',plain,(
    ! [X43: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X43 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('22',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['6','7','22'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('24',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
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

thf('25',plain,(
    ! [X25: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X25 ) @ X25 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('26',plain,(
    ! [X50: $i] :
      ( ( k6_partfun1 @ X50 )
      = ( k6_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('27',plain,(
    ! [X25: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X25 ) @ X25 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('29',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
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

thf('30',plain,(
    ! [X24: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relat_1 @ X24 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('31',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('33',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X31 @ X29 )
        = ( k2_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('34',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('38',plain,(
    ! [X24: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relat_1 @ X24 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('40',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['39'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('41',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ( v4_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['36','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('48',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('50',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('51',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['46','51','52','53'])).

thf('55',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('56',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['31','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('59',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('62',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['30','62'])).

thf('64',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['34','35'])).

thf('65',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('66',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('67',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['63','64','65','66','67','68'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('70',plain,(
    ! [X19: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X19 ) ) @ X19 )
        = X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('71',plain,(
    ! [X50: $i] :
      ( ( k6_partfun1 @ X50 )
      = ( k6_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('72',plain,(
    ! [X19: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X19 ) ) @ X19 )
        = X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['69','72'])).

thf('74',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['29','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('76',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('78',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) @ X16 )
        = ( k5_relat_1 @ X15 @ ( k5_relat_1 @ X14 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X43: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X43 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('81',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['79','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['28','85'])).

thf('87',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('88',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['27','89'])).

thf('91',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['34','35'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('92',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('93',plain,(
    ! [X50: $i] :
      ( ( k6_partfun1 @ X50 )
      = ( k6_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('94',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X17 ) )
      = X17 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X19: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X19 ) ) @ X19 )
        = X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('100',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('103',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['90','91','98','99','100','101','102'])).

thf('104',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) @ X16 )
        = ( k5_relat_1 @ X15 @ ( k5_relat_1 @ X14 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['24','107'])).

thf('109',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('110',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,
    ( ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ sk_D ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['23','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('116',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('118',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('120',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['6','7','22'])).

thf('122',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('123',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v4_relat_1 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('124',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('126',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['118','119'])).

thf('128',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['34','35'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('130',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X22 @ ( k2_relat_1 @ X23 ) )
      | ( ( k9_relat_1 @ X23 @ ( k10_relat_1 @ X23 @ X22 ) )
        = X22 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('133',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['131','132','133'])).

thf('135',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['128','134'])).

thf('136',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['6','7','22'])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('137',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) )
        = ( k10_relat_1 @ X13 @ ( k1_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('138',plain,
    ( ( ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) )
      = ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X17 ) )
      = X17 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('140',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('141',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['118','119'])).

thf('142',plain,
    ( sk_A
    = ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['138','139','140','141'])).

thf('143',plain,
    ( ( k9_relat_1 @ sk_C @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['135','142'])).

thf('144',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['131','132','133'])).

thf('146',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['34','35'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('148',plain,(
    ! [X11: $i] :
      ( ( ( k10_relat_1 @ X11 @ ( k2_relat_1 @ X11 ) )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('149',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_B )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['147','148'])).

thf('150',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('151',plain,
    ( ( k10_relat_1 @ sk_C @ sk_B )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,
    ( ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    = sk_B ),
    inference(demod,[status(thm)],['146','151'])).

thf('153',plain,
    ( sk_A
    = ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['138','139','140','141'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('154',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X9 @ X10 ) @ ( k1_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('155',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A )
    | ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['153','156'])).

thf('158',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v4_relat_1 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('160',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('162',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('164',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,
    ( sk_A
    = ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['138','139','140','141'])).

thf('166',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('167',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['157','164','165','166'])).

thf('168',plain,
    ( ( k9_relat_1 @ sk_C @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['152','167'])).

thf('169',plain,
    ( ( k1_relat_1 @ sk_D )
    = sk_B ),
    inference('sup+',[status(thm)],['143','168'])).

thf('170',plain,(
    ! [X19: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X19 ) ) @ X19 )
        = X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('171',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['169','170'])).

thf('172',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['118','119'])).

thf('173',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['171','172'])).

thf('174',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['171','172'])).

thf('175',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
    = sk_D ),
    inference(demod,[status(thm)],['114','115','120','121','173','174'])).

thf('176',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('177',plain,(
    ! [X25: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k5_relat_1 @ X25 @ ( k2_funct_1 @ X25 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('178',plain,(
    ! [X50: $i] :
      ( ( k6_partfun1 @ X50 )
      = ( k6_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('179',plain,(
    ! [X25: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k5_relat_1 @ X25 @ ( k2_funct_1 @ X25 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(demod,[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('181',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['179','180'])).

thf('182',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('183',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('184',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['181','182','183','184','185'])).

thf('187',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['176','186'])).

thf('188',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('189',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['187','188','189'])).

thf('191',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['157','164','165','166'])).

thf('192',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['190','191'])).

thf('193',plain,
    ( ( k2_funct_1 @ sk_C )
    = sk_D ),
    inference('sup+',[status(thm)],['175','192'])).

thf('194',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['193','194'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Y4QftcV975
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:17:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.79/0.99  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.79/0.99  % Solved by: fo/fo7.sh
% 0.79/0.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.79/0.99  % done 822 iterations in 0.543s
% 0.79/0.99  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.79/0.99  % SZS output start Refutation
% 0.79/0.99  thf(sk_D_type, type, sk_D: $i).
% 0.79/0.99  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.79/0.99  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.79/0.99  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.79/0.99  thf(sk_B_type, type, sk_B: $i).
% 0.79/0.99  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.79/0.99  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.79/0.99  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.79/0.99  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.79/0.99  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.79/0.99  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.79/0.99  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.79/0.99  thf(sk_C_type, type, sk_C: $i).
% 0.79/0.99  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.79/0.99  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.79/0.99  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.79/0.99  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.79/0.99  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.79/0.99  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.79/0.99  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.79/0.99  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.79/0.99  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.79/0.99  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.79/0.99  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.79/0.99  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.79/0.99  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.79/0.99  thf(sk_A_type, type, sk_A: $i).
% 0.79/0.99  thf(t36_funct_2, conjecture,
% 0.79/0.99    (![A:$i,B:$i,C:$i]:
% 0.79/0.99     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.79/0.99         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.79/0.99       ( ![D:$i]:
% 0.79/0.99         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.79/0.99             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.79/0.99           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.79/0.99               ( r2_relset_1 @
% 0.79/0.99                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.79/0.99                 ( k6_partfun1 @ A ) ) & 
% 0.79/0.99               ( v2_funct_1 @ C ) ) =>
% 0.79/0.99             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.79/0.99               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.79/0.99  thf(zf_stmt_0, negated_conjecture,
% 0.79/0.99    (~( ![A:$i,B:$i,C:$i]:
% 0.79/0.99        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.79/0.99            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.79/0.99          ( ![D:$i]:
% 0.79/0.99            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.79/0.99                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.79/0.99              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.79/0.99                  ( r2_relset_1 @
% 0.79/0.99                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.79/0.99                    ( k6_partfun1 @ A ) ) & 
% 0.79/0.99                  ( v2_funct_1 @ C ) ) =>
% 0.79/0.99                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.79/0.99                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.79/0.99    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.79/0.99  thf('0', plain,
% 0.79/0.99      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf('1', plain,
% 0.79/0.99      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf(redefinition_k1_partfun1, axiom,
% 0.79/0.99    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.79/0.99     ( ( ( v1_funct_1 @ E ) & 
% 0.79/0.99         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.79/0.99         ( v1_funct_1 @ F ) & 
% 0.79/0.99         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.79/0.99       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.79/0.99  thf('2', plain,
% 0.79/0.99      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.79/0.99         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 0.79/0.99          | ~ (v1_funct_1 @ X44)
% 0.79/0.99          | ~ (v1_funct_1 @ X47)
% 0.79/0.99          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 0.79/0.99          | ((k1_partfun1 @ X45 @ X46 @ X48 @ X49 @ X44 @ X47)
% 0.79/0.99              = (k5_relat_1 @ X44 @ X47)))),
% 0.79/0.99      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.79/0.99  thf('3', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/0.99         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.79/0.99            = (k5_relat_1 @ sk_C @ X0))
% 0.79/0.99          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.79/0.99          | ~ (v1_funct_1 @ X0)
% 0.79/0.99          | ~ (v1_funct_1 @ sk_C))),
% 0.79/0.99      inference('sup-', [status(thm)], ['1', '2'])).
% 0.79/0.99  thf('4', plain, ((v1_funct_1 @ sk_C)),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf('5', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/0.99         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.79/0.99            = (k5_relat_1 @ sk_C @ X0))
% 0.79/0.99          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.79/0.99          | ~ (v1_funct_1 @ X0))),
% 0.79/0.99      inference('demod', [status(thm)], ['3', '4'])).
% 0.79/0.99  thf('6', plain,
% 0.79/0.99      ((~ (v1_funct_1 @ sk_D)
% 0.79/0.99        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.79/0.99            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.79/0.99      inference('sup-', [status(thm)], ['0', '5'])).
% 0.79/0.99  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf('8', plain,
% 0.79/0.99      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.79/0.99        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.79/0.99        (k6_partfun1 @ sk_A))),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf('9', plain,
% 0.79/0.99      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf('10', plain,
% 0.79/0.99      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf(dt_k1_partfun1, axiom,
% 0.79/0.99    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.79/0.99     ( ( ( v1_funct_1 @ E ) & 
% 0.79/0.99         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.79/0.99         ( v1_funct_1 @ F ) & 
% 0.79/0.99         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.79/0.99       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.79/0.99         ( m1_subset_1 @
% 0.79/0.99           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.79/0.99           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.79/0.99  thf('11', plain,
% 0.79/0.99      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.79/0.99         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.79/0.99          | ~ (v1_funct_1 @ X36)
% 0.79/0.99          | ~ (v1_funct_1 @ X39)
% 0.79/0.99          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.79/0.99          | (m1_subset_1 @ (k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39) @ 
% 0.79/0.99             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X41))))),
% 0.79/0.99      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.79/0.99  thf('12', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/0.99         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.79/0.99           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.79/0.99          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.79/0.99          | ~ (v1_funct_1 @ X1)
% 0.79/0.99          | ~ (v1_funct_1 @ sk_C))),
% 0.79/0.99      inference('sup-', [status(thm)], ['10', '11'])).
% 0.79/0.99  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf('14', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.79/0.99         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.79/0.99           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.79/0.99          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.79/0.99          | ~ (v1_funct_1 @ X1))),
% 0.79/0.99      inference('demod', [status(thm)], ['12', '13'])).
% 0.79/0.99  thf('15', plain,
% 0.79/0.99      ((~ (v1_funct_1 @ sk_D)
% 0.79/0.99        | (m1_subset_1 @ 
% 0.79/0.99           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.79/0.99           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.79/0.99      inference('sup-', [status(thm)], ['9', '14'])).
% 0.79/0.99  thf('16', plain, ((v1_funct_1 @ sk_D)),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf('17', plain,
% 0.79/0.99      ((m1_subset_1 @ 
% 0.79/0.99        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.79/0.99        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.79/0.99      inference('demod', [status(thm)], ['15', '16'])).
% 0.79/0.99  thf(redefinition_r2_relset_1, axiom,
% 0.79/0.99    (![A:$i,B:$i,C:$i,D:$i]:
% 0.79/0.99     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.79/0.99         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.79/0.99       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.79/0.99  thf('18', plain,
% 0.79/0.99      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.79/0.99         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.79/0.99          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.79/0.99          | ((X32) = (X35))
% 0.79/0.99          | ~ (r2_relset_1 @ X33 @ X34 @ X32 @ X35))),
% 0.79/0.99      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.79/0.99  thf('19', plain,
% 0.79/0.99      (![X0 : $i]:
% 0.79/0.99         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.79/0.99             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 0.79/0.99          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 0.79/0.99          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.79/0.99      inference('sup-', [status(thm)], ['17', '18'])).
% 0.79/0.99  thf('20', plain,
% 0.79/0.99      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.79/0.99           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.79/0.99        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.79/0.99            = (k6_partfun1 @ sk_A)))),
% 0.79/0.99      inference('sup-', [status(thm)], ['8', '19'])).
% 0.79/0.99  thf(dt_k6_partfun1, axiom,
% 0.79/0.99    (![A:$i]:
% 0.79/0.99     ( ( m1_subset_1 @
% 0.79/0.99         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.79/0.99       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.79/0.99  thf('21', plain,
% 0.79/0.99      (![X43 : $i]:
% 0.79/0.99         (m1_subset_1 @ (k6_partfun1 @ X43) @ 
% 0.79/0.99          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X43)))),
% 0.79/0.99      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.79/0.99  thf('22', plain,
% 0.79/0.99      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.79/0.99         = (k6_partfun1 @ sk_A))),
% 0.79/0.99      inference('demod', [status(thm)], ['20', '21'])).
% 0.79/0.99  thf('23', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 0.79/0.99      inference('demod', [status(thm)], ['6', '7', '22'])).
% 0.79/0.99  thf(dt_k2_funct_1, axiom,
% 0.79/0.99    (![A:$i]:
% 0.79/0.99     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.79/0.99       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.79/0.99         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.79/0.99  thf('24', plain,
% 0.79/0.99      (![X21 : $i]:
% 0.79/0.99         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 0.79/0.99          | ~ (v1_funct_1 @ X21)
% 0.79/0.99          | ~ (v1_relat_1 @ X21))),
% 0.79/0.99      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.79/0.99  thf(t61_funct_1, axiom,
% 0.79/0.99    (![A:$i]:
% 0.79/0.99     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.79/0.99       ( ( v2_funct_1 @ A ) =>
% 0.79/0.99         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.79/0.99             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.79/0.99           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.79/0.99             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.79/0.99  thf('25', plain,
% 0.79/0.99      (![X25 : $i]:
% 0.79/0.99         (~ (v2_funct_1 @ X25)
% 0.79/0.99          | ((k5_relat_1 @ (k2_funct_1 @ X25) @ X25)
% 0.79/0.99              = (k6_relat_1 @ (k2_relat_1 @ X25)))
% 0.79/0.99          | ~ (v1_funct_1 @ X25)
% 0.79/0.99          | ~ (v1_relat_1 @ X25))),
% 0.79/0.99      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.79/0.99  thf(redefinition_k6_partfun1, axiom,
% 0.79/0.99    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.79/0.99  thf('26', plain, (![X50 : $i]: ((k6_partfun1 @ X50) = (k6_relat_1 @ X50))),
% 0.79/0.99      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.79/0.99  thf('27', plain,
% 0.79/0.99      (![X25 : $i]:
% 0.79/0.99         (~ (v2_funct_1 @ X25)
% 0.79/0.99          | ((k5_relat_1 @ (k2_funct_1 @ X25) @ X25)
% 0.79/0.99              = (k6_partfun1 @ (k2_relat_1 @ X25)))
% 0.79/0.99          | ~ (v1_funct_1 @ X25)
% 0.79/0.99          | ~ (v1_relat_1 @ X25))),
% 0.79/0.99      inference('demod', [status(thm)], ['25', '26'])).
% 0.79/0.99  thf('28', plain,
% 0.79/0.99      (![X21 : $i]:
% 0.79/0.99         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 0.79/0.99          | ~ (v1_funct_1 @ X21)
% 0.79/0.99          | ~ (v1_relat_1 @ X21))),
% 0.79/0.99      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.79/0.99  thf('29', plain,
% 0.79/0.99      (![X21 : $i]:
% 0.79/0.99         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 0.79/0.99          | ~ (v1_funct_1 @ X21)
% 0.79/0.99          | ~ (v1_relat_1 @ X21))),
% 0.79/0.99      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.79/0.99  thf(t55_funct_1, axiom,
% 0.79/0.99    (![A:$i]:
% 0.79/0.99     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.79/0.99       ( ( v2_funct_1 @ A ) =>
% 0.79/0.99         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.79/0.99           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.79/0.99  thf('30', plain,
% 0.79/0.99      (![X24 : $i]:
% 0.79/0.99         (~ (v2_funct_1 @ X24)
% 0.79/0.99          | ((k2_relat_1 @ X24) = (k1_relat_1 @ (k2_funct_1 @ X24)))
% 0.79/0.99          | ~ (v1_funct_1 @ X24)
% 0.79/0.99          | ~ (v1_relat_1 @ X24))),
% 0.79/0.99      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.79/0.99  thf('31', plain,
% 0.79/0.99      (![X21 : $i]:
% 0.79/0.99         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 0.79/0.99          | ~ (v1_funct_1 @ X21)
% 0.79/0.99          | ~ (v1_relat_1 @ X21))),
% 0.79/0.99      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.79/0.99  thf('32', plain,
% 0.79/0.99      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf(redefinition_k2_relset_1, axiom,
% 0.79/0.99    (![A:$i,B:$i,C:$i]:
% 0.79/0.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.79/0.99       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.79/0.99  thf('33', plain,
% 0.79/0.99      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.79/0.99         (((k2_relset_1 @ X30 @ X31 @ X29) = (k2_relat_1 @ X29))
% 0.79/0.99          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.79/0.99      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.79/0.99  thf('34', plain,
% 0.79/0.99      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.79/0.99      inference('sup-', [status(thm)], ['32', '33'])).
% 0.79/0.99  thf('35', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf('36', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.79/0.99      inference('sup+', [status(thm)], ['34', '35'])).
% 0.79/0.99  thf('37', plain,
% 0.79/0.99      (![X21 : $i]:
% 0.79/0.99         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 0.79/0.99          | ~ (v1_funct_1 @ X21)
% 0.79/0.99          | ~ (v1_relat_1 @ X21))),
% 0.79/0.99      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.79/0.99  thf('38', plain,
% 0.79/0.99      (![X24 : $i]:
% 0.79/0.99         (~ (v2_funct_1 @ X24)
% 0.79/0.99          | ((k2_relat_1 @ X24) = (k1_relat_1 @ (k2_funct_1 @ X24)))
% 0.79/0.99          | ~ (v1_funct_1 @ X24)
% 0.79/0.99          | ~ (v1_relat_1 @ X24))),
% 0.79/0.99      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.79/0.99  thf(d10_xboole_0, axiom,
% 0.79/0.99    (![A:$i,B:$i]:
% 0.79/0.99     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.79/0.99  thf('39', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.79/0.99      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.79/0.99  thf('40', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.79/0.99      inference('simplify', [status(thm)], ['39'])).
% 0.79/0.99  thf(d18_relat_1, axiom,
% 0.79/0.99    (![A:$i,B:$i]:
% 0.79/0.99     ( ( v1_relat_1 @ B ) =>
% 0.79/0.99       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.79/0.99  thf('41', plain,
% 0.79/0.99      (![X5 : $i, X6 : $i]:
% 0.79/0.99         (~ (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 0.79/0.99          | (v4_relat_1 @ X5 @ X6)
% 0.79/0.99          | ~ (v1_relat_1 @ X5))),
% 0.79/0.99      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.79/0.99  thf('42', plain,
% 0.79/0.99      (![X0 : $i]:
% 0.79/0.99         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.79/0.99      inference('sup-', [status(thm)], ['40', '41'])).
% 0.79/0.99  thf('43', plain,
% 0.79/0.99      (![X0 : $i]:
% 0.79/0.99         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.79/0.99          | ~ (v1_relat_1 @ X0)
% 0.79/0.99          | ~ (v1_funct_1 @ X0)
% 0.79/0.99          | ~ (v2_funct_1 @ X0)
% 0.79/0.99          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.79/0.99      inference('sup+', [status(thm)], ['38', '42'])).
% 0.79/0.99  thf('44', plain,
% 0.79/0.99      (![X0 : $i]:
% 0.79/0.99         (~ (v1_relat_1 @ X0)
% 0.79/0.99          | ~ (v1_funct_1 @ X0)
% 0.79/0.99          | ~ (v2_funct_1 @ X0)
% 0.79/0.99          | ~ (v1_funct_1 @ X0)
% 0.79/0.99          | ~ (v1_relat_1 @ X0)
% 0.79/0.99          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.79/0.99      inference('sup-', [status(thm)], ['37', '43'])).
% 0.79/0.99  thf('45', plain,
% 0.79/0.99      (![X0 : $i]:
% 0.79/0.99         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.79/0.99          | ~ (v2_funct_1 @ X0)
% 0.79/0.99          | ~ (v1_funct_1 @ X0)
% 0.79/0.99          | ~ (v1_relat_1 @ X0))),
% 0.79/0.99      inference('simplify', [status(thm)], ['44'])).
% 0.79/0.99  thf('46', plain,
% 0.79/0.99      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)
% 0.79/0.99        | ~ (v1_relat_1 @ sk_C)
% 0.79/0.99        | ~ (v1_funct_1 @ sk_C)
% 0.79/0.99        | ~ (v2_funct_1 @ sk_C))),
% 0.79/0.99      inference('sup+', [status(thm)], ['36', '45'])).
% 0.79/0.99  thf('47', plain,
% 0.79/0.99      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf(cc2_relat_1, axiom,
% 0.79/0.99    (![A:$i]:
% 0.79/0.99     ( ( v1_relat_1 @ A ) =>
% 0.79/0.99       ( ![B:$i]:
% 0.79/0.99         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.79/0.99  thf('48', plain,
% 0.79/0.99      (![X3 : $i, X4 : $i]:
% 0.79/0.99         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.79/0.99          | (v1_relat_1 @ X3)
% 0.79/0.99          | ~ (v1_relat_1 @ X4))),
% 0.79/0.99      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.79/0.99  thf('49', plain,
% 0.79/0.99      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.79/0.99      inference('sup-', [status(thm)], ['47', '48'])).
% 0.79/0.99  thf(fc6_relat_1, axiom,
% 0.79/0.99    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.79/0.99  thf('50', plain,
% 0.79/0.99      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.79/0.99      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.79/0.99  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 0.79/0.99      inference('demod', [status(thm)], ['49', '50'])).
% 0.79/0.99  thf('52', plain, ((v1_funct_1 @ sk_C)),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf('53', plain, ((v2_funct_1 @ sk_C)),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf('54', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)),
% 0.79/0.99      inference('demod', [status(thm)], ['46', '51', '52', '53'])).
% 0.79/0.99  thf('55', plain,
% 0.79/0.99      (![X5 : $i, X6 : $i]:
% 0.79/0.99         (~ (v4_relat_1 @ X5 @ X6)
% 0.79/0.99          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 0.79/0.99          | ~ (v1_relat_1 @ X5))),
% 0.79/0.99      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.79/0.99  thf('56', plain,
% 0.79/0.99      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.79/0.99        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 0.79/0.99      inference('sup-', [status(thm)], ['54', '55'])).
% 0.79/0.99  thf('57', plain,
% 0.79/0.99      ((~ (v1_relat_1 @ sk_C)
% 0.79/0.99        | ~ (v1_funct_1 @ sk_C)
% 0.79/0.99        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 0.79/0.99      inference('sup-', [status(thm)], ['31', '56'])).
% 0.79/0.99  thf('58', plain, ((v1_relat_1 @ sk_C)),
% 0.79/0.99      inference('demod', [status(thm)], ['49', '50'])).
% 0.79/0.99  thf('59', plain, ((v1_funct_1 @ sk_C)),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf('60', plain, ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B)),
% 0.79/0.99      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.79/0.99  thf('61', plain,
% 0.79/0.99      (![X0 : $i, X2 : $i]:
% 0.79/0.99         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.79/0.99      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.79/0.99  thf('62', plain,
% 0.79/0.99      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.79/0.99        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.79/0.99      inference('sup-', [status(thm)], ['60', '61'])).
% 0.79/0.99  thf('63', plain,
% 0.79/0.99      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C))
% 0.79/0.99        | ~ (v1_relat_1 @ sk_C)
% 0.79/0.99        | ~ (v1_funct_1 @ sk_C)
% 0.79/0.99        | ~ (v2_funct_1 @ sk_C)
% 0.79/0.99        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.79/0.99      inference('sup-', [status(thm)], ['30', '62'])).
% 0.79/0.99  thf('64', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.79/0.99      inference('sup+', [status(thm)], ['34', '35'])).
% 0.79/0.99  thf('65', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.79/0.99      inference('simplify', [status(thm)], ['39'])).
% 0.79/0.99  thf('66', plain, ((v1_relat_1 @ sk_C)),
% 0.79/0.99      inference('demod', [status(thm)], ['49', '50'])).
% 0.79/0.99  thf('67', plain, ((v1_funct_1 @ sk_C)),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf('68', plain, ((v2_funct_1 @ sk_C)),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf('69', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.79/0.99      inference('demod', [status(thm)], ['63', '64', '65', '66', '67', '68'])).
% 0.79/0.99  thf(t78_relat_1, axiom,
% 0.79/0.99    (![A:$i]:
% 0.79/0.99     ( ( v1_relat_1 @ A ) =>
% 0.79/0.99       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 0.79/0.99  thf('70', plain,
% 0.79/0.99      (![X19 : $i]:
% 0.79/0.99         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X19)) @ X19) = (X19))
% 0.79/0.99          | ~ (v1_relat_1 @ X19))),
% 0.79/0.99      inference('cnf', [status(esa)], [t78_relat_1])).
% 0.79/0.99  thf('71', plain, (![X50 : $i]: ((k6_partfun1 @ X50) = (k6_relat_1 @ X50))),
% 0.79/0.99      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.79/0.99  thf('72', plain,
% 0.79/0.99      (![X19 : $i]:
% 0.79/0.99         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X19)) @ X19) = (X19))
% 0.79/0.99          | ~ (v1_relat_1 @ X19))),
% 0.79/0.99      inference('demod', [status(thm)], ['70', '71'])).
% 0.79/0.99  thf('73', plain,
% 0.79/0.99      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 0.79/0.99          = (k2_funct_1 @ sk_C))
% 0.79/0.99        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.79/0.99      inference('sup+', [status(thm)], ['69', '72'])).
% 0.79/0.99  thf('74', plain,
% 0.79/0.99      ((~ (v1_relat_1 @ sk_C)
% 0.79/0.99        | ~ (v1_funct_1 @ sk_C)
% 0.79/0.99        | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 0.79/0.99            = (k2_funct_1 @ sk_C)))),
% 0.79/0.99      inference('sup-', [status(thm)], ['29', '73'])).
% 0.79/0.99  thf('75', plain, ((v1_relat_1 @ sk_C)),
% 0.79/0.99      inference('demod', [status(thm)], ['49', '50'])).
% 0.79/0.99  thf('76', plain, ((v1_funct_1 @ sk_C)),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf('77', plain,
% 0.79/0.99      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 0.79/0.99         = (k2_funct_1 @ sk_C))),
% 0.79/0.99      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.79/0.99  thf(t55_relat_1, axiom,
% 0.79/0.99    (![A:$i]:
% 0.79/0.99     ( ( v1_relat_1 @ A ) =>
% 0.79/0.99       ( ![B:$i]:
% 0.79/0.99         ( ( v1_relat_1 @ B ) =>
% 0.79/0.99           ( ![C:$i]:
% 0.79/0.99             ( ( v1_relat_1 @ C ) =>
% 0.79/0.99               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.79/0.99                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.79/0.99  thf('78', plain,
% 0.79/0.99      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.79/0.99         (~ (v1_relat_1 @ X14)
% 0.79/0.99          | ((k5_relat_1 @ (k5_relat_1 @ X15 @ X14) @ X16)
% 0.79/0.99              = (k5_relat_1 @ X15 @ (k5_relat_1 @ X14 @ X16)))
% 0.79/0.99          | ~ (v1_relat_1 @ X16)
% 0.79/0.99          | ~ (v1_relat_1 @ X15))),
% 0.79/0.99      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.79/0.99  thf('79', plain,
% 0.79/0.99      (![X0 : $i]:
% 0.79/0.99         (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 0.79/0.99            = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 0.79/0.99               (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)))
% 0.79/0.99          | ~ (v1_relat_1 @ (k6_partfun1 @ sk_B))
% 0.79/0.99          | ~ (v1_relat_1 @ X0)
% 0.79/0.99          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.79/0.99      inference('sup+', [status(thm)], ['77', '78'])).
% 0.79/0.99  thf('80', plain,
% 0.79/0.99      (![X43 : $i]:
% 0.79/0.99         (m1_subset_1 @ (k6_partfun1 @ X43) @ 
% 0.79/0.99          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X43)))),
% 0.79/0.99      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.79/0.99  thf('81', plain,
% 0.79/0.99      (![X3 : $i, X4 : $i]:
% 0.79/0.99         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.79/0.99          | (v1_relat_1 @ X3)
% 0.79/0.99          | ~ (v1_relat_1 @ X4))),
% 0.79/0.99      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.79/0.99  thf('82', plain,
% 0.79/0.99      (![X0 : $i]:
% 0.79/0.99         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X0))
% 0.79/0.99          | (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 0.79/0.99      inference('sup-', [status(thm)], ['80', '81'])).
% 0.79/0.99  thf('83', plain,
% 0.79/0.99      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.79/0.99      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.79/0.99  thf('84', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 0.79/0.99      inference('demod', [status(thm)], ['82', '83'])).
% 0.79/0.99  thf('85', plain,
% 0.79/0.99      (![X0 : $i]:
% 0.79/0.99         (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 0.79/0.99            = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 0.79/0.99               (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)))
% 0.79/0.99          | ~ (v1_relat_1 @ X0)
% 0.79/0.99          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.79/0.99      inference('demod', [status(thm)], ['79', '84'])).
% 0.79/0.99  thf('86', plain,
% 0.79/0.99      (![X0 : $i]:
% 0.79/0.99         (~ (v1_relat_1 @ sk_C)
% 0.79/0.99          | ~ (v1_funct_1 @ sk_C)
% 0.79/0.99          | ~ (v1_relat_1 @ X0)
% 0.79/0.99          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 0.79/0.99              = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 0.79/0.99                 (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))))),
% 0.79/0.99      inference('sup-', [status(thm)], ['28', '85'])).
% 0.79/0.99  thf('87', plain, ((v1_relat_1 @ sk_C)),
% 0.79/0.99      inference('demod', [status(thm)], ['49', '50'])).
% 0.79/0.99  thf('88', plain, ((v1_funct_1 @ sk_C)),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf('89', plain,
% 0.79/0.99      (![X0 : $i]:
% 0.79/0.99         (~ (v1_relat_1 @ X0)
% 0.79/0.99          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 0.79/0.99              = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 0.79/0.99                 (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))))),
% 0.79/0.99      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.79/0.99  thf('90', plain,
% 0.79/0.99      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.79/0.99          = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 0.79/0.99             (k6_partfun1 @ (k2_relat_1 @ sk_C))))
% 0.79/0.99        | ~ (v1_relat_1 @ sk_C)
% 0.79/0.99        | ~ (v1_funct_1 @ sk_C)
% 0.79/0.99        | ~ (v2_funct_1 @ sk_C)
% 0.79/0.99        | ~ (v1_relat_1 @ sk_C))),
% 0.79/0.99      inference('sup+', [status(thm)], ['27', '89'])).
% 0.79/0.99  thf('91', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.79/0.99      inference('sup+', [status(thm)], ['34', '35'])).
% 0.79/0.99  thf(t71_relat_1, axiom,
% 0.79/0.99    (![A:$i]:
% 0.79/0.99     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.79/0.99       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.79/0.99  thf('92', plain, (![X17 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X17)) = (X17))),
% 0.79/0.99      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.79/0.99  thf('93', plain, (![X50 : $i]: ((k6_partfun1 @ X50) = (k6_relat_1 @ X50))),
% 0.79/0.99      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.79/0.99  thf('94', plain, (![X17 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X17)) = (X17))),
% 0.79/0.99      inference('demod', [status(thm)], ['92', '93'])).
% 0.79/0.99  thf('95', plain,
% 0.79/0.99      (![X19 : $i]:
% 0.79/0.99         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X19)) @ X19) = (X19))
% 0.79/0.99          | ~ (v1_relat_1 @ X19))),
% 0.79/0.99      inference('demod', [status(thm)], ['70', '71'])).
% 0.79/0.99  thf('96', plain,
% 0.79/0.99      (![X0 : $i]:
% 0.79/0.99         (((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 0.79/0.99            = (k6_partfun1 @ X0))
% 0.79/0.99          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 0.79/0.99      inference('sup+', [status(thm)], ['94', '95'])).
% 0.79/0.99  thf('97', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 0.79/0.99      inference('demod', [status(thm)], ['82', '83'])).
% 0.79/0.99  thf('98', plain,
% 0.79/0.99      (![X0 : $i]:
% 0.79/0.99         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 0.79/0.99           = (k6_partfun1 @ X0))),
% 0.79/0.99      inference('demod', [status(thm)], ['96', '97'])).
% 0.79/0.99  thf('99', plain, ((v1_relat_1 @ sk_C)),
% 0.79/0.99      inference('demod', [status(thm)], ['49', '50'])).
% 0.79/0.99  thf('100', plain, ((v1_funct_1 @ sk_C)),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf('101', plain, ((v2_funct_1 @ sk_C)),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf('102', plain, ((v1_relat_1 @ sk_C)),
% 0.79/0.99      inference('demod', [status(thm)], ['49', '50'])).
% 0.79/0.99  thf('103', plain,
% 0.79/0.99      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 0.79/0.99      inference('demod', [status(thm)],
% 0.79/0.99                ['90', '91', '98', '99', '100', '101', '102'])).
% 0.79/0.99  thf('104', plain,
% 0.79/0.99      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.79/0.99         (~ (v1_relat_1 @ X14)
% 0.79/0.99          | ((k5_relat_1 @ (k5_relat_1 @ X15 @ X14) @ X16)
% 0.79/0.99              = (k5_relat_1 @ X15 @ (k5_relat_1 @ X14 @ X16)))
% 0.79/0.99          | ~ (v1_relat_1 @ X16)
% 0.79/0.99          | ~ (v1_relat_1 @ X15))),
% 0.79/0.99      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.79/0.99  thf('105', plain,
% 0.79/0.99      (![X0 : $i]:
% 0.79/0.99         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 0.79/0.99            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 0.79/0.99          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.79/0.99          | ~ (v1_relat_1 @ X0)
% 0.79/0.99          | ~ (v1_relat_1 @ sk_C))),
% 0.79/0.99      inference('sup+', [status(thm)], ['103', '104'])).
% 0.79/0.99  thf('106', plain, ((v1_relat_1 @ sk_C)),
% 0.79/0.99      inference('demod', [status(thm)], ['49', '50'])).
% 0.79/0.99  thf('107', plain,
% 0.79/0.99      (![X0 : $i]:
% 0.79/0.99         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 0.79/0.99            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 0.79/0.99          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.79/0.99          | ~ (v1_relat_1 @ X0))),
% 0.79/0.99      inference('demod', [status(thm)], ['105', '106'])).
% 0.79/0.99  thf('108', plain,
% 0.79/0.99      (![X0 : $i]:
% 0.79/0.99         (~ (v1_relat_1 @ sk_C)
% 0.79/0.99          | ~ (v1_funct_1 @ sk_C)
% 0.79/0.99          | ~ (v1_relat_1 @ X0)
% 0.79/0.99          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 0.79/0.99              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 0.79/0.99      inference('sup-', [status(thm)], ['24', '107'])).
% 0.79/0.99  thf('109', plain, ((v1_relat_1 @ sk_C)),
% 0.79/0.99      inference('demod', [status(thm)], ['49', '50'])).
% 0.79/0.99  thf('110', plain, ((v1_funct_1 @ sk_C)),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf('111', plain,
% 0.79/0.99      (![X0 : $i]:
% 0.79/0.99         (~ (v1_relat_1 @ X0)
% 0.79/0.99          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 0.79/0.99              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 0.79/0.99      inference('demod', [status(thm)], ['108', '109', '110'])).
% 0.79/0.99  thf('112', plain,
% 0.79/0.99      (![X0 : $i]:
% 0.79/0.99         (~ (v1_relat_1 @ X0)
% 0.79/0.99          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 0.79/0.99              = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 0.79/0.99                 (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))))),
% 0.79/0.99      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.79/0.99  thf('113', plain,
% 0.79/0.99      (![X0 : $i]:
% 0.79/0.99         (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))
% 0.79/0.99            = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 0.79/0.99               (k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)))
% 0.79/0.99          | ~ (v1_relat_1 @ X0)
% 0.79/0.99          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_C @ X0)))),
% 0.79/0.99      inference('sup+', [status(thm)], ['111', '112'])).
% 0.79/0.99  thf('114', plain,
% 0.79/0.99      ((~ (v1_relat_1 @ (k6_partfun1 @ sk_A))
% 0.79/0.99        | ~ (v1_relat_1 @ sk_D)
% 0.79/0.99        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ sk_D))
% 0.79/0.99            = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 0.79/0.99               (k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D))))),
% 0.79/0.99      inference('sup-', [status(thm)], ['23', '113'])).
% 0.79/0.99  thf('115', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 0.79/0.99      inference('demod', [status(thm)], ['82', '83'])).
% 0.79/0.99  thf('116', plain,
% 0.79/0.99      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf('117', plain,
% 0.79/0.99      (![X3 : $i, X4 : $i]:
% 0.79/0.99         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.79/0.99          | (v1_relat_1 @ X3)
% 0.79/0.99          | ~ (v1_relat_1 @ X4))),
% 0.79/0.99      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.79/0.99  thf('118', plain,
% 0.79/0.99      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.79/0.99      inference('sup-', [status(thm)], ['116', '117'])).
% 0.79/0.99  thf('119', plain,
% 0.79/0.99      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.79/0.99      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.79/0.99  thf('120', plain, ((v1_relat_1 @ sk_D)),
% 0.79/0.99      inference('demod', [status(thm)], ['118', '119'])).
% 0.79/0.99  thf('121', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 0.79/0.99      inference('demod', [status(thm)], ['6', '7', '22'])).
% 0.79/0.99  thf('122', plain,
% 0.79/0.99      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf(cc2_relset_1, axiom,
% 0.79/0.99    (![A:$i,B:$i,C:$i]:
% 0.79/0.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.79/0.99       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.79/0.99  thf('123', plain,
% 0.79/0.99      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.79/0.99         ((v4_relat_1 @ X26 @ X27)
% 0.79/0.99          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.79/0.99      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.79/0.99  thf('124', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 0.79/0.99      inference('sup-', [status(thm)], ['122', '123'])).
% 0.79/0.99  thf('125', plain,
% 0.79/0.99      (![X5 : $i, X6 : $i]:
% 0.79/0.99         (~ (v4_relat_1 @ X5 @ X6)
% 0.79/0.99          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 0.79/0.99          | ~ (v1_relat_1 @ X5))),
% 0.79/0.99      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.79/0.99  thf('126', plain,
% 0.79/0.99      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B))),
% 0.79/0.99      inference('sup-', [status(thm)], ['124', '125'])).
% 0.79/0.99  thf('127', plain, ((v1_relat_1 @ sk_D)),
% 0.79/0.99      inference('demod', [status(thm)], ['118', '119'])).
% 0.79/0.99  thf('128', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B)),
% 0.79/0.99      inference('demod', [status(thm)], ['126', '127'])).
% 0.79/0.99  thf('129', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.79/0.99      inference('sup+', [status(thm)], ['34', '35'])).
% 0.79/0.99  thf(t147_funct_1, axiom,
% 0.79/0.99    (![A:$i,B:$i]:
% 0.79/0.99     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.79/0.99       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.79/0.99         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.79/0.99  thf('130', plain,
% 0.79/0.99      (![X22 : $i, X23 : $i]:
% 0.79/0.99         (~ (r1_tarski @ X22 @ (k2_relat_1 @ X23))
% 0.79/0.99          | ((k9_relat_1 @ X23 @ (k10_relat_1 @ X23 @ X22)) = (X22))
% 0.79/0.99          | ~ (v1_funct_1 @ X23)
% 0.79/0.99          | ~ (v1_relat_1 @ X23))),
% 0.79/0.99      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.79/0.99  thf('131', plain,
% 0.79/0.99      (![X0 : $i]:
% 0.79/0.99         (~ (r1_tarski @ X0 @ sk_B)
% 0.79/0.99          | ~ (v1_relat_1 @ sk_C)
% 0.79/0.99          | ~ (v1_funct_1 @ sk_C)
% 0.79/0.99          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.79/0.99      inference('sup-', [status(thm)], ['129', '130'])).
% 0.79/0.99  thf('132', plain, ((v1_relat_1 @ sk_C)),
% 0.79/0.99      inference('demod', [status(thm)], ['49', '50'])).
% 0.79/0.99  thf('133', plain, ((v1_funct_1 @ sk_C)),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf('134', plain,
% 0.79/0.99      (![X0 : $i]:
% 0.79/0.99         (~ (r1_tarski @ X0 @ sk_B)
% 0.79/0.99          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.79/0.99      inference('demod', [status(thm)], ['131', '132', '133'])).
% 0.79/0.99  thf('135', plain,
% 0.79/0.99      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))
% 0.79/0.99         = (k1_relat_1 @ sk_D))),
% 0.79/0.99      inference('sup-', [status(thm)], ['128', '134'])).
% 0.79/0.99  thf('136', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 0.79/0.99      inference('demod', [status(thm)], ['6', '7', '22'])).
% 0.79/0.99  thf(t182_relat_1, axiom,
% 0.79/0.99    (![A:$i]:
% 0.79/0.99     ( ( v1_relat_1 @ A ) =>
% 0.79/0.99       ( ![B:$i]:
% 0.79/0.99         ( ( v1_relat_1 @ B ) =>
% 0.79/0.99           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.79/0.99             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.79/0.99  thf('137', plain,
% 0.79/0.99      (![X12 : $i, X13 : $i]:
% 0.79/0.99         (~ (v1_relat_1 @ X12)
% 0.79/0.99          | ((k1_relat_1 @ (k5_relat_1 @ X13 @ X12))
% 0.79/0.99              = (k10_relat_1 @ X13 @ (k1_relat_1 @ X12)))
% 0.79/0.99          | ~ (v1_relat_1 @ X13))),
% 0.79/0.99      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.79/0.99  thf('138', plain,
% 0.79/0.99      ((((k1_relat_1 @ (k6_partfun1 @ sk_A))
% 0.79/0.99          = (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))
% 0.79/0.99        | ~ (v1_relat_1 @ sk_C)
% 0.79/0.99        | ~ (v1_relat_1 @ sk_D))),
% 0.79/0.99      inference('sup+', [status(thm)], ['136', '137'])).
% 0.79/0.99  thf('139', plain,
% 0.79/0.99      (![X17 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X17)) = (X17))),
% 0.79/0.99      inference('demod', [status(thm)], ['92', '93'])).
% 0.79/0.99  thf('140', plain, ((v1_relat_1 @ sk_C)),
% 0.79/0.99      inference('demod', [status(thm)], ['49', '50'])).
% 0.79/0.99  thf('141', plain, ((v1_relat_1 @ sk_D)),
% 0.79/0.99      inference('demod', [status(thm)], ['118', '119'])).
% 0.79/0.99  thf('142', plain, (((sk_A) = (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))),
% 0.79/0.99      inference('demod', [status(thm)], ['138', '139', '140', '141'])).
% 0.79/0.99  thf('143', plain, (((k9_relat_1 @ sk_C @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.79/0.99      inference('demod', [status(thm)], ['135', '142'])).
% 0.79/0.99  thf('144', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.79/0.99      inference('simplify', [status(thm)], ['39'])).
% 0.79/0.99  thf('145', plain,
% 0.79/0.99      (![X0 : $i]:
% 0.79/0.99         (~ (r1_tarski @ X0 @ sk_B)
% 0.79/0.99          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.79/0.99      inference('demod', [status(thm)], ['131', '132', '133'])).
% 0.79/0.99  thf('146', plain,
% 0.79/0.99      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_B)) = (sk_B))),
% 0.79/0.99      inference('sup-', [status(thm)], ['144', '145'])).
% 0.79/0.99  thf('147', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.79/0.99      inference('sup+', [status(thm)], ['34', '35'])).
% 0.79/0.99  thf(t169_relat_1, axiom,
% 0.79/0.99    (![A:$i]:
% 0.79/0.99     ( ( v1_relat_1 @ A ) =>
% 0.79/0.99       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.79/0.99  thf('148', plain,
% 0.79/0.99      (![X11 : $i]:
% 0.79/0.99         (((k10_relat_1 @ X11 @ (k2_relat_1 @ X11)) = (k1_relat_1 @ X11))
% 0.79/0.99          | ~ (v1_relat_1 @ X11))),
% 0.79/0.99      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.79/0.99  thf('149', plain,
% 0.79/0.99      ((((k10_relat_1 @ sk_C @ sk_B) = (k1_relat_1 @ sk_C))
% 0.79/0.99        | ~ (v1_relat_1 @ sk_C))),
% 0.79/0.99      inference('sup+', [status(thm)], ['147', '148'])).
% 0.79/0.99  thf('150', plain, ((v1_relat_1 @ sk_C)),
% 0.79/0.99      inference('demod', [status(thm)], ['49', '50'])).
% 0.79/0.99  thf('151', plain, (((k10_relat_1 @ sk_C @ sk_B) = (k1_relat_1 @ sk_C))),
% 0.79/0.99      inference('demod', [status(thm)], ['149', '150'])).
% 0.79/0.99  thf('152', plain, (((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) = (sk_B))),
% 0.79/0.99      inference('demod', [status(thm)], ['146', '151'])).
% 0.79/0.99  thf('153', plain, (((sk_A) = (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))),
% 0.79/0.99      inference('demod', [status(thm)], ['138', '139', '140', '141'])).
% 0.79/0.99  thf(t167_relat_1, axiom,
% 0.79/0.99    (![A:$i,B:$i]:
% 0.79/0.99     ( ( v1_relat_1 @ B ) =>
% 0.79/0.99       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.79/0.99  thf('154', plain,
% 0.79/0.99      (![X9 : $i, X10 : $i]:
% 0.79/0.99         ((r1_tarski @ (k10_relat_1 @ X9 @ X10) @ (k1_relat_1 @ X9))
% 0.79/0.99          | ~ (v1_relat_1 @ X9))),
% 0.79/0.99      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.79/0.99  thf('155', plain,
% 0.79/0.99      (![X0 : $i, X2 : $i]:
% 0.79/0.99         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.79/0.99      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.79/0.99  thf('156', plain,
% 0.79/0.99      (![X0 : $i, X1 : $i]:
% 0.79/0.99         (~ (v1_relat_1 @ X0)
% 0.79/0.99          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 0.79/0.99          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1)))),
% 0.79/0.99      inference('sup-', [status(thm)], ['154', '155'])).
% 0.79/0.99  thf('157', plain,
% 0.79/0.99      ((~ (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)
% 0.79/0.99        | ((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))
% 0.79/0.99        | ~ (v1_relat_1 @ sk_C))),
% 0.79/0.99      inference('sup-', [status(thm)], ['153', '156'])).
% 0.79/0.99  thf('158', plain,
% 0.79/0.99      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf('159', plain,
% 0.79/0.99      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.79/0.99         ((v4_relat_1 @ X26 @ X27)
% 0.79/0.99          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.79/0.99      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.79/0.99  thf('160', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.79/0.99      inference('sup-', [status(thm)], ['158', '159'])).
% 0.79/0.99  thf('161', plain,
% 0.79/0.99      (![X5 : $i, X6 : $i]:
% 0.79/0.99         (~ (v4_relat_1 @ X5 @ X6)
% 0.79/0.99          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 0.79/0.99          | ~ (v1_relat_1 @ X5))),
% 0.79/0.99      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.79/0.99  thf('162', plain,
% 0.79/0.99      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 0.79/0.99      inference('sup-', [status(thm)], ['160', '161'])).
% 0.79/0.99  thf('163', plain, ((v1_relat_1 @ sk_C)),
% 0.79/0.99      inference('demod', [status(thm)], ['49', '50'])).
% 0.79/0.99  thf('164', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.79/0.99      inference('demod', [status(thm)], ['162', '163'])).
% 0.79/0.99  thf('165', plain, (((sk_A) = (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))),
% 0.79/0.99      inference('demod', [status(thm)], ['138', '139', '140', '141'])).
% 0.79/0.99  thf('166', plain, ((v1_relat_1 @ sk_C)),
% 0.79/0.99      inference('demod', [status(thm)], ['49', '50'])).
% 0.79/0.99  thf('167', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.79/0.99      inference('demod', [status(thm)], ['157', '164', '165', '166'])).
% 0.79/0.99  thf('168', plain, (((k9_relat_1 @ sk_C @ sk_A) = (sk_B))),
% 0.79/0.99      inference('demod', [status(thm)], ['152', '167'])).
% 0.79/0.99  thf('169', plain, (((k1_relat_1 @ sk_D) = (sk_B))),
% 0.79/0.99      inference('sup+', [status(thm)], ['143', '168'])).
% 0.79/0.99  thf('170', plain,
% 0.79/0.99      (![X19 : $i]:
% 0.79/0.99         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X19)) @ X19) = (X19))
% 0.79/0.99          | ~ (v1_relat_1 @ X19))),
% 0.79/0.99      inference('demod', [status(thm)], ['70', '71'])).
% 0.79/0.99  thf('171', plain,
% 0.79/0.99      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))
% 0.79/0.99        | ~ (v1_relat_1 @ sk_D))),
% 0.79/0.99      inference('sup+', [status(thm)], ['169', '170'])).
% 0.79/0.99  thf('172', plain, ((v1_relat_1 @ sk_D)),
% 0.79/0.99      inference('demod', [status(thm)], ['118', '119'])).
% 0.79/0.99  thf('173', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))),
% 0.79/0.99      inference('demod', [status(thm)], ['171', '172'])).
% 0.79/0.99  thf('174', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))),
% 0.79/0.99      inference('demod', [status(thm)], ['171', '172'])).
% 0.79/0.99  thf('175', plain,
% 0.79/0.99      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)) = (sk_D))),
% 0.79/0.99      inference('demod', [status(thm)],
% 0.79/0.99                ['114', '115', '120', '121', '173', '174'])).
% 0.79/0.99  thf('176', plain,
% 0.79/0.99      (![X21 : $i]:
% 0.79/0.99         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 0.79/0.99          | ~ (v1_funct_1 @ X21)
% 0.79/0.99          | ~ (v1_relat_1 @ X21))),
% 0.79/0.99      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.79/0.99  thf('177', plain,
% 0.79/0.99      (![X25 : $i]:
% 0.79/0.99         (~ (v2_funct_1 @ X25)
% 0.79/0.99          | ((k5_relat_1 @ X25 @ (k2_funct_1 @ X25))
% 0.79/0.99              = (k6_relat_1 @ (k1_relat_1 @ X25)))
% 0.79/0.99          | ~ (v1_funct_1 @ X25)
% 0.79/0.99          | ~ (v1_relat_1 @ X25))),
% 0.79/0.99      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.79/0.99  thf('178', plain, (![X50 : $i]: ((k6_partfun1 @ X50) = (k6_relat_1 @ X50))),
% 0.79/0.99      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.79/0.99  thf('179', plain,
% 0.79/0.99      (![X25 : $i]:
% 0.79/0.99         (~ (v2_funct_1 @ X25)
% 0.79/0.99          | ((k5_relat_1 @ X25 @ (k2_funct_1 @ X25))
% 0.79/0.99              = (k6_partfun1 @ (k1_relat_1 @ X25)))
% 0.79/0.99          | ~ (v1_funct_1 @ X25)
% 0.79/0.99          | ~ (v1_relat_1 @ X25))),
% 0.79/0.99      inference('demod', [status(thm)], ['177', '178'])).
% 0.79/0.99  thf('180', plain,
% 0.79/0.99      (![X0 : $i]:
% 0.79/0.99         (~ (v1_relat_1 @ X0)
% 0.79/0.99          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 0.79/0.99              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 0.79/0.99      inference('demod', [status(thm)], ['108', '109', '110'])).
% 0.79/0.99  thf('181', plain,
% 0.79/0.99      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 0.79/0.99          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 0.79/0.99             (k6_partfun1 @ (k1_relat_1 @ sk_C))))
% 0.79/0.99        | ~ (v1_relat_1 @ sk_C)
% 0.79/0.99        | ~ (v1_funct_1 @ sk_C)
% 0.79/0.99        | ~ (v2_funct_1 @ sk_C)
% 0.79/0.99        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.79/0.99      inference('sup+', [status(thm)], ['179', '180'])).
% 0.79/0.99  thf('182', plain,
% 0.79/0.99      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 0.79/0.99         = (k2_funct_1 @ sk_C))),
% 0.79/0.99      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.79/0.99  thf('183', plain, ((v1_relat_1 @ sk_C)),
% 0.79/0.99      inference('demod', [status(thm)], ['49', '50'])).
% 0.79/0.99  thf('184', plain, ((v1_funct_1 @ sk_C)),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf('185', plain, ((v2_funct_1 @ sk_C)),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf('186', plain,
% 0.79/0.99      ((((k2_funct_1 @ sk_C)
% 0.79/0.99          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 0.79/0.99             (k6_partfun1 @ (k1_relat_1 @ sk_C))))
% 0.79/0.99        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.79/0.99      inference('demod', [status(thm)], ['181', '182', '183', '184', '185'])).
% 0.79/0.99  thf('187', plain,
% 0.79/0.99      ((~ (v1_relat_1 @ sk_C)
% 0.79/0.99        | ~ (v1_funct_1 @ sk_C)
% 0.79/0.99        | ((k2_funct_1 @ sk_C)
% 0.79/0.99            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 0.79/0.99               (k6_partfun1 @ (k1_relat_1 @ sk_C)))))),
% 0.79/0.99      inference('sup-', [status(thm)], ['176', '186'])).
% 0.79/0.99  thf('188', plain, ((v1_relat_1 @ sk_C)),
% 0.79/0.99      inference('demod', [status(thm)], ['49', '50'])).
% 0.79/0.99  thf('189', plain, ((v1_funct_1 @ sk_C)),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf('190', plain,
% 0.79/0.99      (((k2_funct_1 @ sk_C)
% 0.79/0.99         = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 0.79/0.99            (k6_partfun1 @ (k1_relat_1 @ sk_C))))),
% 0.79/0.99      inference('demod', [status(thm)], ['187', '188', '189'])).
% 0.79/0.99  thf('191', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.79/0.99      inference('demod', [status(thm)], ['157', '164', '165', '166'])).
% 0.79/0.99  thf('192', plain,
% 0.79/0.99      (((k2_funct_1 @ sk_C)
% 0.79/0.99         = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))),
% 0.79/0.99      inference('demod', [status(thm)], ['190', '191'])).
% 0.79/0.99  thf('193', plain, (((k2_funct_1 @ sk_C) = (sk_D))),
% 0.79/0.99      inference('sup+', [status(thm)], ['175', '192'])).
% 0.79/0.99  thf('194', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.79/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.79/0.99  thf('195', plain, ($false),
% 0.79/0.99      inference('simplify_reflect-', [status(thm)], ['193', '194'])).
% 0.79/0.99  
% 0.79/0.99  % SZS output end Refutation
% 0.79/0.99  
% 0.79/1.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

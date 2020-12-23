%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fbmhJAloXJ

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:22 EST 2020

% Result     : Theorem 1.52s
% Output     : Refutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 480 expanded)
%              Number of leaves         :   46 ( 164 expanded)
%              Depth                    :   17
%              Number of atoms          : 1432 (11034 expanded)
%              Number of equality atoms :   86 ( 739 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

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
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( ( k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39 )
        = ( k5_relat_1 @ X36 @ X39 ) ) ) ),
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
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X33 ) ) ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( X16 = X19 )
      | ~ ( r2_relset_1 @ X17 @ X18 @ X16 @ X19 ) ) ),
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
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('24',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('25',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( X7
        = ( k2_funct_1 @ X8 ) )
      | ( ( k5_relat_1 @ X7 @ X8 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X8 ) ) )
      | ( ( k2_relat_1 @ X7 )
       != ( k1_relat_1 @ X8 ) )
      | ~ ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
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
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( r2_relset_1 @ X44 @ X44 @ ( k1_partfun1 @ X44 @ X45 @ X45 @ X44 @ X43 @ X46 ) @ ( k6_partfun1 @ X44 ) )
      | ( ( k2_relset_1 @ X45 @ X44 @ X46 )
        = X44 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) )
      | ~ ( v1_funct_2 @ X46 @ X45 @ X44 )
      | ~ ( v1_funct_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('33',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('34',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( r2_relset_1 @ X44 @ X44 @ ( k1_partfun1 @ X44 @ X45 @ X45 @ X44 @ X43 @ X46 ) @ ( k6_relat_1 @ X44 ) )
      | ( ( k2_relset_1 @ X45 @ X44 @ X46 )
        = X44 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) )
      | ~ ( v1_funct_2 @ X46 @ X45 @ X44 )
      | ~ ( v1_funct_1 @ X46 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['30','38'])).

thf('40',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('41',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( r2_relset_1 @ X17 @ X18 @ X16 @ X19 )
      | ( X16 != X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('42',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_relset_1 @ X17 @ X18 @ X19 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('45',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('46',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['39','43','46','47','48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('53',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('54',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('55',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('59',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
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

thf('63',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ( X22
        = ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('64',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('65',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('66',plain,(
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

thf('67',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('68',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['69','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('73',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_relset_1 @ X11 @ X12 @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('74',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['64','71','74'])).

thf('76',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('82',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B != sk_B )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['29','50','55','56','61','75','76','81'])).

thf('83',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,
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

thf('85',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X4 )
       != ( k1_relat_1 @ X5 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('86',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( v2_funct_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('87',plain,(
    ! [X6: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('88',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['53','54'])).

thf('89',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['59','60'])).

thf('91',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['64','71','74'])).

thf('92',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['79','80'])).

thf('94',plain,
    ( ( sk_B != sk_B )
    | ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['86','87','88','89','90','91','92','93'])).

thf('95',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['83','95'])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('97',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X9 ) )
        = X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('98',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['53','54'])).

thf('100',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v2_funct_1 @ sk_D ),
    inference(simplify,[status(thm)],['94'])).

thf('102',plain,
    ( ( k2_funct_1 @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['98','99','100','101'])).

thf('103',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['102','103'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fbmhJAloXJ
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:53:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.52/1.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.52/1.72  % Solved by: fo/fo7.sh
% 1.52/1.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.52/1.72  % done 387 iterations in 1.268s
% 1.52/1.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.52/1.72  % SZS output start Refutation
% 1.52/1.72  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.52/1.72  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.52/1.72  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.52/1.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.52/1.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.52/1.72  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.52/1.72  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.52/1.72  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.52/1.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.52/1.72  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.52/1.72  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.52/1.72  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.52/1.72  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.52/1.72  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.52/1.72  thf(sk_A_type, type, sk_A: $i).
% 1.52/1.72  thf(sk_D_type, type, sk_D: $i).
% 1.52/1.72  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.52/1.72  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.52/1.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.52/1.72  thf(sk_C_type, type, sk_C: $i).
% 1.52/1.72  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.52/1.72  thf(sk_B_type, type, sk_B: $i).
% 1.52/1.72  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.52/1.72  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.52/1.72  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.52/1.72  thf(t36_funct_2, conjecture,
% 1.52/1.72    (![A:$i,B:$i,C:$i]:
% 1.52/1.72     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.52/1.72         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.52/1.72       ( ![D:$i]:
% 1.52/1.72         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.52/1.72             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.52/1.72           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.52/1.72               ( r2_relset_1 @
% 1.52/1.72                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.52/1.72                 ( k6_partfun1 @ A ) ) & 
% 1.52/1.72               ( v2_funct_1 @ C ) ) =>
% 1.52/1.72             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.52/1.72               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.52/1.72  thf(zf_stmt_0, negated_conjecture,
% 1.52/1.72    (~( ![A:$i,B:$i,C:$i]:
% 1.52/1.72        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.52/1.72            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.52/1.72          ( ![D:$i]:
% 1.52/1.72            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.52/1.72                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.52/1.72              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.52/1.72                  ( r2_relset_1 @
% 1.52/1.72                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.52/1.72                    ( k6_partfun1 @ A ) ) & 
% 1.52/1.72                  ( v2_funct_1 @ C ) ) =>
% 1.52/1.72                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.52/1.72                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.52/1.72    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.52/1.72  thf('0', plain,
% 1.52/1.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.72  thf('1', plain,
% 1.52/1.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.72  thf(redefinition_k1_partfun1, axiom,
% 1.52/1.72    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.52/1.72     ( ( ( v1_funct_1 @ E ) & 
% 1.52/1.72         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.52/1.72         ( v1_funct_1 @ F ) & 
% 1.52/1.72         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.52/1.72       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.52/1.72  thf('2', plain,
% 1.52/1.72      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 1.52/1.72         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 1.52/1.72          | ~ (v1_funct_1 @ X36)
% 1.52/1.72          | ~ (v1_funct_1 @ X39)
% 1.52/1.72          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 1.52/1.72          | ((k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39)
% 1.52/1.72              = (k5_relat_1 @ X36 @ X39)))),
% 1.52/1.72      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.52/1.72  thf('3', plain,
% 1.52/1.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.52/1.72         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.52/1.72            = (k5_relat_1 @ sk_C @ X0))
% 1.52/1.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.52/1.72          | ~ (v1_funct_1 @ X0)
% 1.52/1.72          | ~ (v1_funct_1 @ sk_C))),
% 1.52/1.72      inference('sup-', [status(thm)], ['1', '2'])).
% 1.52/1.72  thf('4', plain, ((v1_funct_1 @ sk_C)),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.72  thf('5', plain,
% 1.52/1.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.52/1.72         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.52/1.72            = (k5_relat_1 @ sk_C @ X0))
% 1.52/1.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.52/1.72          | ~ (v1_funct_1 @ X0))),
% 1.52/1.72      inference('demod', [status(thm)], ['3', '4'])).
% 1.52/1.72  thf('6', plain,
% 1.52/1.72      ((~ (v1_funct_1 @ sk_D)
% 1.52/1.72        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.52/1.72            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.52/1.72      inference('sup-', [status(thm)], ['0', '5'])).
% 1.52/1.72  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.72  thf('8', plain,
% 1.52/1.72      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.52/1.72        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.52/1.72        (k6_partfun1 @ sk_A))),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.72  thf(redefinition_k6_partfun1, axiom,
% 1.52/1.72    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.52/1.72  thf('9', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 1.52/1.72      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.52/1.72  thf('10', plain,
% 1.52/1.72      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.52/1.72        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.52/1.72        (k6_relat_1 @ sk_A))),
% 1.52/1.72      inference('demod', [status(thm)], ['8', '9'])).
% 1.52/1.72  thf('11', plain,
% 1.52/1.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.72  thf('12', plain,
% 1.52/1.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.72  thf(dt_k1_partfun1, axiom,
% 1.52/1.72    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.52/1.72     ( ( ( v1_funct_1 @ E ) & 
% 1.52/1.72         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.52/1.72         ( v1_funct_1 @ F ) & 
% 1.52/1.72         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.52/1.72       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.52/1.72         ( m1_subset_1 @
% 1.52/1.72           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.52/1.72           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.52/1.72  thf('13', plain,
% 1.52/1.72      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.52/1.72         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 1.52/1.72          | ~ (v1_funct_1 @ X28)
% 1.52/1.72          | ~ (v1_funct_1 @ X31)
% 1.52/1.72          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.52/1.72          | (m1_subset_1 @ (k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31) @ 
% 1.52/1.72             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X33))))),
% 1.52/1.72      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.52/1.72  thf('14', plain,
% 1.52/1.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.52/1.72         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.52/1.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.52/1.72          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.52/1.72          | ~ (v1_funct_1 @ X1)
% 1.52/1.72          | ~ (v1_funct_1 @ sk_C))),
% 1.52/1.72      inference('sup-', [status(thm)], ['12', '13'])).
% 1.52/1.72  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.72  thf('16', plain,
% 1.52/1.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.52/1.72         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.52/1.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.52/1.72          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.52/1.72          | ~ (v1_funct_1 @ X1))),
% 1.52/1.72      inference('demod', [status(thm)], ['14', '15'])).
% 1.52/1.72  thf('17', plain,
% 1.52/1.72      ((~ (v1_funct_1 @ sk_D)
% 1.52/1.72        | (m1_subset_1 @ 
% 1.52/1.72           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.52/1.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.52/1.72      inference('sup-', [status(thm)], ['11', '16'])).
% 1.52/1.72  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.72  thf('19', plain,
% 1.52/1.72      ((m1_subset_1 @ 
% 1.52/1.72        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.52/1.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.52/1.72      inference('demod', [status(thm)], ['17', '18'])).
% 1.52/1.72  thf(redefinition_r2_relset_1, axiom,
% 1.52/1.72    (![A:$i,B:$i,C:$i,D:$i]:
% 1.52/1.72     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.52/1.72         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.52/1.72       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.52/1.72  thf('20', plain,
% 1.52/1.72      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 1.52/1.72         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 1.52/1.72          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 1.52/1.72          | ((X16) = (X19))
% 1.52/1.72          | ~ (r2_relset_1 @ X17 @ X18 @ X16 @ X19))),
% 1.52/1.72      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.52/1.72  thf('21', plain,
% 1.52/1.72      (![X0 : $i]:
% 1.52/1.72         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.52/1.72             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 1.52/1.72          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 1.52/1.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.52/1.72      inference('sup-', [status(thm)], ['19', '20'])).
% 1.52/1.72  thf('22', plain,
% 1.52/1.72      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 1.52/1.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.52/1.72        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.52/1.72            = (k6_relat_1 @ sk_A)))),
% 1.52/1.72      inference('sup-', [status(thm)], ['10', '21'])).
% 1.52/1.72  thf(dt_k6_partfun1, axiom,
% 1.52/1.72    (![A:$i]:
% 1.52/1.72     ( ( m1_subset_1 @
% 1.52/1.72         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 1.52/1.72       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 1.52/1.72  thf('23', plain,
% 1.52/1.72      (![X35 : $i]:
% 1.52/1.72         (m1_subset_1 @ (k6_partfun1 @ X35) @ 
% 1.52/1.72          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 1.52/1.72      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.52/1.72  thf('24', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 1.52/1.72      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.52/1.72  thf('25', plain,
% 1.52/1.72      (![X35 : $i]:
% 1.52/1.72         (m1_subset_1 @ (k6_relat_1 @ X35) @ 
% 1.52/1.72          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 1.52/1.72      inference('demod', [status(thm)], ['23', '24'])).
% 1.52/1.72  thf('26', plain,
% 1.52/1.72      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.52/1.72         = (k6_relat_1 @ sk_A))),
% 1.52/1.72      inference('demod', [status(thm)], ['22', '25'])).
% 1.52/1.72  thf('27', plain, (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 1.52/1.72      inference('demod', [status(thm)], ['6', '7', '26'])).
% 1.52/1.72  thf(t64_funct_1, axiom,
% 1.52/1.72    (![A:$i]:
% 1.52/1.72     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.52/1.72       ( ![B:$i]:
% 1.52/1.72         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.52/1.72           ( ( ( v2_funct_1 @ A ) & 
% 1.52/1.72               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 1.52/1.72               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 1.52/1.72             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.52/1.72  thf('28', plain,
% 1.52/1.72      (![X7 : $i, X8 : $i]:
% 1.52/1.72         (~ (v1_relat_1 @ X7)
% 1.52/1.72          | ~ (v1_funct_1 @ X7)
% 1.52/1.72          | ((X7) = (k2_funct_1 @ X8))
% 1.52/1.72          | ((k5_relat_1 @ X7 @ X8) != (k6_relat_1 @ (k2_relat_1 @ X8)))
% 1.52/1.72          | ((k2_relat_1 @ X7) != (k1_relat_1 @ X8))
% 1.52/1.72          | ~ (v2_funct_1 @ X8)
% 1.52/1.72          | ~ (v1_funct_1 @ X8)
% 1.52/1.72          | ~ (v1_relat_1 @ X8))),
% 1.52/1.72      inference('cnf', [status(esa)], [t64_funct_1])).
% 1.52/1.72  thf('29', plain,
% 1.52/1.72      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ (k2_relat_1 @ sk_D)))
% 1.52/1.72        | ~ (v1_relat_1 @ sk_D)
% 1.52/1.72        | ~ (v1_funct_1 @ sk_D)
% 1.52/1.72        | ~ (v2_funct_1 @ sk_D)
% 1.52/1.72        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 1.52/1.72        | ((sk_C) = (k2_funct_1 @ sk_D))
% 1.52/1.72        | ~ (v1_funct_1 @ sk_C)
% 1.52/1.72        | ~ (v1_relat_1 @ sk_C))),
% 1.52/1.72      inference('sup-', [status(thm)], ['27', '28'])).
% 1.52/1.72  thf('30', plain,
% 1.52/1.72      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.52/1.72         = (k6_relat_1 @ sk_A))),
% 1.52/1.72      inference('demod', [status(thm)], ['22', '25'])).
% 1.52/1.72  thf('31', plain,
% 1.52/1.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.72  thf(t24_funct_2, axiom,
% 1.52/1.72    (![A:$i,B:$i,C:$i]:
% 1.52/1.72     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.52/1.72         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.52/1.72       ( ![D:$i]:
% 1.52/1.72         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.52/1.72             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.52/1.72           ( ( r2_relset_1 @
% 1.52/1.72               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 1.52/1.72               ( k6_partfun1 @ B ) ) =>
% 1.52/1.72             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 1.52/1.72  thf('32', plain,
% 1.52/1.72      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 1.52/1.72         (~ (v1_funct_1 @ X43)
% 1.52/1.72          | ~ (v1_funct_2 @ X43 @ X44 @ X45)
% 1.52/1.72          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 1.52/1.72          | ~ (r2_relset_1 @ X44 @ X44 @ 
% 1.52/1.72               (k1_partfun1 @ X44 @ X45 @ X45 @ X44 @ X43 @ X46) @ 
% 1.52/1.72               (k6_partfun1 @ X44))
% 1.52/1.72          | ((k2_relset_1 @ X45 @ X44 @ X46) = (X44))
% 1.52/1.72          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))
% 1.52/1.72          | ~ (v1_funct_2 @ X46 @ X45 @ X44)
% 1.52/1.72          | ~ (v1_funct_1 @ X46))),
% 1.52/1.72      inference('cnf', [status(esa)], [t24_funct_2])).
% 1.52/1.72  thf('33', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 1.52/1.72      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.52/1.72  thf('34', plain,
% 1.52/1.72      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 1.52/1.72         (~ (v1_funct_1 @ X43)
% 1.52/1.72          | ~ (v1_funct_2 @ X43 @ X44 @ X45)
% 1.52/1.72          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 1.52/1.72          | ~ (r2_relset_1 @ X44 @ X44 @ 
% 1.52/1.72               (k1_partfun1 @ X44 @ X45 @ X45 @ X44 @ X43 @ X46) @ 
% 1.52/1.72               (k6_relat_1 @ X44))
% 1.52/1.72          | ((k2_relset_1 @ X45 @ X44 @ X46) = (X44))
% 1.52/1.72          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))
% 1.52/1.72          | ~ (v1_funct_2 @ X46 @ X45 @ X44)
% 1.52/1.72          | ~ (v1_funct_1 @ X46))),
% 1.52/1.72      inference('demod', [status(thm)], ['32', '33'])).
% 1.52/1.72  thf('35', plain,
% 1.52/1.72      (![X0 : $i]:
% 1.52/1.72         (~ (v1_funct_1 @ X0)
% 1.52/1.72          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.52/1.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.52/1.72          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.52/1.72          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.52/1.72               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.52/1.72               (k6_relat_1 @ sk_A))
% 1.52/1.72          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.52/1.72          | ~ (v1_funct_1 @ sk_C))),
% 1.52/1.72      inference('sup-', [status(thm)], ['31', '34'])).
% 1.52/1.72  thf('36', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.72  thf('37', plain, ((v1_funct_1 @ sk_C)),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.72  thf('38', plain,
% 1.52/1.72      (![X0 : $i]:
% 1.52/1.72         (~ (v1_funct_1 @ X0)
% 1.52/1.72          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.52/1.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.52/1.72          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.52/1.72          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.52/1.72               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.52/1.72               (k6_relat_1 @ sk_A)))),
% 1.52/1.72      inference('demod', [status(thm)], ['35', '36', '37'])).
% 1.52/1.72  thf('39', plain,
% 1.52/1.72      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 1.52/1.72           (k6_relat_1 @ sk_A))
% 1.52/1.72        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 1.52/1.72        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.52/1.72        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.52/1.72        | ~ (v1_funct_1 @ sk_D))),
% 1.52/1.72      inference('sup-', [status(thm)], ['30', '38'])).
% 1.52/1.72  thf('40', plain,
% 1.52/1.72      (![X35 : $i]:
% 1.52/1.72         (m1_subset_1 @ (k6_relat_1 @ X35) @ 
% 1.52/1.72          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 1.52/1.72      inference('demod', [status(thm)], ['23', '24'])).
% 1.52/1.72  thf('41', plain,
% 1.52/1.72      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 1.52/1.72         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 1.52/1.72          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 1.52/1.72          | (r2_relset_1 @ X17 @ X18 @ X16 @ X19)
% 1.52/1.72          | ((X16) != (X19)))),
% 1.52/1.72      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.52/1.72  thf('42', plain,
% 1.52/1.72      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.52/1.72         ((r2_relset_1 @ X17 @ X18 @ X19 @ X19)
% 1.52/1.72          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.52/1.72      inference('simplify', [status(thm)], ['41'])).
% 1.52/1.72  thf('43', plain,
% 1.52/1.72      (![X0 : $i]:
% 1.52/1.72         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 1.52/1.72      inference('sup-', [status(thm)], ['40', '42'])).
% 1.52/1.72  thf('44', plain,
% 1.52/1.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.72  thf(redefinition_k2_relset_1, axiom,
% 1.52/1.72    (![A:$i,B:$i,C:$i]:
% 1.52/1.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.52/1.72       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.52/1.72  thf('45', plain,
% 1.52/1.72      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.52/1.72         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 1.52/1.72          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 1.52/1.72      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.52/1.72  thf('46', plain,
% 1.52/1.72      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.52/1.72      inference('sup-', [status(thm)], ['44', '45'])).
% 1.52/1.72  thf('47', plain,
% 1.52/1.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.72  thf('48', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.72  thf('49', plain, ((v1_funct_1 @ sk_D)),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.72  thf('50', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.52/1.72      inference('demod', [status(thm)], ['39', '43', '46', '47', '48', '49'])).
% 1.52/1.72  thf('51', plain,
% 1.52/1.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.72  thf(cc2_relat_1, axiom,
% 1.52/1.72    (![A:$i]:
% 1.52/1.72     ( ( v1_relat_1 @ A ) =>
% 1.52/1.72       ( ![B:$i]:
% 1.52/1.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.52/1.72  thf('52', plain,
% 1.52/1.72      (![X0 : $i, X1 : $i]:
% 1.52/1.72         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.52/1.72          | (v1_relat_1 @ X0)
% 1.52/1.72          | ~ (v1_relat_1 @ X1))),
% 1.52/1.72      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.52/1.72  thf('53', plain,
% 1.52/1.72      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 1.52/1.72      inference('sup-', [status(thm)], ['51', '52'])).
% 1.52/1.72  thf(fc6_relat_1, axiom,
% 1.52/1.72    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.52/1.72  thf('54', plain,
% 1.52/1.72      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.52/1.72      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.52/1.72  thf('55', plain, ((v1_relat_1 @ sk_D)),
% 1.52/1.72      inference('demod', [status(thm)], ['53', '54'])).
% 1.52/1.72  thf('56', plain, ((v1_funct_1 @ sk_D)),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.72  thf('57', plain,
% 1.52/1.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.72  thf('58', plain,
% 1.52/1.72      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.52/1.72         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 1.52/1.72          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 1.52/1.72      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.52/1.72  thf('59', plain,
% 1.52/1.72      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.52/1.72      inference('sup-', [status(thm)], ['57', '58'])).
% 1.52/1.72  thf('60', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.72  thf('61', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.52/1.72      inference('sup+', [status(thm)], ['59', '60'])).
% 1.52/1.72  thf('62', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.72  thf(d1_funct_2, axiom,
% 1.52/1.72    (![A:$i,B:$i,C:$i]:
% 1.52/1.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.52/1.72       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.52/1.72           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.52/1.72             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.52/1.72         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.52/1.72           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.52/1.72             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.52/1.72  thf(zf_stmt_1, axiom,
% 1.52/1.72    (![C:$i,B:$i,A:$i]:
% 1.52/1.72     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.52/1.72       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.52/1.72  thf('63', plain,
% 1.52/1.72      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.52/1.72         (~ (v1_funct_2 @ X24 @ X22 @ X23)
% 1.52/1.72          | ((X22) = (k1_relset_1 @ X22 @ X23 @ X24))
% 1.52/1.72          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.52/1.72  thf('64', plain,
% 1.52/1.72      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 1.52/1.72        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 1.52/1.72      inference('sup-', [status(thm)], ['62', '63'])).
% 1.52/1.72  thf(zf_stmt_2, axiom,
% 1.52/1.72    (![B:$i,A:$i]:
% 1.52/1.72     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.52/1.72       ( zip_tseitin_0 @ B @ A ) ))).
% 1.52/1.72  thf('65', plain,
% 1.52/1.72      (![X20 : $i, X21 : $i]:
% 1.52/1.72         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.52/1.72  thf('66', plain,
% 1.52/1.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.72  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.52/1.72  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.52/1.72  thf(zf_stmt_5, axiom,
% 1.52/1.72    (![A:$i,B:$i,C:$i]:
% 1.52/1.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.52/1.72       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.52/1.72         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.52/1.72           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.52/1.72             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.52/1.72  thf('67', plain,
% 1.52/1.72      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.52/1.72         (~ (zip_tseitin_0 @ X25 @ X26)
% 1.52/1.72          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 1.52/1.72          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.52/1.72  thf('68', plain,
% 1.52/1.72      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 1.52/1.72      inference('sup-', [status(thm)], ['66', '67'])).
% 1.52/1.72  thf('69', plain,
% 1.52/1.72      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 1.52/1.72      inference('sup-', [status(thm)], ['65', '68'])).
% 1.52/1.72  thf('70', plain, (((sk_A) != (k1_xboole_0))),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.72  thf('71', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 1.52/1.72      inference('simplify_reflect-', [status(thm)], ['69', '70'])).
% 1.52/1.72  thf('72', plain,
% 1.52/1.72      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.72  thf(redefinition_k1_relset_1, axiom,
% 1.52/1.72    (![A:$i,B:$i,C:$i]:
% 1.52/1.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.52/1.72       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.52/1.72  thf('73', plain,
% 1.52/1.72      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.52/1.72         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 1.52/1.72          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 1.52/1.72      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.52/1.72  thf('74', plain,
% 1.52/1.72      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.52/1.72      inference('sup-', [status(thm)], ['72', '73'])).
% 1.52/1.72  thf('75', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.52/1.72      inference('demod', [status(thm)], ['64', '71', '74'])).
% 1.52/1.72  thf('76', plain, ((v1_funct_1 @ sk_C)),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.72  thf('77', plain,
% 1.52/1.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.72  thf('78', plain,
% 1.52/1.72      (![X0 : $i, X1 : $i]:
% 1.52/1.72         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.52/1.72          | (v1_relat_1 @ X0)
% 1.52/1.72          | ~ (v1_relat_1 @ X1))),
% 1.52/1.72      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.52/1.72  thf('79', plain,
% 1.52/1.72      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 1.52/1.72      inference('sup-', [status(thm)], ['77', '78'])).
% 1.52/1.72  thf('80', plain,
% 1.52/1.72      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.52/1.72      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.52/1.72  thf('81', plain, ((v1_relat_1 @ sk_C)),
% 1.52/1.72      inference('demod', [status(thm)], ['79', '80'])).
% 1.52/1.72  thf('82', plain,
% 1.52/1.72      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ sk_A))
% 1.52/1.72        | ~ (v2_funct_1 @ sk_D)
% 1.52/1.72        | ((sk_B) != (sk_B))
% 1.52/1.72        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 1.52/1.72      inference('demod', [status(thm)],
% 1.52/1.72                ['29', '50', '55', '56', '61', '75', '76', '81'])).
% 1.52/1.72  thf('83', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 1.52/1.72      inference('simplify', [status(thm)], ['82'])).
% 1.52/1.72  thf('84', plain, (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 1.52/1.72      inference('demod', [status(thm)], ['6', '7', '26'])).
% 1.52/1.72  thf(t48_funct_1, axiom,
% 1.52/1.72    (![A:$i]:
% 1.52/1.72     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.52/1.72       ( ![B:$i]:
% 1.52/1.72         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.52/1.72           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 1.52/1.72               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 1.52/1.72             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 1.52/1.72  thf('85', plain,
% 1.52/1.72      (![X4 : $i, X5 : $i]:
% 1.52/1.72         (~ (v1_relat_1 @ X4)
% 1.52/1.72          | ~ (v1_funct_1 @ X4)
% 1.52/1.72          | (v2_funct_1 @ X5)
% 1.52/1.72          | ((k2_relat_1 @ X4) != (k1_relat_1 @ X5))
% 1.52/1.72          | ~ (v2_funct_1 @ (k5_relat_1 @ X4 @ X5))
% 1.52/1.72          | ~ (v1_funct_1 @ X5)
% 1.52/1.72          | ~ (v1_relat_1 @ X5))),
% 1.52/1.72      inference('cnf', [status(esa)], [t48_funct_1])).
% 1.52/1.72  thf('86', plain,
% 1.52/1.72      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 1.52/1.72        | ~ (v1_relat_1 @ sk_D)
% 1.52/1.72        | ~ (v1_funct_1 @ sk_D)
% 1.52/1.72        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 1.52/1.72        | (v2_funct_1 @ sk_D)
% 1.52/1.72        | ~ (v1_funct_1 @ sk_C)
% 1.52/1.72        | ~ (v1_relat_1 @ sk_C))),
% 1.52/1.72      inference('sup-', [status(thm)], ['84', '85'])).
% 1.52/1.72  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 1.52/1.72  thf('87', plain, (![X6 : $i]: (v2_funct_1 @ (k6_relat_1 @ X6))),
% 1.52/1.72      inference('cnf', [status(esa)], [t52_funct_1])).
% 1.52/1.72  thf('88', plain, ((v1_relat_1 @ sk_D)),
% 1.52/1.72      inference('demod', [status(thm)], ['53', '54'])).
% 1.52/1.72  thf('89', plain, ((v1_funct_1 @ sk_D)),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.72  thf('90', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.52/1.72      inference('sup+', [status(thm)], ['59', '60'])).
% 1.52/1.72  thf('91', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.52/1.72      inference('demod', [status(thm)], ['64', '71', '74'])).
% 1.52/1.72  thf('92', plain, ((v1_funct_1 @ sk_C)),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.72  thf('93', plain, ((v1_relat_1 @ sk_C)),
% 1.52/1.72      inference('demod', [status(thm)], ['79', '80'])).
% 1.52/1.72  thf('94', plain, ((((sk_B) != (sk_B)) | (v2_funct_1 @ sk_D))),
% 1.52/1.72      inference('demod', [status(thm)],
% 1.52/1.72                ['86', '87', '88', '89', '90', '91', '92', '93'])).
% 1.52/1.72  thf('95', plain, ((v2_funct_1 @ sk_D)),
% 1.52/1.72      inference('simplify', [status(thm)], ['94'])).
% 1.52/1.72  thf('96', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 1.52/1.72      inference('demod', [status(thm)], ['83', '95'])).
% 1.52/1.72  thf(t65_funct_1, axiom,
% 1.52/1.72    (![A:$i]:
% 1.52/1.72     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.52/1.72       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 1.52/1.72  thf('97', plain,
% 1.52/1.72      (![X9 : $i]:
% 1.52/1.72         (~ (v2_funct_1 @ X9)
% 1.52/1.72          | ((k2_funct_1 @ (k2_funct_1 @ X9)) = (X9))
% 1.52/1.72          | ~ (v1_funct_1 @ X9)
% 1.52/1.72          | ~ (v1_relat_1 @ X9))),
% 1.52/1.72      inference('cnf', [status(esa)], [t65_funct_1])).
% 1.52/1.72  thf('98', plain,
% 1.52/1.72      ((((k2_funct_1 @ sk_C) = (sk_D))
% 1.52/1.72        | ~ (v1_relat_1 @ sk_D)
% 1.52/1.72        | ~ (v1_funct_1 @ sk_D)
% 1.52/1.72        | ~ (v2_funct_1 @ sk_D))),
% 1.52/1.72      inference('sup+', [status(thm)], ['96', '97'])).
% 1.52/1.72  thf('99', plain, ((v1_relat_1 @ sk_D)),
% 1.52/1.72      inference('demod', [status(thm)], ['53', '54'])).
% 1.52/1.72  thf('100', plain, ((v1_funct_1 @ sk_D)),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.72  thf('101', plain, ((v2_funct_1 @ sk_D)),
% 1.52/1.72      inference('simplify', [status(thm)], ['94'])).
% 1.52/1.72  thf('102', plain, (((k2_funct_1 @ sk_C) = (sk_D))),
% 1.52/1.72      inference('demod', [status(thm)], ['98', '99', '100', '101'])).
% 1.52/1.72  thf('103', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.52/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.52/1.72  thf('104', plain, ($false),
% 1.52/1.72      inference('simplify_reflect-', [status(thm)], ['102', '103'])).
% 1.52/1.72  
% 1.52/1.72  % SZS output end Refutation
% 1.52/1.72  
% 1.52/1.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

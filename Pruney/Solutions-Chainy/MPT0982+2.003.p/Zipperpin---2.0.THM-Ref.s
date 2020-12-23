%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NNwfbXqdE1

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:55 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 380 expanded)
%              Number of leaves         :   50 ( 131 expanded)
%              Depth                    :   16
%              Number of atoms          : 1358 (8087 expanded)
%              Number of equality atoms :   74 ( 464 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(t28_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
                = C )
              & ( v2_funct_1 @ E ) )
           => ( ( C = k1_xboole_0 )
              | ( ( k2_relset_1 @ A @ B @ D )
                = B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ( ( ( v1_funct_1 @ E )
              & ( v1_funct_2 @ E @ B @ C )
              & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
           => ( ( ( ( k2_relset_1 @ A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
                  = C )
                & ( v2_funct_1 @ E ) )
             => ( ( C = k1_xboole_0 )
                | ( ( k2_relset_1 @ A @ B @ D )
                  = B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v5_relat_1 @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v5_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('7',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['4','7'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_D ) )
    | ( sk_B
      = ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) )
        = ( k9_relat_1 @ X5 @ ( k2_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('12',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('22',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ( ( k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46 )
        = ( k5_relat_1 @ X43 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['18','19','28'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('30',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X28 @ X26 )
        = ( k2_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('31',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
    = sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('34',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['31','34'])).

thf('36',plain,
    ( ( ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['11','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['5','6'])).

thf('38',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('40',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) )
    = sk_C ),
    inference(demod,[status(thm)],['36','37','40'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('42',plain,(
    ! [X11: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('43',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t154_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k9_relat_1 @ B @ A )
          = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('44',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k9_relat_1 @ X14 @ X15 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X14 ) @ X15 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('45',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X12 @ ( k10_relat_1 @ X12 @ X13 ) ) @ X13 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k2_funct_1 @ X1 ) @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k9_relat_1 @ X0 @ X1 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k9_relat_1 @ X0 @ X1 ) ) @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k9_relat_1 @ X0 @ X1 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['42','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k9_relat_1 @ X0 @ X1 ) ) @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v2_funct_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['41','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['38','39'])).

thf('53',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    r1_tarski @ ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ sk_C ) @ ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['51','52','53','54'])).

thf('56',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['31','34'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('57',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) ) @ ( k2_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('58',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C )
    | ( ( k2_relat_1 @ sk_E )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v5_relat_1 @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('63',plain,(
    v5_relat_1 @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v5_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('65',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['38','39'])).

thf('67',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['31','34'])).

thf('69',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['38','39'])).

thf('70',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['5','6'])).

thf('71',plain,
    ( ( k2_relat_1 @ sk_E )
    = sk_C ),
    inference(demod,[status(thm)],['60','67','68','69','70'])).

thf('72',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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

thf('73',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k5_relat_1 @ X16 @ ( k2_funct_1 @ X16 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('74',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) )
        = ( k9_relat_1 @ X5 @ ( k2_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('76',plain,(
    ! [X10: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,
    ( ( ( k1_relat_1 @ sk_E )
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v2_funct_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['71','80'])).

thf('82',plain,(
    v1_funct_2 @ sk_E @ sk_B @ sk_C ),
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

thf('83',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('84',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('85',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('86',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
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

thf('87',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('88',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf('90',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    zip_tseitin_1 @ sk_E @ sk_C @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['89','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('93',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('94',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['84','91','94'])).

thf('96',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['38','39'])).

thf('97',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( sk_B
    = ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ sk_C ) ),
    inference(demod,[status(thm)],['81','95','96','97','98'])).

thf('100',plain,(
    r1_tarski @ sk_B @ ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['55','99'])).

thf('101',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['10','100'])).

thf('102',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X28 @ X26 )
        = ( k2_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('105',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ( k2_relat_1 @ sk_D )
 != sk_B ),
    inference(demod,[status(thm)],['102','105'])).

thf('107',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['101','106'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NNwfbXqdE1
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:52:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.51/1.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.51/1.71  % Solved by: fo/fo7.sh
% 1.51/1.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.51/1.71  % done 745 iterations in 1.264s
% 1.51/1.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.51/1.71  % SZS output start Refutation
% 1.51/1.71  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.51/1.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.51/1.71  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.51/1.71  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.51/1.71  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.51/1.71  thf(sk_A_type, type, sk_A: $i).
% 1.51/1.71  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.51/1.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.51/1.71  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.51/1.71  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.51/1.71  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.51/1.71  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.51/1.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.51/1.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.51/1.71  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.51/1.71  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.51/1.71  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.51/1.71  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.51/1.71  thf(sk_D_type, type, sk_D: $i).
% 1.51/1.71  thf(sk_E_type, type, sk_E: $i).
% 1.51/1.71  thf(sk_C_type, type, sk_C: $i).
% 1.51/1.71  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.51/1.71  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.51/1.71  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.51/1.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.51/1.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.51/1.71  thf(sk_B_type, type, sk_B: $i).
% 1.51/1.71  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.51/1.71  thf(t28_funct_2, conjecture,
% 1.51/1.71    (![A:$i,B:$i,C:$i,D:$i]:
% 1.51/1.71     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.51/1.71         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.51/1.71       ( ![E:$i]:
% 1.51/1.71         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.51/1.71             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.51/1.71           ( ( ( ( k2_relset_1 @
% 1.51/1.71                   A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 1.51/1.71                 ( C ) ) & 
% 1.51/1.71               ( v2_funct_1 @ E ) ) =>
% 1.51/1.71             ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 1.51/1.71               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ))).
% 1.51/1.71  thf(zf_stmt_0, negated_conjecture,
% 1.51/1.71    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.51/1.71        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.51/1.71            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.51/1.71          ( ![E:$i]:
% 1.51/1.71            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.51/1.71                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.51/1.71              ( ( ( ( k2_relset_1 @
% 1.51/1.71                      A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 1.51/1.71                    ( C ) ) & 
% 1.51/1.71                  ( v2_funct_1 @ E ) ) =>
% 1.51/1.71                ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 1.51/1.71                  ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ) )),
% 1.51/1.71    inference('cnf.neg', [status(esa)], [t28_funct_2])).
% 1.51/1.71  thf('0', plain,
% 1.51/1.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf(cc2_relset_1, axiom,
% 1.51/1.71    (![A:$i,B:$i,C:$i]:
% 1.51/1.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.51/1.71       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.51/1.71  thf('1', plain,
% 1.51/1.71      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.51/1.71         ((v5_relat_1 @ X20 @ X22)
% 1.51/1.71          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.51/1.71      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.51/1.71  thf('2', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 1.51/1.71      inference('sup-', [status(thm)], ['0', '1'])).
% 1.51/1.71  thf(d19_relat_1, axiom,
% 1.51/1.71    (![A:$i,B:$i]:
% 1.51/1.71     ( ( v1_relat_1 @ B ) =>
% 1.51/1.71       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.51/1.71  thf('3', plain,
% 1.51/1.71      (![X3 : $i, X4 : $i]:
% 1.51/1.71         (~ (v5_relat_1 @ X3 @ X4)
% 1.51/1.71          | (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 1.51/1.71          | ~ (v1_relat_1 @ X3))),
% 1.51/1.71      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.51/1.71  thf('4', plain,
% 1.51/1.71      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 1.51/1.71      inference('sup-', [status(thm)], ['2', '3'])).
% 1.51/1.71  thf('5', plain,
% 1.51/1.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf(cc1_relset_1, axiom,
% 1.51/1.71    (![A:$i,B:$i,C:$i]:
% 1.51/1.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.51/1.71       ( v1_relat_1 @ C ) ))).
% 1.51/1.71  thf('6', plain,
% 1.51/1.71      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.51/1.71         ((v1_relat_1 @ X17)
% 1.51/1.71          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.51/1.71      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.51/1.71  thf('7', plain, ((v1_relat_1 @ sk_D)),
% 1.51/1.71      inference('sup-', [status(thm)], ['5', '6'])).
% 1.51/1.71  thf('8', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 1.51/1.71      inference('demod', [status(thm)], ['4', '7'])).
% 1.51/1.71  thf(d10_xboole_0, axiom,
% 1.51/1.71    (![A:$i,B:$i]:
% 1.51/1.71     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.51/1.71  thf('9', plain,
% 1.51/1.71      (![X0 : $i, X2 : $i]:
% 1.51/1.71         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.51/1.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.51/1.71  thf('10', plain,
% 1.51/1.71      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_D))
% 1.51/1.71        | ((sk_B) = (k2_relat_1 @ sk_D)))),
% 1.51/1.71      inference('sup-', [status(thm)], ['8', '9'])).
% 1.51/1.71  thf(t160_relat_1, axiom,
% 1.51/1.71    (![A:$i]:
% 1.51/1.71     ( ( v1_relat_1 @ A ) =>
% 1.51/1.71       ( ![B:$i]:
% 1.51/1.71         ( ( v1_relat_1 @ B ) =>
% 1.51/1.71           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 1.51/1.71             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.51/1.71  thf('11', plain,
% 1.51/1.71      (![X5 : $i, X6 : $i]:
% 1.51/1.71         (~ (v1_relat_1 @ X5)
% 1.51/1.71          | ((k2_relat_1 @ (k5_relat_1 @ X6 @ X5))
% 1.51/1.71              = (k9_relat_1 @ X5 @ (k2_relat_1 @ X6)))
% 1.51/1.71          | ~ (v1_relat_1 @ X6))),
% 1.51/1.71      inference('cnf', [status(esa)], [t160_relat_1])).
% 1.51/1.71  thf('12', plain,
% 1.51/1.71      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('13', plain,
% 1.51/1.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf(dt_k1_partfun1, axiom,
% 1.51/1.71    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.51/1.71     ( ( ( v1_funct_1 @ E ) & 
% 1.51/1.71         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.51/1.71         ( v1_funct_1 @ F ) & 
% 1.51/1.71         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.51/1.71       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.51/1.71         ( m1_subset_1 @
% 1.51/1.71           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.51/1.71           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.51/1.71  thf('14', plain,
% 1.51/1.71      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 1.51/1.71         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 1.51/1.71          | ~ (v1_funct_1 @ X37)
% 1.51/1.71          | ~ (v1_funct_1 @ X40)
% 1.51/1.71          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 1.51/1.71          | (m1_subset_1 @ (k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40) @ 
% 1.51/1.71             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X42))))),
% 1.51/1.71      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.51/1.71  thf('15', plain,
% 1.51/1.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.71         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 1.51/1.71           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.51/1.71          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.51/1.71          | ~ (v1_funct_1 @ X1)
% 1.51/1.71          | ~ (v1_funct_1 @ sk_D))),
% 1.51/1.71      inference('sup-', [status(thm)], ['13', '14'])).
% 1.51/1.71  thf('16', plain, ((v1_funct_1 @ sk_D)),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('17', plain,
% 1.51/1.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.71         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 1.51/1.71           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.51/1.71          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.51/1.71          | ~ (v1_funct_1 @ X1))),
% 1.51/1.71      inference('demod', [status(thm)], ['15', '16'])).
% 1.51/1.71  thf('18', plain,
% 1.51/1.71      ((~ (v1_funct_1 @ sk_E)
% 1.51/1.71        | (m1_subset_1 @ 
% 1.51/1.71           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 1.51/1.71           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 1.51/1.71      inference('sup-', [status(thm)], ['12', '17'])).
% 1.51/1.71  thf('19', plain, ((v1_funct_1 @ sk_E)),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('20', plain,
% 1.51/1.71      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('21', plain,
% 1.51/1.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf(redefinition_k1_partfun1, axiom,
% 1.51/1.71    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.51/1.71     ( ( ( v1_funct_1 @ E ) & 
% 1.51/1.71         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.51/1.71         ( v1_funct_1 @ F ) & 
% 1.51/1.71         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.51/1.71       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.51/1.71  thf('22', plain,
% 1.51/1.71      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 1.51/1.71         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 1.51/1.71          | ~ (v1_funct_1 @ X43)
% 1.51/1.71          | ~ (v1_funct_1 @ X46)
% 1.51/1.71          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 1.51/1.71          | ((k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46)
% 1.51/1.71              = (k5_relat_1 @ X43 @ X46)))),
% 1.51/1.71      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.51/1.71  thf('23', plain,
% 1.51/1.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.71         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 1.51/1.71            = (k5_relat_1 @ sk_D @ X0))
% 1.51/1.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.51/1.71          | ~ (v1_funct_1 @ X0)
% 1.51/1.71          | ~ (v1_funct_1 @ sk_D))),
% 1.51/1.71      inference('sup-', [status(thm)], ['21', '22'])).
% 1.51/1.71  thf('24', plain, ((v1_funct_1 @ sk_D)),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('25', plain,
% 1.51/1.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.71         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 1.51/1.71            = (k5_relat_1 @ sk_D @ X0))
% 1.51/1.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.51/1.71          | ~ (v1_funct_1 @ X0))),
% 1.51/1.71      inference('demod', [status(thm)], ['23', '24'])).
% 1.51/1.71  thf('26', plain,
% 1.51/1.71      ((~ (v1_funct_1 @ sk_E)
% 1.51/1.71        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 1.51/1.71            = (k5_relat_1 @ sk_D @ sk_E)))),
% 1.51/1.71      inference('sup-', [status(thm)], ['20', '25'])).
% 1.51/1.71  thf('27', plain, ((v1_funct_1 @ sk_E)),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('28', plain,
% 1.51/1.71      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 1.51/1.71         = (k5_relat_1 @ sk_D @ sk_E))),
% 1.51/1.71      inference('demod', [status(thm)], ['26', '27'])).
% 1.51/1.71  thf('29', plain,
% 1.51/1.71      ((m1_subset_1 @ (k5_relat_1 @ sk_D @ sk_E) @ 
% 1.51/1.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.51/1.71      inference('demod', [status(thm)], ['18', '19', '28'])).
% 1.51/1.71  thf(redefinition_k2_relset_1, axiom,
% 1.51/1.71    (![A:$i,B:$i,C:$i]:
% 1.51/1.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.51/1.71       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.51/1.71  thf('30', plain,
% 1.51/1.71      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.51/1.71         (((k2_relset_1 @ X27 @ X28 @ X26) = (k2_relat_1 @ X26))
% 1.51/1.71          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 1.51/1.71      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.51/1.71  thf('31', plain,
% 1.51/1.71      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E))
% 1.51/1.71         = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 1.51/1.71      inference('sup-', [status(thm)], ['29', '30'])).
% 1.51/1.71  thf('32', plain,
% 1.51/1.71      (((k2_relset_1 @ sk_A @ sk_C @ 
% 1.51/1.71         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)) = (sk_C))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('33', plain,
% 1.51/1.71      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 1.51/1.71         = (k5_relat_1 @ sk_D @ sk_E))),
% 1.51/1.71      inference('demod', [status(thm)], ['26', '27'])).
% 1.51/1.71  thf('34', plain,
% 1.51/1.71      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 1.51/1.71      inference('demod', [status(thm)], ['32', '33'])).
% 1.51/1.71  thf('35', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 1.51/1.71      inference('sup+', [status(thm)], ['31', '34'])).
% 1.51/1.71  thf('36', plain,
% 1.51/1.71      ((((k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)) = (sk_C))
% 1.51/1.71        | ~ (v1_relat_1 @ sk_D)
% 1.51/1.71        | ~ (v1_relat_1 @ sk_E))),
% 1.51/1.71      inference('sup+', [status(thm)], ['11', '35'])).
% 1.51/1.71  thf('37', plain, ((v1_relat_1 @ sk_D)),
% 1.51/1.71      inference('sup-', [status(thm)], ['5', '6'])).
% 1.51/1.71  thf('38', plain,
% 1.51/1.71      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('39', plain,
% 1.51/1.71      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.51/1.71         ((v1_relat_1 @ X17)
% 1.51/1.71          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.51/1.71      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.51/1.71  thf('40', plain, ((v1_relat_1 @ sk_E)),
% 1.51/1.71      inference('sup-', [status(thm)], ['38', '39'])).
% 1.51/1.71  thf('41', plain, (((k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)) = (sk_C))),
% 1.51/1.71      inference('demod', [status(thm)], ['36', '37', '40'])).
% 1.51/1.71  thf(dt_k2_funct_1, axiom,
% 1.51/1.71    (![A:$i]:
% 1.51/1.71     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.51/1.71       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.51/1.71         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.51/1.71  thf('42', plain,
% 1.51/1.71      (![X11 : $i]:
% 1.51/1.71         ((v1_funct_1 @ (k2_funct_1 @ X11))
% 1.51/1.71          | ~ (v1_funct_1 @ X11)
% 1.51/1.71          | ~ (v1_relat_1 @ X11))),
% 1.51/1.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.51/1.71  thf('43', plain,
% 1.51/1.71      (![X11 : $i]:
% 1.51/1.71         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 1.51/1.71          | ~ (v1_funct_1 @ X11)
% 1.51/1.71          | ~ (v1_relat_1 @ X11))),
% 1.51/1.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.51/1.71  thf(t154_funct_1, axiom,
% 1.51/1.71    (![A:$i,B:$i]:
% 1.51/1.71     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.51/1.71       ( ( v2_funct_1 @ B ) =>
% 1.51/1.71         ( ( k9_relat_1 @ B @ A ) = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 1.51/1.71  thf('44', plain,
% 1.51/1.71      (![X14 : $i, X15 : $i]:
% 1.51/1.71         (~ (v2_funct_1 @ X14)
% 1.51/1.71          | ((k9_relat_1 @ X14 @ X15)
% 1.51/1.71              = (k10_relat_1 @ (k2_funct_1 @ X14) @ X15))
% 1.51/1.71          | ~ (v1_funct_1 @ X14)
% 1.51/1.71          | ~ (v1_relat_1 @ X14))),
% 1.51/1.71      inference('cnf', [status(esa)], [t154_funct_1])).
% 1.51/1.71  thf(t145_funct_1, axiom,
% 1.51/1.71    (![A:$i,B:$i]:
% 1.51/1.71     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.51/1.71       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 1.51/1.71  thf('45', plain,
% 1.51/1.71      (![X12 : $i, X13 : $i]:
% 1.51/1.71         ((r1_tarski @ (k9_relat_1 @ X12 @ (k10_relat_1 @ X12 @ X13)) @ X13)
% 1.51/1.71          | ~ (v1_funct_1 @ X12)
% 1.51/1.71          | ~ (v1_relat_1 @ X12))),
% 1.51/1.71      inference('cnf', [status(esa)], [t145_funct_1])).
% 1.51/1.71  thf('46', plain,
% 1.51/1.71      (![X0 : $i, X1 : $i]:
% 1.51/1.71         ((r1_tarski @ 
% 1.51/1.71           (k9_relat_1 @ (k2_funct_1 @ X1) @ (k9_relat_1 @ X1 @ X0)) @ X0)
% 1.51/1.71          | ~ (v1_relat_1 @ X1)
% 1.51/1.71          | ~ (v1_funct_1 @ X1)
% 1.51/1.71          | ~ (v2_funct_1 @ X1)
% 1.51/1.71          | ~ (v1_relat_1 @ (k2_funct_1 @ X1))
% 1.51/1.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X1)))),
% 1.51/1.71      inference('sup+', [status(thm)], ['44', '45'])).
% 1.51/1.71  thf('47', plain,
% 1.51/1.71      (![X0 : $i, X1 : $i]:
% 1.51/1.71         (~ (v1_relat_1 @ X0)
% 1.51/1.71          | ~ (v1_funct_1 @ X0)
% 1.51/1.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.51/1.71          | ~ (v2_funct_1 @ X0)
% 1.51/1.71          | ~ (v1_funct_1 @ X0)
% 1.51/1.71          | ~ (v1_relat_1 @ X0)
% 1.51/1.71          | (r1_tarski @ 
% 1.51/1.71             (k9_relat_1 @ (k2_funct_1 @ X0) @ (k9_relat_1 @ X0 @ X1)) @ X1))),
% 1.51/1.71      inference('sup-', [status(thm)], ['43', '46'])).
% 1.51/1.71  thf('48', plain,
% 1.51/1.71      (![X0 : $i, X1 : $i]:
% 1.51/1.71         ((r1_tarski @ 
% 1.51/1.71           (k9_relat_1 @ (k2_funct_1 @ X0) @ (k9_relat_1 @ X0 @ X1)) @ X1)
% 1.51/1.71          | ~ (v2_funct_1 @ X0)
% 1.51/1.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.51/1.71          | ~ (v1_funct_1 @ X0)
% 1.51/1.71          | ~ (v1_relat_1 @ X0))),
% 1.51/1.71      inference('simplify', [status(thm)], ['47'])).
% 1.51/1.71  thf('49', plain,
% 1.51/1.71      (![X0 : $i, X1 : $i]:
% 1.51/1.71         (~ (v1_relat_1 @ X0)
% 1.51/1.71          | ~ (v1_funct_1 @ X0)
% 1.51/1.71          | ~ (v1_relat_1 @ X0)
% 1.51/1.71          | ~ (v1_funct_1 @ X0)
% 1.51/1.71          | ~ (v2_funct_1 @ X0)
% 1.51/1.71          | (r1_tarski @ 
% 1.51/1.71             (k9_relat_1 @ (k2_funct_1 @ X0) @ (k9_relat_1 @ X0 @ X1)) @ X1))),
% 1.51/1.71      inference('sup-', [status(thm)], ['42', '48'])).
% 1.51/1.71  thf('50', plain,
% 1.51/1.71      (![X0 : $i, X1 : $i]:
% 1.51/1.71         ((r1_tarski @ 
% 1.51/1.71           (k9_relat_1 @ (k2_funct_1 @ X0) @ (k9_relat_1 @ X0 @ X1)) @ X1)
% 1.51/1.71          | ~ (v2_funct_1 @ X0)
% 1.51/1.71          | ~ (v1_funct_1 @ X0)
% 1.51/1.71          | ~ (v1_relat_1 @ X0))),
% 1.51/1.71      inference('simplify', [status(thm)], ['49'])).
% 1.51/1.71  thf('51', plain,
% 1.51/1.71      (((r1_tarski @ (k9_relat_1 @ (k2_funct_1 @ sk_E) @ sk_C) @ 
% 1.51/1.71         (k2_relat_1 @ sk_D))
% 1.51/1.71        | ~ (v1_relat_1 @ sk_E)
% 1.51/1.71        | ~ (v1_funct_1 @ sk_E)
% 1.51/1.71        | ~ (v2_funct_1 @ sk_E))),
% 1.51/1.71      inference('sup+', [status(thm)], ['41', '50'])).
% 1.51/1.71  thf('52', plain, ((v1_relat_1 @ sk_E)),
% 1.51/1.71      inference('sup-', [status(thm)], ['38', '39'])).
% 1.51/1.71  thf('53', plain, ((v1_funct_1 @ sk_E)),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('54', plain, ((v2_funct_1 @ sk_E)),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('55', plain,
% 1.51/1.71      ((r1_tarski @ (k9_relat_1 @ (k2_funct_1 @ sk_E) @ sk_C) @ 
% 1.51/1.71        (k2_relat_1 @ sk_D))),
% 1.51/1.71      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 1.51/1.71  thf('56', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 1.51/1.71      inference('sup+', [status(thm)], ['31', '34'])).
% 1.51/1.71  thf(t45_relat_1, axiom,
% 1.51/1.71    (![A:$i]:
% 1.51/1.71     ( ( v1_relat_1 @ A ) =>
% 1.51/1.71       ( ![B:$i]:
% 1.51/1.71         ( ( v1_relat_1 @ B ) =>
% 1.51/1.71           ( r1_tarski @
% 1.51/1.71             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 1.51/1.71  thf('57', plain,
% 1.51/1.71      (![X7 : $i, X8 : $i]:
% 1.51/1.71         (~ (v1_relat_1 @ X7)
% 1.51/1.71          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X8 @ X7)) @ 
% 1.51/1.71             (k2_relat_1 @ X7))
% 1.51/1.71          | ~ (v1_relat_1 @ X8))),
% 1.51/1.71      inference('cnf', [status(esa)], [t45_relat_1])).
% 1.51/1.71  thf('58', plain,
% 1.51/1.71      (![X0 : $i, X2 : $i]:
% 1.51/1.71         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.51/1.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.51/1.71  thf('59', plain,
% 1.51/1.71      (![X0 : $i, X1 : $i]:
% 1.51/1.71         (~ (v1_relat_1 @ X1)
% 1.51/1.71          | ~ (v1_relat_1 @ X0)
% 1.51/1.71          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 1.51/1.71               (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 1.51/1.71          | ((k2_relat_1 @ X0) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 1.51/1.71      inference('sup-', [status(thm)], ['57', '58'])).
% 1.51/1.71  thf('60', plain,
% 1.51/1.71      ((~ (r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C)
% 1.51/1.71        | ((k2_relat_1 @ sk_E) = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))
% 1.51/1.71        | ~ (v1_relat_1 @ sk_E)
% 1.51/1.71        | ~ (v1_relat_1 @ sk_D))),
% 1.51/1.71      inference('sup-', [status(thm)], ['56', '59'])).
% 1.51/1.71  thf('61', plain,
% 1.51/1.71      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('62', plain,
% 1.51/1.71      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.51/1.71         ((v5_relat_1 @ X20 @ X22)
% 1.51/1.71          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.51/1.71      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.51/1.71  thf('63', plain, ((v5_relat_1 @ sk_E @ sk_C)),
% 1.51/1.71      inference('sup-', [status(thm)], ['61', '62'])).
% 1.51/1.71  thf('64', plain,
% 1.51/1.71      (![X3 : $i, X4 : $i]:
% 1.51/1.71         (~ (v5_relat_1 @ X3 @ X4)
% 1.51/1.71          | (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 1.51/1.71          | ~ (v1_relat_1 @ X3))),
% 1.51/1.71      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.51/1.71  thf('65', plain,
% 1.51/1.71      ((~ (v1_relat_1 @ sk_E) | (r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C))),
% 1.51/1.71      inference('sup-', [status(thm)], ['63', '64'])).
% 1.51/1.71  thf('66', plain, ((v1_relat_1 @ sk_E)),
% 1.51/1.71      inference('sup-', [status(thm)], ['38', '39'])).
% 1.51/1.71  thf('67', plain, ((r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C)),
% 1.51/1.71      inference('demod', [status(thm)], ['65', '66'])).
% 1.51/1.71  thf('68', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 1.51/1.71      inference('sup+', [status(thm)], ['31', '34'])).
% 1.51/1.71  thf('69', plain, ((v1_relat_1 @ sk_E)),
% 1.51/1.71      inference('sup-', [status(thm)], ['38', '39'])).
% 1.51/1.71  thf('70', plain, ((v1_relat_1 @ sk_D)),
% 1.51/1.71      inference('sup-', [status(thm)], ['5', '6'])).
% 1.51/1.71  thf('71', plain, (((k2_relat_1 @ sk_E) = (sk_C))),
% 1.51/1.71      inference('demod', [status(thm)], ['60', '67', '68', '69', '70'])).
% 1.51/1.71  thf('72', plain,
% 1.51/1.71      (![X11 : $i]:
% 1.51/1.71         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 1.51/1.71          | ~ (v1_funct_1 @ X11)
% 1.51/1.71          | ~ (v1_relat_1 @ X11))),
% 1.51/1.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.51/1.71  thf(t61_funct_1, axiom,
% 1.51/1.71    (![A:$i]:
% 1.51/1.71     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.51/1.71       ( ( v2_funct_1 @ A ) =>
% 1.51/1.71         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 1.51/1.71             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.51/1.71           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 1.51/1.71             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.51/1.71  thf('73', plain,
% 1.51/1.71      (![X16 : $i]:
% 1.51/1.71         (~ (v2_funct_1 @ X16)
% 1.51/1.71          | ((k5_relat_1 @ X16 @ (k2_funct_1 @ X16))
% 1.51/1.71              = (k6_relat_1 @ (k1_relat_1 @ X16)))
% 1.51/1.71          | ~ (v1_funct_1 @ X16)
% 1.51/1.71          | ~ (v1_relat_1 @ X16))),
% 1.51/1.71      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.51/1.71  thf('74', plain,
% 1.51/1.71      (![X5 : $i, X6 : $i]:
% 1.51/1.71         (~ (v1_relat_1 @ X5)
% 1.51/1.71          | ((k2_relat_1 @ (k5_relat_1 @ X6 @ X5))
% 1.51/1.71              = (k9_relat_1 @ X5 @ (k2_relat_1 @ X6)))
% 1.51/1.71          | ~ (v1_relat_1 @ X6))),
% 1.51/1.71      inference('cnf', [status(esa)], [t160_relat_1])).
% 1.51/1.71  thf('75', plain,
% 1.51/1.71      (![X0 : $i]:
% 1.51/1.71         (((k2_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 1.51/1.71            = (k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))
% 1.51/1.71          | ~ (v1_relat_1 @ X0)
% 1.51/1.71          | ~ (v1_funct_1 @ X0)
% 1.51/1.71          | ~ (v2_funct_1 @ X0)
% 1.51/1.71          | ~ (v1_relat_1 @ X0)
% 1.51/1.71          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.51/1.71      inference('sup+', [status(thm)], ['73', '74'])).
% 1.51/1.71  thf(t71_relat_1, axiom,
% 1.51/1.71    (![A:$i]:
% 1.51/1.71     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.51/1.71       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.51/1.71  thf('76', plain, (![X10 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 1.51/1.71      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.51/1.71  thf('77', plain,
% 1.51/1.71      (![X0 : $i]:
% 1.51/1.71         (((k1_relat_1 @ X0)
% 1.51/1.71            = (k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))
% 1.51/1.71          | ~ (v1_relat_1 @ X0)
% 1.51/1.71          | ~ (v1_funct_1 @ X0)
% 1.51/1.71          | ~ (v2_funct_1 @ X0)
% 1.51/1.71          | ~ (v1_relat_1 @ X0)
% 1.51/1.71          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.51/1.71      inference('demod', [status(thm)], ['75', '76'])).
% 1.51/1.71  thf('78', plain,
% 1.51/1.71      (![X0 : $i]:
% 1.51/1.71         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.51/1.71          | ~ (v2_funct_1 @ X0)
% 1.51/1.71          | ~ (v1_funct_1 @ X0)
% 1.51/1.71          | ~ (v1_relat_1 @ X0)
% 1.51/1.71          | ((k1_relat_1 @ X0)
% 1.51/1.71              = (k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))))),
% 1.51/1.71      inference('simplify', [status(thm)], ['77'])).
% 1.51/1.71  thf('79', plain,
% 1.51/1.71      (![X0 : $i]:
% 1.51/1.71         (~ (v1_relat_1 @ X0)
% 1.51/1.71          | ~ (v1_funct_1 @ X0)
% 1.51/1.71          | ((k1_relat_1 @ X0)
% 1.51/1.71              = (k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))
% 1.51/1.71          | ~ (v1_relat_1 @ X0)
% 1.51/1.71          | ~ (v1_funct_1 @ X0)
% 1.51/1.71          | ~ (v2_funct_1 @ X0))),
% 1.51/1.71      inference('sup-', [status(thm)], ['72', '78'])).
% 1.51/1.71  thf('80', plain,
% 1.51/1.71      (![X0 : $i]:
% 1.51/1.71         (~ (v2_funct_1 @ X0)
% 1.51/1.71          | ((k1_relat_1 @ X0)
% 1.51/1.71              = (k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))
% 1.51/1.71          | ~ (v1_funct_1 @ X0)
% 1.51/1.71          | ~ (v1_relat_1 @ X0))),
% 1.51/1.71      inference('simplify', [status(thm)], ['79'])).
% 1.51/1.71  thf('81', plain,
% 1.51/1.71      ((((k1_relat_1 @ sk_E) = (k9_relat_1 @ (k2_funct_1 @ sk_E) @ sk_C))
% 1.51/1.71        | ~ (v1_relat_1 @ sk_E)
% 1.51/1.71        | ~ (v1_funct_1 @ sk_E)
% 1.51/1.71        | ~ (v2_funct_1 @ sk_E))),
% 1.51/1.71      inference('sup+', [status(thm)], ['71', '80'])).
% 1.51/1.71  thf('82', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf(d1_funct_2, axiom,
% 1.51/1.71    (![A:$i,B:$i,C:$i]:
% 1.51/1.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.51/1.71       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.51/1.71           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.51/1.71             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.51/1.71         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.51/1.71           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.51/1.71             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.51/1.71  thf(zf_stmt_1, axiom,
% 1.51/1.71    (![C:$i,B:$i,A:$i]:
% 1.51/1.71     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.51/1.71       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.51/1.71  thf('83', plain,
% 1.51/1.71      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.51/1.71         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 1.51/1.71          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 1.51/1.71          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.51/1.71  thf('84', plain,
% 1.51/1.71      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 1.51/1.71        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E)))),
% 1.51/1.71      inference('sup-', [status(thm)], ['82', '83'])).
% 1.51/1.71  thf(zf_stmt_2, axiom,
% 1.51/1.71    (![B:$i,A:$i]:
% 1.51/1.71     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.51/1.71       ( zip_tseitin_0 @ B @ A ) ))).
% 1.51/1.71  thf('85', plain,
% 1.51/1.71      (![X29 : $i, X30 : $i]:
% 1.51/1.71         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.51/1.71  thf('86', plain,
% 1.51/1.71      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.51/1.71  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.51/1.71  thf(zf_stmt_5, axiom,
% 1.51/1.71    (![A:$i,B:$i,C:$i]:
% 1.51/1.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.51/1.71       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.51/1.71         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.51/1.71           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.51/1.71             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.51/1.71  thf('87', plain,
% 1.51/1.71      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.51/1.71         (~ (zip_tseitin_0 @ X34 @ X35)
% 1.51/1.71          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 1.51/1.71          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.51/1.71  thf('88', plain,
% 1.51/1.71      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 1.51/1.71      inference('sup-', [status(thm)], ['86', '87'])).
% 1.51/1.71  thf('89', plain,
% 1.51/1.71      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B))),
% 1.51/1.71      inference('sup-', [status(thm)], ['85', '88'])).
% 1.51/1.71  thf('90', plain, (((sk_C) != (k1_xboole_0))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('91', plain, ((zip_tseitin_1 @ sk_E @ sk_C @ sk_B)),
% 1.51/1.71      inference('simplify_reflect-', [status(thm)], ['89', '90'])).
% 1.51/1.71  thf('92', plain,
% 1.51/1.71      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf(redefinition_k1_relset_1, axiom,
% 1.51/1.71    (![A:$i,B:$i,C:$i]:
% 1.51/1.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.51/1.71       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.51/1.71  thf('93', plain,
% 1.51/1.71      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.51/1.71         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 1.51/1.71          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.51/1.71      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.51/1.71  thf('94', plain,
% 1.51/1.71      (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 1.51/1.71      inference('sup-', [status(thm)], ['92', '93'])).
% 1.51/1.71  thf('95', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 1.51/1.71      inference('demod', [status(thm)], ['84', '91', '94'])).
% 1.51/1.71  thf('96', plain, ((v1_relat_1 @ sk_E)),
% 1.51/1.71      inference('sup-', [status(thm)], ['38', '39'])).
% 1.51/1.71  thf('97', plain, ((v1_funct_1 @ sk_E)),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('98', plain, ((v2_funct_1 @ sk_E)),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('99', plain, (((sk_B) = (k9_relat_1 @ (k2_funct_1 @ sk_E) @ sk_C))),
% 1.51/1.71      inference('demod', [status(thm)], ['81', '95', '96', '97', '98'])).
% 1.51/1.71  thf('100', plain, ((r1_tarski @ sk_B @ (k2_relat_1 @ sk_D))),
% 1.51/1.71      inference('demod', [status(thm)], ['55', '99'])).
% 1.51/1.71  thf('101', plain, (((sk_B) = (k2_relat_1 @ sk_D))),
% 1.51/1.71      inference('demod', [status(thm)], ['10', '100'])).
% 1.51/1.71  thf('102', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) != (sk_B))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('103', plain,
% 1.51/1.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('104', plain,
% 1.51/1.71      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.51/1.71         (((k2_relset_1 @ X27 @ X28 @ X26) = (k2_relat_1 @ X26))
% 1.51/1.71          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 1.51/1.71      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.51/1.71  thf('105', plain,
% 1.51/1.71      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.51/1.71      inference('sup-', [status(thm)], ['103', '104'])).
% 1.51/1.71  thf('106', plain, (((k2_relat_1 @ sk_D) != (sk_B))),
% 1.51/1.71      inference('demod', [status(thm)], ['102', '105'])).
% 1.51/1.71  thf('107', plain, ($false),
% 1.51/1.71      inference('simplify_reflect-', [status(thm)], ['101', '106'])).
% 1.51/1.71  
% 1.51/1.71  % SZS output end Refutation
% 1.51/1.71  
% 1.51/1.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

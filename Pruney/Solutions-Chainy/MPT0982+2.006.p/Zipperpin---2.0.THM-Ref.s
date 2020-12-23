%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Z8uKy5Iqlz

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:55 EST 2020

% Result     : Theorem 2.02s
% Output     : Refutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 376 expanded)
%              Number of leaves         :   48 ( 129 expanded)
%              Depth                    :   16
%              Number of atoms          : 1339 (8078 expanded)
%              Number of equality atoms :   70 ( 460 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v5_relat_1 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
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
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X40 ) ) ) ) ),
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
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ( ( k1_partfun1 @ X42 @ X43 @ X45 @ X46 @ X41 @ X44 )
        = ( k5_relat_1 @ X41 @ X44 ) ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('40',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) )
    = sk_C ),
    inference(demod,[status(thm)],['36','37','40'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('42',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('43',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf(t154_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k9_relat_1 @ B @ A )
          = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('44',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k9_relat_1 @ X12 @ X13 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X12 ) @ X13 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('45',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X10 @ ( k10_relat_1 @ X10 @ X11 ) ) @ X11 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
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
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k9_relat_1 @ X0 @ X1 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k9_relat_1 @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v5_relat_1 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
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
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('73',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) )
        = ( k9_relat_1 @ X5 @ ( k2_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf(t58_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('74',plain,(
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X14 @ ( k2_funct_1 @ X14 ) ) )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ sk_C )
      = ( k1_relat_1 @ sk_E ) )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v2_funct_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['71','78'])).

thf('80',plain,(
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

thf('81',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('82',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('83',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('84',plain,(
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

thf('85',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('86',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    zip_tseitin_1 @ sk_E @ sk_C @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['87','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('91',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('92',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['82','89','92'])).

thf('94',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['38','39'])).

thf('95',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_E ) @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['79','93','94','95','96'])).

thf('98',plain,(
    r1_tarski @ sk_B @ ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['55','97'])).

thf('99',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['10','98'])).

thf('100',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('103',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ( k2_relat_1 @ sk_D )
 != sk_B ),
    inference(demod,[status(thm)],['100','103'])).

thf('105',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['99','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Z8uKy5Iqlz
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:56:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.02/2.27  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.02/2.27  % Solved by: fo/fo7.sh
% 2.02/2.27  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.02/2.27  % done 804 iterations in 1.806s
% 2.02/2.27  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.02/2.27  % SZS output start Refutation
% 2.02/2.27  thf(sk_B_type, type, sk_B: $i).
% 2.02/2.27  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 2.02/2.27  thf(sk_D_type, type, sk_D: $i).
% 2.02/2.27  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.02/2.27  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.02/2.27  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.02/2.27  thf(sk_E_type, type, sk_E: $i).
% 2.02/2.27  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.02/2.27  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.02/2.27  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.02/2.27  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.02/2.27  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.02/2.27  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.02/2.27  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.02/2.27  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.02/2.27  thf(sk_A_type, type, sk_A: $i).
% 2.02/2.27  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.02/2.27  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.02/2.27  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.02/2.27  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.02/2.27  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.02/2.27  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.02/2.27  thf(sk_C_type, type, sk_C: $i).
% 2.02/2.27  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.02/2.27  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.02/2.27  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.02/2.27  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 2.02/2.27  thf(t28_funct_2, conjecture,
% 2.02/2.27    (![A:$i,B:$i,C:$i,D:$i]:
% 2.02/2.27     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.02/2.27         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.02/2.27       ( ![E:$i]:
% 2.02/2.27         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.02/2.27             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.02/2.27           ( ( ( ( k2_relset_1 @
% 2.02/2.27                   A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 2.02/2.27                 ( C ) ) & 
% 2.02/2.27               ( v2_funct_1 @ E ) ) =>
% 2.02/2.27             ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 2.02/2.27               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ))).
% 2.02/2.27  thf(zf_stmt_0, negated_conjecture,
% 2.02/2.27    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 2.02/2.27        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.02/2.27            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.02/2.27          ( ![E:$i]:
% 2.02/2.27            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.02/2.27                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.02/2.27              ( ( ( ( k2_relset_1 @
% 2.02/2.27                      A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 2.02/2.27                    ( C ) ) & 
% 2.02/2.27                  ( v2_funct_1 @ E ) ) =>
% 2.02/2.27                ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 2.02/2.27                  ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ) )),
% 2.02/2.27    inference('cnf.neg', [status(esa)], [t28_funct_2])).
% 2.02/2.27  thf('0', plain,
% 2.02/2.27      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.02/2.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.02/2.27  thf(cc2_relset_1, axiom,
% 2.02/2.27    (![A:$i,B:$i,C:$i]:
% 2.02/2.27     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.02/2.27       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.02/2.27  thf('1', plain,
% 2.02/2.27      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.02/2.27         ((v5_relat_1 @ X18 @ X20)
% 2.02/2.27          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 2.02/2.27      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.02/2.27  thf('2', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 2.02/2.27      inference('sup-', [status(thm)], ['0', '1'])).
% 2.02/2.27  thf(d19_relat_1, axiom,
% 2.02/2.27    (![A:$i,B:$i]:
% 2.02/2.27     ( ( v1_relat_1 @ B ) =>
% 2.02/2.27       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 2.02/2.27  thf('3', plain,
% 2.02/2.27      (![X3 : $i, X4 : $i]:
% 2.02/2.27         (~ (v5_relat_1 @ X3 @ X4)
% 2.02/2.27          | (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 2.02/2.27          | ~ (v1_relat_1 @ X3))),
% 2.02/2.27      inference('cnf', [status(esa)], [d19_relat_1])).
% 2.02/2.27  thf('4', plain,
% 2.02/2.27      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 2.02/2.27      inference('sup-', [status(thm)], ['2', '3'])).
% 2.02/2.27  thf('5', plain,
% 2.02/2.27      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.02/2.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.02/2.27  thf(cc1_relset_1, axiom,
% 2.02/2.27    (![A:$i,B:$i,C:$i]:
% 2.02/2.27     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.02/2.27       ( v1_relat_1 @ C ) ))).
% 2.02/2.27  thf('6', plain,
% 2.02/2.27      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.02/2.27         ((v1_relat_1 @ X15)
% 2.02/2.27          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 2.02/2.27      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.02/2.27  thf('7', plain, ((v1_relat_1 @ sk_D)),
% 2.02/2.27      inference('sup-', [status(thm)], ['5', '6'])).
% 2.02/2.27  thf('8', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 2.02/2.27      inference('demod', [status(thm)], ['4', '7'])).
% 2.02/2.27  thf(d10_xboole_0, axiom,
% 2.02/2.27    (![A:$i,B:$i]:
% 2.02/2.27     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.02/2.27  thf('9', plain,
% 2.02/2.27      (![X0 : $i, X2 : $i]:
% 2.02/2.27         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.02/2.27      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.02/2.27  thf('10', plain,
% 2.02/2.27      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_D))
% 2.02/2.27        | ((sk_B) = (k2_relat_1 @ sk_D)))),
% 2.02/2.27      inference('sup-', [status(thm)], ['8', '9'])).
% 2.02/2.27  thf(t160_relat_1, axiom,
% 2.02/2.27    (![A:$i]:
% 2.02/2.27     ( ( v1_relat_1 @ A ) =>
% 2.02/2.27       ( ![B:$i]:
% 2.02/2.27         ( ( v1_relat_1 @ B ) =>
% 2.02/2.27           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 2.02/2.27             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 2.02/2.27  thf('11', plain,
% 2.02/2.27      (![X5 : $i, X6 : $i]:
% 2.02/2.27         (~ (v1_relat_1 @ X5)
% 2.02/2.27          | ((k2_relat_1 @ (k5_relat_1 @ X6 @ X5))
% 2.02/2.27              = (k9_relat_1 @ X5 @ (k2_relat_1 @ X6)))
% 2.02/2.27          | ~ (v1_relat_1 @ X6))),
% 2.02/2.27      inference('cnf', [status(esa)], [t160_relat_1])).
% 2.02/2.27  thf('12', plain,
% 2.02/2.27      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.02/2.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.02/2.27  thf('13', plain,
% 2.02/2.27      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.02/2.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.02/2.27  thf(dt_k1_partfun1, axiom,
% 2.02/2.27    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.02/2.27     ( ( ( v1_funct_1 @ E ) & 
% 2.02/2.27         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.02/2.27         ( v1_funct_1 @ F ) & 
% 2.02/2.27         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.02/2.27       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.02/2.27         ( m1_subset_1 @
% 2.02/2.27           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.02/2.27           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 2.02/2.27  thf('14', plain,
% 2.02/2.27      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 2.02/2.27         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 2.02/2.27          | ~ (v1_funct_1 @ X35)
% 2.02/2.27          | ~ (v1_funct_1 @ X38)
% 2.02/2.27          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 2.02/2.27          | (m1_subset_1 @ (k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38) @ 
% 2.02/2.27             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X40))))),
% 2.02/2.27      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 2.02/2.27  thf('15', plain,
% 2.02/2.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.02/2.27         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 2.02/2.27           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.02/2.27          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.02/2.27          | ~ (v1_funct_1 @ X1)
% 2.02/2.27          | ~ (v1_funct_1 @ sk_D))),
% 2.02/2.27      inference('sup-', [status(thm)], ['13', '14'])).
% 2.02/2.27  thf('16', plain, ((v1_funct_1 @ sk_D)),
% 2.02/2.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.02/2.27  thf('17', plain,
% 2.02/2.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.02/2.27         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 2.02/2.27           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.02/2.27          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.02/2.27          | ~ (v1_funct_1 @ X1))),
% 2.02/2.27      inference('demod', [status(thm)], ['15', '16'])).
% 2.02/2.27  thf('18', plain,
% 2.02/2.27      ((~ (v1_funct_1 @ sk_E)
% 2.02/2.27        | (m1_subset_1 @ 
% 2.02/2.27           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 2.02/2.27           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 2.02/2.27      inference('sup-', [status(thm)], ['12', '17'])).
% 2.02/2.27  thf('19', plain, ((v1_funct_1 @ sk_E)),
% 2.02/2.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.02/2.27  thf('20', plain,
% 2.02/2.27      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.02/2.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.02/2.27  thf('21', plain,
% 2.02/2.27      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.02/2.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.02/2.27  thf(redefinition_k1_partfun1, axiom,
% 2.02/2.27    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.02/2.27     ( ( ( v1_funct_1 @ E ) & 
% 2.02/2.27         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.02/2.27         ( v1_funct_1 @ F ) & 
% 2.02/2.27         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.02/2.27       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.02/2.27  thf('22', plain,
% 2.02/2.27      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 2.02/2.27         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 2.02/2.27          | ~ (v1_funct_1 @ X41)
% 2.02/2.27          | ~ (v1_funct_1 @ X44)
% 2.02/2.27          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 2.02/2.27          | ((k1_partfun1 @ X42 @ X43 @ X45 @ X46 @ X41 @ X44)
% 2.02/2.27              = (k5_relat_1 @ X41 @ X44)))),
% 2.02/2.27      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 2.02/2.27  thf('23', plain,
% 2.02/2.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.02/2.27         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 2.02/2.27            = (k5_relat_1 @ sk_D @ X0))
% 2.02/2.27          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.02/2.27          | ~ (v1_funct_1 @ X0)
% 2.02/2.27          | ~ (v1_funct_1 @ sk_D))),
% 2.02/2.27      inference('sup-', [status(thm)], ['21', '22'])).
% 2.02/2.27  thf('24', plain, ((v1_funct_1 @ sk_D)),
% 2.02/2.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.02/2.27  thf('25', plain,
% 2.02/2.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.02/2.27         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 2.02/2.27            = (k5_relat_1 @ sk_D @ X0))
% 2.02/2.27          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.02/2.27          | ~ (v1_funct_1 @ X0))),
% 2.02/2.27      inference('demod', [status(thm)], ['23', '24'])).
% 2.02/2.27  thf('26', plain,
% 2.02/2.27      ((~ (v1_funct_1 @ sk_E)
% 2.02/2.27        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 2.02/2.27            = (k5_relat_1 @ sk_D @ sk_E)))),
% 2.02/2.27      inference('sup-', [status(thm)], ['20', '25'])).
% 2.02/2.27  thf('27', plain, ((v1_funct_1 @ sk_E)),
% 2.02/2.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.02/2.27  thf('28', plain,
% 2.02/2.27      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 2.02/2.27         = (k5_relat_1 @ sk_D @ sk_E))),
% 2.02/2.27      inference('demod', [status(thm)], ['26', '27'])).
% 2.02/2.27  thf('29', plain,
% 2.02/2.27      ((m1_subset_1 @ (k5_relat_1 @ sk_D @ sk_E) @ 
% 2.02/2.27        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 2.02/2.27      inference('demod', [status(thm)], ['18', '19', '28'])).
% 2.02/2.27  thf(redefinition_k2_relset_1, axiom,
% 2.02/2.27    (![A:$i,B:$i,C:$i]:
% 2.02/2.27     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.02/2.27       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.02/2.27  thf('30', plain,
% 2.02/2.27      (![X24 : $i, X25 : $i, X26 : $i]:
% 2.02/2.27         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 2.02/2.27          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 2.02/2.27      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.02/2.27  thf('31', plain,
% 2.02/2.27      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E))
% 2.02/2.27         = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 2.02/2.27      inference('sup-', [status(thm)], ['29', '30'])).
% 2.02/2.27  thf('32', plain,
% 2.02/2.27      (((k2_relset_1 @ sk_A @ sk_C @ 
% 2.02/2.27         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)) = (sk_C))),
% 2.02/2.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.02/2.27  thf('33', plain,
% 2.02/2.27      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 2.02/2.27         = (k5_relat_1 @ sk_D @ sk_E))),
% 2.02/2.27      inference('demod', [status(thm)], ['26', '27'])).
% 2.02/2.27  thf('34', plain,
% 2.02/2.27      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 2.02/2.27      inference('demod', [status(thm)], ['32', '33'])).
% 2.02/2.27  thf('35', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 2.02/2.27      inference('sup+', [status(thm)], ['31', '34'])).
% 2.02/2.27  thf('36', plain,
% 2.02/2.27      ((((k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)) = (sk_C))
% 2.02/2.27        | ~ (v1_relat_1 @ sk_D)
% 2.02/2.27        | ~ (v1_relat_1 @ sk_E))),
% 2.02/2.27      inference('sup+', [status(thm)], ['11', '35'])).
% 2.02/2.27  thf('37', plain, ((v1_relat_1 @ sk_D)),
% 2.02/2.27      inference('sup-', [status(thm)], ['5', '6'])).
% 2.02/2.27  thf('38', plain,
% 2.02/2.27      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.02/2.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.02/2.27  thf('39', plain,
% 2.02/2.27      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.02/2.27         ((v1_relat_1 @ X15)
% 2.02/2.27          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 2.02/2.27      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.02/2.27  thf('40', plain, ((v1_relat_1 @ sk_E)),
% 2.02/2.27      inference('sup-', [status(thm)], ['38', '39'])).
% 2.02/2.27  thf('41', plain, (((k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)) = (sk_C))),
% 2.02/2.27      inference('demod', [status(thm)], ['36', '37', '40'])).
% 2.02/2.27  thf(fc6_funct_1, axiom,
% 2.02/2.27    (![A:$i]:
% 2.02/2.27     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 2.02/2.27       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 2.02/2.27         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 2.02/2.27         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 2.02/2.27  thf('42', plain,
% 2.02/2.27      (![X9 : $i]:
% 2.02/2.27         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 2.02/2.27          | ~ (v2_funct_1 @ X9)
% 2.02/2.27          | ~ (v1_funct_1 @ X9)
% 2.02/2.27          | ~ (v1_relat_1 @ X9))),
% 2.02/2.27      inference('cnf', [status(esa)], [fc6_funct_1])).
% 2.02/2.27  thf('43', plain,
% 2.02/2.27      (![X9 : $i]:
% 2.02/2.27         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 2.02/2.27          | ~ (v2_funct_1 @ X9)
% 2.02/2.27          | ~ (v1_funct_1 @ X9)
% 2.02/2.27          | ~ (v1_relat_1 @ X9))),
% 2.02/2.27      inference('cnf', [status(esa)], [fc6_funct_1])).
% 2.02/2.27  thf(t154_funct_1, axiom,
% 2.02/2.27    (![A:$i,B:$i]:
% 2.02/2.27     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.02/2.27       ( ( v2_funct_1 @ B ) =>
% 2.02/2.27         ( ( k9_relat_1 @ B @ A ) = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 2.02/2.27  thf('44', plain,
% 2.02/2.27      (![X12 : $i, X13 : $i]:
% 2.02/2.27         (~ (v2_funct_1 @ X12)
% 2.02/2.27          | ((k9_relat_1 @ X12 @ X13)
% 2.02/2.27              = (k10_relat_1 @ (k2_funct_1 @ X12) @ X13))
% 2.02/2.27          | ~ (v1_funct_1 @ X12)
% 2.02/2.27          | ~ (v1_relat_1 @ X12))),
% 2.02/2.27      inference('cnf', [status(esa)], [t154_funct_1])).
% 2.02/2.27  thf(t145_funct_1, axiom,
% 2.02/2.27    (![A:$i,B:$i]:
% 2.02/2.27     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.02/2.27       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 2.02/2.27  thf('45', plain,
% 2.02/2.27      (![X10 : $i, X11 : $i]:
% 2.02/2.27         ((r1_tarski @ (k9_relat_1 @ X10 @ (k10_relat_1 @ X10 @ X11)) @ X11)
% 2.02/2.27          | ~ (v1_funct_1 @ X10)
% 2.02/2.27          | ~ (v1_relat_1 @ X10))),
% 2.02/2.27      inference('cnf', [status(esa)], [t145_funct_1])).
% 2.02/2.27  thf('46', plain,
% 2.02/2.27      (![X0 : $i, X1 : $i]:
% 2.02/2.27         ((r1_tarski @ 
% 2.02/2.27           (k9_relat_1 @ (k2_funct_1 @ X1) @ (k9_relat_1 @ X1 @ X0)) @ X0)
% 2.02/2.27          | ~ (v1_relat_1 @ X1)
% 2.02/2.27          | ~ (v1_funct_1 @ X1)
% 2.02/2.27          | ~ (v2_funct_1 @ X1)
% 2.02/2.27          | ~ (v1_relat_1 @ (k2_funct_1 @ X1))
% 2.02/2.27          | ~ (v1_funct_1 @ (k2_funct_1 @ X1)))),
% 2.02/2.27      inference('sup+', [status(thm)], ['44', '45'])).
% 2.02/2.27  thf('47', plain,
% 2.02/2.27      (![X0 : $i, X1 : $i]:
% 2.02/2.27         (~ (v1_relat_1 @ X0)
% 2.02/2.27          | ~ (v1_funct_1 @ X0)
% 2.02/2.27          | ~ (v2_funct_1 @ X0)
% 2.02/2.27          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.02/2.27          | ~ (v2_funct_1 @ X0)
% 2.02/2.27          | ~ (v1_funct_1 @ X0)
% 2.02/2.27          | ~ (v1_relat_1 @ X0)
% 2.02/2.27          | (r1_tarski @ 
% 2.02/2.27             (k9_relat_1 @ (k2_funct_1 @ X0) @ (k9_relat_1 @ X0 @ X1)) @ X1))),
% 2.02/2.27      inference('sup-', [status(thm)], ['43', '46'])).
% 2.02/2.27  thf('48', plain,
% 2.02/2.27      (![X0 : $i, X1 : $i]:
% 2.02/2.27         ((r1_tarski @ 
% 2.02/2.27           (k9_relat_1 @ (k2_funct_1 @ X0) @ (k9_relat_1 @ X0 @ X1)) @ X1)
% 2.02/2.27          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.02/2.27          | ~ (v2_funct_1 @ X0)
% 2.02/2.27          | ~ (v1_funct_1 @ X0)
% 2.02/2.27          | ~ (v1_relat_1 @ X0))),
% 2.02/2.27      inference('simplify', [status(thm)], ['47'])).
% 2.02/2.27  thf('49', plain,
% 2.02/2.27      (![X0 : $i, X1 : $i]:
% 2.02/2.27         (~ (v1_relat_1 @ X0)
% 2.02/2.27          | ~ (v1_funct_1 @ X0)
% 2.02/2.27          | ~ (v2_funct_1 @ X0)
% 2.02/2.27          | ~ (v1_relat_1 @ X0)
% 2.02/2.27          | ~ (v1_funct_1 @ X0)
% 2.02/2.27          | ~ (v2_funct_1 @ X0)
% 2.02/2.27          | (r1_tarski @ 
% 2.02/2.27             (k9_relat_1 @ (k2_funct_1 @ X0) @ (k9_relat_1 @ X0 @ X1)) @ X1))),
% 2.02/2.27      inference('sup-', [status(thm)], ['42', '48'])).
% 2.02/2.27  thf('50', plain,
% 2.02/2.27      (![X0 : $i, X1 : $i]:
% 2.02/2.27         ((r1_tarski @ 
% 2.02/2.27           (k9_relat_1 @ (k2_funct_1 @ X0) @ (k9_relat_1 @ X0 @ X1)) @ X1)
% 2.02/2.27          | ~ (v2_funct_1 @ X0)
% 2.02/2.27          | ~ (v1_funct_1 @ X0)
% 2.02/2.27          | ~ (v1_relat_1 @ X0))),
% 2.02/2.27      inference('simplify', [status(thm)], ['49'])).
% 2.02/2.27  thf('51', plain,
% 2.02/2.27      (((r1_tarski @ (k9_relat_1 @ (k2_funct_1 @ sk_E) @ sk_C) @ 
% 2.02/2.27         (k2_relat_1 @ sk_D))
% 2.02/2.27        | ~ (v1_relat_1 @ sk_E)
% 2.02/2.27        | ~ (v1_funct_1 @ sk_E)
% 2.02/2.27        | ~ (v2_funct_1 @ sk_E))),
% 2.02/2.27      inference('sup+', [status(thm)], ['41', '50'])).
% 2.02/2.27  thf('52', plain, ((v1_relat_1 @ sk_E)),
% 2.02/2.27      inference('sup-', [status(thm)], ['38', '39'])).
% 2.02/2.27  thf('53', plain, ((v1_funct_1 @ sk_E)),
% 2.02/2.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.02/2.27  thf('54', plain, ((v2_funct_1 @ sk_E)),
% 2.02/2.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.02/2.27  thf('55', plain,
% 2.02/2.27      ((r1_tarski @ (k9_relat_1 @ (k2_funct_1 @ sk_E) @ sk_C) @ 
% 2.02/2.27        (k2_relat_1 @ sk_D))),
% 2.02/2.27      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 2.02/2.27  thf('56', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 2.02/2.27      inference('sup+', [status(thm)], ['31', '34'])).
% 2.02/2.27  thf(t45_relat_1, axiom,
% 2.02/2.27    (![A:$i]:
% 2.02/2.27     ( ( v1_relat_1 @ A ) =>
% 2.02/2.27       ( ![B:$i]:
% 2.02/2.27         ( ( v1_relat_1 @ B ) =>
% 2.02/2.27           ( r1_tarski @
% 2.02/2.27             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 2.02/2.27  thf('57', plain,
% 2.02/2.27      (![X7 : $i, X8 : $i]:
% 2.02/2.27         (~ (v1_relat_1 @ X7)
% 2.02/2.27          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X8 @ X7)) @ 
% 2.02/2.27             (k2_relat_1 @ X7))
% 2.02/2.27          | ~ (v1_relat_1 @ X8))),
% 2.02/2.27      inference('cnf', [status(esa)], [t45_relat_1])).
% 2.02/2.27  thf('58', plain,
% 2.02/2.27      (![X0 : $i, X2 : $i]:
% 2.02/2.27         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.02/2.27      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.02/2.27  thf('59', plain,
% 2.02/2.27      (![X0 : $i, X1 : $i]:
% 2.02/2.27         (~ (v1_relat_1 @ X1)
% 2.02/2.27          | ~ (v1_relat_1 @ X0)
% 2.02/2.27          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 2.02/2.27               (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 2.02/2.27          | ((k2_relat_1 @ X0) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 2.02/2.27      inference('sup-', [status(thm)], ['57', '58'])).
% 2.02/2.27  thf('60', plain,
% 2.02/2.27      ((~ (r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C)
% 2.02/2.27        | ((k2_relat_1 @ sk_E) = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))
% 2.02/2.27        | ~ (v1_relat_1 @ sk_E)
% 2.02/2.27        | ~ (v1_relat_1 @ sk_D))),
% 2.02/2.27      inference('sup-', [status(thm)], ['56', '59'])).
% 2.02/2.27  thf('61', plain,
% 2.02/2.27      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.02/2.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.02/2.27  thf('62', plain,
% 2.02/2.27      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.02/2.27         ((v5_relat_1 @ X18 @ X20)
% 2.02/2.27          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 2.02/2.27      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.02/2.27  thf('63', plain, ((v5_relat_1 @ sk_E @ sk_C)),
% 2.02/2.27      inference('sup-', [status(thm)], ['61', '62'])).
% 2.02/2.27  thf('64', plain,
% 2.02/2.27      (![X3 : $i, X4 : $i]:
% 2.02/2.27         (~ (v5_relat_1 @ X3 @ X4)
% 2.02/2.27          | (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 2.02/2.27          | ~ (v1_relat_1 @ X3))),
% 2.02/2.27      inference('cnf', [status(esa)], [d19_relat_1])).
% 2.02/2.27  thf('65', plain,
% 2.02/2.27      ((~ (v1_relat_1 @ sk_E) | (r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C))),
% 2.02/2.27      inference('sup-', [status(thm)], ['63', '64'])).
% 2.02/2.27  thf('66', plain, ((v1_relat_1 @ sk_E)),
% 2.02/2.27      inference('sup-', [status(thm)], ['38', '39'])).
% 2.02/2.27  thf('67', plain, ((r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C)),
% 2.02/2.27      inference('demod', [status(thm)], ['65', '66'])).
% 2.02/2.27  thf('68', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 2.02/2.27      inference('sup+', [status(thm)], ['31', '34'])).
% 2.02/2.27  thf('69', plain, ((v1_relat_1 @ sk_E)),
% 2.02/2.27      inference('sup-', [status(thm)], ['38', '39'])).
% 2.02/2.27  thf('70', plain, ((v1_relat_1 @ sk_D)),
% 2.02/2.27      inference('sup-', [status(thm)], ['5', '6'])).
% 2.02/2.27  thf('71', plain, (((k2_relat_1 @ sk_E) = (sk_C))),
% 2.02/2.27      inference('demod', [status(thm)], ['60', '67', '68', '69', '70'])).
% 2.02/2.27  thf('72', plain,
% 2.02/2.27      (![X9 : $i]:
% 2.02/2.27         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 2.02/2.27          | ~ (v2_funct_1 @ X9)
% 2.02/2.27          | ~ (v1_funct_1 @ X9)
% 2.02/2.27          | ~ (v1_relat_1 @ X9))),
% 2.02/2.27      inference('cnf', [status(esa)], [fc6_funct_1])).
% 2.02/2.27  thf('73', plain,
% 2.02/2.27      (![X5 : $i, X6 : $i]:
% 2.02/2.27         (~ (v1_relat_1 @ X5)
% 2.02/2.27          | ((k2_relat_1 @ (k5_relat_1 @ X6 @ X5))
% 2.02/2.27              = (k9_relat_1 @ X5 @ (k2_relat_1 @ X6)))
% 2.02/2.27          | ~ (v1_relat_1 @ X6))),
% 2.02/2.27      inference('cnf', [status(esa)], [t160_relat_1])).
% 2.02/2.27  thf(t58_funct_1, axiom,
% 2.02/2.27    (![A:$i]:
% 2.02/2.27     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.02/2.27       ( ( v2_funct_1 @ A ) =>
% 2.02/2.27         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 2.02/2.27             ( k1_relat_1 @ A ) ) & 
% 2.02/2.27           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 2.02/2.27             ( k1_relat_1 @ A ) ) ) ) ))).
% 2.02/2.27  thf('74', plain,
% 2.02/2.27      (![X14 : $i]:
% 2.02/2.27         (~ (v2_funct_1 @ X14)
% 2.02/2.27          | ((k2_relat_1 @ (k5_relat_1 @ X14 @ (k2_funct_1 @ X14)))
% 2.02/2.27              = (k1_relat_1 @ X14))
% 2.02/2.27          | ~ (v1_funct_1 @ X14)
% 2.02/2.27          | ~ (v1_relat_1 @ X14))),
% 2.02/2.27      inference('cnf', [status(esa)], [t58_funct_1])).
% 2.02/2.27  thf('75', plain,
% 2.02/2.27      (![X0 : $i]:
% 2.02/2.27         (((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 2.02/2.27            = (k1_relat_1 @ X0))
% 2.02/2.27          | ~ (v1_relat_1 @ X0)
% 2.02/2.27          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.02/2.27          | ~ (v1_relat_1 @ X0)
% 2.02/2.27          | ~ (v1_funct_1 @ X0)
% 2.02/2.27          | ~ (v2_funct_1 @ X0))),
% 2.02/2.27      inference('sup+', [status(thm)], ['73', '74'])).
% 2.02/2.27  thf('76', plain,
% 2.02/2.27      (![X0 : $i]:
% 2.02/2.27         (~ (v2_funct_1 @ X0)
% 2.02/2.27          | ~ (v1_funct_1 @ X0)
% 2.02/2.27          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.02/2.27          | ~ (v1_relat_1 @ X0)
% 2.02/2.27          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 2.02/2.27              = (k1_relat_1 @ X0)))),
% 2.02/2.27      inference('simplify', [status(thm)], ['75'])).
% 2.02/2.27  thf('77', plain,
% 2.02/2.27      (![X0 : $i]:
% 2.02/2.27         (~ (v1_relat_1 @ X0)
% 2.02/2.27          | ~ (v1_funct_1 @ X0)
% 2.02/2.27          | ~ (v2_funct_1 @ X0)
% 2.02/2.27          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 2.02/2.27              = (k1_relat_1 @ X0))
% 2.02/2.27          | ~ (v1_relat_1 @ X0)
% 2.02/2.27          | ~ (v1_funct_1 @ X0)
% 2.02/2.27          | ~ (v2_funct_1 @ X0))),
% 2.02/2.27      inference('sup-', [status(thm)], ['72', '76'])).
% 2.02/2.27  thf('78', plain,
% 2.02/2.27      (![X0 : $i]:
% 2.02/2.27         (((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 2.02/2.27            = (k1_relat_1 @ X0))
% 2.02/2.27          | ~ (v2_funct_1 @ X0)
% 2.02/2.27          | ~ (v1_funct_1 @ X0)
% 2.02/2.27          | ~ (v1_relat_1 @ X0))),
% 2.02/2.27      inference('simplify', [status(thm)], ['77'])).
% 2.02/2.27  thf('79', plain,
% 2.02/2.27      ((((k9_relat_1 @ (k2_funct_1 @ sk_E) @ sk_C) = (k1_relat_1 @ sk_E))
% 2.02/2.27        | ~ (v1_relat_1 @ sk_E)
% 2.02/2.27        | ~ (v1_funct_1 @ sk_E)
% 2.02/2.27        | ~ (v2_funct_1 @ sk_E))),
% 2.02/2.27      inference('sup+', [status(thm)], ['71', '78'])).
% 2.02/2.27  thf('80', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 2.02/2.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.02/2.27  thf(d1_funct_2, axiom,
% 2.02/2.27    (![A:$i,B:$i,C:$i]:
% 2.02/2.27     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.02/2.27       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.02/2.27           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.02/2.27             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.02/2.27         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.02/2.27           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.02/2.27             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.02/2.27  thf(zf_stmt_1, axiom,
% 2.02/2.27    (![C:$i,B:$i,A:$i]:
% 2.02/2.27     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.02/2.27       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.02/2.27  thf('81', plain,
% 2.02/2.27      (![X29 : $i, X30 : $i, X31 : $i]:
% 2.02/2.27         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 2.02/2.27          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 2.02/2.27          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 2.02/2.27      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.02/2.27  thf('82', plain,
% 2.02/2.27      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 2.02/2.27        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E)))),
% 2.02/2.27      inference('sup-', [status(thm)], ['80', '81'])).
% 2.02/2.27  thf(zf_stmt_2, axiom,
% 2.02/2.27    (![B:$i,A:$i]:
% 2.02/2.27     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.02/2.27       ( zip_tseitin_0 @ B @ A ) ))).
% 2.02/2.27  thf('83', plain,
% 2.02/2.27      (![X27 : $i, X28 : $i]:
% 2.02/2.27         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 2.02/2.27      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.02/2.27  thf('84', plain,
% 2.02/2.27      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.02/2.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.02/2.27  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.02/2.27  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 2.02/2.27  thf(zf_stmt_5, axiom,
% 2.02/2.27    (![A:$i,B:$i,C:$i]:
% 2.02/2.27     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.02/2.27       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.02/2.27         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.02/2.27           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.02/2.27             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.02/2.27  thf('85', plain,
% 2.02/2.27      (![X32 : $i, X33 : $i, X34 : $i]:
% 2.02/2.27         (~ (zip_tseitin_0 @ X32 @ X33)
% 2.02/2.27          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 2.02/2.27          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 2.02/2.27      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.02/2.27  thf('86', plain,
% 2.02/2.27      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 2.02/2.27      inference('sup-', [status(thm)], ['84', '85'])).
% 2.02/2.27  thf('87', plain,
% 2.02/2.27      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B))),
% 2.02/2.27      inference('sup-', [status(thm)], ['83', '86'])).
% 2.02/2.27  thf('88', plain, (((sk_C) != (k1_xboole_0))),
% 2.02/2.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.02/2.27  thf('89', plain, ((zip_tseitin_1 @ sk_E @ sk_C @ sk_B)),
% 2.02/2.27      inference('simplify_reflect-', [status(thm)], ['87', '88'])).
% 2.02/2.27  thf('90', plain,
% 2.02/2.27      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.02/2.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.02/2.27  thf(redefinition_k1_relset_1, axiom,
% 2.02/2.27    (![A:$i,B:$i,C:$i]:
% 2.02/2.27     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.02/2.27       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.02/2.27  thf('91', plain,
% 2.02/2.27      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.02/2.27         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 2.02/2.27          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 2.02/2.27      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.02/2.27  thf('92', plain,
% 2.02/2.27      (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 2.02/2.27      inference('sup-', [status(thm)], ['90', '91'])).
% 2.02/2.27  thf('93', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 2.02/2.27      inference('demod', [status(thm)], ['82', '89', '92'])).
% 2.02/2.27  thf('94', plain, ((v1_relat_1 @ sk_E)),
% 2.02/2.27      inference('sup-', [status(thm)], ['38', '39'])).
% 2.02/2.27  thf('95', plain, ((v1_funct_1 @ sk_E)),
% 2.02/2.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.02/2.27  thf('96', plain, ((v2_funct_1 @ sk_E)),
% 2.02/2.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.02/2.27  thf('97', plain, (((k9_relat_1 @ (k2_funct_1 @ sk_E) @ sk_C) = (sk_B))),
% 2.02/2.27      inference('demod', [status(thm)], ['79', '93', '94', '95', '96'])).
% 2.02/2.27  thf('98', plain, ((r1_tarski @ sk_B @ (k2_relat_1 @ sk_D))),
% 2.02/2.27      inference('demod', [status(thm)], ['55', '97'])).
% 2.02/2.27  thf('99', plain, (((sk_B) = (k2_relat_1 @ sk_D))),
% 2.02/2.27      inference('demod', [status(thm)], ['10', '98'])).
% 2.02/2.27  thf('100', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) != (sk_B))),
% 2.02/2.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.02/2.27  thf('101', plain,
% 2.02/2.27      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.02/2.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.02/2.27  thf('102', plain,
% 2.02/2.27      (![X24 : $i, X25 : $i, X26 : $i]:
% 2.02/2.27         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 2.02/2.27          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 2.02/2.27      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.02/2.27  thf('103', plain,
% 2.02/2.27      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.02/2.27      inference('sup-', [status(thm)], ['101', '102'])).
% 2.02/2.27  thf('104', plain, (((k2_relat_1 @ sk_D) != (sk_B))),
% 2.02/2.27      inference('demod', [status(thm)], ['100', '103'])).
% 2.02/2.27  thf('105', plain, ($false),
% 2.02/2.27      inference('simplify_reflect-', [status(thm)], ['99', '104'])).
% 2.02/2.27  
% 2.02/2.27  % SZS output end Refutation
% 2.02/2.27  
% 2.02/2.28  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

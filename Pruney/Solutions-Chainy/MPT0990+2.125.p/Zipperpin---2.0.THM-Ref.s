%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Y80einkmV2

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:16 EST 2020

% Result     : Theorem 0.80s
% Output     : Refutation 0.80s
% Verified   : 
% Statistics : Number of formulae       :  211 ( 473 expanded)
%              Number of leaves         :   43 ( 163 expanded)
%              Depth                    :   28
%              Number of atoms          : 1762 (8772 expanded)
%              Number of equality atoms :   81 ( 547 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( ( k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41 )
        = ( k5_relat_1 @ X38 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','9'])).

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
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X35 ) ) ) ) ),
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

thf('19',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('20',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('21',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( X26 = X29 )
      | ~ ( r2_relset_1 @ X27 @ X28 @ X26 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','22'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('24',plain,(
    ! [X37: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('25',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('26',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
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

thf('27',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X19 ) @ X19 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('28',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('29',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X19 ) @ X19 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
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

thf('31',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relat_1 @ X18 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('32',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('34',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('35',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('39',plain,(
    ! [X15: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('40',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relat_1 @ X18 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('41',plain,(
    ! [X45: $i] :
      ( ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X45 ) @ ( k2_relat_1 @ X45 ) ) ) )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('42',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['37','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('53',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('54',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['49','54','55','56'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('58',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v4_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k1_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['32','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['52','53'])).

thf('62',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['31','63'])).

thf('65',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['35','36'])).

thf('66',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['52','53'])).

thf('67',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    r1_tarski @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['64','65','66','67','68'])).

thf('70',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('71',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['35','36'])).

thf('72',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relat_1 @ X18 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('73',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X11 ) @ X12 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X12 ) @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('74',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('75',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X11 ) @ X12 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X12 ) @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k2_funct_1 @ sk_C ) )
        = ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['71','76'])).

thf('78',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['52','53'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k2_funct_1 @ sk_C ) )
        = ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['77','78','79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k2_funct_1 @ sk_C ) )
        = ( k2_funct_1 @ sk_C ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','81'])).

thf('83',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['52','53'])).

thf('84',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k2_funct_1 @ sk_C ) )
        = ( k2_funct_1 @ sk_C ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['69','85'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('87',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) @ X10 )
        = ( k5_relat_1 @ X9 @ ( k5_relat_1 @ X8 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X37: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('93',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['88','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['30','94'])).

thf('96',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['52','53'])).

thf('97',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['29','98'])).

thf('100',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['35','36'])).

thf('101',plain,(
    ! [X37: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('102',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k6_partfun1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v4_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k1_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k6_partfun1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('107',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k6_partfun1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X11 ) @ X12 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X12 ) @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['52','53'])).

thf('113',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['52','53'])).

thf('116',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['99','100','111','112','113','114','115'])).

thf('117',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) @ X10 )
        = ( k5_relat_1 @ X9 @ ( k5_relat_1 @ X8 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['52','53'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','120'])).

thf('122',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['52','53'])).

thf('123',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['121','122','123'])).

thf('125',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['25','124'])).

thf('126',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('128',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v4_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k1_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('130',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('133',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('135',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['130','135'])).

thf('137',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X11 ) @ X12 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X12 ) @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('138',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = sk_D ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['133','134'])).

thf('140',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('142',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('144',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v4_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k1_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('146',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['52','53'])).

thf('148',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k1_relat_1 @ X18 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('150',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ( ( k5_relat_1 @ X13 @ ( k6_relat_1 @ X14 ) )
        = X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('151',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('152',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ( ( k5_relat_1 @ X13 @ ( k6_partfun1 @ X14 ) )
        = X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ X1 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['149','152'])).

thf('154',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['148','153'])).

thf('155',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['52','53'])).

thf('158',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['154','155','156','157'])).

thf('159',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['141','158'])).

thf('160',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['52','53'])).

thf('161',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['159','160','161'])).

thf('163',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['133','134'])).

thf('164',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['125','140','162','163'])).

thf('165',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['164','165'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Y80einkmV2
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:05:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.80/1.03  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.80/1.03  % Solved by: fo/fo7.sh
% 0.80/1.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.80/1.03  % done 1009 iterations in 0.570s
% 0.80/1.03  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.80/1.03  % SZS output start Refutation
% 0.80/1.03  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.80/1.03  thf(sk_A_type, type, sk_A: $i).
% 0.80/1.03  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.80/1.03  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.80/1.03  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.80/1.03  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.80/1.03  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.80/1.03  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.80/1.03  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.80/1.03  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.80/1.03  thf(sk_D_type, type, sk_D: $i).
% 0.80/1.03  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.80/1.03  thf(sk_C_type, type, sk_C: $i).
% 0.80/1.03  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.80/1.03  thf(sk_B_type, type, sk_B: $i).
% 0.80/1.03  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.80/1.03  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.80/1.03  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.80/1.03  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.80/1.03  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.80/1.03  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.80/1.03  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.80/1.03  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.80/1.03  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.80/1.03  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.80/1.03  thf(t36_funct_2, conjecture,
% 0.80/1.03    (![A:$i,B:$i,C:$i]:
% 0.80/1.03     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.80/1.03         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.80/1.03       ( ![D:$i]:
% 0.80/1.03         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.80/1.03             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.80/1.03           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.80/1.03               ( r2_relset_1 @
% 0.80/1.03                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.80/1.03                 ( k6_partfun1 @ A ) ) & 
% 0.80/1.03               ( v2_funct_1 @ C ) ) =>
% 0.80/1.03             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.80/1.03               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.80/1.03  thf(zf_stmt_0, negated_conjecture,
% 0.80/1.03    (~( ![A:$i,B:$i,C:$i]:
% 0.80/1.03        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.80/1.03            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.80/1.03          ( ![D:$i]:
% 0.80/1.03            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.80/1.03                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.80/1.03              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.80/1.03                  ( r2_relset_1 @
% 0.80/1.03                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.80/1.03                    ( k6_partfun1 @ A ) ) & 
% 0.80/1.03                  ( v2_funct_1 @ C ) ) =>
% 0.80/1.03                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.80/1.03                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.80/1.03    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.80/1.03  thf('0', plain,
% 0.80/1.03      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.80/1.03        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.80/1.03        (k6_partfun1 @ sk_A))),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('1', plain,
% 0.80/1.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('2', plain,
% 0.80/1.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf(redefinition_k1_partfun1, axiom,
% 0.80/1.03    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.80/1.03     ( ( ( v1_funct_1 @ E ) & 
% 0.80/1.03         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.80/1.03         ( v1_funct_1 @ F ) & 
% 0.80/1.03         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.80/1.03       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.80/1.03  thf('3', plain,
% 0.80/1.03      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.80/1.03         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.80/1.03          | ~ (v1_funct_1 @ X38)
% 0.80/1.03          | ~ (v1_funct_1 @ X41)
% 0.80/1.03          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 0.80/1.03          | ((k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41)
% 0.80/1.03              = (k5_relat_1 @ X38 @ X41)))),
% 0.80/1.03      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.80/1.03  thf('4', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.80/1.03         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.80/1.03            = (k5_relat_1 @ sk_C @ X0))
% 0.80/1.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.80/1.03          | ~ (v1_funct_1 @ X0)
% 0.80/1.03          | ~ (v1_funct_1 @ sk_C))),
% 0.80/1.03      inference('sup-', [status(thm)], ['2', '3'])).
% 0.80/1.03  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('6', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.80/1.03         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.80/1.03            = (k5_relat_1 @ sk_C @ X0))
% 0.80/1.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.80/1.03          | ~ (v1_funct_1 @ X0))),
% 0.80/1.03      inference('demod', [status(thm)], ['4', '5'])).
% 0.80/1.03  thf('7', plain,
% 0.80/1.03      ((~ (v1_funct_1 @ sk_D)
% 0.80/1.03        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.80/1.03            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['1', '6'])).
% 0.80/1.03  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('9', plain,
% 0.80/1.03      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.80/1.03         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.80/1.03      inference('demod', [status(thm)], ['7', '8'])).
% 0.80/1.03  thf('10', plain,
% 0.80/1.03      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.80/1.03        (k6_partfun1 @ sk_A))),
% 0.80/1.03      inference('demod', [status(thm)], ['0', '9'])).
% 0.80/1.03  thf('11', plain,
% 0.80/1.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('12', plain,
% 0.80/1.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf(dt_k1_partfun1, axiom,
% 0.80/1.03    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.80/1.03     ( ( ( v1_funct_1 @ E ) & 
% 0.80/1.03         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.80/1.03         ( v1_funct_1 @ F ) & 
% 0.80/1.03         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.80/1.03       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.80/1.03         ( m1_subset_1 @
% 0.80/1.03           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.80/1.03           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.80/1.03  thf('13', plain,
% 0.80/1.03      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.80/1.03         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.80/1.03          | ~ (v1_funct_1 @ X30)
% 0.80/1.03          | ~ (v1_funct_1 @ X33)
% 0.80/1.03          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.80/1.03          | (m1_subset_1 @ (k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33) @ 
% 0.80/1.03             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X35))))),
% 0.80/1.03      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.80/1.03  thf('14', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.80/1.03         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.80/1.03           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.80/1.03          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.80/1.03          | ~ (v1_funct_1 @ X1)
% 0.80/1.03          | ~ (v1_funct_1 @ sk_C))),
% 0.80/1.03      inference('sup-', [status(thm)], ['12', '13'])).
% 0.80/1.03  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('16', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.80/1.03         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.80/1.03           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.80/1.03          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.80/1.03          | ~ (v1_funct_1 @ X1))),
% 0.80/1.03      inference('demod', [status(thm)], ['14', '15'])).
% 0.80/1.03  thf('17', plain,
% 0.80/1.03      ((~ (v1_funct_1 @ sk_D)
% 0.80/1.03        | (m1_subset_1 @ 
% 0.80/1.03           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.80/1.03           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.80/1.03      inference('sup-', [status(thm)], ['11', '16'])).
% 0.80/1.03  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('19', plain,
% 0.80/1.03      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.80/1.03         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.80/1.03      inference('demod', [status(thm)], ['7', '8'])).
% 0.80/1.03  thf('20', plain,
% 0.80/1.03      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.80/1.03        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.80/1.03      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.80/1.03  thf(redefinition_r2_relset_1, axiom,
% 0.80/1.03    (![A:$i,B:$i,C:$i,D:$i]:
% 0.80/1.03     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.80/1.03         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.80/1.03       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.80/1.03  thf('21', plain,
% 0.80/1.03      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.80/1.03         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.80/1.03          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.80/1.03          | ((X26) = (X29))
% 0.80/1.03          | ~ (r2_relset_1 @ X27 @ X28 @ X26 @ X29))),
% 0.80/1.03      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.80/1.03  thf('22', plain,
% 0.80/1.03      (![X0 : $i]:
% 0.80/1.03         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 0.80/1.03          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 0.80/1.03          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.80/1.03      inference('sup-', [status(thm)], ['20', '21'])).
% 0.80/1.03  thf('23', plain,
% 0.80/1.03      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.80/1.03           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.80/1.03        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['10', '22'])).
% 0.80/1.03  thf(dt_k6_partfun1, axiom,
% 0.80/1.03    (![A:$i]:
% 0.80/1.03     ( ( m1_subset_1 @
% 0.80/1.03         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.80/1.03       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.80/1.03  thf('24', plain,
% 0.80/1.03      (![X37 : $i]:
% 0.80/1.03         (m1_subset_1 @ (k6_partfun1 @ X37) @ 
% 0.80/1.03          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))),
% 0.80/1.03      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.80/1.03  thf('25', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.80/1.03      inference('demod', [status(thm)], ['23', '24'])).
% 0.80/1.03  thf(dt_k2_funct_1, axiom,
% 0.80/1.03    (![A:$i]:
% 0.80/1.03     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.80/1.03       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.80/1.03         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.80/1.03  thf('26', plain,
% 0.80/1.03      (![X15 : $i]:
% 0.80/1.03         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 0.80/1.03          | ~ (v1_funct_1 @ X15)
% 0.80/1.03          | ~ (v1_relat_1 @ X15))),
% 0.80/1.03      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.80/1.03  thf(t61_funct_1, axiom,
% 0.80/1.03    (![A:$i]:
% 0.80/1.03     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.80/1.03       ( ( v2_funct_1 @ A ) =>
% 0.80/1.03         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.80/1.03             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.80/1.03           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.80/1.03             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.80/1.03  thf('27', plain,
% 0.80/1.03      (![X19 : $i]:
% 0.80/1.03         (~ (v2_funct_1 @ X19)
% 0.80/1.03          | ((k5_relat_1 @ (k2_funct_1 @ X19) @ X19)
% 0.80/1.03              = (k6_relat_1 @ (k2_relat_1 @ X19)))
% 0.80/1.03          | ~ (v1_funct_1 @ X19)
% 0.80/1.03          | ~ (v1_relat_1 @ X19))),
% 0.80/1.03      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.80/1.03  thf(redefinition_k6_partfun1, axiom,
% 0.80/1.03    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.80/1.03  thf('28', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 0.80/1.03      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.80/1.03  thf('29', plain,
% 0.80/1.03      (![X19 : $i]:
% 0.80/1.03         (~ (v2_funct_1 @ X19)
% 0.80/1.03          | ((k5_relat_1 @ (k2_funct_1 @ X19) @ X19)
% 0.80/1.03              = (k6_partfun1 @ (k2_relat_1 @ X19)))
% 0.80/1.03          | ~ (v1_funct_1 @ X19)
% 0.80/1.03          | ~ (v1_relat_1 @ X19))),
% 0.80/1.03      inference('demod', [status(thm)], ['27', '28'])).
% 0.80/1.03  thf('30', plain,
% 0.80/1.03      (![X15 : $i]:
% 0.80/1.03         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 0.80/1.03          | ~ (v1_funct_1 @ X15)
% 0.80/1.03          | ~ (v1_relat_1 @ X15))),
% 0.80/1.03      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.80/1.03  thf(t55_funct_1, axiom,
% 0.80/1.03    (![A:$i]:
% 0.80/1.03     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.80/1.03       ( ( v2_funct_1 @ A ) =>
% 0.80/1.03         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.80/1.03           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.80/1.03  thf('31', plain,
% 0.80/1.03      (![X18 : $i]:
% 0.80/1.03         (~ (v2_funct_1 @ X18)
% 0.80/1.03          | ((k2_relat_1 @ X18) = (k1_relat_1 @ (k2_funct_1 @ X18)))
% 0.80/1.03          | ~ (v1_funct_1 @ X18)
% 0.80/1.03          | ~ (v1_relat_1 @ X18))),
% 0.80/1.03      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.80/1.03  thf('32', plain,
% 0.80/1.03      (![X15 : $i]:
% 0.80/1.03         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 0.80/1.03          | ~ (v1_funct_1 @ X15)
% 0.80/1.03          | ~ (v1_relat_1 @ X15))),
% 0.80/1.03      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.80/1.03  thf('33', plain,
% 0.80/1.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf(redefinition_k2_relset_1, axiom,
% 0.80/1.03    (![A:$i,B:$i,C:$i]:
% 0.80/1.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.80/1.03       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.80/1.03  thf('34', plain,
% 0.80/1.03      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.80/1.03         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 0.80/1.03          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.80/1.03      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.80/1.03  thf('35', plain,
% 0.80/1.03      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.80/1.03      inference('sup-', [status(thm)], ['33', '34'])).
% 0.80/1.03  thf('36', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('37', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.80/1.03      inference('sup+', [status(thm)], ['35', '36'])).
% 0.80/1.03  thf('38', plain,
% 0.80/1.03      (![X15 : $i]:
% 0.80/1.03         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 0.80/1.03          | ~ (v1_funct_1 @ X15)
% 0.80/1.03          | ~ (v1_relat_1 @ X15))),
% 0.80/1.03      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.80/1.03  thf('39', plain,
% 0.80/1.03      (![X15 : $i]:
% 0.80/1.03         ((v1_funct_1 @ (k2_funct_1 @ X15))
% 0.80/1.03          | ~ (v1_funct_1 @ X15)
% 0.80/1.03          | ~ (v1_relat_1 @ X15))),
% 0.80/1.03      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.80/1.03  thf('40', plain,
% 0.80/1.03      (![X18 : $i]:
% 0.80/1.03         (~ (v2_funct_1 @ X18)
% 0.80/1.03          | ((k2_relat_1 @ X18) = (k1_relat_1 @ (k2_funct_1 @ X18)))
% 0.80/1.03          | ~ (v1_funct_1 @ X18)
% 0.80/1.03          | ~ (v1_relat_1 @ X18))),
% 0.80/1.03      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.80/1.03  thf(t3_funct_2, axiom,
% 0.80/1.03    (![A:$i]:
% 0.80/1.03     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.80/1.03       ( ( v1_funct_1 @ A ) & 
% 0.80/1.03         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.80/1.03         ( m1_subset_1 @
% 0.80/1.03           A @ 
% 0.80/1.03           ( k1_zfmisc_1 @
% 0.80/1.03             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.80/1.03  thf('41', plain,
% 0.80/1.03      (![X45 : $i]:
% 0.80/1.03         ((m1_subset_1 @ X45 @ 
% 0.80/1.03           (k1_zfmisc_1 @ 
% 0.80/1.03            (k2_zfmisc_1 @ (k1_relat_1 @ X45) @ (k2_relat_1 @ X45))))
% 0.80/1.03          | ~ (v1_funct_1 @ X45)
% 0.80/1.03          | ~ (v1_relat_1 @ X45))),
% 0.80/1.03      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.80/1.03  thf(cc2_relset_1, axiom,
% 0.80/1.03    (![A:$i,B:$i,C:$i]:
% 0.80/1.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.80/1.03       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.80/1.03  thf('42', plain,
% 0.80/1.03      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.80/1.03         ((v4_relat_1 @ X20 @ X21)
% 0.80/1.03          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.80/1.03      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.80/1.03  thf('43', plain,
% 0.80/1.03      (![X0 : $i]:
% 0.80/1.03         (~ (v1_relat_1 @ X0)
% 0.80/1.03          | ~ (v1_funct_1 @ X0)
% 0.80/1.03          | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['41', '42'])).
% 0.80/1.03  thf('44', plain,
% 0.80/1.03      (![X0 : $i]:
% 0.80/1.03         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.80/1.03          | ~ (v1_relat_1 @ X0)
% 0.80/1.03          | ~ (v1_funct_1 @ X0)
% 0.80/1.03          | ~ (v2_funct_1 @ X0)
% 0.80/1.03          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.80/1.03          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.80/1.03      inference('sup+', [status(thm)], ['40', '43'])).
% 0.80/1.03  thf('45', plain,
% 0.80/1.03      (![X0 : $i]:
% 0.80/1.03         (~ (v1_relat_1 @ X0)
% 0.80/1.03          | ~ (v1_funct_1 @ X0)
% 0.80/1.03          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.80/1.03          | ~ (v2_funct_1 @ X0)
% 0.80/1.03          | ~ (v1_funct_1 @ X0)
% 0.80/1.03          | ~ (v1_relat_1 @ X0)
% 0.80/1.03          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['39', '44'])).
% 0.80/1.03  thf('46', plain,
% 0.80/1.03      (![X0 : $i]:
% 0.80/1.03         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.80/1.03          | ~ (v2_funct_1 @ X0)
% 0.80/1.03          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.80/1.03          | ~ (v1_funct_1 @ X0)
% 0.80/1.03          | ~ (v1_relat_1 @ X0))),
% 0.80/1.03      inference('simplify', [status(thm)], ['45'])).
% 0.80/1.03  thf('47', plain,
% 0.80/1.03      (![X0 : $i]:
% 0.80/1.03         (~ (v1_relat_1 @ X0)
% 0.80/1.03          | ~ (v1_funct_1 @ X0)
% 0.80/1.03          | ~ (v1_relat_1 @ X0)
% 0.80/1.03          | ~ (v1_funct_1 @ X0)
% 0.80/1.03          | ~ (v2_funct_1 @ X0)
% 0.80/1.03          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['38', '46'])).
% 0.80/1.03  thf('48', plain,
% 0.80/1.03      (![X0 : $i]:
% 0.80/1.03         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.80/1.03          | ~ (v2_funct_1 @ X0)
% 0.80/1.03          | ~ (v1_funct_1 @ X0)
% 0.80/1.03          | ~ (v1_relat_1 @ X0))),
% 0.80/1.03      inference('simplify', [status(thm)], ['47'])).
% 0.80/1.03  thf('49', plain,
% 0.80/1.03      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)
% 0.80/1.03        | ~ (v1_relat_1 @ sk_C)
% 0.80/1.03        | ~ (v1_funct_1 @ sk_C)
% 0.80/1.03        | ~ (v2_funct_1 @ sk_C))),
% 0.80/1.03      inference('sup+', [status(thm)], ['37', '48'])).
% 0.80/1.03  thf('50', plain,
% 0.80/1.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf(cc2_relat_1, axiom,
% 0.80/1.03    (![A:$i]:
% 0.80/1.03     ( ( v1_relat_1 @ A ) =>
% 0.80/1.03       ( ![B:$i]:
% 0.80/1.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.80/1.03  thf('51', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.80/1.03          | (v1_relat_1 @ X0)
% 0.80/1.03          | ~ (v1_relat_1 @ X1))),
% 0.80/1.03      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.80/1.03  thf('52', plain,
% 0.80/1.03      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.80/1.03      inference('sup-', [status(thm)], ['50', '51'])).
% 0.80/1.03  thf(fc6_relat_1, axiom,
% 0.80/1.03    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.80/1.03  thf('53', plain,
% 0.80/1.03      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.80/1.03      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.80/1.03  thf('54', plain, ((v1_relat_1 @ sk_C)),
% 0.80/1.03      inference('demod', [status(thm)], ['52', '53'])).
% 0.80/1.03  thf('55', plain, ((v1_funct_1 @ sk_C)),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('56', plain, ((v2_funct_1 @ sk_C)),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('57', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)),
% 0.80/1.03      inference('demod', [status(thm)], ['49', '54', '55', '56'])).
% 0.80/1.03  thf(d18_relat_1, axiom,
% 0.80/1.03    (![A:$i,B:$i]:
% 0.80/1.03     ( ( v1_relat_1 @ B ) =>
% 0.80/1.03       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.80/1.03  thf('58', plain,
% 0.80/1.03      (![X2 : $i, X3 : $i]:
% 0.80/1.03         (~ (v4_relat_1 @ X2 @ X3)
% 0.80/1.03          | (r1_tarski @ (k1_relat_1 @ X2) @ X3)
% 0.80/1.03          | ~ (v1_relat_1 @ X2))),
% 0.80/1.03      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.80/1.03  thf('59', plain,
% 0.80/1.03      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.80/1.03        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 0.80/1.03      inference('sup-', [status(thm)], ['57', '58'])).
% 0.80/1.03  thf('60', plain,
% 0.80/1.03      ((~ (v1_relat_1 @ sk_C)
% 0.80/1.03        | ~ (v1_funct_1 @ sk_C)
% 0.80/1.03        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 0.80/1.03      inference('sup-', [status(thm)], ['32', '59'])).
% 0.80/1.03  thf('61', plain, ((v1_relat_1 @ sk_C)),
% 0.80/1.03      inference('demod', [status(thm)], ['52', '53'])).
% 0.80/1.03  thf('62', plain, ((v1_funct_1 @ sk_C)),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('63', plain, ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B)),
% 0.80/1.03      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.80/1.03  thf('64', plain,
% 0.80/1.03      (((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)
% 0.80/1.03        | ~ (v1_relat_1 @ sk_C)
% 0.80/1.03        | ~ (v1_funct_1 @ sk_C)
% 0.80/1.03        | ~ (v2_funct_1 @ sk_C))),
% 0.80/1.03      inference('sup+', [status(thm)], ['31', '63'])).
% 0.80/1.03  thf('65', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.80/1.03      inference('sup+', [status(thm)], ['35', '36'])).
% 0.80/1.03  thf('66', plain, ((v1_relat_1 @ sk_C)),
% 0.80/1.03      inference('demod', [status(thm)], ['52', '53'])).
% 0.80/1.03  thf('67', plain, ((v1_funct_1 @ sk_C)),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('68', plain, ((v2_funct_1 @ sk_C)),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('69', plain, ((r1_tarski @ sk_B @ sk_B)),
% 0.80/1.03      inference('demod', [status(thm)], ['64', '65', '66', '67', '68'])).
% 0.80/1.03  thf('70', plain,
% 0.80/1.03      (![X15 : $i]:
% 0.80/1.03         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 0.80/1.03          | ~ (v1_funct_1 @ X15)
% 0.80/1.03          | ~ (v1_relat_1 @ X15))),
% 0.80/1.03      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.80/1.03  thf('71', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.80/1.03      inference('sup+', [status(thm)], ['35', '36'])).
% 0.80/1.03  thf('72', plain,
% 0.80/1.03      (![X18 : $i]:
% 0.80/1.03         (~ (v2_funct_1 @ X18)
% 0.80/1.03          | ((k2_relat_1 @ X18) = (k1_relat_1 @ (k2_funct_1 @ X18)))
% 0.80/1.03          | ~ (v1_funct_1 @ X18)
% 0.80/1.03          | ~ (v1_relat_1 @ X18))),
% 0.80/1.03      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.80/1.03  thf(t77_relat_1, axiom,
% 0.80/1.03    (![A:$i,B:$i]:
% 0.80/1.03     ( ( v1_relat_1 @ B ) =>
% 0.80/1.03       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.80/1.03         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 0.80/1.03  thf('73', plain,
% 0.80/1.03      (![X11 : $i, X12 : $i]:
% 0.80/1.03         (~ (r1_tarski @ (k1_relat_1 @ X11) @ X12)
% 0.80/1.03          | ((k5_relat_1 @ (k6_relat_1 @ X12) @ X11) = (X11))
% 0.80/1.03          | ~ (v1_relat_1 @ X11))),
% 0.80/1.03      inference('cnf', [status(esa)], [t77_relat_1])).
% 0.80/1.03  thf('74', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 0.80/1.03      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.80/1.03  thf('75', plain,
% 0.80/1.03      (![X11 : $i, X12 : $i]:
% 0.80/1.03         (~ (r1_tarski @ (k1_relat_1 @ X11) @ X12)
% 0.80/1.03          | ((k5_relat_1 @ (k6_partfun1 @ X12) @ X11) = (X11))
% 0.80/1.03          | ~ (v1_relat_1 @ X11))),
% 0.80/1.03      inference('demod', [status(thm)], ['73', '74'])).
% 0.80/1.03  thf('76', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         (~ (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 0.80/1.03          | ~ (v1_relat_1 @ X0)
% 0.80/1.03          | ~ (v1_funct_1 @ X0)
% 0.80/1.03          | ~ (v2_funct_1 @ X0)
% 0.80/1.03          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.80/1.03          | ((k5_relat_1 @ (k6_partfun1 @ X1) @ (k2_funct_1 @ X0))
% 0.80/1.03              = (k2_funct_1 @ X0)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['72', '75'])).
% 0.80/1.03  thf('77', plain,
% 0.80/1.03      (![X0 : $i]:
% 0.80/1.03         (~ (r1_tarski @ sk_B @ X0)
% 0.80/1.03          | ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k2_funct_1 @ sk_C))
% 0.80/1.03              = (k2_funct_1 @ sk_C))
% 0.80/1.03          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.80/1.03          | ~ (v2_funct_1 @ sk_C)
% 0.80/1.03          | ~ (v1_funct_1 @ sk_C)
% 0.80/1.03          | ~ (v1_relat_1 @ sk_C))),
% 0.80/1.03      inference('sup-', [status(thm)], ['71', '76'])).
% 0.80/1.03  thf('78', plain, ((v2_funct_1 @ sk_C)),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('79', plain, ((v1_funct_1 @ sk_C)),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('80', plain, ((v1_relat_1 @ sk_C)),
% 0.80/1.03      inference('demod', [status(thm)], ['52', '53'])).
% 0.80/1.03  thf('81', plain,
% 0.80/1.03      (![X0 : $i]:
% 0.80/1.03         (~ (r1_tarski @ sk_B @ X0)
% 0.80/1.03          | ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k2_funct_1 @ sk_C))
% 0.80/1.03              = (k2_funct_1 @ sk_C))
% 0.80/1.03          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.80/1.03      inference('demod', [status(thm)], ['77', '78', '79', '80'])).
% 0.80/1.03  thf('82', plain,
% 0.80/1.03      (![X0 : $i]:
% 0.80/1.03         (~ (v1_relat_1 @ sk_C)
% 0.80/1.03          | ~ (v1_funct_1 @ sk_C)
% 0.80/1.03          | ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k2_funct_1 @ sk_C))
% 0.80/1.03              = (k2_funct_1 @ sk_C))
% 0.80/1.03          | ~ (r1_tarski @ sk_B @ X0))),
% 0.80/1.03      inference('sup-', [status(thm)], ['70', '81'])).
% 0.80/1.03  thf('83', plain, ((v1_relat_1 @ sk_C)),
% 0.80/1.03      inference('demod', [status(thm)], ['52', '53'])).
% 0.80/1.03  thf('84', plain, ((v1_funct_1 @ sk_C)),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('85', plain,
% 0.80/1.03      (![X0 : $i]:
% 0.80/1.03         (((k5_relat_1 @ (k6_partfun1 @ X0) @ (k2_funct_1 @ sk_C))
% 0.80/1.03            = (k2_funct_1 @ sk_C))
% 0.80/1.03          | ~ (r1_tarski @ sk_B @ X0))),
% 0.80/1.03      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.80/1.03  thf('86', plain,
% 0.80/1.03      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 0.80/1.03         = (k2_funct_1 @ sk_C))),
% 0.80/1.03      inference('sup-', [status(thm)], ['69', '85'])).
% 0.80/1.03  thf(t55_relat_1, axiom,
% 0.80/1.03    (![A:$i]:
% 0.80/1.03     ( ( v1_relat_1 @ A ) =>
% 0.80/1.03       ( ![B:$i]:
% 0.80/1.03         ( ( v1_relat_1 @ B ) =>
% 0.80/1.03           ( ![C:$i]:
% 0.80/1.03             ( ( v1_relat_1 @ C ) =>
% 0.80/1.03               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.80/1.03                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.80/1.03  thf('87', plain,
% 0.80/1.03      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.80/1.03         (~ (v1_relat_1 @ X8)
% 0.80/1.03          | ((k5_relat_1 @ (k5_relat_1 @ X9 @ X8) @ X10)
% 0.80/1.03              = (k5_relat_1 @ X9 @ (k5_relat_1 @ X8 @ X10)))
% 0.80/1.03          | ~ (v1_relat_1 @ X10)
% 0.80/1.03          | ~ (v1_relat_1 @ X9))),
% 0.80/1.03      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.80/1.03  thf('88', plain,
% 0.80/1.03      (![X0 : $i]:
% 0.80/1.03         (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 0.80/1.03            = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 0.80/1.03               (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)))
% 0.80/1.03          | ~ (v1_relat_1 @ (k6_partfun1 @ sk_B))
% 0.80/1.03          | ~ (v1_relat_1 @ X0)
% 0.80/1.03          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.80/1.03      inference('sup+', [status(thm)], ['86', '87'])).
% 0.80/1.03  thf('89', plain,
% 0.80/1.03      (![X37 : $i]:
% 0.80/1.03         (m1_subset_1 @ (k6_partfun1 @ X37) @ 
% 0.80/1.03          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))),
% 0.80/1.03      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.80/1.03  thf('90', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.80/1.03          | (v1_relat_1 @ X0)
% 0.80/1.03          | ~ (v1_relat_1 @ X1))),
% 0.80/1.03      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.80/1.03  thf('91', plain,
% 0.80/1.03      (![X0 : $i]:
% 0.80/1.03         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X0))
% 0.80/1.03          | (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['89', '90'])).
% 0.80/1.03  thf('92', plain,
% 0.80/1.03      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.80/1.03      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.80/1.03  thf('93', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 0.80/1.03      inference('demod', [status(thm)], ['91', '92'])).
% 0.80/1.03  thf('94', plain,
% 0.80/1.03      (![X0 : $i]:
% 0.80/1.03         (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 0.80/1.03            = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 0.80/1.03               (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)))
% 0.80/1.03          | ~ (v1_relat_1 @ X0)
% 0.80/1.03          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.80/1.03      inference('demod', [status(thm)], ['88', '93'])).
% 0.80/1.03  thf('95', plain,
% 0.80/1.03      (![X0 : $i]:
% 0.80/1.03         (~ (v1_relat_1 @ sk_C)
% 0.80/1.03          | ~ (v1_funct_1 @ sk_C)
% 0.80/1.03          | ~ (v1_relat_1 @ X0)
% 0.80/1.03          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 0.80/1.03              = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 0.80/1.03                 (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))))),
% 0.80/1.03      inference('sup-', [status(thm)], ['30', '94'])).
% 0.80/1.03  thf('96', plain, ((v1_relat_1 @ sk_C)),
% 0.80/1.03      inference('demod', [status(thm)], ['52', '53'])).
% 0.80/1.03  thf('97', plain, ((v1_funct_1 @ sk_C)),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('98', plain,
% 0.80/1.03      (![X0 : $i]:
% 0.80/1.03         (~ (v1_relat_1 @ X0)
% 0.80/1.03          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 0.80/1.03              = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 0.80/1.03                 (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))))),
% 0.80/1.03      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.80/1.03  thf('99', plain,
% 0.80/1.03      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.80/1.03          = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 0.80/1.03             (k6_partfun1 @ (k2_relat_1 @ sk_C))))
% 0.80/1.03        | ~ (v1_relat_1 @ sk_C)
% 0.80/1.03        | ~ (v1_funct_1 @ sk_C)
% 0.80/1.03        | ~ (v2_funct_1 @ sk_C)
% 0.80/1.03        | ~ (v1_relat_1 @ sk_C))),
% 0.80/1.03      inference('sup+', [status(thm)], ['29', '98'])).
% 0.80/1.03  thf('100', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.80/1.03      inference('sup+', [status(thm)], ['35', '36'])).
% 0.80/1.03  thf('101', plain,
% 0.80/1.03      (![X37 : $i]:
% 0.80/1.03         (m1_subset_1 @ (k6_partfun1 @ X37) @ 
% 0.80/1.03          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))),
% 0.80/1.03      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.80/1.03  thf('102', plain,
% 0.80/1.03      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.80/1.03         ((v4_relat_1 @ X20 @ X21)
% 0.80/1.03          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.80/1.03      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.80/1.03  thf('103', plain, (![X0 : $i]: (v4_relat_1 @ (k6_partfun1 @ X0) @ X0)),
% 0.80/1.03      inference('sup-', [status(thm)], ['101', '102'])).
% 0.80/1.03  thf('104', plain,
% 0.80/1.03      (![X2 : $i, X3 : $i]:
% 0.80/1.03         (~ (v4_relat_1 @ X2 @ X3)
% 0.80/1.03          | (r1_tarski @ (k1_relat_1 @ X2) @ X3)
% 0.80/1.03          | ~ (v1_relat_1 @ X2))),
% 0.80/1.03      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.80/1.03  thf('105', plain,
% 0.80/1.03      (![X0 : $i]:
% 0.80/1.03         (~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 0.80/1.03          | (r1_tarski @ (k1_relat_1 @ (k6_partfun1 @ X0)) @ X0))),
% 0.80/1.03      inference('sup-', [status(thm)], ['103', '104'])).
% 0.80/1.03  thf('106', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 0.80/1.03      inference('demod', [status(thm)], ['91', '92'])).
% 0.80/1.03  thf('107', plain,
% 0.80/1.03      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ (k6_partfun1 @ X0)) @ X0)),
% 0.80/1.03      inference('demod', [status(thm)], ['105', '106'])).
% 0.80/1.03  thf('108', plain,
% 0.80/1.03      (![X11 : $i, X12 : $i]:
% 0.80/1.03         (~ (r1_tarski @ (k1_relat_1 @ X11) @ X12)
% 0.80/1.03          | ((k5_relat_1 @ (k6_partfun1 @ X12) @ X11) = (X11))
% 0.80/1.03          | ~ (v1_relat_1 @ X11))),
% 0.80/1.03      inference('demod', [status(thm)], ['73', '74'])).
% 0.80/1.03  thf('109', plain,
% 0.80/1.03      (![X0 : $i]:
% 0.80/1.03         (~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 0.80/1.03          | ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 0.80/1.03              = (k6_partfun1 @ X0)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['107', '108'])).
% 0.80/1.03  thf('110', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 0.80/1.03      inference('demod', [status(thm)], ['91', '92'])).
% 0.80/1.03  thf('111', plain,
% 0.80/1.03      (![X0 : $i]:
% 0.80/1.03         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 0.80/1.03           = (k6_partfun1 @ X0))),
% 0.80/1.03      inference('demod', [status(thm)], ['109', '110'])).
% 0.80/1.03  thf('112', plain, ((v1_relat_1 @ sk_C)),
% 0.80/1.03      inference('demod', [status(thm)], ['52', '53'])).
% 0.80/1.03  thf('113', plain, ((v1_funct_1 @ sk_C)),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('114', plain, ((v2_funct_1 @ sk_C)),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('115', plain, ((v1_relat_1 @ sk_C)),
% 0.80/1.03      inference('demod', [status(thm)], ['52', '53'])).
% 0.80/1.03  thf('116', plain,
% 0.80/1.03      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 0.80/1.03      inference('demod', [status(thm)],
% 0.80/1.03                ['99', '100', '111', '112', '113', '114', '115'])).
% 0.80/1.03  thf('117', plain,
% 0.80/1.03      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.80/1.03         (~ (v1_relat_1 @ X8)
% 0.80/1.03          | ((k5_relat_1 @ (k5_relat_1 @ X9 @ X8) @ X10)
% 0.80/1.03              = (k5_relat_1 @ X9 @ (k5_relat_1 @ X8 @ X10)))
% 0.80/1.03          | ~ (v1_relat_1 @ X10)
% 0.80/1.03          | ~ (v1_relat_1 @ X9))),
% 0.80/1.03      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.80/1.03  thf('118', plain,
% 0.80/1.03      (![X0 : $i]:
% 0.80/1.03         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 0.80/1.03            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 0.80/1.03          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.80/1.03          | ~ (v1_relat_1 @ X0)
% 0.80/1.03          | ~ (v1_relat_1 @ sk_C))),
% 0.80/1.03      inference('sup+', [status(thm)], ['116', '117'])).
% 0.80/1.03  thf('119', plain, ((v1_relat_1 @ sk_C)),
% 0.80/1.03      inference('demod', [status(thm)], ['52', '53'])).
% 0.80/1.03  thf('120', plain,
% 0.80/1.03      (![X0 : $i]:
% 0.80/1.03         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 0.80/1.03            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 0.80/1.03          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.80/1.03          | ~ (v1_relat_1 @ X0))),
% 0.80/1.03      inference('demod', [status(thm)], ['118', '119'])).
% 0.80/1.03  thf('121', plain,
% 0.80/1.03      (![X0 : $i]:
% 0.80/1.03         (~ (v1_relat_1 @ sk_C)
% 0.80/1.03          | ~ (v1_funct_1 @ sk_C)
% 0.80/1.03          | ~ (v1_relat_1 @ X0)
% 0.80/1.03          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 0.80/1.03              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 0.80/1.03      inference('sup-', [status(thm)], ['26', '120'])).
% 0.80/1.03  thf('122', plain, ((v1_relat_1 @ sk_C)),
% 0.80/1.03      inference('demod', [status(thm)], ['52', '53'])).
% 0.80/1.03  thf('123', plain, ((v1_funct_1 @ sk_C)),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('124', plain,
% 0.80/1.03      (![X0 : $i]:
% 0.80/1.03         (~ (v1_relat_1 @ X0)
% 0.80/1.03          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 0.80/1.03              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 0.80/1.03      inference('demod', [status(thm)], ['121', '122', '123'])).
% 0.80/1.03  thf('125', plain,
% 0.80/1.03      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 0.80/1.03          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 0.80/1.03        | ~ (v1_relat_1 @ sk_D))),
% 0.80/1.03      inference('sup+', [status(thm)], ['25', '124'])).
% 0.80/1.03  thf('126', plain,
% 0.80/1.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('127', plain,
% 0.80/1.03      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.80/1.03         ((v4_relat_1 @ X20 @ X21)
% 0.80/1.03          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.80/1.03      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.80/1.03  thf('128', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 0.80/1.03      inference('sup-', [status(thm)], ['126', '127'])).
% 0.80/1.03  thf('129', plain,
% 0.80/1.03      (![X2 : $i, X3 : $i]:
% 0.80/1.03         (~ (v4_relat_1 @ X2 @ X3)
% 0.80/1.03          | (r1_tarski @ (k1_relat_1 @ X2) @ X3)
% 0.80/1.03          | ~ (v1_relat_1 @ X2))),
% 0.80/1.03      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.80/1.03  thf('130', plain,
% 0.80/1.03      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B))),
% 0.80/1.03      inference('sup-', [status(thm)], ['128', '129'])).
% 0.80/1.03  thf('131', plain,
% 0.80/1.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('132', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.80/1.03          | (v1_relat_1 @ X0)
% 0.80/1.03          | ~ (v1_relat_1 @ X1))),
% 0.80/1.03      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.80/1.03  thf('133', plain,
% 0.80/1.03      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.80/1.03      inference('sup-', [status(thm)], ['131', '132'])).
% 0.80/1.03  thf('134', plain,
% 0.80/1.03      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.80/1.03      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.80/1.03  thf('135', plain, ((v1_relat_1 @ sk_D)),
% 0.80/1.03      inference('demod', [status(thm)], ['133', '134'])).
% 0.80/1.03  thf('136', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B)),
% 0.80/1.03      inference('demod', [status(thm)], ['130', '135'])).
% 0.80/1.03  thf('137', plain,
% 0.80/1.03      (![X11 : $i, X12 : $i]:
% 0.80/1.03         (~ (r1_tarski @ (k1_relat_1 @ X11) @ X12)
% 0.80/1.03          | ((k5_relat_1 @ (k6_partfun1 @ X12) @ X11) = (X11))
% 0.80/1.03          | ~ (v1_relat_1 @ X11))),
% 0.80/1.03      inference('demod', [status(thm)], ['73', '74'])).
% 0.80/1.03  thf('138', plain,
% 0.80/1.03      ((~ (v1_relat_1 @ sk_D)
% 0.80/1.03        | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['136', '137'])).
% 0.80/1.03  thf('139', plain, ((v1_relat_1 @ sk_D)),
% 0.80/1.03      inference('demod', [status(thm)], ['133', '134'])).
% 0.80/1.03  thf('140', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))),
% 0.80/1.03      inference('demod', [status(thm)], ['138', '139'])).
% 0.80/1.03  thf('141', plain,
% 0.80/1.03      (![X15 : $i]:
% 0.80/1.03         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 0.80/1.03          | ~ (v1_funct_1 @ X15)
% 0.80/1.03          | ~ (v1_relat_1 @ X15))),
% 0.80/1.03      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.80/1.03  thf('142', plain,
% 0.80/1.03      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('143', plain,
% 0.80/1.03      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.80/1.03         ((v4_relat_1 @ X20 @ X21)
% 0.80/1.03          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.80/1.03      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.80/1.03  thf('144', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.80/1.03      inference('sup-', [status(thm)], ['142', '143'])).
% 0.80/1.03  thf('145', plain,
% 0.80/1.03      (![X2 : $i, X3 : $i]:
% 0.80/1.03         (~ (v4_relat_1 @ X2 @ X3)
% 0.80/1.03          | (r1_tarski @ (k1_relat_1 @ X2) @ X3)
% 0.80/1.03          | ~ (v1_relat_1 @ X2))),
% 0.80/1.03      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.80/1.03  thf('146', plain,
% 0.80/1.03      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 0.80/1.03      inference('sup-', [status(thm)], ['144', '145'])).
% 0.80/1.03  thf('147', plain, ((v1_relat_1 @ sk_C)),
% 0.80/1.03      inference('demod', [status(thm)], ['52', '53'])).
% 0.80/1.03  thf('148', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.80/1.03      inference('demod', [status(thm)], ['146', '147'])).
% 0.80/1.03  thf('149', plain,
% 0.80/1.03      (![X18 : $i]:
% 0.80/1.03         (~ (v2_funct_1 @ X18)
% 0.80/1.03          | ((k1_relat_1 @ X18) = (k2_relat_1 @ (k2_funct_1 @ X18)))
% 0.80/1.03          | ~ (v1_funct_1 @ X18)
% 0.80/1.03          | ~ (v1_relat_1 @ X18))),
% 0.80/1.03      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.80/1.03  thf(t79_relat_1, axiom,
% 0.80/1.03    (![A:$i,B:$i]:
% 0.80/1.03     ( ( v1_relat_1 @ B ) =>
% 0.80/1.03       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.80/1.03         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.80/1.03  thf('150', plain,
% 0.80/1.03      (![X13 : $i, X14 : $i]:
% 0.80/1.03         (~ (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 0.80/1.03          | ((k5_relat_1 @ X13 @ (k6_relat_1 @ X14)) = (X13))
% 0.80/1.03          | ~ (v1_relat_1 @ X13))),
% 0.80/1.03      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.80/1.03  thf('151', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 0.80/1.03      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.80/1.03  thf('152', plain,
% 0.80/1.03      (![X13 : $i, X14 : $i]:
% 0.80/1.03         (~ (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 0.80/1.03          | ((k5_relat_1 @ X13 @ (k6_partfun1 @ X14)) = (X13))
% 0.80/1.03          | ~ (v1_relat_1 @ X13))),
% 0.80/1.03      inference('demod', [status(thm)], ['150', '151'])).
% 0.80/1.03  thf('153', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.80/1.03          | ~ (v1_relat_1 @ X0)
% 0.80/1.03          | ~ (v1_funct_1 @ X0)
% 0.80/1.03          | ~ (v2_funct_1 @ X0)
% 0.80/1.03          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.80/1.03          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ X1))
% 0.80/1.03              = (k2_funct_1 @ X0)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['149', '152'])).
% 0.80/1.03  thf('154', plain,
% 0.80/1.03      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 0.80/1.03          = (k2_funct_1 @ sk_C))
% 0.80/1.03        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.80/1.03        | ~ (v2_funct_1 @ sk_C)
% 0.80/1.03        | ~ (v1_funct_1 @ sk_C)
% 0.80/1.03        | ~ (v1_relat_1 @ sk_C))),
% 0.80/1.03      inference('sup-', [status(thm)], ['148', '153'])).
% 0.80/1.03  thf('155', plain, ((v2_funct_1 @ sk_C)),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('156', plain, ((v1_funct_1 @ sk_C)),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('157', plain, ((v1_relat_1 @ sk_C)),
% 0.80/1.03      inference('demod', [status(thm)], ['52', '53'])).
% 0.80/1.03  thf('158', plain,
% 0.80/1.03      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 0.80/1.03          = (k2_funct_1 @ sk_C))
% 0.80/1.03        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.80/1.03      inference('demod', [status(thm)], ['154', '155', '156', '157'])).
% 0.80/1.03  thf('159', plain,
% 0.80/1.03      ((~ (v1_relat_1 @ sk_C)
% 0.80/1.03        | ~ (v1_funct_1 @ sk_C)
% 0.80/1.03        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 0.80/1.03            = (k2_funct_1 @ sk_C)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['141', '158'])).
% 0.80/1.03  thf('160', plain, ((v1_relat_1 @ sk_C)),
% 0.80/1.03      inference('demod', [status(thm)], ['52', '53'])).
% 0.80/1.03  thf('161', plain, ((v1_funct_1 @ sk_C)),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('162', plain,
% 0.80/1.03      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 0.80/1.03         = (k2_funct_1 @ sk_C))),
% 0.80/1.03      inference('demod', [status(thm)], ['159', '160', '161'])).
% 0.80/1.03  thf('163', plain, ((v1_relat_1 @ sk_D)),
% 0.80/1.03      inference('demod', [status(thm)], ['133', '134'])).
% 0.80/1.03  thf('164', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 0.80/1.03      inference('demod', [status(thm)], ['125', '140', '162', '163'])).
% 0.80/1.03  thf('165', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('166', plain, ($false),
% 0.80/1.03      inference('simplify_reflect-', [status(thm)], ['164', '165'])).
% 0.80/1.03  
% 0.80/1.03  % SZS output end Refutation
% 0.80/1.03  
% 0.87/1.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

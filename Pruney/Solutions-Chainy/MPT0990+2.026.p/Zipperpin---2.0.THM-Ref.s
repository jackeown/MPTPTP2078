%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kinHbzl6lb

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:58 EST 2020

% Result     : Theorem 6.66s
% Output     : Refutation 6.68s
% Verified   : 
% Statistics : Number of formulae       :  386 (2178 expanded)
%              Number of leaves         :   52 ( 652 expanded)
%              Depth                    :   58
%              Number of atoms          : 4179 (50889 expanded)
%              Number of equality atoms :  255 (3446 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('1',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
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

thf('2',plain,(
    r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('5',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( ( k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40 )
        = ( k5_relat_1 @ X37 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['2','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('15',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X32 @ X33 @ X35 @ X36 @ X31 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_A_1 ) ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('22',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_A_1 ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('23',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( X26 = X29 )
      | ~ ( r2_relset_1 @ X27 @ X28 @ X26 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_A_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_A_1 ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A_1 ) ) ),
    inference('sup-',[status(thm)],['12','24'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('26',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('27',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('28',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['25','28'])).

thf(t66_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( v2_funct_1 @ B ) )
           => ( ( k2_funct_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k5_relat_1 @ ( k2_funct_1 @ B ) @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('30',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ( ( k2_funct_1 @ ( k5_relat_1 @ X18 @ X17 ) )
        = ( k5_relat_1 @ ( k2_funct_1 @ X17 ) @ ( k2_funct_1 @ X18 ) ) )
      | ~ ( v2_funct_1 @ X17 )
      | ~ ( v2_funct_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t66_funct_1])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('32',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('33',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('37',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['33','34'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('38',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_relat_1 @ X13 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t47_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('39',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X4 @ X5 ) )
        = ( k2_relat_1 @ X5 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X5 ) @ ( k2_relat_1 @ X4 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ sk_C ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v2_funct_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('45',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('46',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ sk_C ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['41','42','43','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ sk_C ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['44','45'])).

thf('50',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ sk_C ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['35','51'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('53',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('54',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['44','45'])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
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

thf('57',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ( X57 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X58 )
      | ~ ( v1_funct_2 @ X58 @ X59 @ X57 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X57 ) ) )
      | ( ( k5_relat_1 @ X58 @ ( k2_funct_1 @ X58 ) )
        = ( k6_partfun1 @ X59 ) )
      | ~ ( v2_funct_1 @ X58 )
      | ( ( k2_relset_1 @ X59 @ X57 @ X58 )
       != X57 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('58',plain,
    ( ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A_1 ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_2 @ sk_C @ sk_A_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A_1 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','59','60','61','62'])).

thf('64',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A_1 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A_1 ) ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('67',plain,(
    ! [X7: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X7 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('68',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('69',plain,(
    ! [X7: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X7 ) )
      = X7 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( sk_A_1
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['52','54','55','66','69'])).

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

thf('71',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ( X14
        = ( k2_funct_1 @ X15 ) )
      | ( ( k5_relat_1 @ X14 @ X15 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X15 ) ) )
      | ( ( k2_relat_1 @ X14 )
       != ( k1_relat_1 @ X15 ) )
      | ~ ( v2_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('72',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('73',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ( X14
        = ( k2_funct_1 @ X15 ) )
      | ( ( k5_relat_1 @ X14 @ X15 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X15 ) ) )
      | ( ( k2_relat_1 @ X14 )
       != ( k1_relat_1 @ X15 ) )
      | ~ ( v2_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ sk_C ) )
       != ( k6_partfun1 @ sk_A_1 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['33','34'])).

thf('76',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('77',plain,(
    ! [X12: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('78',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('79',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_relat_1 @ X13 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('80',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('81',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('82',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k1_relat_1 @ X13 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('83',plain,(
    ! [X12: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('84',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('85',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('86',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X16 ) )
        = X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('87',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('88',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_relat_1 @ X13 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('89',plain,(
    ! [X8: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X8 ) ) @ X8 )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('90',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('91',plain,(
    ! [X8: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X8 ) ) @ X8 )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['88','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['87','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ X0 )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['86','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ X0 )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['85','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ X0 )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ X0 )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['84','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ X0 )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ X0 )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['83','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ X0 )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['82','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['81','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['80','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['79','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['78','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['77','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['76','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,
    ( ( v1_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['75','116'])).

thf('118',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['33','34'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('120',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['118','119'])).

thf('121',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['44','45'])).

thf('122',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['120','121','122','123'])).

thf('125',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['44','45'])).

thf('126',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['117','124','125','126','127'])).

thf('129',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['33','34'])).

thf('130',plain,(
    ! [X12: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('131',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('132',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('133',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_relat_1 @ X13 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('134',plain,(
    ! [X12: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('135',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('136',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('138',plain,(
    ! [X12: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['136','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['135','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['134','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['133','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['132','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['131','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['130','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,
    ( ( v2_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['129','152'])).

thf('154',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['120','121','122','123'])).

thf('155',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['44','45'])).

thf('156',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['153','154','155','156','157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ sk_C ) )
       != ( k6_partfun1 @ sk_A_1 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['74','128','158'])).

thf('160',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['33','34'])).

thf('161',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('162',plain,(
    ! [X12: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('163',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('164',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_relat_1 @ X13 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('165',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('166',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('167',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('168',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['166','169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['165','171'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['164','173'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['163','174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['175'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['162','176'])).

thf('178',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['161','178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['179'])).

thf('181',plain,
    ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['160','180'])).

thf('182',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['120','121','122','123'])).

thf('183',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['44','45'])).

thf('184',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['181','182','183','184','185'])).

thf('187',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('188',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_relat_1 @ X13 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('189',plain,(
    ! [X12: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('190',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('191',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A_1 ) ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

thf('192',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ( X14
        = ( k2_funct_1 @ X15 ) )
      | ( ( k5_relat_1 @ X14 @ X15 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X15 ) ) )
      | ( ( k2_relat_1 @ X14 )
       != ( k1_relat_1 @ X15 ) )
      | ~ ( v2_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('193',plain,
    ( ( ( k6_partfun1 @ sk_A_1 )
     != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['33','34'])).

thf('195',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['44','45'])).

thf('197',plain,
    ( ( ( k6_partfun1 @ sk_A_1 )
     != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( sk_B
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['193','194','195','196'])).

thf('198',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['117','124','125','126','127'])).

thf('199',plain,
    ( ( ( k6_partfun1 @ sk_A_1 )
     != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( sk_B
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['197','198'])).

thf('200',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_B
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k6_partfun1 @ sk_A_1 )
     != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['190','199'])).

thf('201',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['44','45'])).

thf('202',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,
    ( ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_B
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k6_partfun1 @ sk_A_1 )
     != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['200','201','202'])).

thf('204',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k6_partfun1 @ sk_A_1 )
     != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ( sk_B
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['189','203'])).

thf('205',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['44','45'])).

thf('206',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,
    ( ( ( k6_partfun1 @ sk_A_1 )
     != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ( sk_B
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['204','205','206','207'])).

thf('209',plain,
    ( sk_A_1
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['52','54','55','66','69'])).

thf('210',plain,
    ( ( ( k6_partfun1 @ sk_A_1 )
     != ( k6_partfun1 @ sk_A_1 ) )
    | ( sk_B
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['208','209'])).

thf('211',plain,
    ( ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_B
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['210'])).

thf('212',plain,
    ( ( sk_B
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['188','211'])).

thf('213',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['33','34'])).

thf('214',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['44','45'])).

thf('215',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,
    ( ( sk_B != sk_B )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['212','213','214','215','216'])).

thf('218',plain,
    ( sk_C
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['217'])).

thf('219',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k1_relat_1 @ X13 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('220',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['218','219'])).

thf('221',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['33','34'])).

thf('222',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['117','124','125','126','127'])).

thf('223',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['153','154','155','156','157'])).

thf('224',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_B )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['220','221','222','223'])).

thf('225',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['187','224'])).

thf('226',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['44','45'])).

thf('227',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = sk_B ),
    inference(demod,[status(thm)],['225','226','227'])).

thf('229',plain,
    ( sk_C
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['217'])).

thf('230',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ sk_C ) )
       != ( k6_partfun1 @ sk_A_1 ) )
      | ( ( k2_relat_1 @ X0 )
       != sk_B )
      | ( X0 = sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['159','186','228','229'])).

thf('231',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k5_relat_1 @ sk_C @ X0 ) )
       != ( k6_partfun1 @ sk_A_1 ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ X0 )
        = sk_C )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != sk_B ) ) ),
    inference('sup-',[status(thm)],['30','230'])).

thf('232',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['44','45'])).

thf('233',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k5_relat_1 @ sk_C @ X0 ) )
       != ( k6_partfun1 @ sk_A_1 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ X0 )
        = sk_C )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != sk_B ) ) ),
    inference(demod,[status(thm)],['231','232','233','234'])).

thf('236',plain,
    ( ( ( k2_funct_1 @ ( k6_partfun1 @ sk_A_1 ) )
     != ( k6_partfun1 @ sk_A_1 ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) )
     != sk_B )
    | ( ( k2_funct_1 @ sk_D )
      = sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['29','235'])).

thf(t67_funct_1,axiom,(
    ! [A: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('237',plain,(
    ! [X19: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ X19 ) )
      = ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_1])).

thf('238',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('239',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('240',plain,(
    ! [X19: $i] :
      ( ( k2_funct_1 @ ( k6_partfun1 @ X19 ) )
      = ( k6_partfun1 @ X19 ) ) ),
    inference(demod,[status(thm)],['237','238','239'])).

thf('241',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('243',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['241','242'])).

thf('244',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,
    ( ( ( k6_partfun1 @ sk_A_1 )
     != ( k6_partfun1 @ sk_A_1 ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) )
     != sk_B )
    | ( ( k2_funct_1 @ sk_D )
      = sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['236','240','243','244'])).

thf('246',plain,
    ( ~ ( v2_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_D ) )
    | ( ( k2_funct_1 @ sk_D )
      = sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) )
     != sk_B ) ),
    inference(simplify,[status(thm)],['245'])).

thf('247',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) )
     != sk_B )
    | ( ( k2_funct_1 @ sk_D )
      = sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['1','246'])).

thf('248',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['241','242'])).

thf('249',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('250',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) )
     != sk_B )
    | ( ( k2_funct_1 @ sk_D )
      = sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['247','248','249'])).

thf('251',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k2_funct_1 @ sk_D )
      = sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['0','250'])).

thf('252',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['241','242'])).

thf('253',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,
    ( ~ ( v2_funct_1 @ sk_D )
    | ( ( k2_funct_1 @ sk_D )
      = sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) )
     != sk_B ) ),
    inference(demod,[status(thm)],['251','252','253'])).

thf('255',plain,
    ( ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('256',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('257',plain,
    ( ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['255','256'])).

thf('258',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
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

thf('259',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_funct_2 @ X52 @ X53 @ X54 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X54 ) ) )
      | ( zip_tseitin_0 @ X52 @ X55 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X56 @ X53 @ X53 @ X54 @ X55 @ X52 ) )
      | ( zip_tseitin_1 @ X54 @ X53 )
      | ( ( k2_relset_1 @ X56 @ X53 @ X55 )
       != X53 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X53 ) ) )
      | ~ ( v1_funct_2 @ X55 @ X56 @ X53 )
      | ~ ( v1_funct_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('260',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A_1 @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A_1 @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A_1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['258','259'])).

thf('261',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A_1 @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A_1 @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['260','261','262'])).

thf('264',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A_1 ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A_1 @ sk_B )
    | ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['257','263'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('265',plain,(
    ! [X11: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('266',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('267',plain,(
    ! [X11: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X11 ) ) ),
    inference(demod,[status(thm)],['265','266'])).

thf('268',plain,
    ( ( k2_relset_1 @ sk_A_1 @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('269',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('270',plain,(
    v1_funct_2 @ sk_C @ sk_A_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('271',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('272',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A_1 @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['264','267','268','269','270','271'])).

thf('273',plain,
    ( ( zip_tseitin_1 @ sk_A_1 @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['272'])).

thf('274',plain,(
    ! [X50: $i,X51: $i] :
      ( ( X50 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('275',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['273','274'])).

thf('276',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('277',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['275','276'])).

thf('278',plain,(
    ! [X48: $i,X49: $i] :
      ( ( v2_funct_1 @ X49 )
      | ~ ( zip_tseitin_0 @ X49 @ X48 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('279',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['277','278'])).

thf('280',plain,
    ( ( ( k2_funct_1 @ sk_D )
      = sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) )
     != sk_B ) ),
    inference(demod,[status(thm)],['254','279'])).

thf('281',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('282',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ( X57 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X58 )
      | ~ ( v1_funct_2 @ X58 @ X59 @ X57 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X57 ) ) )
      | ( ( k5_relat_1 @ X58 @ ( k2_funct_1 @ X58 ) )
        = ( k6_partfun1 @ X59 ) )
      | ~ ( v2_funct_1 @ X58 )
      | ( ( k2_relset_1 @ X59 @ X57 @ X58 )
       != X57 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('283',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A_1 @ sk_D )
     != sk_A_1 )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A_1 )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['281','282'])).

thf('284',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('285',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('286',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['284','285'])).

thf('287',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('288',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('289',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A_1 )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_A_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['283','286','287','288'])).

thf('290',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('291',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A_1 )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['289','290'])).

thf('292',plain,
    ( ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('293',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B ) ) ),
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

thf('294',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( r2_relset_1 @ X45 @ X45 @ ( k1_partfun1 @ X45 @ X46 @ X46 @ X45 @ X44 @ X47 ) @ ( k6_partfun1 @ X45 ) )
      | ( ( k2_relset_1 @ X46 @ X45 @ X47 )
        = X45 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) )
      | ~ ( v1_funct_2 @ X47 @ X46 @ X45 )
      | ~ ( v1_funct_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('295',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A_1 @ X0 )
        = sk_A_1 )
      | ~ ( r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A_1 ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['293','294'])).

thf('296',plain,(
    v1_funct_2 @ sk_C @ sk_A_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('297',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('298',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A_1 @ X0 )
        = sk_A_1 )
      | ~ ( r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A_1 ) ) ) ),
    inference(demod,[status(thm)],['295','296','297'])).

thf('299',plain,
    ( ~ ( r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A_1 ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A_1 @ sk_D )
      = sk_A_1 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A_1 )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['292','298'])).

thf('300',plain,(
    r2_relset_1 @ sk_A_1 @ sk_A_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['2','11'])).

thf('301',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['284','285'])).

thf('302',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('303',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('304',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('305',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A_1 ),
    inference(demod,[status(thm)],['299','300','301','302','303','304'])).

thf('306',plain,
    ( ( sk_A_1 != sk_A_1 )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['291','305'])).

thf('307',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['306'])).

thf('308',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['277','278'])).

thf('309',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['307','308'])).

thf('310',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('311',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('312',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('313',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['311','312'])).

thf('314',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['313'])).

thf('315',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['310','314'])).

thf('316',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['315'])).

thf('317',plain,
    ( ( ( k2_relat_1 @ ( k6_partfun1 @ sk_B ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['309','316'])).

thf('318',plain,(
    ! [X7: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X7 ) )
      = X7 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('319',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['241','242'])).

thf('320',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('321',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['277','278'])).

thf('322',plain,
    ( sk_B
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['317','318','319','320','321'])).

thf('323',plain,
    ( ( ( k2_funct_1 @ sk_D )
      = sk_C )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['280','322'])).

thf('324',plain,
    ( ( k2_funct_1 @ sk_D )
    = sk_C ),
    inference(simplify,[status(thm)],['323'])).

thf('325',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X16 ) )
        = X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('326',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['324','325'])).

thf('327',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['241','242'])).

thf('328',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('329',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['277','278'])).

thf('330',plain,
    ( ( k2_funct_1 @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['326','327','328','329'])).

thf('331',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('332',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['330','331'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kinHbzl6lb
% 0.15/0.37  % Computer   : n021.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 16:28:34 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 6.66/6.84  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.66/6.84  % Solved by: fo/fo7.sh
% 6.66/6.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.66/6.84  % done 4264 iterations in 6.345s
% 6.66/6.84  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.66/6.84  % SZS output start Refutation
% 6.66/6.84  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.66/6.84  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 6.66/6.84  thf(sk_A_1_type, type, sk_A_1: $i).
% 6.66/6.84  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 6.66/6.84  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 6.66/6.84  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 6.66/6.84  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 6.66/6.84  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 6.66/6.84  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 6.66/6.84  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 6.66/6.84  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 6.66/6.84  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.66/6.84  thf(sk_C_type, type, sk_C: $i).
% 6.66/6.84  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 6.66/6.84  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 6.66/6.84  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.66/6.84  thf(sk_D_type, type, sk_D: $i).
% 6.66/6.84  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.66/6.84  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 6.66/6.84  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 6.66/6.84  thf(sk_B_type, type, sk_B: $i).
% 6.66/6.84  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 6.66/6.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.66/6.84  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 6.66/6.84  thf(dt_k2_funct_1, axiom,
% 6.66/6.84    (![A:$i]:
% 6.66/6.84     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.66/6.84       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 6.66/6.84         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 6.66/6.84  thf('0', plain,
% 6.66/6.84      (![X9 : $i]:
% 6.66/6.84         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 6.66/6.84          | ~ (v1_funct_1 @ X9)
% 6.66/6.84          | ~ (v1_relat_1 @ X9))),
% 6.66/6.84      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.66/6.84  thf('1', plain,
% 6.66/6.84      (![X9 : $i]:
% 6.66/6.84         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 6.66/6.84          | ~ (v1_funct_1 @ X9)
% 6.66/6.84          | ~ (v1_relat_1 @ X9))),
% 6.66/6.84      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.66/6.84  thf(t36_funct_2, conjecture,
% 6.66/6.84    (![A:$i,B:$i,C:$i]:
% 6.66/6.84     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.66/6.84         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.66/6.84       ( ![D:$i]:
% 6.66/6.84         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 6.66/6.84             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 6.66/6.84           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 6.66/6.84               ( r2_relset_1 @
% 6.66/6.84                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 6.66/6.84                 ( k6_partfun1 @ A ) ) & 
% 6.66/6.84               ( v2_funct_1 @ C ) ) =>
% 6.66/6.84             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 6.66/6.84               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 6.66/6.84  thf(zf_stmt_0, negated_conjecture,
% 6.66/6.84    (~( ![A:$i,B:$i,C:$i]:
% 6.66/6.84        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.66/6.84            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.66/6.84          ( ![D:$i]:
% 6.66/6.84            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 6.66/6.84                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 6.66/6.84              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 6.66/6.84                  ( r2_relset_1 @
% 6.66/6.84                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 6.66/6.84                    ( k6_partfun1 @ A ) ) & 
% 6.66/6.84                  ( v2_funct_1 @ C ) ) =>
% 6.66/6.84                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 6.66/6.84                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 6.66/6.84    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 6.66/6.84  thf('2', plain,
% 6.66/6.84      ((r2_relset_1 @ sk_A_1 @ sk_A_1 @ 
% 6.66/6.84        (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D) @ 
% 6.66/6.84        (k6_partfun1 @ sk_A_1))),
% 6.66/6.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.84  thf('3', plain,
% 6.66/6.84      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 6.66/6.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.84  thf('4', plain,
% 6.66/6.84      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 6.66/6.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.84  thf(redefinition_k1_partfun1, axiom,
% 6.66/6.84    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 6.66/6.84     ( ( ( v1_funct_1 @ E ) & 
% 6.66/6.84         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 6.66/6.84         ( v1_funct_1 @ F ) & 
% 6.66/6.84         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 6.66/6.84       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 6.66/6.84  thf('5', plain,
% 6.66/6.84      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 6.66/6.84         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 6.66/6.84          | ~ (v1_funct_1 @ X37)
% 6.66/6.84          | ~ (v1_funct_1 @ X40)
% 6.66/6.84          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 6.66/6.84          | ((k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40)
% 6.66/6.84              = (k5_relat_1 @ X37 @ X40)))),
% 6.66/6.84      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 6.66/6.84  thf('6', plain,
% 6.66/6.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.66/6.84         (((k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 6.66/6.84            = (k5_relat_1 @ sk_C @ X0))
% 6.66/6.84          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 6.66/6.84          | ~ (v1_funct_1 @ X0)
% 6.66/6.84          | ~ (v1_funct_1 @ sk_C))),
% 6.66/6.84      inference('sup-', [status(thm)], ['4', '5'])).
% 6.66/6.84  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 6.66/6.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.84  thf('8', plain,
% 6.66/6.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.66/6.84         (((k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 6.66/6.84            = (k5_relat_1 @ sk_C @ X0))
% 6.66/6.84          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 6.66/6.84          | ~ (v1_funct_1 @ X0))),
% 6.66/6.84      inference('demod', [status(thm)], ['6', '7'])).
% 6.66/6.84  thf('9', plain,
% 6.66/6.84      ((~ (v1_funct_1 @ sk_D)
% 6.66/6.84        | ((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 6.66/6.84            = (k5_relat_1 @ sk_C @ sk_D)))),
% 6.66/6.84      inference('sup-', [status(thm)], ['3', '8'])).
% 6.66/6.84  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 6.66/6.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.84  thf('11', plain,
% 6.66/6.84      (((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 6.66/6.84         = (k5_relat_1 @ sk_C @ sk_D))),
% 6.66/6.84      inference('demod', [status(thm)], ['9', '10'])).
% 6.66/6.84  thf('12', plain,
% 6.66/6.84      ((r2_relset_1 @ sk_A_1 @ sk_A_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 6.66/6.84        (k6_partfun1 @ sk_A_1))),
% 6.66/6.84      inference('demod', [status(thm)], ['2', '11'])).
% 6.66/6.84  thf('13', plain,
% 6.66/6.84      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 6.66/6.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.84  thf('14', plain,
% 6.66/6.84      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 6.66/6.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.84  thf(dt_k1_partfun1, axiom,
% 6.66/6.84    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 6.66/6.84     ( ( ( v1_funct_1 @ E ) & 
% 6.66/6.84         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 6.66/6.84         ( v1_funct_1 @ F ) & 
% 6.66/6.84         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 6.66/6.84       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 6.66/6.84         ( m1_subset_1 @
% 6.66/6.84           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 6.66/6.84           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 6.66/6.84  thf('15', plain,
% 6.66/6.84      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 6.66/6.84         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 6.66/6.84          | ~ (v1_funct_1 @ X31)
% 6.66/6.84          | ~ (v1_funct_1 @ X34)
% 6.66/6.84          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 6.66/6.84          | (m1_subset_1 @ (k1_partfun1 @ X32 @ X33 @ X35 @ X36 @ X31 @ X34) @ 
% 6.66/6.84             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X36))))),
% 6.66/6.84      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 6.66/6.84  thf('16', plain,
% 6.66/6.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.66/6.84         ((m1_subset_1 @ (k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 6.66/6.84           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ X0)))
% 6.66/6.84          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 6.66/6.84          | ~ (v1_funct_1 @ X1)
% 6.66/6.84          | ~ (v1_funct_1 @ sk_C))),
% 6.66/6.84      inference('sup-', [status(thm)], ['14', '15'])).
% 6.66/6.84  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 6.66/6.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.84  thf('18', plain,
% 6.66/6.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.66/6.84         ((m1_subset_1 @ (k1_partfun1 @ sk_A_1 @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 6.66/6.84           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ X0)))
% 6.66/6.84          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 6.66/6.84          | ~ (v1_funct_1 @ X1))),
% 6.66/6.84      inference('demod', [status(thm)], ['16', '17'])).
% 6.66/6.84  thf('19', plain,
% 6.66/6.84      ((~ (v1_funct_1 @ sk_D)
% 6.66/6.84        | (m1_subset_1 @ 
% 6.66/6.84           (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D) @ 
% 6.66/6.84           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_A_1))))),
% 6.66/6.84      inference('sup-', [status(thm)], ['13', '18'])).
% 6.66/6.84  thf('20', plain, ((v1_funct_1 @ sk_D)),
% 6.66/6.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.84  thf('21', plain,
% 6.66/6.84      (((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 6.66/6.84         = (k5_relat_1 @ sk_C @ sk_D))),
% 6.66/6.84      inference('demod', [status(thm)], ['9', '10'])).
% 6.66/6.84  thf('22', plain,
% 6.66/6.84      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 6.66/6.84        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_A_1)))),
% 6.66/6.84      inference('demod', [status(thm)], ['19', '20', '21'])).
% 6.66/6.84  thf(redefinition_r2_relset_1, axiom,
% 6.66/6.84    (![A:$i,B:$i,C:$i,D:$i]:
% 6.66/6.84     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 6.66/6.84         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.66/6.84       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 6.66/6.84  thf('23', plain,
% 6.66/6.84      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 6.66/6.84         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 6.66/6.84          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 6.66/6.84          | ((X26) = (X29))
% 6.66/6.84          | ~ (r2_relset_1 @ X27 @ X28 @ X26 @ X29))),
% 6.66/6.84      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 6.66/6.84  thf('24', plain,
% 6.66/6.84      (![X0 : $i]:
% 6.66/6.84         (~ (r2_relset_1 @ sk_A_1 @ sk_A_1 @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 6.66/6.84          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 6.66/6.84          | ~ (m1_subset_1 @ X0 @ 
% 6.66/6.84               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_A_1))))),
% 6.66/6.84      inference('sup-', [status(thm)], ['22', '23'])).
% 6.66/6.84  thf('25', plain,
% 6.66/6.84      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A_1) @ 
% 6.66/6.84           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_A_1)))
% 6.66/6.84        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A_1)))),
% 6.66/6.84      inference('sup-', [status(thm)], ['12', '24'])).
% 6.66/6.84  thf(t29_relset_1, axiom,
% 6.66/6.84    (![A:$i]:
% 6.66/6.84     ( m1_subset_1 @
% 6.66/6.84       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 6.66/6.84  thf('26', plain,
% 6.66/6.84      (![X30 : $i]:
% 6.66/6.84         (m1_subset_1 @ (k6_relat_1 @ X30) @ 
% 6.66/6.84          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))),
% 6.66/6.84      inference('cnf', [status(esa)], [t29_relset_1])).
% 6.66/6.84  thf(redefinition_k6_partfun1, axiom,
% 6.66/6.84    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 6.66/6.84  thf('27', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 6.66/6.84      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 6.66/6.84  thf('28', plain,
% 6.66/6.84      (![X30 : $i]:
% 6.66/6.84         (m1_subset_1 @ (k6_partfun1 @ X30) @ 
% 6.66/6.84          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))),
% 6.66/6.84      inference('demod', [status(thm)], ['26', '27'])).
% 6.66/6.84  thf('29', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A_1))),
% 6.66/6.84      inference('demod', [status(thm)], ['25', '28'])).
% 6.66/6.84  thf(t66_funct_1, axiom,
% 6.66/6.84    (![A:$i]:
% 6.66/6.84     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.66/6.84       ( ![B:$i]:
% 6.66/6.84         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 6.66/6.84           ( ( ( v2_funct_1 @ A ) & ( v2_funct_1 @ B ) ) =>
% 6.66/6.84             ( ( k2_funct_1 @ ( k5_relat_1 @ A @ B ) ) =
% 6.66/6.84               ( k5_relat_1 @ ( k2_funct_1 @ B ) @ ( k2_funct_1 @ A ) ) ) ) ) ) ))).
% 6.66/6.84  thf('30', plain,
% 6.66/6.84      (![X17 : $i, X18 : $i]:
% 6.66/6.84         (~ (v1_relat_1 @ X17)
% 6.66/6.84          | ~ (v1_funct_1 @ X17)
% 6.66/6.84          | ((k2_funct_1 @ (k5_relat_1 @ X18 @ X17))
% 6.66/6.84              = (k5_relat_1 @ (k2_funct_1 @ X17) @ (k2_funct_1 @ X18)))
% 6.66/6.84          | ~ (v2_funct_1 @ X17)
% 6.66/6.84          | ~ (v2_funct_1 @ X18)
% 6.66/6.84          | ~ (v1_funct_1 @ X18)
% 6.66/6.84          | ~ (v1_relat_1 @ X18))),
% 6.66/6.84      inference('cnf', [status(esa)], [t66_funct_1])).
% 6.66/6.84  thf('31', plain,
% 6.66/6.84      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 6.66/6.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.84  thf(redefinition_k2_relset_1, axiom,
% 6.66/6.84    (![A:$i,B:$i,C:$i]:
% 6.66/6.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.66/6.84       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 6.66/6.84  thf('32', plain,
% 6.66/6.84      (![X23 : $i, X24 : $i, X25 : $i]:
% 6.66/6.84         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 6.66/6.84          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 6.66/6.84      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 6.66/6.84  thf('33', plain,
% 6.66/6.84      (((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 6.66/6.84      inference('sup-', [status(thm)], ['31', '32'])).
% 6.66/6.84  thf('34', plain, (((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) = (sk_B))),
% 6.66/6.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.84  thf('35', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 6.66/6.84      inference('sup+', [status(thm)], ['33', '34'])).
% 6.66/6.84  thf('36', plain,
% 6.66/6.84      (![X9 : $i]:
% 6.66/6.84         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 6.66/6.84          | ~ (v1_funct_1 @ X9)
% 6.66/6.84          | ~ (v1_relat_1 @ X9))),
% 6.66/6.84      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.66/6.84  thf('37', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 6.66/6.84      inference('sup+', [status(thm)], ['33', '34'])).
% 6.66/6.84  thf(t55_funct_1, axiom,
% 6.66/6.84    (![A:$i]:
% 6.66/6.84     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.66/6.84       ( ( v2_funct_1 @ A ) =>
% 6.66/6.84         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 6.66/6.84           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 6.66/6.84  thf('38', plain,
% 6.66/6.84      (![X13 : $i]:
% 6.66/6.84         (~ (v2_funct_1 @ X13)
% 6.66/6.84          | ((k2_relat_1 @ X13) = (k1_relat_1 @ (k2_funct_1 @ X13)))
% 6.66/6.84          | ~ (v1_funct_1 @ X13)
% 6.66/6.84          | ~ (v1_relat_1 @ X13))),
% 6.66/6.84      inference('cnf', [status(esa)], [t55_funct_1])).
% 6.66/6.84  thf(t47_relat_1, axiom,
% 6.66/6.84    (![A:$i]:
% 6.66/6.84     ( ( v1_relat_1 @ A ) =>
% 6.66/6.84       ( ![B:$i]:
% 6.66/6.84         ( ( v1_relat_1 @ B ) =>
% 6.66/6.84           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 6.66/6.84             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 6.66/6.84  thf('39', plain,
% 6.66/6.84      (![X4 : $i, X5 : $i]:
% 6.66/6.84         (~ (v1_relat_1 @ X4)
% 6.66/6.84          | ((k2_relat_1 @ (k5_relat_1 @ X4 @ X5)) = (k2_relat_1 @ X5))
% 6.66/6.84          | ~ (r1_tarski @ (k1_relat_1 @ X5) @ (k2_relat_1 @ X4))
% 6.66/6.84          | ~ (v1_relat_1 @ X5))),
% 6.66/6.84      inference('cnf', [status(esa)], [t47_relat_1])).
% 6.66/6.84  thf('40', plain,
% 6.66/6.84      (![X0 : $i, X1 : $i]:
% 6.66/6.84         (~ (r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X1))
% 6.66/6.84          | ~ (v1_relat_1 @ X0)
% 6.66/6.84          | ~ (v1_funct_1 @ X0)
% 6.66/6.84          | ~ (v2_funct_1 @ X0)
% 6.66/6.84          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.66/6.84          | ((k2_relat_1 @ (k5_relat_1 @ X1 @ (k2_funct_1 @ X0)))
% 6.66/6.84              = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 6.66/6.84          | ~ (v1_relat_1 @ X1))),
% 6.66/6.84      inference('sup-', [status(thm)], ['38', '39'])).
% 6.66/6.84  thf('41', plain,
% 6.66/6.84      (![X0 : $i]:
% 6.66/6.84         (~ (r1_tarski @ sk_B @ (k2_relat_1 @ X0))
% 6.66/6.84          | ~ (v1_relat_1 @ X0)
% 6.66/6.84          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ sk_C)))
% 6.66/6.84              = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 6.66/6.84          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 6.66/6.84          | ~ (v2_funct_1 @ sk_C)
% 6.66/6.84          | ~ (v1_funct_1 @ sk_C)
% 6.66/6.84          | ~ (v1_relat_1 @ sk_C))),
% 6.66/6.84      inference('sup-', [status(thm)], ['37', '40'])).
% 6.66/6.84  thf('42', plain, ((v2_funct_1 @ sk_C)),
% 6.66/6.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.84  thf('43', plain, ((v1_funct_1 @ sk_C)),
% 6.66/6.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.84  thf('44', plain,
% 6.66/6.84      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 6.66/6.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.84  thf(cc1_relset_1, axiom,
% 6.66/6.84    (![A:$i,B:$i,C:$i]:
% 6.66/6.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.66/6.84       ( v1_relat_1 @ C ) ))).
% 6.66/6.84  thf('45', plain,
% 6.66/6.84      (![X20 : $i, X21 : $i, X22 : $i]:
% 6.66/6.84         ((v1_relat_1 @ X20)
% 6.66/6.84          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 6.66/6.84      inference('cnf', [status(esa)], [cc1_relset_1])).
% 6.66/6.84  thf('46', plain, ((v1_relat_1 @ sk_C)),
% 6.66/6.84      inference('sup-', [status(thm)], ['44', '45'])).
% 6.66/6.84  thf('47', plain,
% 6.66/6.84      (![X0 : $i]:
% 6.66/6.84         (~ (r1_tarski @ sk_B @ (k2_relat_1 @ X0))
% 6.66/6.84          | ~ (v1_relat_1 @ X0)
% 6.66/6.84          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ sk_C)))
% 6.66/6.84              = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 6.66/6.84          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 6.66/6.84      inference('demod', [status(thm)], ['41', '42', '43', '46'])).
% 6.66/6.84  thf('48', plain,
% 6.66/6.84      (![X0 : $i]:
% 6.66/6.84         (~ (v1_relat_1 @ sk_C)
% 6.66/6.84          | ~ (v1_funct_1 @ sk_C)
% 6.66/6.84          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ sk_C)))
% 6.66/6.84              = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 6.66/6.84          | ~ (v1_relat_1 @ X0)
% 6.66/6.84          | ~ (r1_tarski @ sk_B @ (k2_relat_1 @ X0)))),
% 6.66/6.84      inference('sup-', [status(thm)], ['36', '47'])).
% 6.66/6.84  thf('49', plain, ((v1_relat_1 @ sk_C)),
% 6.66/6.84      inference('sup-', [status(thm)], ['44', '45'])).
% 6.66/6.84  thf('50', plain, ((v1_funct_1 @ sk_C)),
% 6.66/6.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.84  thf('51', plain,
% 6.66/6.84      (![X0 : $i]:
% 6.66/6.84         (((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ sk_C)))
% 6.66/6.84            = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 6.66/6.84          | ~ (v1_relat_1 @ X0)
% 6.66/6.84          | ~ (r1_tarski @ sk_B @ (k2_relat_1 @ X0)))),
% 6.66/6.84      inference('demod', [status(thm)], ['48', '49', '50'])).
% 6.66/6.84  thf('52', plain,
% 6.66/6.84      ((~ (r1_tarski @ sk_B @ sk_B)
% 6.66/6.84        | ~ (v1_relat_1 @ sk_C)
% 6.66/6.84        | ((k2_relat_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 6.66/6.84            = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 6.66/6.84      inference('sup-', [status(thm)], ['35', '51'])).
% 6.66/6.84  thf(d10_xboole_0, axiom,
% 6.66/6.84    (![A:$i,B:$i]:
% 6.66/6.84     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 6.66/6.84  thf('53', plain,
% 6.66/6.84      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 6.66/6.84      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.66/6.84  thf('54', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 6.66/6.84      inference('simplify', [status(thm)], ['53'])).
% 6.66/6.84  thf('55', plain, ((v1_relat_1 @ sk_C)),
% 6.66/6.84      inference('sup-', [status(thm)], ['44', '45'])).
% 6.66/6.84  thf('56', plain,
% 6.66/6.84      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 6.66/6.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.84  thf(t35_funct_2, axiom,
% 6.66/6.84    (![A:$i,B:$i,C:$i]:
% 6.66/6.84     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.66/6.84         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.66/6.84       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 6.66/6.84         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 6.66/6.84           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 6.66/6.84             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 6.66/6.84  thf('57', plain,
% 6.66/6.84      (![X57 : $i, X58 : $i, X59 : $i]:
% 6.66/6.84         (((X57) = (k1_xboole_0))
% 6.66/6.84          | ~ (v1_funct_1 @ X58)
% 6.66/6.84          | ~ (v1_funct_2 @ X58 @ X59 @ X57)
% 6.66/6.84          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X57)))
% 6.66/6.84          | ((k5_relat_1 @ X58 @ (k2_funct_1 @ X58)) = (k6_partfun1 @ X59))
% 6.66/6.84          | ~ (v2_funct_1 @ X58)
% 6.66/6.84          | ((k2_relset_1 @ X59 @ X57 @ X58) != (X57)))),
% 6.66/6.84      inference('cnf', [status(esa)], [t35_funct_2])).
% 6.66/6.84  thf('58', plain,
% 6.66/6.84      ((((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) != (sk_B))
% 6.66/6.84        | ~ (v2_funct_1 @ sk_C)
% 6.66/6.84        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A_1))
% 6.66/6.84        | ~ (v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)
% 6.66/6.84        | ~ (v1_funct_1 @ sk_C)
% 6.66/6.84        | ((sk_B) = (k1_xboole_0)))),
% 6.66/6.84      inference('sup-', [status(thm)], ['56', '57'])).
% 6.66/6.84  thf('59', plain, (((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) = (sk_B))),
% 6.66/6.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.84  thf('60', plain, ((v2_funct_1 @ sk_C)),
% 6.66/6.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.84  thf('61', plain, ((v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)),
% 6.66/6.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.84  thf('62', plain, ((v1_funct_1 @ sk_C)),
% 6.66/6.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.84  thf('63', plain,
% 6.66/6.84      ((((sk_B) != (sk_B))
% 6.66/6.84        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A_1))
% 6.66/6.84        | ((sk_B) = (k1_xboole_0)))),
% 6.66/6.84      inference('demod', [status(thm)], ['58', '59', '60', '61', '62'])).
% 6.66/6.84  thf('64', plain,
% 6.66/6.84      ((((sk_B) = (k1_xboole_0))
% 6.66/6.84        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A_1)))),
% 6.66/6.84      inference('simplify', [status(thm)], ['63'])).
% 6.66/6.84  thf('65', plain, (((sk_B) != (k1_xboole_0))),
% 6.66/6.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.84  thf('66', plain,
% 6.66/6.84      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A_1))),
% 6.66/6.84      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 6.66/6.84  thf(t71_relat_1, axiom,
% 6.66/6.84    (![A:$i]:
% 6.66/6.84     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 6.66/6.84       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 6.66/6.84  thf('67', plain, (![X7 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X7)) = (X7))),
% 6.66/6.84      inference('cnf', [status(esa)], [t71_relat_1])).
% 6.66/6.84  thf('68', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 6.66/6.84      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 6.66/6.84  thf('69', plain, (![X7 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X7)) = (X7))),
% 6.66/6.84      inference('demod', [status(thm)], ['67', '68'])).
% 6.66/6.84  thf('70', plain, (((sk_A_1) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 6.66/6.84      inference('demod', [status(thm)], ['52', '54', '55', '66', '69'])).
% 6.66/6.84  thf(t64_funct_1, axiom,
% 6.66/6.84    (![A:$i]:
% 6.66/6.84     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.66/6.84       ( ![B:$i]:
% 6.66/6.84         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 6.66/6.84           ( ( ( v2_funct_1 @ A ) & 
% 6.66/6.84               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 6.66/6.84               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 6.66/6.84             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 6.66/6.84  thf('71', plain,
% 6.66/6.84      (![X14 : $i, X15 : $i]:
% 6.66/6.84         (~ (v1_relat_1 @ X14)
% 6.66/6.84          | ~ (v1_funct_1 @ X14)
% 6.66/6.84          | ((X14) = (k2_funct_1 @ X15))
% 6.66/6.84          | ((k5_relat_1 @ X14 @ X15) != (k6_relat_1 @ (k2_relat_1 @ X15)))
% 6.66/6.84          | ((k2_relat_1 @ X14) != (k1_relat_1 @ X15))
% 6.66/6.84          | ~ (v2_funct_1 @ X15)
% 6.66/6.84          | ~ (v1_funct_1 @ X15)
% 6.66/6.84          | ~ (v1_relat_1 @ X15))),
% 6.66/6.84      inference('cnf', [status(esa)], [t64_funct_1])).
% 6.66/6.84  thf('72', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 6.66/6.84      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 6.66/6.84  thf('73', plain,
% 6.66/6.84      (![X14 : $i, X15 : $i]:
% 6.66/6.84         (~ (v1_relat_1 @ X14)
% 6.66/6.84          | ~ (v1_funct_1 @ X14)
% 6.66/6.84          | ((X14) = (k2_funct_1 @ X15))
% 6.66/6.84          | ((k5_relat_1 @ X14 @ X15) != (k6_partfun1 @ (k2_relat_1 @ X15)))
% 6.66/6.84          | ((k2_relat_1 @ X14) != (k1_relat_1 @ X15))
% 6.66/6.84          | ~ (v2_funct_1 @ X15)
% 6.66/6.84          | ~ (v1_funct_1 @ X15)
% 6.66/6.84          | ~ (v1_relat_1 @ X15))),
% 6.66/6.84      inference('demod', [status(thm)], ['71', '72'])).
% 6.66/6.84  thf('74', plain,
% 6.66/6.84      (![X0 : $i]:
% 6.66/6.84         (((k5_relat_1 @ X0 @ (k2_funct_1 @ sk_C)) != (k6_partfun1 @ sk_A_1))
% 6.66/6.84          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 6.66/6.84          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 6.66/6.84          | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 6.66/6.84          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 6.66/6.84          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 6.66/6.84          | ~ (v1_funct_1 @ X0)
% 6.66/6.84          | ~ (v1_relat_1 @ X0))),
% 6.66/6.84      inference('sup-', [status(thm)], ['70', '73'])).
% 6.66/6.84  thf('75', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 6.66/6.84      inference('sup+', [status(thm)], ['33', '34'])).
% 6.66/6.84  thf('76', plain,
% 6.66/6.84      (![X9 : $i]:
% 6.66/6.84         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 6.66/6.84          | ~ (v1_funct_1 @ X9)
% 6.66/6.84          | ~ (v1_relat_1 @ X9))),
% 6.66/6.84      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.66/6.84  thf(fc6_funct_1, axiom,
% 6.66/6.84    (![A:$i]:
% 6.66/6.84     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 6.66/6.84       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 6.66/6.84         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 6.66/6.84         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 6.66/6.84  thf('77', plain,
% 6.66/6.84      (![X12 : $i]:
% 6.66/6.84         ((v2_funct_1 @ (k2_funct_1 @ X12))
% 6.66/6.84          | ~ (v2_funct_1 @ X12)
% 6.66/6.84          | ~ (v1_funct_1 @ X12)
% 6.66/6.84          | ~ (v1_relat_1 @ X12))),
% 6.66/6.84      inference('cnf', [status(esa)], [fc6_funct_1])).
% 6.66/6.84  thf('78', plain,
% 6.66/6.84      (![X9 : $i]:
% 6.66/6.84         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 6.66/6.84          | ~ (v1_funct_1 @ X9)
% 6.66/6.84          | ~ (v1_relat_1 @ X9))),
% 6.66/6.84      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.66/6.84  thf('79', plain,
% 6.66/6.84      (![X13 : $i]:
% 6.66/6.84         (~ (v2_funct_1 @ X13)
% 6.66/6.84          | ((k2_relat_1 @ X13) = (k1_relat_1 @ (k2_funct_1 @ X13)))
% 6.66/6.84          | ~ (v1_funct_1 @ X13)
% 6.66/6.84          | ~ (v1_relat_1 @ X13))),
% 6.66/6.84      inference('cnf', [status(esa)], [t55_funct_1])).
% 6.66/6.84  thf('80', plain,
% 6.66/6.84      (![X9 : $i]:
% 6.66/6.84         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 6.66/6.84          | ~ (v1_funct_1 @ X9)
% 6.66/6.84          | ~ (v1_relat_1 @ X9))),
% 6.66/6.84      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.66/6.84  thf('81', plain,
% 6.66/6.84      (![X9 : $i]:
% 6.66/6.84         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 6.66/6.84          | ~ (v1_funct_1 @ X9)
% 6.66/6.84          | ~ (v1_relat_1 @ X9))),
% 6.66/6.84      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.66/6.84  thf('82', plain,
% 6.66/6.84      (![X13 : $i]:
% 6.66/6.84         (~ (v2_funct_1 @ X13)
% 6.66/6.84          | ((k1_relat_1 @ X13) = (k2_relat_1 @ (k2_funct_1 @ X13)))
% 6.66/6.84          | ~ (v1_funct_1 @ X13)
% 6.66/6.84          | ~ (v1_relat_1 @ X13))),
% 6.66/6.85      inference('cnf', [status(esa)], [t55_funct_1])).
% 6.66/6.85  thf('83', plain,
% 6.66/6.85      (![X12 : $i]:
% 6.66/6.85         ((v2_funct_1 @ (k2_funct_1 @ X12))
% 6.66/6.85          | ~ (v2_funct_1 @ X12)
% 6.66/6.85          | ~ (v1_funct_1 @ X12)
% 6.66/6.85          | ~ (v1_relat_1 @ X12))),
% 6.66/6.85      inference('cnf', [status(esa)], [fc6_funct_1])).
% 6.66/6.85  thf('84', plain,
% 6.66/6.85      (![X9 : $i]:
% 6.66/6.85         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 6.66/6.85          | ~ (v1_funct_1 @ X9)
% 6.66/6.85          | ~ (v1_relat_1 @ X9))),
% 6.66/6.85      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.66/6.85  thf('85', plain,
% 6.66/6.85      (![X9 : $i]:
% 6.66/6.85         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 6.66/6.85          | ~ (v1_funct_1 @ X9)
% 6.66/6.85          | ~ (v1_relat_1 @ X9))),
% 6.66/6.85      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.66/6.85  thf(t65_funct_1, axiom,
% 6.66/6.85    (![A:$i]:
% 6.66/6.85     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.66/6.85       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 6.66/6.85  thf('86', plain,
% 6.66/6.85      (![X16 : $i]:
% 6.66/6.85         (~ (v2_funct_1 @ X16)
% 6.66/6.85          | ((k2_funct_1 @ (k2_funct_1 @ X16)) = (X16))
% 6.66/6.85          | ~ (v1_funct_1 @ X16)
% 6.66/6.85          | ~ (v1_relat_1 @ X16))),
% 6.66/6.85      inference('cnf', [status(esa)], [t65_funct_1])).
% 6.66/6.85  thf('87', plain,
% 6.66/6.85      (![X9 : $i]:
% 6.66/6.85         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 6.66/6.85          | ~ (v1_funct_1 @ X9)
% 6.66/6.85          | ~ (v1_relat_1 @ X9))),
% 6.66/6.85      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.66/6.85  thf('88', plain,
% 6.66/6.85      (![X13 : $i]:
% 6.66/6.85         (~ (v2_funct_1 @ X13)
% 6.66/6.85          | ((k2_relat_1 @ X13) = (k1_relat_1 @ (k2_funct_1 @ X13)))
% 6.66/6.85          | ~ (v1_funct_1 @ X13)
% 6.66/6.85          | ~ (v1_relat_1 @ X13))),
% 6.66/6.85      inference('cnf', [status(esa)], [t55_funct_1])).
% 6.66/6.85  thf(t78_relat_1, axiom,
% 6.66/6.85    (![A:$i]:
% 6.66/6.85     ( ( v1_relat_1 @ A ) =>
% 6.66/6.85       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 6.66/6.85  thf('89', plain,
% 6.66/6.85      (![X8 : $i]:
% 6.66/6.85         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X8)) @ X8) = (X8))
% 6.66/6.85          | ~ (v1_relat_1 @ X8))),
% 6.66/6.85      inference('cnf', [status(esa)], [t78_relat_1])).
% 6.66/6.85  thf('90', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 6.66/6.85      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 6.66/6.85  thf('91', plain,
% 6.66/6.85      (![X8 : $i]:
% 6.66/6.85         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X8)) @ X8) = (X8))
% 6.66/6.85          | ~ (v1_relat_1 @ X8))),
% 6.66/6.85      inference('demod', [status(thm)], ['89', '90'])).
% 6.66/6.85  thf('92', plain,
% 6.66/6.85      (![X0 : $i]:
% 6.66/6.85         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 6.66/6.85            = (k2_funct_1 @ X0))
% 6.66/6.85          | ~ (v1_relat_1 @ X0)
% 6.66/6.85          | ~ (v1_funct_1 @ X0)
% 6.66/6.85          | ~ (v2_funct_1 @ X0)
% 6.66/6.85          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 6.66/6.85      inference('sup+', [status(thm)], ['88', '91'])).
% 6.66/6.85  thf('93', plain,
% 6.66/6.85      (![X0 : $i]:
% 6.66/6.85         (~ (v1_relat_1 @ X0)
% 6.66/6.85          | ~ (v1_funct_1 @ X0)
% 6.66/6.85          | ~ (v2_funct_1 @ X0)
% 6.66/6.85          | ~ (v1_funct_1 @ X0)
% 6.66/6.85          | ~ (v1_relat_1 @ X0)
% 6.66/6.85          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 6.66/6.85              (k2_funct_1 @ X0)) = (k2_funct_1 @ X0)))),
% 6.66/6.85      inference('sup-', [status(thm)], ['87', '92'])).
% 6.66/6.85  thf('94', plain,
% 6.66/6.85      (![X0 : $i]:
% 6.66/6.85         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 6.66/6.85            = (k2_funct_1 @ X0))
% 6.66/6.85          | ~ (v2_funct_1 @ X0)
% 6.66/6.85          | ~ (v1_funct_1 @ X0)
% 6.66/6.85          | ~ (v1_relat_1 @ X0))),
% 6.66/6.85      inference('simplify', [status(thm)], ['93'])).
% 6.66/6.85  thf('95', plain,
% 6.66/6.85      (![X0 : $i]:
% 6.66/6.85         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))) @ X0)
% 6.66/6.85            = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 6.66/6.85          | ~ (v1_relat_1 @ X0)
% 6.66/6.85          | ~ (v1_funct_1 @ X0)
% 6.66/6.85          | ~ (v2_funct_1 @ X0)
% 6.66/6.85          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.66/6.85          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.66/6.85          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 6.66/6.85      inference('sup+', [status(thm)], ['86', '94'])).
% 6.66/6.85  thf('96', plain,
% 6.66/6.85      (![X0 : $i]:
% 6.66/6.85         (~ (v1_relat_1 @ X0)
% 6.66/6.85          | ~ (v1_funct_1 @ X0)
% 6.66/6.85          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 6.66/6.85          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.66/6.85          | ~ (v2_funct_1 @ X0)
% 6.66/6.85          | ~ (v1_funct_1 @ X0)
% 6.66/6.85          | ~ (v1_relat_1 @ X0)
% 6.66/6.85          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))) @ 
% 6.66/6.85              X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 6.66/6.85      inference('sup-', [status(thm)], ['85', '95'])).
% 6.66/6.85  thf('97', plain,
% 6.66/6.85      (![X0 : $i]:
% 6.66/6.85         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))) @ X0)
% 6.66/6.85            = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 6.66/6.85          | ~ (v2_funct_1 @ X0)
% 6.66/6.85          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.66/6.85          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 6.66/6.85          | ~ (v1_funct_1 @ X0)
% 6.66/6.85          | ~ (v1_relat_1 @ X0))),
% 6.66/6.85      inference('simplify', [status(thm)], ['96'])).
% 6.66/6.85  thf('98', plain,
% 6.66/6.85      (![X0 : $i]:
% 6.66/6.85         (~ (v1_relat_1 @ X0)
% 6.66/6.85          | ~ (v1_funct_1 @ X0)
% 6.66/6.85          | ~ (v1_relat_1 @ X0)
% 6.66/6.85          | ~ (v1_funct_1 @ X0)
% 6.66/6.85          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 6.66/6.85          | ~ (v2_funct_1 @ X0)
% 6.66/6.85          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))) @ 
% 6.66/6.85              X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 6.66/6.85      inference('sup-', [status(thm)], ['84', '97'])).
% 6.66/6.85  thf('99', plain,
% 6.66/6.85      (![X0 : $i]:
% 6.66/6.85         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))) @ X0)
% 6.66/6.85            = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 6.66/6.85          | ~ (v2_funct_1 @ X0)
% 6.66/6.85          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 6.66/6.85          | ~ (v1_funct_1 @ X0)
% 6.66/6.85          | ~ (v1_relat_1 @ X0))),
% 6.66/6.85      inference('simplify', [status(thm)], ['98'])).
% 6.66/6.85  thf('100', plain,
% 6.66/6.85      (![X0 : $i]:
% 6.66/6.85         (~ (v1_relat_1 @ X0)
% 6.66/6.85          | ~ (v1_funct_1 @ X0)
% 6.66/6.85          | ~ (v2_funct_1 @ X0)
% 6.66/6.85          | ~ (v1_relat_1 @ X0)
% 6.66/6.85          | ~ (v1_funct_1 @ X0)
% 6.66/6.85          | ~ (v2_funct_1 @ X0)
% 6.66/6.85          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))) @ 
% 6.66/6.85              X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 6.66/6.85      inference('sup-', [status(thm)], ['83', '99'])).
% 6.66/6.85  thf('101', plain,
% 6.66/6.85      (![X0 : $i]:
% 6.66/6.85         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))) @ X0)
% 6.66/6.85            = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 6.66/6.85          | ~ (v2_funct_1 @ X0)
% 6.66/6.85          | ~ (v1_funct_1 @ X0)
% 6.66/6.85          | ~ (v1_relat_1 @ X0))),
% 6.66/6.85      inference('simplify', [status(thm)], ['100'])).
% 6.66/6.85  thf('102', plain,
% 6.66/6.85      (![X0 : $i]:
% 6.66/6.85         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0)
% 6.66/6.85            = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 6.66/6.85          | ~ (v1_relat_1 @ X0)
% 6.66/6.85          | ~ (v1_funct_1 @ X0)
% 6.66/6.85          | ~ (v2_funct_1 @ X0)
% 6.66/6.85          | ~ (v1_relat_1 @ X0)
% 6.66/6.85          | ~ (v1_funct_1 @ X0)
% 6.66/6.85          | ~ (v2_funct_1 @ X0))),
% 6.66/6.85      inference('sup+', [status(thm)], ['82', '101'])).
% 6.66/6.85  thf('103', plain,
% 6.66/6.85      (![X0 : $i]:
% 6.66/6.85         (~ (v2_funct_1 @ X0)
% 6.66/6.85          | ~ (v1_funct_1 @ X0)
% 6.66/6.85          | ~ (v1_relat_1 @ X0)
% 6.66/6.85          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0)
% 6.66/6.85              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 6.66/6.85      inference('simplify', [status(thm)], ['102'])).
% 6.66/6.85  thf('104', plain,
% 6.66/6.85      (![X9 : $i]:
% 6.66/6.85         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 6.66/6.85          | ~ (v1_funct_1 @ X9)
% 6.66/6.85          | ~ (v1_relat_1 @ X9))),
% 6.66/6.85      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.66/6.85  thf('105', plain,
% 6.66/6.85      (![X0 : $i]:
% 6.66/6.85         ((v1_funct_1 @ (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 6.66/6.85          | ~ (v1_relat_1 @ X0)
% 6.66/6.85          | ~ (v1_funct_1 @ X0)
% 6.66/6.85          | ~ (v2_funct_1 @ X0)
% 6.66/6.85          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.66/6.85          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 6.66/6.85      inference('sup+', [status(thm)], ['103', '104'])).
% 6.66/6.85  thf('106', plain,
% 6.66/6.85      (![X0 : $i]:
% 6.66/6.85         (~ (v1_relat_1 @ X0)
% 6.66/6.85          | ~ (v1_funct_1 @ X0)
% 6.66/6.85          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.66/6.85          | ~ (v2_funct_1 @ X0)
% 6.66/6.85          | ~ (v1_funct_1 @ X0)
% 6.66/6.85          | ~ (v1_relat_1 @ X0)
% 6.66/6.85          | (v1_funct_1 @ (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0)))),
% 6.66/6.85      inference('sup-', [status(thm)], ['81', '105'])).
% 6.66/6.85  thf('107', plain,
% 6.66/6.85      (![X0 : $i]:
% 6.66/6.85         ((v1_funct_1 @ (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 6.66/6.85          | ~ (v2_funct_1 @ X0)
% 6.66/6.85          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.66/6.85          | ~ (v1_funct_1 @ X0)
% 6.66/6.85          | ~ (v1_relat_1 @ X0))),
% 6.66/6.85      inference('simplify', [status(thm)], ['106'])).
% 6.66/6.85  thf('108', plain,
% 6.66/6.85      (![X0 : $i]:
% 6.66/6.85         (~ (v1_relat_1 @ X0)
% 6.66/6.85          | ~ (v1_funct_1 @ X0)
% 6.66/6.85          | ~ (v1_relat_1 @ X0)
% 6.66/6.85          | ~ (v1_funct_1 @ X0)
% 6.66/6.85          | ~ (v2_funct_1 @ X0)
% 6.66/6.85          | (v1_funct_1 @ (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0)))),
% 6.66/6.85      inference('sup-', [status(thm)], ['80', '107'])).
% 6.66/6.85  thf('109', plain,
% 6.66/6.85      (![X0 : $i]:
% 6.66/6.85         ((v1_funct_1 @ (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 6.66/6.85          | ~ (v2_funct_1 @ X0)
% 6.66/6.85          | ~ (v1_funct_1 @ X0)
% 6.66/6.85          | ~ (v1_relat_1 @ X0))),
% 6.66/6.85      inference('simplify', [status(thm)], ['108'])).
% 6.66/6.85  thf('110', plain,
% 6.66/6.85      (![X0 : $i]:
% 6.66/6.85         ((v1_funct_1 @ 
% 6.66/6.85           (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0)))
% 6.66/6.85          | ~ (v1_relat_1 @ X0)
% 6.66/6.85          | ~ (v1_funct_1 @ X0)
% 6.66/6.85          | ~ (v2_funct_1 @ X0)
% 6.66/6.85          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.66/6.85          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.66/6.85          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 6.66/6.85      inference('sup+', [status(thm)], ['79', '109'])).
% 6.66/6.85  thf('111', plain,
% 6.66/6.85      (![X0 : $i]:
% 6.66/6.85         (~ (v1_relat_1 @ X0)
% 6.66/6.85          | ~ (v1_funct_1 @ X0)
% 6.66/6.85          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 6.66/6.85          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.66/6.85          | ~ (v2_funct_1 @ X0)
% 6.66/6.85          | ~ (v1_funct_1 @ X0)
% 6.66/6.85          | ~ (v1_relat_1 @ X0)
% 6.66/6.85          | (v1_funct_1 @ 
% 6.66/6.85             (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 6.66/6.85              (k2_funct_1 @ X0))))),
% 6.66/6.85      inference('sup-', [status(thm)], ['78', '110'])).
% 6.68/6.85  thf('112', plain,
% 6.68/6.85      (![X0 : $i]:
% 6.68/6.85         ((v1_funct_1 @ 
% 6.68/6.85           (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0)))
% 6.68/6.85          | ~ (v2_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.68/6.85          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ X0))),
% 6.68/6.85      inference('simplify', [status(thm)], ['111'])).
% 6.68/6.85  thf('113', plain,
% 6.68/6.85      (![X0 : $i]:
% 6.68/6.85         (~ (v1_relat_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v2_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.68/6.85          | ~ (v2_funct_1 @ X0)
% 6.68/6.85          | (v1_funct_1 @ 
% 6.68/6.85             (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 6.68/6.85              (k2_funct_1 @ X0))))),
% 6.68/6.85      inference('sup-', [status(thm)], ['77', '112'])).
% 6.68/6.85  thf('114', plain,
% 6.68/6.85      (![X0 : $i]:
% 6.68/6.85         ((v1_funct_1 @ 
% 6.68/6.85           (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0)))
% 6.68/6.85          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.68/6.85          | ~ (v2_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ X0))),
% 6.68/6.85      inference('simplify', [status(thm)], ['113'])).
% 6.68/6.85  thf('115', plain,
% 6.68/6.85      (![X0 : $i]:
% 6.68/6.85         (~ (v1_relat_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v2_funct_1 @ X0)
% 6.68/6.85          | (v1_funct_1 @ 
% 6.68/6.85             (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 6.68/6.85              (k2_funct_1 @ X0))))),
% 6.68/6.85      inference('sup-', [status(thm)], ['76', '114'])).
% 6.68/6.85  thf('116', plain,
% 6.68/6.85      (![X0 : $i]:
% 6.68/6.85         ((v1_funct_1 @ 
% 6.68/6.85           (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0)))
% 6.68/6.85          | ~ (v2_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ X0))),
% 6.68/6.85      inference('simplify', [status(thm)], ['115'])).
% 6.68/6.85  thf('117', plain,
% 6.68/6.85      (((v1_funct_1 @ (k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C)))
% 6.68/6.85        | ~ (v1_relat_1 @ sk_C)
% 6.68/6.85        | ~ (v1_funct_1 @ sk_C)
% 6.68/6.85        | ~ (v2_funct_1 @ sk_C))),
% 6.68/6.85      inference('sup+', [status(thm)], ['75', '116'])).
% 6.68/6.85  thf('118', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 6.68/6.85      inference('sup+', [status(thm)], ['33', '34'])).
% 6.68/6.85  thf('119', plain,
% 6.68/6.85      (![X0 : $i]:
% 6.68/6.85         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 6.68/6.85            = (k2_funct_1 @ X0))
% 6.68/6.85          | ~ (v2_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ X0))),
% 6.68/6.85      inference('simplify', [status(thm)], ['93'])).
% 6.68/6.85  thf('120', plain,
% 6.68/6.85      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 6.68/6.85          = (k2_funct_1 @ sk_C))
% 6.68/6.85        | ~ (v1_relat_1 @ sk_C)
% 6.68/6.85        | ~ (v1_funct_1 @ sk_C)
% 6.68/6.85        | ~ (v2_funct_1 @ sk_C))),
% 6.68/6.85      inference('sup+', [status(thm)], ['118', '119'])).
% 6.68/6.85  thf('121', plain, ((v1_relat_1 @ sk_C)),
% 6.68/6.85      inference('sup-', [status(thm)], ['44', '45'])).
% 6.68/6.85  thf('122', plain, ((v1_funct_1 @ sk_C)),
% 6.68/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.68/6.85  thf('123', plain, ((v2_funct_1 @ sk_C)),
% 6.68/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.68/6.85  thf('124', plain,
% 6.68/6.85      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 6.68/6.85         = (k2_funct_1 @ sk_C))),
% 6.68/6.85      inference('demod', [status(thm)], ['120', '121', '122', '123'])).
% 6.68/6.85  thf('125', plain, ((v1_relat_1 @ sk_C)),
% 6.68/6.85      inference('sup-', [status(thm)], ['44', '45'])).
% 6.68/6.85  thf('126', plain, ((v1_funct_1 @ sk_C)),
% 6.68/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.68/6.85  thf('127', plain, ((v2_funct_1 @ sk_C)),
% 6.68/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.68/6.85  thf('128', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 6.68/6.85      inference('demod', [status(thm)], ['117', '124', '125', '126', '127'])).
% 6.68/6.85  thf('129', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 6.68/6.85      inference('sup+', [status(thm)], ['33', '34'])).
% 6.68/6.85  thf('130', plain,
% 6.68/6.85      (![X12 : $i]:
% 6.68/6.85         ((v2_funct_1 @ (k2_funct_1 @ X12))
% 6.68/6.85          | ~ (v2_funct_1 @ X12)
% 6.68/6.85          | ~ (v1_funct_1 @ X12)
% 6.68/6.85          | ~ (v1_relat_1 @ X12))),
% 6.68/6.85      inference('cnf', [status(esa)], [fc6_funct_1])).
% 6.68/6.85  thf('131', plain,
% 6.68/6.85      (![X9 : $i]:
% 6.68/6.85         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 6.68/6.85          | ~ (v1_funct_1 @ X9)
% 6.68/6.85          | ~ (v1_relat_1 @ X9))),
% 6.68/6.85      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.68/6.85  thf('132', plain,
% 6.68/6.85      (![X9 : $i]:
% 6.68/6.85         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 6.68/6.85          | ~ (v1_funct_1 @ X9)
% 6.68/6.85          | ~ (v1_relat_1 @ X9))),
% 6.68/6.85      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.68/6.85  thf('133', plain,
% 6.68/6.85      (![X13 : $i]:
% 6.68/6.85         (~ (v2_funct_1 @ X13)
% 6.68/6.85          | ((k2_relat_1 @ X13) = (k1_relat_1 @ (k2_funct_1 @ X13)))
% 6.68/6.85          | ~ (v1_funct_1 @ X13)
% 6.68/6.85          | ~ (v1_relat_1 @ X13))),
% 6.68/6.85      inference('cnf', [status(esa)], [t55_funct_1])).
% 6.68/6.85  thf('134', plain,
% 6.68/6.85      (![X12 : $i]:
% 6.68/6.85         ((v2_funct_1 @ (k2_funct_1 @ X12))
% 6.68/6.85          | ~ (v2_funct_1 @ X12)
% 6.68/6.85          | ~ (v1_funct_1 @ X12)
% 6.68/6.85          | ~ (v1_relat_1 @ X12))),
% 6.68/6.85      inference('cnf', [status(esa)], [fc6_funct_1])).
% 6.68/6.85  thf('135', plain,
% 6.68/6.85      (![X9 : $i]:
% 6.68/6.85         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 6.68/6.85          | ~ (v1_funct_1 @ X9)
% 6.68/6.85          | ~ (v1_relat_1 @ X9))),
% 6.68/6.85      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.68/6.85  thf('136', plain,
% 6.68/6.85      (![X9 : $i]:
% 6.68/6.85         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 6.68/6.85          | ~ (v1_funct_1 @ X9)
% 6.68/6.85          | ~ (v1_relat_1 @ X9))),
% 6.68/6.85      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.68/6.85  thf('137', plain,
% 6.68/6.85      (![X0 : $i]:
% 6.68/6.85         (~ (v2_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ X0)
% 6.68/6.85          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0)
% 6.68/6.85              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 6.68/6.85      inference('simplify', [status(thm)], ['102'])).
% 6.68/6.85  thf('138', plain,
% 6.68/6.85      (![X12 : $i]:
% 6.68/6.85         ((v2_funct_1 @ (k2_funct_1 @ X12))
% 6.68/6.85          | ~ (v2_funct_1 @ X12)
% 6.68/6.85          | ~ (v1_funct_1 @ X12)
% 6.68/6.85          | ~ (v1_relat_1 @ X12))),
% 6.68/6.85      inference('cnf', [status(esa)], [fc6_funct_1])).
% 6.68/6.85  thf('139', plain,
% 6.68/6.85      (![X0 : $i]:
% 6.68/6.85         ((v2_funct_1 @ (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 6.68/6.85          | ~ (v1_relat_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v2_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.68/6.85          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.68/6.85          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 6.68/6.85      inference('sup+', [status(thm)], ['137', '138'])).
% 6.68/6.85  thf('140', plain,
% 6.68/6.85      (![X0 : $i]:
% 6.68/6.85         (~ (v1_relat_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 6.68/6.85          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.68/6.85          | ~ (v2_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ X0)
% 6.68/6.85          | (v2_funct_1 @ (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0)))),
% 6.68/6.85      inference('sup-', [status(thm)], ['136', '139'])).
% 6.68/6.85  thf('141', plain,
% 6.68/6.85      (![X0 : $i]:
% 6.68/6.85         ((v2_funct_1 @ (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 6.68/6.85          | ~ (v2_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.68/6.85          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ X0))),
% 6.68/6.85      inference('simplify', [status(thm)], ['140'])).
% 6.68/6.85  thf('142', plain,
% 6.68/6.85      (![X0 : $i]:
% 6.68/6.85         (~ (v1_relat_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 6.68/6.85          | ~ (v2_funct_1 @ X0)
% 6.68/6.85          | (v2_funct_1 @ (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0)))),
% 6.68/6.85      inference('sup-', [status(thm)], ['135', '141'])).
% 6.68/6.85  thf('143', plain,
% 6.68/6.85      (![X0 : $i]:
% 6.68/6.85         ((v2_funct_1 @ (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 6.68/6.85          | ~ (v2_funct_1 @ X0)
% 6.68/6.85          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ X0))),
% 6.68/6.85      inference('simplify', [status(thm)], ['142'])).
% 6.68/6.85  thf('144', plain,
% 6.68/6.85      (![X0 : $i]:
% 6.68/6.85         (~ (v1_relat_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v2_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v2_funct_1 @ X0)
% 6.68/6.85          | (v2_funct_1 @ (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0)))),
% 6.68/6.85      inference('sup-', [status(thm)], ['134', '143'])).
% 6.68/6.85  thf('145', plain,
% 6.68/6.85      (![X0 : $i]:
% 6.68/6.85         ((v2_funct_1 @ (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 6.68/6.85          | ~ (v2_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ X0))),
% 6.68/6.85      inference('simplify', [status(thm)], ['144'])).
% 6.68/6.85  thf('146', plain,
% 6.68/6.85      (![X0 : $i]:
% 6.68/6.85         ((v2_funct_1 @ 
% 6.68/6.85           (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0)))
% 6.68/6.85          | ~ (v1_relat_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v2_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.68/6.85          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.68/6.85          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 6.68/6.85      inference('sup+', [status(thm)], ['133', '145'])).
% 6.68/6.85  thf('147', plain,
% 6.68/6.85      (![X0 : $i]:
% 6.68/6.85         (~ (v1_relat_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 6.68/6.85          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.68/6.85          | ~ (v2_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ X0)
% 6.68/6.85          | (v2_funct_1 @ 
% 6.68/6.85             (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 6.68/6.85              (k2_funct_1 @ X0))))),
% 6.68/6.85      inference('sup-', [status(thm)], ['132', '146'])).
% 6.68/6.85  thf('148', plain,
% 6.68/6.85      (![X0 : $i]:
% 6.68/6.85         ((v2_funct_1 @ 
% 6.68/6.85           (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0)))
% 6.68/6.85          | ~ (v2_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.68/6.85          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ X0))),
% 6.68/6.85      inference('simplify', [status(thm)], ['147'])).
% 6.68/6.85  thf('149', plain,
% 6.68/6.85      (![X0 : $i]:
% 6.68/6.85         (~ (v1_relat_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 6.68/6.85          | ~ (v2_funct_1 @ X0)
% 6.68/6.85          | (v2_funct_1 @ 
% 6.68/6.85             (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 6.68/6.85              (k2_funct_1 @ X0))))),
% 6.68/6.85      inference('sup-', [status(thm)], ['131', '148'])).
% 6.68/6.85  thf('150', plain,
% 6.68/6.85      (![X0 : $i]:
% 6.68/6.85         ((v2_funct_1 @ 
% 6.68/6.85           (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0)))
% 6.68/6.85          | ~ (v2_funct_1 @ X0)
% 6.68/6.85          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ X0))),
% 6.68/6.85      inference('simplify', [status(thm)], ['149'])).
% 6.68/6.85  thf('151', plain,
% 6.68/6.85      (![X0 : $i]:
% 6.68/6.85         (~ (v1_relat_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v2_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v2_funct_1 @ X0)
% 6.68/6.85          | (v2_funct_1 @ 
% 6.68/6.85             (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 6.68/6.85              (k2_funct_1 @ X0))))),
% 6.68/6.85      inference('sup-', [status(thm)], ['130', '150'])).
% 6.68/6.85  thf('152', plain,
% 6.68/6.85      (![X0 : $i]:
% 6.68/6.85         ((v2_funct_1 @ 
% 6.68/6.85           (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0)))
% 6.68/6.85          | ~ (v2_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ X0))),
% 6.68/6.85      inference('simplify', [status(thm)], ['151'])).
% 6.68/6.85  thf('153', plain,
% 6.68/6.85      (((v2_funct_1 @ (k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C)))
% 6.68/6.85        | ~ (v1_relat_1 @ sk_C)
% 6.68/6.85        | ~ (v1_funct_1 @ sk_C)
% 6.68/6.85        | ~ (v2_funct_1 @ sk_C))),
% 6.68/6.85      inference('sup+', [status(thm)], ['129', '152'])).
% 6.68/6.85  thf('154', plain,
% 6.68/6.85      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 6.68/6.85         = (k2_funct_1 @ sk_C))),
% 6.68/6.85      inference('demod', [status(thm)], ['120', '121', '122', '123'])).
% 6.68/6.85  thf('155', plain, ((v1_relat_1 @ sk_C)),
% 6.68/6.85      inference('sup-', [status(thm)], ['44', '45'])).
% 6.68/6.85  thf('156', plain, ((v1_funct_1 @ sk_C)),
% 6.68/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.68/6.85  thf('157', plain, ((v2_funct_1 @ sk_C)),
% 6.68/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.68/6.85  thf('158', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 6.68/6.85      inference('demod', [status(thm)], ['153', '154', '155', '156', '157'])).
% 6.68/6.85  thf('159', plain,
% 6.68/6.85      (![X0 : $i]:
% 6.68/6.85         (((k5_relat_1 @ X0 @ (k2_funct_1 @ sk_C)) != (k6_partfun1 @ sk_A_1))
% 6.68/6.85          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 6.68/6.85          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 6.68/6.85          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ X0))),
% 6.68/6.85      inference('demod', [status(thm)], ['74', '128', '158'])).
% 6.68/6.85  thf('160', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 6.68/6.85      inference('sup+', [status(thm)], ['33', '34'])).
% 6.68/6.85  thf('161', plain,
% 6.68/6.85      (![X9 : $i]:
% 6.68/6.85         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 6.68/6.85          | ~ (v1_funct_1 @ X9)
% 6.68/6.85          | ~ (v1_relat_1 @ X9))),
% 6.68/6.85      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.68/6.85  thf('162', plain,
% 6.68/6.85      (![X12 : $i]:
% 6.68/6.85         ((v2_funct_1 @ (k2_funct_1 @ X12))
% 6.68/6.85          | ~ (v2_funct_1 @ X12)
% 6.68/6.85          | ~ (v1_funct_1 @ X12)
% 6.68/6.85          | ~ (v1_relat_1 @ X12))),
% 6.68/6.85      inference('cnf', [status(esa)], [fc6_funct_1])).
% 6.68/6.85  thf('163', plain,
% 6.68/6.85      (![X9 : $i]:
% 6.68/6.85         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 6.68/6.85          | ~ (v1_funct_1 @ X9)
% 6.68/6.85          | ~ (v1_relat_1 @ X9))),
% 6.68/6.85      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.68/6.85  thf('164', plain,
% 6.68/6.85      (![X13 : $i]:
% 6.68/6.85         (~ (v2_funct_1 @ X13)
% 6.68/6.85          | ((k2_relat_1 @ X13) = (k1_relat_1 @ (k2_funct_1 @ X13)))
% 6.68/6.85          | ~ (v1_funct_1 @ X13)
% 6.68/6.85          | ~ (v1_relat_1 @ X13))),
% 6.68/6.85      inference('cnf', [status(esa)], [t55_funct_1])).
% 6.68/6.85  thf('165', plain,
% 6.68/6.85      (![X9 : $i]:
% 6.68/6.85         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 6.68/6.85          | ~ (v1_funct_1 @ X9)
% 6.68/6.85          | ~ (v1_relat_1 @ X9))),
% 6.68/6.85      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.68/6.85  thf('166', plain,
% 6.68/6.85      (![X9 : $i]:
% 6.68/6.85         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 6.68/6.85          | ~ (v1_funct_1 @ X9)
% 6.68/6.85          | ~ (v1_relat_1 @ X9))),
% 6.68/6.85      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.68/6.85  thf('167', plain,
% 6.68/6.85      (![X0 : $i]:
% 6.68/6.85         (~ (v2_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ X0)
% 6.68/6.85          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0)
% 6.68/6.85              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 6.68/6.85      inference('simplify', [status(thm)], ['102'])).
% 6.68/6.85  thf('168', plain,
% 6.68/6.85      (![X9 : $i]:
% 6.68/6.85         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 6.68/6.85          | ~ (v1_funct_1 @ X9)
% 6.68/6.85          | ~ (v1_relat_1 @ X9))),
% 6.68/6.85      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.68/6.85  thf('169', plain,
% 6.68/6.85      (![X0 : $i]:
% 6.68/6.85         ((v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 6.68/6.85          | ~ (v1_relat_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v2_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.68/6.85          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 6.68/6.85      inference('sup+', [status(thm)], ['167', '168'])).
% 6.68/6.85  thf('170', plain,
% 6.68/6.85      (![X0 : $i]:
% 6.68/6.85         (~ (v1_relat_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.68/6.85          | ~ (v2_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ X0)
% 6.68/6.85          | (v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0)))),
% 6.68/6.85      inference('sup-', [status(thm)], ['166', '169'])).
% 6.68/6.85  thf('171', plain,
% 6.68/6.85      (![X0 : $i]:
% 6.68/6.85         ((v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 6.68/6.85          | ~ (v2_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ X0))),
% 6.68/6.85      inference('simplify', [status(thm)], ['170'])).
% 6.68/6.85  thf('172', plain,
% 6.68/6.85      (![X0 : $i]:
% 6.68/6.85         (~ (v1_relat_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v2_funct_1 @ X0)
% 6.68/6.85          | (v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0)))),
% 6.68/6.85      inference('sup-', [status(thm)], ['165', '171'])).
% 6.68/6.85  thf('173', plain,
% 6.68/6.85      (![X0 : $i]:
% 6.68/6.85         ((v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 6.68/6.85          | ~ (v2_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ X0))),
% 6.68/6.85      inference('simplify', [status(thm)], ['172'])).
% 6.68/6.85  thf('174', plain,
% 6.68/6.85      (![X0 : $i]:
% 6.68/6.85         ((v1_relat_1 @ 
% 6.68/6.85           (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0)))
% 6.68/6.85          | ~ (v1_relat_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v2_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.68/6.85          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.68/6.85          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 6.68/6.85      inference('sup+', [status(thm)], ['164', '173'])).
% 6.68/6.85  thf('175', plain,
% 6.68/6.85      (![X0 : $i]:
% 6.68/6.85         (~ (v1_relat_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 6.68/6.85          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.68/6.85          | ~ (v2_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ X0)
% 6.68/6.85          | (v1_relat_1 @ 
% 6.68/6.85             (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 6.68/6.85              (k2_funct_1 @ X0))))),
% 6.68/6.85      inference('sup-', [status(thm)], ['163', '174'])).
% 6.68/6.85  thf('176', plain,
% 6.68/6.85      (![X0 : $i]:
% 6.68/6.85         ((v1_relat_1 @ 
% 6.68/6.85           (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0)))
% 6.68/6.85          | ~ (v2_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.68/6.85          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ X0))),
% 6.68/6.85      inference('simplify', [status(thm)], ['175'])).
% 6.68/6.85  thf('177', plain,
% 6.68/6.85      (![X0 : $i]:
% 6.68/6.85         (~ (v1_relat_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v2_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.68/6.85          | ~ (v2_funct_1 @ X0)
% 6.68/6.85          | (v1_relat_1 @ 
% 6.68/6.85             (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 6.68/6.85              (k2_funct_1 @ X0))))),
% 6.68/6.85      inference('sup-', [status(thm)], ['162', '176'])).
% 6.68/6.85  thf('178', plain,
% 6.68/6.85      (![X0 : $i]:
% 6.68/6.85         ((v1_relat_1 @ 
% 6.68/6.85           (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0)))
% 6.68/6.85          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.68/6.85          | ~ (v2_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ X0))),
% 6.68/6.85      inference('simplify', [status(thm)], ['177'])).
% 6.68/6.85  thf('179', plain,
% 6.68/6.85      (![X0 : $i]:
% 6.68/6.85         (~ (v1_relat_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v2_funct_1 @ X0)
% 6.68/6.85          | (v1_relat_1 @ 
% 6.68/6.85             (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 6.68/6.85              (k2_funct_1 @ X0))))),
% 6.68/6.85      inference('sup-', [status(thm)], ['161', '178'])).
% 6.68/6.85  thf('180', plain,
% 6.68/6.85      (![X0 : $i]:
% 6.68/6.85         ((v1_relat_1 @ 
% 6.68/6.85           (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0)))
% 6.68/6.85          | ~ (v2_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ X0))),
% 6.68/6.85      inference('simplify', [status(thm)], ['179'])).
% 6.68/6.85  thf('181', plain,
% 6.68/6.85      (((v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C)))
% 6.68/6.85        | ~ (v1_relat_1 @ sk_C)
% 6.68/6.85        | ~ (v1_funct_1 @ sk_C)
% 6.68/6.85        | ~ (v2_funct_1 @ sk_C))),
% 6.68/6.85      inference('sup+', [status(thm)], ['160', '180'])).
% 6.68/6.85  thf('182', plain,
% 6.68/6.85      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 6.68/6.85         = (k2_funct_1 @ sk_C))),
% 6.68/6.85      inference('demod', [status(thm)], ['120', '121', '122', '123'])).
% 6.68/6.85  thf('183', plain, ((v1_relat_1 @ sk_C)),
% 6.68/6.85      inference('sup-', [status(thm)], ['44', '45'])).
% 6.68/6.85  thf('184', plain, ((v1_funct_1 @ sk_C)),
% 6.68/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.68/6.85  thf('185', plain, ((v2_funct_1 @ sk_C)),
% 6.68/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.68/6.85  thf('186', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 6.68/6.85      inference('demod', [status(thm)], ['181', '182', '183', '184', '185'])).
% 6.68/6.85  thf('187', plain,
% 6.68/6.85      (![X9 : $i]:
% 6.68/6.85         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 6.68/6.85          | ~ (v1_funct_1 @ X9)
% 6.68/6.85          | ~ (v1_relat_1 @ X9))),
% 6.68/6.85      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.68/6.85  thf('188', plain,
% 6.68/6.85      (![X13 : $i]:
% 6.68/6.85         (~ (v2_funct_1 @ X13)
% 6.68/6.85          | ((k2_relat_1 @ X13) = (k1_relat_1 @ (k2_funct_1 @ X13)))
% 6.68/6.85          | ~ (v1_funct_1 @ X13)
% 6.68/6.85          | ~ (v1_relat_1 @ X13))),
% 6.68/6.85      inference('cnf', [status(esa)], [t55_funct_1])).
% 6.68/6.85  thf('189', plain,
% 6.68/6.85      (![X12 : $i]:
% 6.68/6.85         ((v2_funct_1 @ (k2_funct_1 @ X12))
% 6.68/6.85          | ~ (v2_funct_1 @ X12)
% 6.68/6.85          | ~ (v1_funct_1 @ X12)
% 6.68/6.85          | ~ (v1_relat_1 @ X12))),
% 6.68/6.85      inference('cnf', [status(esa)], [fc6_funct_1])).
% 6.68/6.85  thf('190', plain,
% 6.68/6.85      (![X9 : $i]:
% 6.68/6.85         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 6.68/6.85          | ~ (v1_funct_1 @ X9)
% 6.68/6.85          | ~ (v1_relat_1 @ X9))),
% 6.68/6.85      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.68/6.85  thf('191', plain,
% 6.68/6.85      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A_1))),
% 6.68/6.85      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 6.68/6.85  thf('192', plain,
% 6.68/6.85      (![X14 : $i, X15 : $i]:
% 6.68/6.85         (~ (v1_relat_1 @ X14)
% 6.68/6.85          | ~ (v1_funct_1 @ X14)
% 6.68/6.85          | ((X14) = (k2_funct_1 @ X15))
% 6.68/6.85          | ((k5_relat_1 @ X14 @ X15) != (k6_partfun1 @ (k2_relat_1 @ X15)))
% 6.68/6.85          | ((k2_relat_1 @ X14) != (k1_relat_1 @ X15))
% 6.68/6.85          | ~ (v2_funct_1 @ X15)
% 6.68/6.85          | ~ (v1_funct_1 @ X15)
% 6.68/6.85          | ~ (v1_relat_1 @ X15))),
% 6.68/6.85      inference('demod', [status(thm)], ['71', '72'])).
% 6.68/6.85  thf('193', plain,
% 6.68/6.85      ((((k6_partfun1 @ sk_A_1)
% 6.68/6.85          != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))
% 6.68/6.85        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 6.68/6.85        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 6.68/6.85        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 6.68/6.85        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 6.68/6.85        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 6.68/6.85        | ~ (v1_funct_1 @ sk_C)
% 6.68/6.85        | ~ (v1_relat_1 @ sk_C))),
% 6.68/6.85      inference('sup-', [status(thm)], ['191', '192'])).
% 6.68/6.85  thf('194', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 6.68/6.85      inference('sup+', [status(thm)], ['33', '34'])).
% 6.68/6.85  thf('195', plain, ((v1_funct_1 @ sk_C)),
% 6.68/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.68/6.85  thf('196', plain, ((v1_relat_1 @ sk_C)),
% 6.68/6.85      inference('sup-', [status(thm)], ['44', '45'])).
% 6.68/6.85  thf('197', plain,
% 6.68/6.85      ((((k6_partfun1 @ sk_A_1)
% 6.68/6.85          != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))
% 6.68/6.85        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 6.68/6.85        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 6.68/6.85        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 6.68/6.85        | ((sk_B) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 6.68/6.85        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 6.68/6.85      inference('demod', [status(thm)], ['193', '194', '195', '196'])).
% 6.68/6.85  thf('198', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 6.68/6.85      inference('demod', [status(thm)], ['117', '124', '125', '126', '127'])).
% 6.68/6.85  thf('199', plain,
% 6.68/6.85      ((((k6_partfun1 @ sk_A_1)
% 6.68/6.85          != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))
% 6.68/6.85        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 6.68/6.85        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 6.68/6.85        | ((sk_B) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 6.68/6.85        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 6.68/6.85      inference('demod', [status(thm)], ['197', '198'])).
% 6.68/6.85  thf('200', plain,
% 6.68/6.85      ((~ (v1_relat_1 @ sk_C)
% 6.68/6.85        | ~ (v1_funct_1 @ sk_C)
% 6.68/6.85        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 6.68/6.85        | ((sk_B) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 6.68/6.85        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 6.68/6.85        | ((k6_partfun1 @ sk_A_1)
% 6.68/6.85            != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 6.68/6.85      inference('sup-', [status(thm)], ['190', '199'])).
% 6.68/6.85  thf('201', plain, ((v1_relat_1 @ sk_C)),
% 6.68/6.85      inference('sup-', [status(thm)], ['44', '45'])).
% 6.68/6.85  thf('202', plain, ((v1_funct_1 @ sk_C)),
% 6.68/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.68/6.85  thf('203', plain,
% 6.68/6.85      ((((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 6.68/6.85        | ((sk_B) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 6.68/6.85        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 6.68/6.85        | ((k6_partfun1 @ sk_A_1)
% 6.68/6.85            != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 6.68/6.85      inference('demod', [status(thm)], ['200', '201', '202'])).
% 6.68/6.85  thf('204', plain,
% 6.68/6.85      ((~ (v1_relat_1 @ sk_C)
% 6.68/6.85        | ~ (v1_funct_1 @ sk_C)
% 6.68/6.85        | ~ (v2_funct_1 @ sk_C)
% 6.68/6.85        | ((k6_partfun1 @ sk_A_1)
% 6.68/6.85            != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))
% 6.68/6.85        | ((sk_B) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 6.68/6.85        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 6.68/6.85      inference('sup-', [status(thm)], ['189', '203'])).
% 6.68/6.85  thf('205', plain, ((v1_relat_1 @ sk_C)),
% 6.68/6.85      inference('sup-', [status(thm)], ['44', '45'])).
% 6.68/6.85  thf('206', plain, ((v1_funct_1 @ sk_C)),
% 6.68/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.68/6.85  thf('207', plain, ((v2_funct_1 @ sk_C)),
% 6.68/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.68/6.85  thf('208', plain,
% 6.68/6.85      ((((k6_partfun1 @ sk_A_1)
% 6.68/6.85          != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))
% 6.68/6.85        | ((sk_B) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 6.68/6.85        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 6.68/6.85      inference('demod', [status(thm)], ['204', '205', '206', '207'])).
% 6.68/6.85  thf('209', plain, (((sk_A_1) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 6.68/6.85      inference('demod', [status(thm)], ['52', '54', '55', '66', '69'])).
% 6.68/6.85  thf('210', plain,
% 6.68/6.85      ((((k6_partfun1 @ sk_A_1) != (k6_partfun1 @ sk_A_1))
% 6.68/6.85        | ((sk_B) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 6.68/6.85        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 6.68/6.85      inference('demod', [status(thm)], ['208', '209'])).
% 6.68/6.85  thf('211', plain,
% 6.68/6.85      ((((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 6.68/6.85        | ((sk_B) != (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 6.68/6.85      inference('simplify', [status(thm)], ['210'])).
% 6.68/6.85  thf('212', plain,
% 6.68/6.85      ((((sk_B) != (k2_relat_1 @ sk_C))
% 6.68/6.85        | ~ (v1_relat_1 @ sk_C)
% 6.68/6.85        | ~ (v1_funct_1 @ sk_C)
% 6.68/6.85        | ~ (v2_funct_1 @ sk_C)
% 6.68/6.85        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 6.68/6.85      inference('sup-', [status(thm)], ['188', '211'])).
% 6.68/6.85  thf('213', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 6.68/6.85      inference('sup+', [status(thm)], ['33', '34'])).
% 6.68/6.85  thf('214', plain, ((v1_relat_1 @ sk_C)),
% 6.68/6.85      inference('sup-', [status(thm)], ['44', '45'])).
% 6.68/6.85  thf('215', plain, ((v1_funct_1 @ sk_C)),
% 6.68/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.68/6.85  thf('216', plain, ((v2_funct_1 @ sk_C)),
% 6.68/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.68/6.85  thf('217', plain,
% 6.68/6.85      ((((sk_B) != (sk_B)) | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 6.68/6.85      inference('demod', [status(thm)], ['212', '213', '214', '215', '216'])).
% 6.68/6.85  thf('218', plain, (((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 6.68/6.85      inference('simplify', [status(thm)], ['217'])).
% 6.68/6.85  thf('219', plain,
% 6.68/6.85      (![X13 : $i]:
% 6.68/6.85         (~ (v2_funct_1 @ X13)
% 6.68/6.85          | ((k1_relat_1 @ X13) = (k2_relat_1 @ (k2_funct_1 @ X13)))
% 6.68/6.85          | ~ (v1_funct_1 @ X13)
% 6.68/6.85          | ~ (v1_relat_1 @ X13))),
% 6.68/6.85      inference('cnf', [status(esa)], [t55_funct_1])).
% 6.68/6.85  thf('220', plain,
% 6.68/6.85      ((((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))
% 6.68/6.85        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 6.68/6.85        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 6.68/6.85        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 6.68/6.85      inference('sup+', [status(thm)], ['218', '219'])).
% 6.68/6.85  thf('221', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 6.68/6.85      inference('sup+', [status(thm)], ['33', '34'])).
% 6.68/6.85  thf('222', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 6.68/6.85      inference('demod', [status(thm)], ['117', '124', '125', '126', '127'])).
% 6.68/6.85  thf('223', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 6.68/6.85      inference('demod', [status(thm)], ['153', '154', '155', '156', '157'])).
% 6.68/6.85  thf('224', plain,
% 6.68/6.85      ((((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_B))
% 6.68/6.85        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 6.68/6.85      inference('demod', [status(thm)], ['220', '221', '222', '223'])).
% 6.68/6.85  thf('225', plain,
% 6.68/6.85      ((~ (v1_relat_1 @ sk_C)
% 6.68/6.85        | ~ (v1_funct_1 @ sk_C)
% 6.68/6.85        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_B)))),
% 6.68/6.85      inference('sup-', [status(thm)], ['187', '224'])).
% 6.68/6.85  thf('226', plain, ((v1_relat_1 @ sk_C)),
% 6.68/6.85      inference('sup-', [status(thm)], ['44', '45'])).
% 6.68/6.85  thf('227', plain, ((v1_funct_1 @ sk_C)),
% 6.68/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.68/6.85  thf('228', plain, (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_B))),
% 6.68/6.85      inference('demod', [status(thm)], ['225', '226', '227'])).
% 6.68/6.85  thf('229', plain, (((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 6.68/6.85      inference('simplify', [status(thm)], ['217'])).
% 6.68/6.85  thf('230', plain,
% 6.68/6.85      (![X0 : $i]:
% 6.68/6.85         (((k5_relat_1 @ X0 @ (k2_funct_1 @ sk_C)) != (k6_partfun1 @ sk_A_1))
% 6.68/6.85          | ((k2_relat_1 @ X0) != (sk_B))
% 6.68/6.85          | ((X0) = (sk_C))
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ X0))),
% 6.68/6.85      inference('demod', [status(thm)], ['159', '186', '228', '229'])).
% 6.68/6.85  thf('231', plain,
% 6.68/6.85      (![X0 : $i]:
% 6.68/6.85         (((k2_funct_1 @ (k5_relat_1 @ sk_C @ X0)) != (k6_partfun1 @ sk_A_1))
% 6.68/6.85          | ~ (v1_relat_1 @ sk_C)
% 6.68/6.85          | ~ (v1_funct_1 @ sk_C)
% 6.68/6.85          | ~ (v2_funct_1 @ sk_C)
% 6.68/6.85          | ~ (v2_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.68/6.85          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.68/6.85          | ((k2_funct_1 @ X0) = (sk_C))
% 6.68/6.85          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (sk_B)))),
% 6.68/6.85      inference('sup-', [status(thm)], ['30', '230'])).
% 6.68/6.85  thf('232', plain, ((v1_relat_1 @ sk_C)),
% 6.68/6.85      inference('sup-', [status(thm)], ['44', '45'])).
% 6.68/6.85  thf('233', plain, ((v1_funct_1 @ sk_C)),
% 6.68/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.68/6.85  thf('234', plain, ((v2_funct_1 @ sk_C)),
% 6.68/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.68/6.85  thf('235', plain,
% 6.68/6.85      (![X0 : $i]:
% 6.68/6.85         (((k2_funct_1 @ (k5_relat_1 @ sk_C @ X0)) != (k6_partfun1 @ sk_A_1))
% 6.68/6.85          | ~ (v2_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.68/6.85          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.68/6.85          | ((k2_funct_1 @ X0) = (sk_C))
% 6.68/6.85          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (sk_B)))),
% 6.68/6.85      inference('demod', [status(thm)], ['231', '232', '233', '234'])).
% 6.68/6.85  thf('236', plain,
% 6.68/6.85      ((((k2_funct_1 @ (k6_partfun1 @ sk_A_1)) != (k6_partfun1 @ sk_A_1))
% 6.68/6.85        | ((k2_relat_1 @ (k2_funct_1 @ sk_D)) != (sk_B))
% 6.68/6.85        | ((k2_funct_1 @ sk_D) = (sk_C))
% 6.68/6.85        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_D))
% 6.68/6.85        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D))
% 6.68/6.85        | ~ (v1_relat_1 @ sk_D)
% 6.68/6.85        | ~ (v1_funct_1 @ sk_D)
% 6.68/6.85        | ~ (v2_funct_1 @ sk_D))),
% 6.68/6.85      inference('sup-', [status(thm)], ['29', '235'])).
% 6.68/6.85  thf(t67_funct_1, axiom,
% 6.68/6.85    (![A:$i]: ( ( k2_funct_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 6.68/6.85  thf('237', plain,
% 6.68/6.85      (![X19 : $i]: ((k2_funct_1 @ (k6_relat_1 @ X19)) = (k6_relat_1 @ X19))),
% 6.68/6.85      inference('cnf', [status(esa)], [t67_funct_1])).
% 6.68/6.85  thf('238', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 6.68/6.85      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 6.68/6.85  thf('239', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 6.68/6.85      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 6.68/6.85  thf('240', plain,
% 6.68/6.85      (![X19 : $i]: ((k2_funct_1 @ (k6_partfun1 @ X19)) = (k6_partfun1 @ X19))),
% 6.68/6.85      inference('demod', [status(thm)], ['237', '238', '239'])).
% 6.68/6.85  thf('241', plain,
% 6.68/6.85      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 6.68/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.68/6.85  thf('242', plain,
% 6.68/6.85      (![X20 : $i, X21 : $i, X22 : $i]:
% 6.68/6.85         ((v1_relat_1 @ X20)
% 6.68/6.85          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 6.68/6.85      inference('cnf', [status(esa)], [cc1_relset_1])).
% 6.68/6.85  thf('243', plain, ((v1_relat_1 @ sk_D)),
% 6.68/6.85      inference('sup-', [status(thm)], ['241', '242'])).
% 6.68/6.85  thf('244', plain, ((v1_funct_1 @ sk_D)),
% 6.68/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.68/6.85  thf('245', plain,
% 6.68/6.85      ((((k6_partfun1 @ sk_A_1) != (k6_partfun1 @ sk_A_1))
% 6.68/6.85        | ((k2_relat_1 @ (k2_funct_1 @ sk_D)) != (sk_B))
% 6.68/6.85        | ((k2_funct_1 @ sk_D) = (sk_C))
% 6.68/6.85        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_D))
% 6.68/6.85        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D))
% 6.68/6.85        | ~ (v2_funct_1 @ sk_D))),
% 6.68/6.85      inference('demod', [status(thm)], ['236', '240', '243', '244'])).
% 6.68/6.85  thf('246', plain,
% 6.68/6.85      ((~ (v2_funct_1 @ sk_D)
% 6.68/6.85        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D))
% 6.68/6.85        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_D))
% 6.68/6.85        | ((k2_funct_1 @ sk_D) = (sk_C))
% 6.68/6.85        | ((k2_relat_1 @ (k2_funct_1 @ sk_D)) != (sk_B)))),
% 6.68/6.85      inference('simplify', [status(thm)], ['245'])).
% 6.68/6.85  thf('247', plain,
% 6.68/6.85      ((~ (v1_relat_1 @ sk_D)
% 6.68/6.85        | ~ (v1_funct_1 @ sk_D)
% 6.68/6.85        | ((k2_relat_1 @ (k2_funct_1 @ sk_D)) != (sk_B))
% 6.68/6.85        | ((k2_funct_1 @ sk_D) = (sk_C))
% 6.68/6.85        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_D))
% 6.68/6.85        | ~ (v2_funct_1 @ sk_D))),
% 6.68/6.85      inference('sup-', [status(thm)], ['1', '246'])).
% 6.68/6.85  thf('248', plain, ((v1_relat_1 @ sk_D)),
% 6.68/6.85      inference('sup-', [status(thm)], ['241', '242'])).
% 6.68/6.85  thf('249', plain, ((v1_funct_1 @ sk_D)),
% 6.68/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.68/6.85  thf('250', plain,
% 6.68/6.85      ((((k2_relat_1 @ (k2_funct_1 @ sk_D)) != (sk_B))
% 6.68/6.85        | ((k2_funct_1 @ sk_D) = (sk_C))
% 6.68/6.85        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_D))
% 6.68/6.85        | ~ (v2_funct_1 @ sk_D))),
% 6.68/6.85      inference('demod', [status(thm)], ['247', '248', '249'])).
% 6.68/6.85  thf('251', plain,
% 6.68/6.85      ((~ (v1_relat_1 @ sk_D)
% 6.68/6.85        | ~ (v1_funct_1 @ sk_D)
% 6.68/6.85        | ~ (v2_funct_1 @ sk_D)
% 6.68/6.85        | ((k2_funct_1 @ sk_D) = (sk_C))
% 6.68/6.85        | ((k2_relat_1 @ (k2_funct_1 @ sk_D)) != (sk_B)))),
% 6.68/6.85      inference('sup-', [status(thm)], ['0', '250'])).
% 6.68/6.85  thf('252', plain, ((v1_relat_1 @ sk_D)),
% 6.68/6.85      inference('sup-', [status(thm)], ['241', '242'])).
% 6.68/6.85  thf('253', plain, ((v1_funct_1 @ sk_D)),
% 6.68/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.68/6.85  thf('254', plain,
% 6.68/6.85      ((~ (v2_funct_1 @ sk_D)
% 6.68/6.85        | ((k2_funct_1 @ sk_D) = (sk_C))
% 6.68/6.85        | ((k2_relat_1 @ (k2_funct_1 @ sk_D)) != (sk_B)))),
% 6.68/6.85      inference('demod', [status(thm)], ['251', '252', '253'])).
% 6.68/6.85  thf('255', plain,
% 6.68/6.85      (((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 6.68/6.85         = (k5_relat_1 @ sk_C @ sk_D))),
% 6.68/6.85      inference('demod', [status(thm)], ['9', '10'])).
% 6.68/6.85  thf('256', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A_1))),
% 6.68/6.85      inference('demod', [status(thm)], ['25', '28'])).
% 6.68/6.85  thf('257', plain,
% 6.68/6.85      (((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 6.68/6.85         = (k6_partfun1 @ sk_A_1))),
% 6.68/6.85      inference('demod', [status(thm)], ['255', '256'])).
% 6.68/6.85  thf('258', plain,
% 6.68/6.85      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 6.68/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.68/6.85  thf(t30_funct_2, axiom,
% 6.68/6.85    (![A:$i,B:$i,C:$i,D:$i]:
% 6.68/6.85     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 6.68/6.85         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 6.68/6.85       ( ![E:$i]:
% 6.68/6.85         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 6.68/6.85             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 6.68/6.85           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 6.68/6.85               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 6.68/6.85             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 6.68/6.85               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 6.68/6.85  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 6.68/6.85  thf(zf_stmt_2, axiom,
% 6.68/6.85    (![C:$i,B:$i]:
% 6.68/6.85     ( ( zip_tseitin_1 @ C @ B ) =>
% 6.68/6.85       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 6.68/6.85  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 6.68/6.85  thf(zf_stmt_4, axiom,
% 6.68/6.85    (![E:$i,D:$i]:
% 6.68/6.85     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 6.68/6.85  thf(zf_stmt_5, axiom,
% 6.68/6.85    (![A:$i,B:$i,C:$i,D:$i]:
% 6.68/6.85     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 6.68/6.85         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.68/6.85       ( ![E:$i]:
% 6.68/6.85         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 6.68/6.85             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 6.68/6.85           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 6.68/6.85               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 6.68/6.85             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 6.68/6.85  thf('259', plain,
% 6.68/6.85      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 6.68/6.85         (~ (v1_funct_1 @ X52)
% 6.68/6.85          | ~ (v1_funct_2 @ X52 @ X53 @ X54)
% 6.68/6.85          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X54)))
% 6.68/6.85          | (zip_tseitin_0 @ X52 @ X55)
% 6.68/6.85          | ~ (v2_funct_1 @ (k1_partfun1 @ X56 @ X53 @ X53 @ X54 @ X55 @ X52))
% 6.68/6.85          | (zip_tseitin_1 @ X54 @ X53)
% 6.68/6.85          | ((k2_relset_1 @ X56 @ X53 @ X55) != (X53))
% 6.68/6.85          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X53)))
% 6.68/6.85          | ~ (v1_funct_2 @ X55 @ X56 @ X53)
% 6.68/6.85          | ~ (v1_funct_1 @ X55))),
% 6.68/6.85      inference('cnf', [status(esa)], [zf_stmt_5])).
% 6.68/6.85  thf('260', plain,
% 6.68/6.85      (![X0 : $i, X1 : $i]:
% 6.68/6.85         (~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 6.68/6.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 6.68/6.85          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 6.68/6.85          | (zip_tseitin_1 @ sk_A_1 @ sk_B)
% 6.68/6.85          | ~ (v2_funct_1 @ 
% 6.68/6.85               (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A_1 @ X0 @ sk_D))
% 6.68/6.85          | (zip_tseitin_0 @ sk_D @ X0)
% 6.68/6.85          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A_1)
% 6.68/6.85          | ~ (v1_funct_1 @ sk_D))),
% 6.68/6.85      inference('sup-', [status(thm)], ['258', '259'])).
% 6.68/6.85  thf('261', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A_1)),
% 6.68/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.68/6.85  thf('262', plain, ((v1_funct_1 @ sk_D)),
% 6.68/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.68/6.85  thf('263', plain,
% 6.68/6.85      (![X0 : $i, X1 : $i]:
% 6.68/6.85         (~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 6.68/6.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 6.68/6.85          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 6.68/6.85          | (zip_tseitin_1 @ sk_A_1 @ sk_B)
% 6.68/6.85          | ~ (v2_funct_1 @ 
% 6.68/6.85               (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A_1 @ X0 @ sk_D))
% 6.68/6.85          | (zip_tseitin_0 @ sk_D @ X0))),
% 6.68/6.85      inference('demod', [status(thm)], ['260', '261', '262'])).
% 6.68/6.85  thf('264', plain,
% 6.68/6.85      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A_1))
% 6.68/6.85        | (zip_tseitin_0 @ sk_D @ sk_C)
% 6.68/6.85        | (zip_tseitin_1 @ sk_A_1 @ sk_B)
% 6.68/6.85        | ((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) != (sk_B))
% 6.68/6.85        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))
% 6.68/6.85        | ~ (v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)
% 6.68/6.85        | ~ (v1_funct_1 @ sk_C))),
% 6.68/6.85      inference('sup-', [status(thm)], ['257', '263'])).
% 6.68/6.85  thf(fc4_funct_1, axiom,
% 6.68/6.85    (![A:$i]:
% 6.68/6.85     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 6.68/6.85       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 6.68/6.85  thf('265', plain, (![X11 : $i]: (v2_funct_1 @ (k6_relat_1 @ X11))),
% 6.68/6.85      inference('cnf', [status(esa)], [fc4_funct_1])).
% 6.68/6.85  thf('266', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 6.68/6.85      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 6.68/6.85  thf('267', plain, (![X11 : $i]: (v2_funct_1 @ (k6_partfun1 @ X11))),
% 6.68/6.85      inference('demod', [status(thm)], ['265', '266'])).
% 6.68/6.85  thf('268', plain, (((k2_relset_1 @ sk_A_1 @ sk_B @ sk_C) = (sk_B))),
% 6.68/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.68/6.85  thf('269', plain,
% 6.68/6.85      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 6.68/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.68/6.85  thf('270', plain, ((v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)),
% 6.68/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.68/6.85  thf('271', plain, ((v1_funct_1 @ sk_C)),
% 6.68/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.68/6.85  thf('272', plain,
% 6.68/6.85      (((zip_tseitin_0 @ sk_D @ sk_C)
% 6.68/6.85        | (zip_tseitin_1 @ sk_A_1 @ sk_B)
% 6.68/6.85        | ((sk_B) != (sk_B)))),
% 6.68/6.85      inference('demod', [status(thm)],
% 6.68/6.85                ['264', '267', '268', '269', '270', '271'])).
% 6.68/6.85  thf('273', plain,
% 6.68/6.85      (((zip_tseitin_1 @ sk_A_1 @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 6.68/6.85      inference('simplify', [status(thm)], ['272'])).
% 6.68/6.85  thf('274', plain,
% 6.68/6.85      (![X50 : $i, X51 : $i]:
% 6.68/6.85         (((X50) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X50 @ X51))),
% 6.68/6.85      inference('cnf', [status(esa)], [zf_stmt_2])).
% 6.68/6.85  thf('275', plain,
% 6.68/6.85      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A_1) = (k1_xboole_0)))),
% 6.68/6.85      inference('sup-', [status(thm)], ['273', '274'])).
% 6.68/6.85  thf('276', plain, (((sk_A_1) != (k1_xboole_0))),
% 6.68/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.68/6.85  thf('277', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 6.68/6.85      inference('simplify_reflect-', [status(thm)], ['275', '276'])).
% 6.68/6.85  thf('278', plain,
% 6.68/6.85      (![X48 : $i, X49 : $i]:
% 6.68/6.85         ((v2_funct_1 @ X49) | ~ (zip_tseitin_0 @ X49 @ X48))),
% 6.68/6.85      inference('cnf', [status(esa)], [zf_stmt_4])).
% 6.68/6.85  thf('279', plain, ((v2_funct_1 @ sk_D)),
% 6.68/6.85      inference('sup-', [status(thm)], ['277', '278'])).
% 6.68/6.85  thf('280', plain,
% 6.68/6.85      ((((k2_funct_1 @ sk_D) = (sk_C))
% 6.68/6.85        | ((k2_relat_1 @ (k2_funct_1 @ sk_D)) != (sk_B)))),
% 6.68/6.85      inference('demod', [status(thm)], ['254', '279'])).
% 6.68/6.85  thf('281', plain,
% 6.68/6.85      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 6.68/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.68/6.85  thf('282', plain,
% 6.68/6.85      (![X57 : $i, X58 : $i, X59 : $i]:
% 6.68/6.85         (((X57) = (k1_xboole_0))
% 6.68/6.85          | ~ (v1_funct_1 @ X58)
% 6.68/6.85          | ~ (v1_funct_2 @ X58 @ X59 @ X57)
% 6.68/6.85          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X57)))
% 6.68/6.85          | ((k5_relat_1 @ X58 @ (k2_funct_1 @ X58)) = (k6_partfun1 @ X59))
% 6.68/6.85          | ~ (v2_funct_1 @ X58)
% 6.68/6.85          | ((k2_relset_1 @ X59 @ X57 @ X58) != (X57)))),
% 6.68/6.85      inference('cnf', [status(esa)], [t35_funct_2])).
% 6.68/6.85  thf('283', plain,
% 6.68/6.85      ((((k2_relset_1 @ sk_B @ sk_A_1 @ sk_D) != (sk_A_1))
% 6.68/6.85        | ~ (v2_funct_1 @ sk_D)
% 6.68/6.85        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 6.68/6.85        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A_1)
% 6.68/6.85        | ~ (v1_funct_1 @ sk_D)
% 6.68/6.85        | ((sk_A_1) = (k1_xboole_0)))),
% 6.68/6.85      inference('sup-', [status(thm)], ['281', '282'])).
% 6.68/6.85  thf('284', plain,
% 6.68/6.85      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 6.68/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.68/6.85  thf('285', plain,
% 6.68/6.85      (![X23 : $i, X24 : $i, X25 : $i]:
% 6.68/6.85         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 6.68/6.85          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 6.68/6.85      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 6.68/6.85  thf('286', plain,
% 6.68/6.85      (((k2_relset_1 @ sk_B @ sk_A_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 6.68/6.85      inference('sup-', [status(thm)], ['284', '285'])).
% 6.68/6.85  thf('287', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A_1)),
% 6.68/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.68/6.85  thf('288', plain, ((v1_funct_1 @ sk_D)),
% 6.68/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.68/6.85  thf('289', plain,
% 6.68/6.85      ((((k2_relat_1 @ sk_D) != (sk_A_1))
% 6.68/6.85        | ~ (v2_funct_1 @ sk_D)
% 6.68/6.85        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 6.68/6.85        | ((sk_A_1) = (k1_xboole_0)))),
% 6.68/6.85      inference('demod', [status(thm)], ['283', '286', '287', '288'])).
% 6.68/6.85  thf('290', plain, (((sk_A_1) != (k1_xboole_0))),
% 6.68/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.68/6.85  thf('291', plain,
% 6.68/6.85      ((((k2_relat_1 @ sk_D) != (sk_A_1))
% 6.68/6.85        | ~ (v2_funct_1 @ sk_D)
% 6.68/6.85        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 6.68/6.85      inference('simplify_reflect-', [status(thm)], ['289', '290'])).
% 6.68/6.85  thf('292', plain,
% 6.68/6.85      (((k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ sk_D)
% 6.68/6.85         = (k5_relat_1 @ sk_C @ sk_D))),
% 6.68/6.85      inference('demod', [status(thm)], ['9', '10'])).
% 6.68/6.85  thf('293', plain,
% 6.68/6.85      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B)))),
% 6.68/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.68/6.85  thf(t24_funct_2, axiom,
% 6.68/6.85    (![A:$i,B:$i,C:$i]:
% 6.68/6.85     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.68/6.85         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.68/6.85       ( ![D:$i]:
% 6.68/6.85         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 6.68/6.85             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 6.68/6.85           ( ( r2_relset_1 @
% 6.68/6.85               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 6.68/6.85               ( k6_partfun1 @ B ) ) =>
% 6.68/6.85             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 6.68/6.85  thf('294', plain,
% 6.68/6.85      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 6.68/6.85         (~ (v1_funct_1 @ X44)
% 6.68/6.85          | ~ (v1_funct_2 @ X44 @ X45 @ X46)
% 6.68/6.85          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 6.68/6.85          | ~ (r2_relset_1 @ X45 @ X45 @ 
% 6.68/6.85               (k1_partfun1 @ X45 @ X46 @ X46 @ X45 @ X44 @ X47) @ 
% 6.68/6.85               (k6_partfun1 @ X45))
% 6.68/6.85          | ((k2_relset_1 @ X46 @ X45 @ X47) = (X45))
% 6.68/6.85          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45)))
% 6.68/6.85          | ~ (v1_funct_2 @ X47 @ X46 @ X45)
% 6.68/6.85          | ~ (v1_funct_1 @ X47))),
% 6.68/6.85      inference('cnf', [status(esa)], [t24_funct_2])).
% 6.68/6.85  thf('295', plain,
% 6.68/6.85      (![X0 : $i]:
% 6.68/6.85         (~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A_1)
% 6.68/6.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))
% 6.68/6.85          | ((k2_relset_1 @ sk_B @ sk_A_1 @ X0) = (sk_A_1))
% 6.68/6.85          | ~ (r2_relset_1 @ sk_A_1 @ sk_A_1 @ 
% 6.68/6.85               (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ X0) @ 
% 6.68/6.85               (k6_partfun1 @ sk_A_1))
% 6.68/6.85          | ~ (v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)
% 6.68/6.85          | ~ (v1_funct_1 @ sk_C))),
% 6.68/6.85      inference('sup-', [status(thm)], ['293', '294'])).
% 6.68/6.85  thf('296', plain, ((v1_funct_2 @ sk_C @ sk_A_1 @ sk_B)),
% 6.68/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.68/6.85  thf('297', plain, ((v1_funct_1 @ sk_C)),
% 6.68/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.68/6.85  thf('298', plain,
% 6.68/6.85      (![X0 : $i]:
% 6.68/6.85         (~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A_1)
% 6.68/6.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))
% 6.68/6.85          | ((k2_relset_1 @ sk_B @ sk_A_1 @ X0) = (sk_A_1))
% 6.68/6.85          | ~ (r2_relset_1 @ sk_A_1 @ sk_A_1 @ 
% 6.68/6.85               (k1_partfun1 @ sk_A_1 @ sk_B @ sk_B @ sk_A_1 @ sk_C @ X0) @ 
% 6.68/6.85               (k6_partfun1 @ sk_A_1)))),
% 6.68/6.85      inference('demod', [status(thm)], ['295', '296', '297'])).
% 6.68/6.85  thf('299', plain,
% 6.68/6.85      ((~ (r2_relset_1 @ sk_A_1 @ sk_A_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 6.68/6.85           (k6_partfun1 @ sk_A_1))
% 6.68/6.85        | ((k2_relset_1 @ sk_B @ sk_A_1 @ sk_D) = (sk_A_1))
% 6.68/6.85        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))
% 6.68/6.85        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A_1)
% 6.68/6.85        | ~ (v1_funct_1 @ sk_D))),
% 6.68/6.85      inference('sup-', [status(thm)], ['292', '298'])).
% 6.68/6.85  thf('300', plain,
% 6.68/6.85      ((r2_relset_1 @ sk_A_1 @ sk_A_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 6.68/6.85        (k6_partfun1 @ sk_A_1))),
% 6.68/6.85      inference('demod', [status(thm)], ['2', '11'])).
% 6.68/6.85  thf('301', plain,
% 6.68/6.85      (((k2_relset_1 @ sk_B @ sk_A_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 6.68/6.85      inference('sup-', [status(thm)], ['284', '285'])).
% 6.68/6.85  thf('302', plain,
% 6.68/6.85      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A_1)))),
% 6.68/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.68/6.85  thf('303', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A_1)),
% 6.68/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.68/6.85  thf('304', plain, ((v1_funct_1 @ sk_D)),
% 6.68/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.68/6.85  thf('305', plain, (((k2_relat_1 @ sk_D) = (sk_A_1))),
% 6.68/6.85      inference('demod', [status(thm)],
% 6.68/6.85                ['299', '300', '301', '302', '303', '304'])).
% 6.68/6.85  thf('306', plain,
% 6.68/6.85      ((((sk_A_1) != (sk_A_1))
% 6.68/6.85        | ~ (v2_funct_1 @ sk_D)
% 6.68/6.85        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 6.68/6.85      inference('demod', [status(thm)], ['291', '305'])).
% 6.68/6.85  thf('307', plain,
% 6.68/6.85      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 6.68/6.85        | ~ (v2_funct_1 @ sk_D))),
% 6.68/6.85      inference('simplify', [status(thm)], ['306'])).
% 6.68/6.85  thf('308', plain, ((v2_funct_1 @ sk_D)),
% 6.68/6.85      inference('sup-', [status(thm)], ['277', '278'])).
% 6.68/6.85  thf('309', plain,
% 6.68/6.85      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 6.68/6.85      inference('demod', [status(thm)], ['307', '308'])).
% 6.68/6.85  thf('310', plain,
% 6.68/6.85      (![X9 : $i]:
% 6.68/6.85         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 6.68/6.85          | ~ (v1_funct_1 @ X9)
% 6.68/6.85          | ~ (v1_relat_1 @ X9))),
% 6.68/6.85      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.68/6.85  thf('311', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 6.68/6.85      inference('simplify', [status(thm)], ['53'])).
% 6.68/6.85  thf('312', plain,
% 6.68/6.85      (![X0 : $i, X1 : $i]:
% 6.68/6.85         (~ (r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X1))
% 6.68/6.85          | ~ (v1_relat_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v2_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.68/6.85          | ((k2_relat_1 @ (k5_relat_1 @ X1 @ (k2_funct_1 @ X0)))
% 6.68/6.85              = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 6.68/6.85          | ~ (v1_relat_1 @ X1))),
% 6.68/6.85      inference('sup-', [status(thm)], ['38', '39'])).
% 6.68/6.85  thf('313', plain,
% 6.68/6.85      (![X0 : $i]:
% 6.68/6.85         (~ (v1_relat_1 @ X0)
% 6.68/6.85          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 6.68/6.85              = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 6.68/6.85          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.68/6.85          | ~ (v2_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ X0))),
% 6.68/6.85      inference('sup-', [status(thm)], ['311', '312'])).
% 6.68/6.85  thf('314', plain,
% 6.68/6.85      (![X0 : $i]:
% 6.68/6.85         (~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v2_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.68/6.85          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 6.68/6.85              = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 6.68/6.85          | ~ (v1_relat_1 @ X0))),
% 6.68/6.85      inference('simplify', [status(thm)], ['313'])).
% 6.68/6.85  thf('315', plain,
% 6.68/6.85      (![X0 : $i]:
% 6.68/6.85         (~ (v1_relat_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ X0)
% 6.68/6.85          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 6.68/6.85              = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 6.68/6.85          | ~ (v2_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_funct_1 @ X0))),
% 6.68/6.85      inference('sup-', [status(thm)], ['310', '314'])).
% 6.68/6.85  thf('316', plain,
% 6.68/6.85      (![X0 : $i]:
% 6.68/6.85         (~ (v2_funct_1 @ X0)
% 6.68/6.85          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 6.68/6.85              = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 6.68/6.85          | ~ (v1_funct_1 @ X0)
% 6.68/6.85          | ~ (v1_relat_1 @ X0))),
% 6.68/6.85      inference('simplify', [status(thm)], ['315'])).
% 6.68/6.85  thf('317', plain,
% 6.68/6.85      ((((k2_relat_1 @ (k6_partfun1 @ sk_B))
% 6.68/6.85          = (k2_relat_1 @ (k2_funct_1 @ sk_D)))
% 6.68/6.85        | ~ (v1_relat_1 @ sk_D)
% 6.68/6.85        | ~ (v1_funct_1 @ sk_D)
% 6.68/6.85        | ~ (v2_funct_1 @ sk_D))),
% 6.68/6.85      inference('sup+', [status(thm)], ['309', '316'])).
% 6.68/6.85  thf('318', plain, (![X7 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X7)) = (X7))),
% 6.68/6.85      inference('demod', [status(thm)], ['67', '68'])).
% 6.68/6.85  thf('319', plain, ((v1_relat_1 @ sk_D)),
% 6.68/6.85      inference('sup-', [status(thm)], ['241', '242'])).
% 6.68/6.85  thf('320', plain, ((v1_funct_1 @ sk_D)),
% 6.68/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.68/6.85  thf('321', plain, ((v2_funct_1 @ sk_D)),
% 6.68/6.85      inference('sup-', [status(thm)], ['277', '278'])).
% 6.68/6.85  thf('322', plain, (((sk_B) = (k2_relat_1 @ (k2_funct_1 @ sk_D)))),
% 6.68/6.85      inference('demod', [status(thm)], ['317', '318', '319', '320', '321'])).
% 6.68/6.85  thf('323', plain, ((((k2_funct_1 @ sk_D) = (sk_C)) | ((sk_B) != (sk_B)))),
% 6.68/6.85      inference('demod', [status(thm)], ['280', '322'])).
% 6.68/6.85  thf('324', plain, (((k2_funct_1 @ sk_D) = (sk_C))),
% 6.68/6.85      inference('simplify', [status(thm)], ['323'])).
% 6.68/6.85  thf('325', plain,
% 6.68/6.85      (![X16 : $i]:
% 6.68/6.85         (~ (v2_funct_1 @ X16)
% 6.68/6.85          | ((k2_funct_1 @ (k2_funct_1 @ X16)) = (X16))
% 6.68/6.85          | ~ (v1_funct_1 @ X16)
% 6.68/6.85          | ~ (v1_relat_1 @ X16))),
% 6.68/6.85      inference('cnf', [status(esa)], [t65_funct_1])).
% 6.68/6.85  thf('326', plain,
% 6.68/6.85      ((((k2_funct_1 @ sk_C) = (sk_D))
% 6.68/6.85        | ~ (v1_relat_1 @ sk_D)
% 6.68/6.85        | ~ (v1_funct_1 @ sk_D)
% 6.68/6.85        | ~ (v2_funct_1 @ sk_D))),
% 6.68/6.85      inference('sup+', [status(thm)], ['324', '325'])).
% 6.68/6.85  thf('327', plain, ((v1_relat_1 @ sk_D)),
% 6.68/6.85      inference('sup-', [status(thm)], ['241', '242'])).
% 6.68/6.85  thf('328', plain, ((v1_funct_1 @ sk_D)),
% 6.68/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.68/6.85  thf('329', plain, ((v2_funct_1 @ sk_D)),
% 6.68/6.85      inference('sup-', [status(thm)], ['277', '278'])).
% 6.68/6.85  thf('330', plain, (((k2_funct_1 @ sk_C) = (sk_D))),
% 6.68/6.85      inference('demod', [status(thm)], ['326', '327', '328', '329'])).
% 6.68/6.85  thf('331', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 6.68/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.68/6.85  thf('332', plain, ($false),
% 6.68/6.85      inference('simplify_reflect-', [status(thm)], ['330', '331'])).
% 6.68/6.85  
% 6.68/6.85  % SZS output end Refutation
% 6.68/6.85  
% 6.68/6.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bfetCuq3eV

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:01 EST 2020

% Result     : Theorem 7.61s
% Output     : Refutation 7.61s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 482 expanded)
%              Number of leaves         :   46 ( 153 expanded)
%              Depth                    :   18
%              Number of atoms          : 1312 (9447 expanded)
%              Number of equality atoms :   45 ( 113 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t29_funct_2,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
             => ( ( v2_funct_1 @ C )
                & ( v2_funct_2 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_funct_2])).

thf('0',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('2',plain,(
    ! [X21: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X57: $i] :
      ( ( k6_partfun1 @ X57 )
      = ( k6_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('4',plain,(
    ! [X21: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X21 ) )
      = X21 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X16: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(fc24_relat_1,axiom,(
    ! [A: $i] :
      ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('8',plain,(
    ! [X57: $i] :
      ( ( k6_partfun1 @ X57 )
      = ( k6_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('9',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X24 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','9'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k6_partfun1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,
    ( ! [X0: $i] :
        ( ~ ( v2_funct_1 @ ( k6_partfun1 @ X0 ) )
        | ~ ( v1_xboole_0 @ sk_C )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('15',plain,(
    ! [X28: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('16',plain,(
    ! [X57: $i] :
      ( ( k6_partfun1 @ X57 )
      = ( k6_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('17',plain,(
    ! [X28: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X28 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ sk_C )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(condensation,[status(thm)],['18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
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

thf('22',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X53 ) ) )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_funct_1 @ X54 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X56 ) ) )
      | ( ( k1_partfun1 @ X52 @ X53 @ X55 @ X56 @ X51 @ X54 )
        = ( k5_relat_1 @ X51 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
           => ( ( ( C = k1_xboole_0 )
                & ( B != k1_xboole_0 ) )
              | ( v2_funct_1 @ D ) ) ) ) ) )).

thf('30',plain,(
    ! [X58: $i,X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ~ ( v1_funct_1 @ X58 )
      | ~ ( v1_funct_2 @ X58 @ X59 @ X60 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X60 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X61 @ X59 @ X59 @ X60 @ X62 @ X58 ) )
      | ( v2_funct_1 @ X62 )
      | ( X60 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X61 @ X59 ) ) )
      | ~ ( v1_funct_2 @ X62 @ X61 @ X59 )
      | ~ ( v1_funct_1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['28','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf('40',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('42',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
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

thf('45',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X43 @ X44 @ X46 @ X47 @ X42 @ X45 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X47 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','48'])).

thf('50',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('53',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('54',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( X36 = X39 )
      | ~ ( r2_relset_1 @ X37 @ X38 @ X36 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','55'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('57',plain,(
    ! [X49: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X49 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('58',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X28: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X28 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('60',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','58','59'])).

thf('61',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('62',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(fc4_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('63',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_xboole_0 @ X7 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('65',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_xboole_0 @ X9 )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('66',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_C ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['62','67'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('69',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('70',plain,
    ( ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['19','70'])).

thf('72',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('73',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['71','72'])).

thf('74',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','73'])).

thf('75',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('76',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v1_relat_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('77',plain,(
    v1_relat_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('79',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['77','78'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('80',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X18 @ X17 ) ) @ ( k2_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('81',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ( v5_relat_1 @ X12 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( v5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( v5_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['79','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v1_relat_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('86',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v1_relat_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('89',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v5_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['83','86','89'])).

thf('91',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v5_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('92',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('94',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) @ ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['92','93'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('95',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('96',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
    | ( ( k2_relat_1 @ sk_D )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('98',plain,(
    ! [X21: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X21 ) )
      = X21 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('99',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('100',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v5_relat_1 @ X33 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('101',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v5_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('103',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['84','85'])).

thf('105',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('107',plain,(
    ! [X21: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X21 ) )
      = X21 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('108',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['96','97','98','105','106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('110',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ( v5_relat_1 @ X12 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('113',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k2_relat_1 @ X41 )
       != X40 )
      | ( v2_funct_2 @ X41 @ X40 )
      | ~ ( v5_relat_1 @ X41 @ X40 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('114',plain,(
    ! [X41: $i] :
      ( ~ ( v1_relat_1 @ X41 )
      | ~ ( v5_relat_1 @ X41 @ ( k2_relat_1 @ X41 ) )
      | ( v2_funct_2 @ X41 @ ( k2_relat_1 @ X41 ) ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['112','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,
    ( ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['108','116'])).

thf('118',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['84','85'])).

thf('119',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    $false ),
    inference(demod,[status(thm)],['74','119'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bfetCuq3eV
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:02:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 7.61/7.78  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 7.61/7.78  % Solved by: fo/fo7.sh
% 7.61/7.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.61/7.78  % done 6425 iterations in 7.310s
% 7.61/7.78  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 7.61/7.78  % SZS output start Refutation
% 7.61/7.78  thf(sk_D_type, type, sk_D: $i).
% 7.61/7.78  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 7.61/7.78  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 7.61/7.78  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 7.61/7.78  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 7.61/7.78  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 7.61/7.78  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 7.61/7.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 7.61/7.78  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 7.61/7.78  thf(sk_C_type, type, sk_C: $i).
% 7.61/7.78  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 7.61/7.78  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 7.61/7.78  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 7.61/7.78  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 7.61/7.78  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 7.61/7.78  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 7.61/7.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.61/7.78  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 7.61/7.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 7.61/7.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 7.61/7.78  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 7.61/7.78  thf(sk_B_type, type, sk_B: $i).
% 7.61/7.78  thf(sk_A_type, type, sk_A: $i).
% 7.61/7.78  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 7.61/7.78  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 7.61/7.78  thf(t29_funct_2, conjecture,
% 7.61/7.78    (![A:$i,B:$i,C:$i]:
% 7.61/7.78     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 7.61/7.78         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 7.61/7.78       ( ![D:$i]:
% 7.61/7.78         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 7.61/7.78             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 7.61/7.78           ( ( r2_relset_1 @
% 7.61/7.78               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 7.61/7.78               ( k6_partfun1 @ A ) ) =>
% 7.61/7.78             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 7.61/7.78  thf(zf_stmt_0, negated_conjecture,
% 7.61/7.78    (~( ![A:$i,B:$i,C:$i]:
% 7.61/7.78        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 7.61/7.78            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 7.61/7.78          ( ![D:$i]:
% 7.61/7.78            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 7.61/7.78                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 7.61/7.78              ( ( r2_relset_1 @
% 7.61/7.78                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 7.61/7.78                  ( k6_partfun1 @ A ) ) =>
% 7.61/7.78                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 7.61/7.78    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 7.61/7.78  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 7.61/7.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.61/7.78  thf('1', plain,
% 7.61/7.78      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 7.61/7.78      inference('split', [status(esa)], ['0'])).
% 7.61/7.78  thf(t71_relat_1, axiom,
% 7.61/7.78    (![A:$i]:
% 7.61/7.78     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 7.61/7.78       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 7.61/7.78  thf('2', plain, (![X21 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 7.61/7.78      inference('cnf', [status(esa)], [t71_relat_1])).
% 7.61/7.78  thf(redefinition_k6_partfun1, axiom,
% 7.61/7.78    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 7.61/7.78  thf('3', plain, (![X57 : $i]: ((k6_partfun1 @ X57) = (k6_relat_1 @ X57))),
% 7.61/7.78      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 7.61/7.78  thf('4', plain, (![X21 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X21)) = (X21))),
% 7.61/7.78      inference('demod', [status(thm)], ['2', '3'])).
% 7.61/7.78  thf(fc9_relat_1, axiom,
% 7.61/7.78    (![A:$i]:
% 7.61/7.78     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 7.61/7.78       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 7.61/7.78  thf('5', plain,
% 7.61/7.78      (![X16 : $i]:
% 7.61/7.78         (~ (v1_xboole_0 @ (k2_relat_1 @ X16))
% 7.61/7.78          | ~ (v1_relat_1 @ X16)
% 7.61/7.78          | (v1_xboole_0 @ X16))),
% 7.61/7.78      inference('cnf', [status(esa)], [fc9_relat_1])).
% 7.61/7.78  thf('6', plain,
% 7.61/7.78      (![X0 : $i]:
% 7.61/7.78         (~ (v1_xboole_0 @ X0)
% 7.61/7.78          | (v1_xboole_0 @ (k6_partfun1 @ X0))
% 7.61/7.78          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 7.61/7.78      inference('sup-', [status(thm)], ['4', '5'])).
% 7.61/7.78  thf(fc24_relat_1, axiom,
% 7.61/7.78    (![A:$i]:
% 7.61/7.78     ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 7.61/7.78       ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 7.61/7.78       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 7.61/7.78  thf('7', plain, (![X24 : $i]: (v1_relat_1 @ (k6_relat_1 @ X24))),
% 7.61/7.78      inference('cnf', [status(esa)], [fc24_relat_1])).
% 7.61/7.78  thf('8', plain, (![X57 : $i]: ((k6_partfun1 @ X57) = (k6_relat_1 @ X57))),
% 7.61/7.78      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 7.61/7.78  thf('9', plain, (![X24 : $i]: (v1_relat_1 @ (k6_partfun1 @ X24))),
% 7.61/7.78      inference('demod', [status(thm)], ['7', '8'])).
% 7.61/7.78  thf('10', plain,
% 7.61/7.78      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k6_partfun1 @ X0)))),
% 7.61/7.78      inference('demod', [status(thm)], ['6', '9'])).
% 7.61/7.78  thf(t8_boole, axiom,
% 7.61/7.78    (![A:$i,B:$i]:
% 7.61/7.78     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 7.61/7.78  thf('11', plain,
% 7.61/7.78      (![X3 : $i, X4 : $i]:
% 7.61/7.78         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 7.61/7.78      inference('cnf', [status(esa)], [t8_boole])).
% 7.61/7.78  thf('12', plain,
% 7.61/7.78      (![X0 : $i, X1 : $i]:
% 7.61/7.78         (~ (v1_xboole_0 @ X0)
% 7.61/7.78          | ((k6_partfun1 @ X0) = (X1))
% 7.61/7.78          | ~ (v1_xboole_0 @ X1))),
% 7.61/7.78      inference('sup-', [status(thm)], ['10', '11'])).
% 7.61/7.78  thf('13', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 7.61/7.78      inference('split', [status(esa)], ['0'])).
% 7.61/7.78  thf('14', plain,
% 7.61/7.78      ((![X0 : $i]:
% 7.61/7.78          (~ (v2_funct_1 @ (k6_partfun1 @ X0))
% 7.61/7.78           | ~ (v1_xboole_0 @ sk_C)
% 7.61/7.78           | ~ (v1_xboole_0 @ X0)))
% 7.61/7.78         <= (~ ((v2_funct_1 @ sk_C)))),
% 7.61/7.78      inference('sup-', [status(thm)], ['12', '13'])).
% 7.61/7.78  thf(fc4_funct_1, axiom,
% 7.61/7.78    (![A:$i]:
% 7.61/7.78     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 7.61/7.78       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 7.61/7.78  thf('15', plain, (![X28 : $i]: (v2_funct_1 @ (k6_relat_1 @ X28))),
% 7.61/7.78      inference('cnf', [status(esa)], [fc4_funct_1])).
% 7.61/7.78  thf('16', plain, (![X57 : $i]: ((k6_partfun1 @ X57) = (k6_relat_1 @ X57))),
% 7.61/7.78      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 7.61/7.78  thf('17', plain, (![X28 : $i]: (v2_funct_1 @ (k6_partfun1 @ X28))),
% 7.61/7.78      inference('demod', [status(thm)], ['15', '16'])).
% 7.61/7.78  thf('18', plain,
% 7.61/7.78      ((![X0 : $i]: (~ (v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ X0)))
% 7.61/7.78         <= (~ ((v2_funct_1 @ sk_C)))),
% 7.61/7.78      inference('demod', [status(thm)], ['14', '17'])).
% 7.61/7.78  thf('19', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 7.61/7.78      inference('condensation', [status(thm)], ['18'])).
% 7.61/7.78  thf('20', plain,
% 7.61/7.78      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 7.61/7.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.61/7.78  thf('21', plain,
% 7.61/7.78      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 7.61/7.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.61/7.78  thf(redefinition_k1_partfun1, axiom,
% 7.61/7.78    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 7.61/7.78     ( ( ( v1_funct_1 @ E ) & 
% 7.61/7.78         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 7.61/7.78         ( v1_funct_1 @ F ) & 
% 7.61/7.78         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 7.61/7.78       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 7.61/7.78  thf('22', plain,
% 7.61/7.78      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 7.61/7.78         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X53)))
% 7.61/7.78          | ~ (v1_funct_1 @ X51)
% 7.61/7.78          | ~ (v1_funct_1 @ X54)
% 7.61/7.78          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X56)))
% 7.61/7.78          | ((k1_partfun1 @ X52 @ X53 @ X55 @ X56 @ X51 @ X54)
% 7.61/7.78              = (k5_relat_1 @ X51 @ X54)))),
% 7.61/7.78      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 7.61/7.78  thf('23', plain,
% 7.61/7.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.61/7.78         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 7.61/7.78            = (k5_relat_1 @ sk_C @ X0))
% 7.61/7.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 7.61/7.78          | ~ (v1_funct_1 @ X0)
% 7.61/7.78          | ~ (v1_funct_1 @ sk_C))),
% 7.61/7.78      inference('sup-', [status(thm)], ['21', '22'])).
% 7.61/7.78  thf('24', plain, ((v1_funct_1 @ sk_C)),
% 7.61/7.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.61/7.78  thf('25', plain,
% 7.61/7.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.61/7.78         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 7.61/7.78            = (k5_relat_1 @ sk_C @ X0))
% 7.61/7.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 7.61/7.78          | ~ (v1_funct_1 @ X0))),
% 7.61/7.78      inference('demod', [status(thm)], ['23', '24'])).
% 7.61/7.78  thf('26', plain,
% 7.61/7.78      ((~ (v1_funct_1 @ sk_D)
% 7.61/7.78        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 7.61/7.78            = (k5_relat_1 @ sk_C @ sk_D)))),
% 7.61/7.78      inference('sup-', [status(thm)], ['20', '25'])).
% 7.61/7.78  thf('27', plain, ((v1_funct_1 @ sk_D)),
% 7.61/7.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.61/7.78  thf('28', plain,
% 7.61/7.78      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 7.61/7.78         = (k5_relat_1 @ sk_C @ sk_D))),
% 7.61/7.78      inference('demod', [status(thm)], ['26', '27'])).
% 7.61/7.78  thf('29', plain,
% 7.61/7.78      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 7.61/7.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.61/7.78  thf(t26_funct_2, axiom,
% 7.61/7.78    (![A:$i,B:$i,C:$i,D:$i]:
% 7.61/7.78     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 7.61/7.78         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 7.61/7.78       ( ![E:$i]:
% 7.61/7.78         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 7.61/7.78             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 7.61/7.78           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 7.61/7.78             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 7.61/7.78               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 7.61/7.78  thf('30', plain,
% 7.61/7.78      (![X58 : $i, X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 7.61/7.78         (~ (v1_funct_1 @ X58)
% 7.61/7.78          | ~ (v1_funct_2 @ X58 @ X59 @ X60)
% 7.61/7.78          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X60)))
% 7.61/7.78          | ~ (v2_funct_1 @ (k1_partfun1 @ X61 @ X59 @ X59 @ X60 @ X62 @ X58))
% 7.61/7.78          | (v2_funct_1 @ X62)
% 7.61/7.78          | ((X60) = (k1_xboole_0))
% 7.61/7.78          | ~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X61 @ X59)))
% 7.61/7.78          | ~ (v1_funct_2 @ X62 @ X61 @ X59)
% 7.61/7.78          | ~ (v1_funct_1 @ X62))),
% 7.61/7.78      inference('cnf', [status(esa)], [t26_funct_2])).
% 7.61/7.78  thf('31', plain,
% 7.61/7.78      (![X0 : $i, X1 : $i]:
% 7.61/7.78         (~ (v1_funct_1 @ X0)
% 7.61/7.78          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 7.61/7.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 7.61/7.78          | ((sk_A) = (k1_xboole_0))
% 7.61/7.78          | (v2_funct_1 @ X0)
% 7.61/7.78          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 7.61/7.78          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 7.61/7.78          | ~ (v1_funct_1 @ sk_D))),
% 7.61/7.78      inference('sup-', [status(thm)], ['29', '30'])).
% 7.61/7.78  thf('32', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 7.61/7.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.61/7.78  thf('33', plain, ((v1_funct_1 @ sk_D)),
% 7.61/7.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.61/7.78  thf('34', plain,
% 7.61/7.78      (![X0 : $i, X1 : $i]:
% 7.61/7.78         (~ (v1_funct_1 @ X0)
% 7.61/7.78          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 7.61/7.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 7.61/7.78          | ((sk_A) = (k1_xboole_0))
% 7.61/7.78          | (v2_funct_1 @ X0)
% 7.61/7.78          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 7.61/7.78      inference('demod', [status(thm)], ['31', '32', '33'])).
% 7.61/7.78  thf('35', plain,
% 7.61/7.78      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 7.61/7.78        | (v2_funct_1 @ sk_C)
% 7.61/7.78        | ((sk_A) = (k1_xboole_0))
% 7.61/7.78        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 7.61/7.78        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 7.61/7.78        | ~ (v1_funct_1 @ sk_C))),
% 7.61/7.78      inference('sup-', [status(thm)], ['28', '34'])).
% 7.61/7.78  thf('36', plain,
% 7.61/7.78      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 7.61/7.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.61/7.78  thf('37', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 7.61/7.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.61/7.78  thf('38', plain, ((v1_funct_1 @ sk_C)),
% 7.61/7.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.61/7.78  thf('39', plain,
% 7.61/7.78      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 7.61/7.78        | (v2_funct_1 @ sk_C)
% 7.61/7.78        | ((sk_A) = (k1_xboole_0)))),
% 7.61/7.78      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 7.61/7.78  thf('40', plain,
% 7.61/7.78      ((r2_relset_1 @ sk_A @ sk_A @ 
% 7.61/7.78        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 7.61/7.78        (k6_partfun1 @ sk_A))),
% 7.61/7.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.61/7.78  thf('41', plain,
% 7.61/7.78      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 7.61/7.78         = (k5_relat_1 @ sk_C @ sk_D))),
% 7.61/7.78      inference('demod', [status(thm)], ['26', '27'])).
% 7.61/7.78  thf('42', plain,
% 7.61/7.78      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 7.61/7.78        (k6_partfun1 @ sk_A))),
% 7.61/7.78      inference('demod', [status(thm)], ['40', '41'])).
% 7.61/7.78  thf('43', plain,
% 7.61/7.78      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 7.61/7.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.61/7.78  thf('44', plain,
% 7.61/7.78      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 7.61/7.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.61/7.78  thf(dt_k1_partfun1, axiom,
% 7.61/7.78    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 7.61/7.78     ( ( ( v1_funct_1 @ E ) & 
% 7.61/7.78         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 7.61/7.78         ( v1_funct_1 @ F ) & 
% 7.61/7.78         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 7.61/7.78       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 7.61/7.78         ( m1_subset_1 @
% 7.61/7.78           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 7.61/7.78           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 7.61/7.78  thf('45', plain,
% 7.61/7.78      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 7.61/7.78         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 7.61/7.78          | ~ (v1_funct_1 @ X42)
% 7.61/7.78          | ~ (v1_funct_1 @ X45)
% 7.61/7.78          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 7.61/7.78          | (m1_subset_1 @ (k1_partfun1 @ X43 @ X44 @ X46 @ X47 @ X42 @ X45) @ 
% 7.61/7.78             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X47))))),
% 7.61/7.78      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 7.61/7.78  thf('46', plain,
% 7.61/7.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.61/7.78         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 7.61/7.78           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 7.61/7.78          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 7.61/7.78          | ~ (v1_funct_1 @ X1)
% 7.61/7.78          | ~ (v1_funct_1 @ sk_C))),
% 7.61/7.78      inference('sup-', [status(thm)], ['44', '45'])).
% 7.61/7.78  thf('47', plain, ((v1_funct_1 @ sk_C)),
% 7.61/7.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.61/7.78  thf('48', plain,
% 7.61/7.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.61/7.78         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 7.61/7.78           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 7.61/7.78          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 7.61/7.78          | ~ (v1_funct_1 @ X1))),
% 7.61/7.78      inference('demod', [status(thm)], ['46', '47'])).
% 7.61/7.78  thf('49', plain,
% 7.61/7.78      ((~ (v1_funct_1 @ sk_D)
% 7.61/7.78        | (m1_subset_1 @ 
% 7.61/7.78           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 7.61/7.78           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 7.61/7.78      inference('sup-', [status(thm)], ['43', '48'])).
% 7.61/7.78  thf('50', plain, ((v1_funct_1 @ sk_D)),
% 7.61/7.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.61/7.78  thf('51', plain,
% 7.61/7.78      ((m1_subset_1 @ 
% 7.61/7.78        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 7.61/7.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 7.61/7.78      inference('demod', [status(thm)], ['49', '50'])).
% 7.61/7.78  thf('52', plain,
% 7.61/7.78      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 7.61/7.78         = (k5_relat_1 @ sk_C @ sk_D))),
% 7.61/7.78      inference('demod', [status(thm)], ['26', '27'])).
% 7.61/7.78  thf('53', plain,
% 7.61/7.78      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 7.61/7.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 7.61/7.78      inference('demod', [status(thm)], ['51', '52'])).
% 7.61/7.78  thf(redefinition_r2_relset_1, axiom,
% 7.61/7.78    (![A:$i,B:$i,C:$i,D:$i]:
% 7.61/7.78     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 7.61/7.78         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 7.61/7.78       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 7.61/7.78  thf('54', plain,
% 7.61/7.78      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 7.61/7.78         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 7.61/7.78          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 7.61/7.78          | ((X36) = (X39))
% 7.61/7.78          | ~ (r2_relset_1 @ X37 @ X38 @ X36 @ X39))),
% 7.61/7.78      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 7.61/7.78  thf('55', plain,
% 7.61/7.78      (![X0 : $i]:
% 7.61/7.78         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 7.61/7.78          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 7.61/7.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 7.61/7.78      inference('sup-', [status(thm)], ['53', '54'])).
% 7.61/7.78  thf('56', plain,
% 7.61/7.78      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 7.61/7.78           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 7.61/7.78        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 7.61/7.78      inference('sup-', [status(thm)], ['42', '55'])).
% 7.61/7.78  thf(dt_k6_partfun1, axiom,
% 7.61/7.78    (![A:$i]:
% 7.61/7.78     ( ( m1_subset_1 @
% 7.61/7.78         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 7.61/7.78       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 7.61/7.78  thf('57', plain,
% 7.61/7.78      (![X49 : $i]:
% 7.61/7.78         (m1_subset_1 @ (k6_partfun1 @ X49) @ 
% 7.61/7.78          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X49)))),
% 7.61/7.78      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 7.61/7.78  thf('58', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 7.61/7.78      inference('demod', [status(thm)], ['56', '57'])).
% 7.61/7.78  thf('59', plain, (![X28 : $i]: (v2_funct_1 @ (k6_partfun1 @ X28))),
% 7.61/7.78      inference('demod', [status(thm)], ['15', '16'])).
% 7.61/7.78  thf('60', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 7.61/7.78      inference('demod', [status(thm)], ['39', '58', '59'])).
% 7.61/7.78  thf('61', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 7.61/7.78      inference('split', [status(esa)], ['0'])).
% 7.61/7.78  thf('62', plain, ((((sk_A) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C)))),
% 7.61/7.78      inference('sup-', [status(thm)], ['60', '61'])).
% 7.61/7.78  thf(fc4_zfmisc_1, axiom,
% 7.61/7.78    (![A:$i,B:$i]:
% 7.61/7.78     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 7.61/7.78  thf('63', plain,
% 7.61/7.78      (![X7 : $i, X8 : $i]:
% 7.61/7.78         (~ (v1_xboole_0 @ X7) | (v1_xboole_0 @ (k2_zfmisc_1 @ X7 @ X8)))),
% 7.61/7.78      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 7.61/7.78  thf('64', plain,
% 7.61/7.78      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 7.61/7.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.61/7.78  thf(cc1_subset_1, axiom,
% 7.61/7.78    (![A:$i]:
% 7.61/7.78     ( ( v1_xboole_0 @ A ) =>
% 7.61/7.78       ( ![B:$i]:
% 7.61/7.78         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 7.61/7.78  thf('65', plain,
% 7.61/7.78      (![X9 : $i, X10 : $i]:
% 7.61/7.78         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 7.61/7.78          | (v1_xboole_0 @ X9)
% 7.61/7.78          | ~ (v1_xboole_0 @ X10))),
% 7.61/7.78      inference('cnf', [status(esa)], [cc1_subset_1])).
% 7.61/7.78  thf('66', plain,
% 7.61/7.78      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 7.61/7.78      inference('sup-', [status(thm)], ['64', '65'])).
% 7.61/7.78  thf('67', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C))),
% 7.61/7.78      inference('sup-', [status(thm)], ['63', '66'])).
% 7.61/7.78  thf('68', plain,
% 7.61/7.78      (((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_C)))
% 7.61/7.78         <= (~ ((v2_funct_1 @ sk_C)))),
% 7.61/7.78      inference('sup-', [status(thm)], ['62', '67'])).
% 7.61/7.78  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 7.61/7.78  thf('69', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 7.61/7.78      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 7.61/7.78  thf('70', plain, (((v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 7.61/7.78      inference('demod', [status(thm)], ['68', '69'])).
% 7.61/7.78  thf('71', plain, (((v2_funct_1 @ sk_C))),
% 7.61/7.78      inference('demod', [status(thm)], ['19', '70'])).
% 7.61/7.78  thf('72', plain, (~ ((v2_funct_2 @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_C))),
% 7.61/7.78      inference('split', [status(esa)], ['0'])).
% 7.61/7.78  thf('73', plain, (~ ((v2_funct_2 @ sk_D @ sk_A))),
% 7.61/7.78      inference('sat_resolution*', [status(thm)], ['71', '72'])).
% 7.61/7.78  thf('74', plain, (~ (v2_funct_2 @ sk_D @ sk_A)),
% 7.61/7.78      inference('simpl_trail', [status(thm)], ['1', '73'])).
% 7.61/7.78  thf('75', plain,
% 7.61/7.78      ((m1_subset_1 @ 
% 7.61/7.78        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 7.61/7.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 7.61/7.78      inference('demod', [status(thm)], ['49', '50'])).
% 7.61/7.78  thf(cc1_relset_1, axiom,
% 7.61/7.78    (![A:$i,B:$i,C:$i]:
% 7.61/7.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.61/7.78       ( v1_relat_1 @ C ) ))).
% 7.61/7.78  thf('76', plain,
% 7.61/7.78      (![X30 : $i, X31 : $i, X32 : $i]:
% 7.61/7.78         ((v1_relat_1 @ X30)
% 7.61/7.78          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 7.61/7.78      inference('cnf', [status(esa)], [cc1_relset_1])).
% 7.61/7.78  thf('77', plain,
% 7.61/7.78      ((v1_relat_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D))),
% 7.61/7.78      inference('sup-', [status(thm)], ['75', '76'])).
% 7.61/7.78  thf('78', plain,
% 7.61/7.78      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 7.61/7.78         = (k5_relat_1 @ sk_C @ sk_D))),
% 7.61/7.78      inference('demod', [status(thm)], ['26', '27'])).
% 7.61/7.78  thf('79', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))),
% 7.61/7.78      inference('demod', [status(thm)], ['77', '78'])).
% 7.61/7.78  thf(t45_relat_1, axiom,
% 7.61/7.78    (![A:$i]:
% 7.61/7.78     ( ( v1_relat_1 @ A ) =>
% 7.61/7.78       ( ![B:$i]:
% 7.61/7.78         ( ( v1_relat_1 @ B ) =>
% 7.61/7.78           ( r1_tarski @
% 7.61/7.78             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 7.61/7.78  thf('80', plain,
% 7.61/7.78      (![X17 : $i, X18 : $i]:
% 7.61/7.78         (~ (v1_relat_1 @ X17)
% 7.61/7.78          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X18 @ X17)) @ 
% 7.61/7.78             (k2_relat_1 @ X17))
% 7.61/7.78          | ~ (v1_relat_1 @ X18))),
% 7.61/7.78      inference('cnf', [status(esa)], [t45_relat_1])).
% 7.61/7.78  thf(d19_relat_1, axiom,
% 7.61/7.78    (![A:$i,B:$i]:
% 7.61/7.78     ( ( v1_relat_1 @ B ) =>
% 7.61/7.78       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 7.61/7.78  thf('81', plain,
% 7.61/7.78      (![X12 : $i, X13 : $i]:
% 7.61/7.78         (~ (r1_tarski @ (k2_relat_1 @ X12) @ X13)
% 7.61/7.78          | (v5_relat_1 @ X12 @ X13)
% 7.61/7.78          | ~ (v1_relat_1 @ X12))),
% 7.61/7.78      inference('cnf', [status(esa)], [d19_relat_1])).
% 7.61/7.78  thf('82', plain,
% 7.61/7.78      (![X0 : $i, X1 : $i]:
% 7.61/7.78         (~ (v1_relat_1 @ X1)
% 7.61/7.78          | ~ (v1_relat_1 @ X0)
% 7.61/7.78          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 7.61/7.78          | (v5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 7.61/7.78      inference('sup-', [status(thm)], ['80', '81'])).
% 7.61/7.78  thf('83', plain,
% 7.61/7.78      (((v5_relat_1 @ (k5_relat_1 @ sk_C @ sk_D) @ (k2_relat_1 @ sk_D))
% 7.61/7.78        | ~ (v1_relat_1 @ sk_D)
% 7.61/7.78        | ~ (v1_relat_1 @ sk_C))),
% 7.61/7.78      inference('sup-', [status(thm)], ['79', '82'])).
% 7.61/7.78  thf('84', plain,
% 7.61/7.78      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 7.61/7.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.61/7.78  thf('85', plain,
% 7.61/7.78      (![X30 : $i, X31 : $i, X32 : $i]:
% 7.61/7.78         ((v1_relat_1 @ X30)
% 7.61/7.78          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 7.61/7.78      inference('cnf', [status(esa)], [cc1_relset_1])).
% 7.61/7.78  thf('86', plain, ((v1_relat_1 @ sk_D)),
% 7.61/7.78      inference('sup-', [status(thm)], ['84', '85'])).
% 7.61/7.78  thf('87', plain,
% 7.61/7.78      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 7.61/7.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.61/7.78  thf('88', plain,
% 7.61/7.78      (![X30 : $i, X31 : $i, X32 : $i]:
% 7.61/7.78         ((v1_relat_1 @ X30)
% 7.61/7.78          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 7.61/7.78      inference('cnf', [status(esa)], [cc1_relset_1])).
% 7.61/7.78  thf('89', plain, ((v1_relat_1 @ sk_C)),
% 7.61/7.78      inference('sup-', [status(thm)], ['87', '88'])).
% 7.61/7.78  thf('90', plain,
% 7.61/7.78      ((v5_relat_1 @ (k5_relat_1 @ sk_C @ sk_D) @ (k2_relat_1 @ sk_D))),
% 7.61/7.78      inference('demod', [status(thm)], ['83', '86', '89'])).
% 7.61/7.78  thf('91', plain,
% 7.61/7.78      (![X12 : $i, X13 : $i]:
% 7.61/7.78         (~ (v5_relat_1 @ X12 @ X13)
% 7.61/7.78          | (r1_tarski @ (k2_relat_1 @ X12) @ X13)
% 7.61/7.78          | ~ (v1_relat_1 @ X12))),
% 7.61/7.78      inference('cnf', [status(esa)], [d19_relat_1])).
% 7.61/7.78  thf('92', plain,
% 7.61/7.78      ((~ (v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 7.61/7.78        | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ 
% 7.61/7.78           (k2_relat_1 @ sk_D)))),
% 7.61/7.78      inference('sup-', [status(thm)], ['90', '91'])).
% 7.61/7.78  thf('93', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))),
% 7.61/7.78      inference('demod', [status(thm)], ['77', '78'])).
% 7.61/7.78  thf('94', plain,
% 7.61/7.78      ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ 
% 7.61/7.78        (k2_relat_1 @ sk_D))),
% 7.61/7.78      inference('demod', [status(thm)], ['92', '93'])).
% 7.61/7.78  thf(d10_xboole_0, axiom,
% 7.61/7.78    (![A:$i,B:$i]:
% 7.61/7.78     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 7.61/7.78  thf('95', plain,
% 7.61/7.78      (![X0 : $i, X2 : $i]:
% 7.61/7.78         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 7.61/7.78      inference('cnf', [status(esa)], [d10_xboole_0])).
% 7.61/7.78  thf('96', plain,
% 7.61/7.78      ((~ (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 7.61/7.78           (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 7.61/7.78        | ((k2_relat_1 @ sk_D) = (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))))),
% 7.61/7.78      inference('sup-', [status(thm)], ['94', '95'])).
% 7.61/7.78  thf('97', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 7.61/7.78      inference('demod', [status(thm)], ['56', '57'])).
% 7.61/7.78  thf('98', plain, (![X21 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X21)) = (X21))),
% 7.61/7.78      inference('demod', [status(thm)], ['2', '3'])).
% 7.61/7.78  thf('99', plain,
% 7.61/7.78      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 7.61/7.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.61/7.78  thf(cc2_relset_1, axiom,
% 7.61/7.78    (![A:$i,B:$i,C:$i]:
% 7.61/7.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.61/7.78       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 7.61/7.78  thf('100', plain,
% 7.61/7.78      (![X33 : $i, X34 : $i, X35 : $i]:
% 7.61/7.78         ((v5_relat_1 @ X33 @ X35)
% 7.61/7.78          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 7.61/7.78      inference('cnf', [status(esa)], [cc2_relset_1])).
% 7.61/7.78  thf('101', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 7.61/7.78      inference('sup-', [status(thm)], ['99', '100'])).
% 7.61/7.78  thf('102', plain,
% 7.61/7.78      (![X12 : $i, X13 : $i]:
% 7.61/7.78         (~ (v5_relat_1 @ X12 @ X13)
% 7.61/7.78          | (r1_tarski @ (k2_relat_1 @ X12) @ X13)
% 7.61/7.78          | ~ (v1_relat_1 @ X12))),
% 7.61/7.78      inference('cnf', [status(esa)], [d19_relat_1])).
% 7.61/7.78  thf('103', plain,
% 7.61/7.78      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 7.61/7.78      inference('sup-', [status(thm)], ['101', '102'])).
% 7.61/7.78  thf('104', plain, ((v1_relat_1 @ sk_D)),
% 7.61/7.78      inference('sup-', [status(thm)], ['84', '85'])).
% 7.61/7.78  thf('105', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 7.61/7.78      inference('demod', [status(thm)], ['103', '104'])).
% 7.61/7.78  thf('106', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 7.61/7.78      inference('demod', [status(thm)], ['56', '57'])).
% 7.61/7.78  thf('107', plain,
% 7.61/7.78      (![X21 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X21)) = (X21))),
% 7.61/7.78      inference('demod', [status(thm)], ['2', '3'])).
% 7.61/7.78  thf('108', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 7.61/7.78      inference('demod', [status(thm)], ['96', '97', '98', '105', '106', '107'])).
% 7.61/7.78  thf('109', plain,
% 7.61/7.78      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 7.61/7.78      inference('cnf', [status(esa)], [d10_xboole_0])).
% 7.61/7.78  thf('110', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 7.61/7.78      inference('simplify', [status(thm)], ['109'])).
% 7.61/7.78  thf('111', plain,
% 7.61/7.78      (![X12 : $i, X13 : $i]:
% 7.61/7.78         (~ (r1_tarski @ (k2_relat_1 @ X12) @ X13)
% 7.61/7.78          | (v5_relat_1 @ X12 @ X13)
% 7.61/7.78          | ~ (v1_relat_1 @ X12))),
% 7.61/7.78      inference('cnf', [status(esa)], [d19_relat_1])).
% 7.61/7.78  thf('112', plain,
% 7.61/7.78      (![X0 : $i]:
% 7.61/7.78         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 7.61/7.78      inference('sup-', [status(thm)], ['110', '111'])).
% 7.61/7.78  thf(d3_funct_2, axiom,
% 7.61/7.78    (![A:$i,B:$i]:
% 7.61/7.78     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 7.61/7.78       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 7.61/7.78  thf('113', plain,
% 7.61/7.78      (![X40 : $i, X41 : $i]:
% 7.61/7.78         (((k2_relat_1 @ X41) != (X40))
% 7.61/7.78          | (v2_funct_2 @ X41 @ X40)
% 7.61/7.78          | ~ (v5_relat_1 @ X41 @ X40)
% 7.61/7.78          | ~ (v1_relat_1 @ X41))),
% 7.61/7.78      inference('cnf', [status(esa)], [d3_funct_2])).
% 7.61/7.78  thf('114', plain,
% 7.61/7.78      (![X41 : $i]:
% 7.61/7.78         (~ (v1_relat_1 @ X41)
% 7.61/7.78          | ~ (v5_relat_1 @ X41 @ (k2_relat_1 @ X41))
% 7.61/7.78          | (v2_funct_2 @ X41 @ (k2_relat_1 @ X41)))),
% 7.61/7.78      inference('simplify', [status(thm)], ['113'])).
% 7.61/7.78  thf('115', plain,
% 7.61/7.78      (![X0 : $i]:
% 7.61/7.78         (~ (v1_relat_1 @ X0)
% 7.61/7.78          | (v2_funct_2 @ X0 @ (k2_relat_1 @ X0))
% 7.61/7.78          | ~ (v1_relat_1 @ X0))),
% 7.61/7.78      inference('sup-', [status(thm)], ['112', '114'])).
% 7.61/7.78  thf('116', plain,
% 7.61/7.78      (![X0 : $i]:
% 7.61/7.78         ((v2_funct_2 @ X0 @ (k2_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 7.61/7.78      inference('simplify', [status(thm)], ['115'])).
% 7.61/7.78  thf('117', plain, (((v2_funct_2 @ sk_D @ sk_A) | ~ (v1_relat_1 @ sk_D))),
% 7.61/7.78      inference('sup+', [status(thm)], ['108', '116'])).
% 7.61/7.78  thf('118', plain, ((v1_relat_1 @ sk_D)),
% 7.61/7.78      inference('sup-', [status(thm)], ['84', '85'])).
% 7.61/7.78  thf('119', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 7.61/7.78      inference('demod', [status(thm)], ['117', '118'])).
% 7.61/7.78  thf('120', plain, ($false), inference('demod', [status(thm)], ['74', '119'])).
% 7.61/7.78  
% 7.61/7.78  % SZS output end Refutation
% 7.61/7.78  
% 7.61/7.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

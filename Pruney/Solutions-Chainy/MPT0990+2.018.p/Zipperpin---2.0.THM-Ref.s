%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9U6y4ucVzH

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:56 EST 2020

% Result     : Theorem 1.09s
% Output     : Refutation 1.09s
% Verified   : 
% Statistics : Number of formulae       :  277 ( 671 expanded)
%              Number of leaves         :   46 ( 232 expanded)
%              Depth                    :   51
%              Number of atoms          : 2218 (11567 expanded)
%              Number of equality atoms :  124 ( 833 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

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
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ( ( k1_partfun1 @ X42 @ X43 @ X45 @ X46 @ X41 @ X44 )
        = ( k5_relat_1 @ X41 @ X44 ) ) ) ),
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
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X40 ) ) ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( X30 = X33 )
      | ~ ( r2_relset_1 @ X31 @ X32 @ X30 @ X33 ) ) ),
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
    ! [X34: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('22',plain,(
    ! [X47: $i] :
      ( ( k6_partfun1 @ X47 )
      = ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('23',plain,(
    ! [X34: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['6','7','24'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('26',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
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
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X20 ) @ X20 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('28',plain,(
    ! [X47: $i] :
      ( ( k6_partfun1 @ X47 )
      = ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('29',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X20 ) @ X20 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X20 ) @ X20 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('31',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X20 ) @ X20 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('32',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X20 ) @ X20 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('33',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X20 ) @ X20 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('34',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('35',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
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

thf('36',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k2_relat_1 @ X19 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('37',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('38',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('39',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('41',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X29 @ X27 )
        = ( k2_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('42',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('46',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k2_relat_1 @ X19 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('47',plain,(
    ! [X34: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('48',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v4_relat_1 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k6_partfun1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k6_partfun1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('52',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('53',plain,(
    ! [X47: $i] :
      ( ( k6_partfun1 @ X47 )
      = ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('54',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X17 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('55',plain,(
    ! [X9: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('56',plain,(
    ! [X47: $i] :
      ( ( k6_partfun1 @ X47 )
      = ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('57',plain,(
    ! [X9: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X9 ) )
      = X9 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['51','54','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ( v4_relat_1 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['46','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['44','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('66',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('67',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['64','67','68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('72',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['39','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['65','66'])).

thf('75',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['73','74','75'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('77',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X11 ) @ X12 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X12 ) @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('78',plain,(
    ! [X47: $i] :
      ( ( k6_partfun1 @ X47 )
      = ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('79',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X11 ) @ X12 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X12 ) @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','80'])).

thf('82',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['65','66'])).

thf('83',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('85',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X5 @ X4 ) )
        = ( k10_relat_1 @ X5 @ ( k1_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('86',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k10_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X17 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('88',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k10_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k10_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['37','88'])).

thf('90',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['65','66'])).

thf('91',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k10_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k10_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['36','92'])).

thf('94',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['42','43'])).

thf('95',plain,(
    ! [X10: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('96',plain,(
    ! [X47: $i] :
      ( ( k6_partfun1 @ X47 )
      = ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('97',plain,(
    ! [X10: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X10 ) )
      = X10 ) ),
    inference(demod,[status(thm)],['95','96'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('98',plain,(
    ! [X15: $i] :
      ( ( ( k5_relat_1 @ X15 @ ( k6_relat_1 @ ( k2_relat_1 @ X15 ) ) )
        = X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('99',plain,(
    ! [X47: $i] :
      ( ( k6_partfun1 @ X47 )
      = ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('100',plain,(
    ! [X15: $i] :
      ( ( ( k5_relat_1 @ X15 @ ( k6_partfun1 @ ( k2_relat_1 @ X15 ) ) )
        = X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['97','100'])).

thf('102',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X17 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X5 @ X4 ) )
        = ( k10_relat_1 @ X5 @ ( k1_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
        = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X9: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X9 ) )
      = X9 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('107',plain,(
    ! [X9: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X9 ) )
      = X9 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('108',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X17 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('109',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X17 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('110',plain,(
    ! [X0: $i] :
      ( X0
      = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['105','106','107','108','109'])).

thf('111',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['65','66'])).

thf('112',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = sk_B ),
    inference(demod,[status(thm)],['93','94','110','111','112','113'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('115',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ X3 ) @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) @ sk_B )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','116'])).

thf('118',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['65','66'])).

thf('119',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) @ sk_B ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X5 @ X4 ) )
        = ( k10_relat_1 @ X5 @ ( k1_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ( v4_relat_1 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( v4_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) @ sk_B )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['120','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) )
      | ( v4_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','124'])).

thf('126',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['65','66'])).

thf('127',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) )
      | ( v4_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['125','126','127'])).

thf('129',plain,
    ( ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v4_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['33','128'])).

thf('130',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['42','43'])).

thf('131',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X17 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('132',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['65','66'])).

thf('133',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['65','66'])).

thf('136',plain,(
    v4_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['129','130','131','132','133','134','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('138',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,
    ( ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['32','138'])).

thf('140',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['42','43'])).

thf('141',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X17 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('142',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['65','66'])).

thf('143',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['139','140','141','142','143','144'])).

thf('146',plain,(
    ! [X9: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X9 ) )
      = X9 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('147',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X11 ) @ X12 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X12 ) @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X17 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) ) )
    = ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['145','150'])).

thf('152',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k6_partfun1 @ ( k1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) ) ) )
      = ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['31','151'])).

thf('153',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['42','43'])).

thf('154',plain,(
    ! [X9: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X9 ) )
      = X9 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('156',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['65','66'])).

thf('157',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( k6_partfun1 @ sk_B )
    = ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['152','153','154','155','156','157','158'])).

thf('160',plain,(
    ! [X9: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X9 ) )
      = X9 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('161',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    = ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X9: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X9 ) )
      = X9 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('163',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['51','54','57'])).

thf('165',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X11 ) @ X12 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X12 ) @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['163','166'])).

thf('168',plain,
    ( ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['30','167'])).

thf('169',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['42','43'])).

thf('170',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X17 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('171',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['65','66'])).

thf('172',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['168','169','170','171','172','173'])).

thf('175',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['29','174'])).

thf('176',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['42','43'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('178',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['65','66'])).

thf('179',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ( k6_partfun1 @ sk_B )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['175','176','177','178','179','180'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('182',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) @ X8 )
        = ( k5_relat_1 @ X7 @ ( k5_relat_1 @ X6 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('183',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['181','182'])).

thf('184',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['65','66'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['183','184'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','185'])).

thf('187',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['65','66'])).

thf('188',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['186','187','188'])).

thf('190',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['25','189'])).

thf('191',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v4_relat_1 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('193',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('195',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('198',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['195','198'])).

thf('200',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X11 ) @ X12 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X12 ) @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('201',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = sk_D ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['196','197'])).

thf('203',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['201','202'])).

thf('204',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('205',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v4_relat_1 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('207',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('209',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['207','208'])).

thf('210',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['65','66'])).

thf('211',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['209','210'])).

thf('212',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k1_relat_1 @ X19 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('213',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ( ( k5_relat_1 @ X13 @ ( k6_relat_1 @ X14 ) )
        = X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('214',plain,(
    ! [X47: $i] :
      ( ( k6_partfun1 @ X47 )
      = ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('215',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ( ( k5_relat_1 @ X13 @ ( k6_partfun1 @ X14 ) )
        = X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['213','214'])).

thf('216',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ X1 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['212','215'])).

thf('217',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['211','216'])).

thf('218',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['65','66'])).

thf('221',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['217','218','219','220'])).

thf('222',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['204','221'])).

thf('223',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['65','66'])).

thf('224',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['222','223','224'])).

thf('226',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['196','197'])).

thf('227',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['190','203','225','226'])).

thf('228',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['227','228'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9U6y4ucVzH
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:29:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.09/1.32  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.09/1.32  % Solved by: fo/fo7.sh
% 1.09/1.32  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.09/1.32  % done 1323 iterations in 0.877s
% 1.09/1.32  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.09/1.32  % SZS output start Refutation
% 1.09/1.32  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.09/1.32  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.09/1.32  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.09/1.32  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.09/1.32  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.09/1.32  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.09/1.32  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.09/1.32  thf(sk_D_type, type, sk_D: $i).
% 1.09/1.32  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.09/1.32  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.09/1.32  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.09/1.32  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.09/1.32  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.09/1.32  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.09/1.32  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.09/1.32  thf(sk_C_type, type, sk_C: $i).
% 1.09/1.32  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.09/1.32  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.09/1.32  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.09/1.32  thf(sk_A_type, type, sk_A: $i).
% 1.09/1.32  thf(sk_B_type, type, sk_B: $i).
% 1.09/1.32  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.09/1.32  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.09/1.32  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.09/1.32  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.09/1.32  thf(t36_funct_2, conjecture,
% 1.09/1.32    (![A:$i,B:$i,C:$i]:
% 1.09/1.32     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.09/1.32         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.09/1.32       ( ![D:$i]:
% 1.09/1.32         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.09/1.32             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.09/1.32           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.09/1.32               ( r2_relset_1 @
% 1.09/1.32                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.09/1.32                 ( k6_partfun1 @ A ) ) & 
% 1.09/1.32               ( v2_funct_1 @ C ) ) =>
% 1.09/1.32             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.09/1.32               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.09/1.32  thf(zf_stmt_0, negated_conjecture,
% 1.09/1.32    (~( ![A:$i,B:$i,C:$i]:
% 1.09/1.32        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.09/1.32            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.09/1.32          ( ![D:$i]:
% 1.09/1.32            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.09/1.32                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.09/1.32              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.09/1.32                  ( r2_relset_1 @
% 1.09/1.32                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.09/1.32                    ( k6_partfun1 @ A ) ) & 
% 1.09/1.32                  ( v2_funct_1 @ C ) ) =>
% 1.09/1.32                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.09/1.32                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.09/1.32    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.09/1.32  thf('0', plain,
% 1.09/1.32      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.09/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.32  thf('1', plain,
% 1.09/1.32      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.09/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.32  thf(redefinition_k1_partfun1, axiom,
% 1.09/1.32    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.09/1.32     ( ( ( v1_funct_1 @ E ) & 
% 1.09/1.32         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.09/1.32         ( v1_funct_1 @ F ) & 
% 1.09/1.32         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.09/1.32       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.09/1.32  thf('2', plain,
% 1.09/1.32      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 1.09/1.32         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 1.09/1.32          | ~ (v1_funct_1 @ X41)
% 1.09/1.32          | ~ (v1_funct_1 @ X44)
% 1.09/1.32          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 1.09/1.32          | ((k1_partfun1 @ X42 @ X43 @ X45 @ X46 @ X41 @ X44)
% 1.09/1.32              = (k5_relat_1 @ X41 @ X44)))),
% 1.09/1.32      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.09/1.32  thf('3', plain,
% 1.09/1.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.09/1.32         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.09/1.32            = (k5_relat_1 @ sk_C @ X0))
% 1.09/1.32          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.09/1.32          | ~ (v1_funct_1 @ X0)
% 1.09/1.32          | ~ (v1_funct_1 @ sk_C))),
% 1.09/1.32      inference('sup-', [status(thm)], ['1', '2'])).
% 1.09/1.32  thf('4', plain, ((v1_funct_1 @ sk_C)),
% 1.09/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.32  thf('5', plain,
% 1.09/1.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.09/1.32         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.09/1.32            = (k5_relat_1 @ sk_C @ X0))
% 1.09/1.32          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.09/1.32          | ~ (v1_funct_1 @ X0))),
% 1.09/1.32      inference('demod', [status(thm)], ['3', '4'])).
% 1.09/1.32  thf('6', plain,
% 1.09/1.32      ((~ (v1_funct_1 @ sk_D)
% 1.09/1.32        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.09/1.32            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.09/1.32      inference('sup-', [status(thm)], ['0', '5'])).
% 1.09/1.32  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 1.09/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.32  thf('8', plain,
% 1.09/1.32      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.09/1.32        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.09/1.32        (k6_partfun1 @ sk_A))),
% 1.09/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.32  thf('9', plain,
% 1.09/1.32      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.09/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.32  thf('10', plain,
% 1.09/1.32      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.09/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.32  thf(dt_k1_partfun1, axiom,
% 1.09/1.32    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.09/1.32     ( ( ( v1_funct_1 @ E ) & 
% 1.09/1.32         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.09/1.32         ( v1_funct_1 @ F ) & 
% 1.09/1.32         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.09/1.32       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.09/1.32         ( m1_subset_1 @
% 1.09/1.32           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.09/1.32           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.09/1.32  thf('11', plain,
% 1.09/1.32      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 1.09/1.32         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 1.09/1.32          | ~ (v1_funct_1 @ X35)
% 1.09/1.32          | ~ (v1_funct_1 @ X38)
% 1.09/1.32          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 1.09/1.32          | (m1_subset_1 @ (k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38) @ 
% 1.09/1.32             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X40))))),
% 1.09/1.32      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.09/1.32  thf('12', plain,
% 1.09/1.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.09/1.32         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.09/1.32           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.09/1.32          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.09/1.32          | ~ (v1_funct_1 @ X1)
% 1.09/1.32          | ~ (v1_funct_1 @ sk_C))),
% 1.09/1.32      inference('sup-', [status(thm)], ['10', '11'])).
% 1.09/1.32  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 1.09/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.32  thf('14', plain,
% 1.09/1.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.09/1.32         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.09/1.32           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.09/1.32          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.09/1.32          | ~ (v1_funct_1 @ X1))),
% 1.09/1.32      inference('demod', [status(thm)], ['12', '13'])).
% 1.09/1.32  thf('15', plain,
% 1.09/1.32      ((~ (v1_funct_1 @ sk_D)
% 1.09/1.32        | (m1_subset_1 @ 
% 1.09/1.32           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.09/1.32           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.09/1.32      inference('sup-', [status(thm)], ['9', '14'])).
% 1.09/1.32  thf('16', plain, ((v1_funct_1 @ sk_D)),
% 1.09/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.32  thf('17', plain,
% 1.09/1.32      ((m1_subset_1 @ 
% 1.09/1.32        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.09/1.32        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.09/1.32      inference('demod', [status(thm)], ['15', '16'])).
% 1.09/1.32  thf(redefinition_r2_relset_1, axiom,
% 1.09/1.32    (![A:$i,B:$i,C:$i,D:$i]:
% 1.09/1.32     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.09/1.32         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.09/1.32       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.09/1.32  thf('18', plain,
% 1.09/1.32      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.09/1.32         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 1.09/1.32          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 1.09/1.32          | ((X30) = (X33))
% 1.09/1.32          | ~ (r2_relset_1 @ X31 @ X32 @ X30 @ X33))),
% 1.09/1.32      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.09/1.32  thf('19', plain,
% 1.09/1.32      (![X0 : $i]:
% 1.09/1.32         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.09/1.32             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 1.09/1.32          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 1.09/1.32          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.09/1.32      inference('sup-', [status(thm)], ['17', '18'])).
% 1.09/1.32  thf('20', plain,
% 1.09/1.32      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 1.09/1.32           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.09/1.32        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.09/1.32            = (k6_partfun1 @ sk_A)))),
% 1.09/1.32      inference('sup-', [status(thm)], ['8', '19'])).
% 1.09/1.32  thf(t29_relset_1, axiom,
% 1.09/1.32    (![A:$i]:
% 1.09/1.32     ( m1_subset_1 @
% 1.09/1.32       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 1.09/1.32  thf('21', plain,
% 1.09/1.32      (![X34 : $i]:
% 1.09/1.32         (m1_subset_1 @ (k6_relat_1 @ X34) @ 
% 1.09/1.32          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))),
% 1.09/1.32      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.09/1.32  thf(redefinition_k6_partfun1, axiom,
% 1.09/1.32    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.09/1.32  thf('22', plain, (![X47 : $i]: ((k6_partfun1 @ X47) = (k6_relat_1 @ X47))),
% 1.09/1.32      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.09/1.32  thf('23', plain,
% 1.09/1.32      (![X34 : $i]:
% 1.09/1.32         (m1_subset_1 @ (k6_partfun1 @ X34) @ 
% 1.09/1.32          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))),
% 1.09/1.32      inference('demod', [status(thm)], ['21', '22'])).
% 1.09/1.32  thf('24', plain,
% 1.09/1.32      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.09/1.32         = (k6_partfun1 @ sk_A))),
% 1.09/1.32      inference('demod', [status(thm)], ['20', '23'])).
% 1.09/1.32  thf('25', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 1.09/1.32      inference('demod', [status(thm)], ['6', '7', '24'])).
% 1.09/1.32  thf(dt_k2_funct_1, axiom,
% 1.09/1.32    (![A:$i]:
% 1.09/1.32     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.09/1.32       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.09/1.32         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.09/1.32  thf('26', plain,
% 1.09/1.32      (![X16 : $i]:
% 1.09/1.32         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 1.09/1.32          | ~ (v1_funct_1 @ X16)
% 1.09/1.32          | ~ (v1_relat_1 @ X16))),
% 1.09/1.32      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.09/1.32  thf(t61_funct_1, axiom,
% 1.09/1.32    (![A:$i]:
% 1.09/1.32     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.09/1.32       ( ( v2_funct_1 @ A ) =>
% 1.09/1.32         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 1.09/1.32             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.09/1.32           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 1.09/1.32             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.09/1.32  thf('27', plain,
% 1.09/1.32      (![X20 : $i]:
% 1.09/1.32         (~ (v2_funct_1 @ X20)
% 1.09/1.32          | ((k5_relat_1 @ (k2_funct_1 @ X20) @ X20)
% 1.09/1.32              = (k6_relat_1 @ (k2_relat_1 @ X20)))
% 1.09/1.32          | ~ (v1_funct_1 @ X20)
% 1.09/1.32          | ~ (v1_relat_1 @ X20))),
% 1.09/1.32      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.09/1.32  thf('28', plain, (![X47 : $i]: ((k6_partfun1 @ X47) = (k6_relat_1 @ X47))),
% 1.09/1.32      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.09/1.32  thf('29', plain,
% 1.09/1.32      (![X20 : $i]:
% 1.09/1.32         (~ (v2_funct_1 @ X20)
% 1.09/1.32          | ((k5_relat_1 @ (k2_funct_1 @ X20) @ X20)
% 1.09/1.32              = (k6_partfun1 @ (k2_relat_1 @ X20)))
% 1.09/1.32          | ~ (v1_funct_1 @ X20)
% 1.09/1.32          | ~ (v1_relat_1 @ X20))),
% 1.09/1.32      inference('demod', [status(thm)], ['27', '28'])).
% 1.09/1.32  thf('30', plain,
% 1.09/1.32      (![X20 : $i]:
% 1.09/1.32         (~ (v2_funct_1 @ X20)
% 1.09/1.32          | ((k5_relat_1 @ (k2_funct_1 @ X20) @ X20)
% 1.09/1.32              = (k6_partfun1 @ (k2_relat_1 @ X20)))
% 1.09/1.32          | ~ (v1_funct_1 @ X20)
% 1.09/1.32          | ~ (v1_relat_1 @ X20))),
% 1.09/1.32      inference('demod', [status(thm)], ['27', '28'])).
% 1.09/1.32  thf('31', plain,
% 1.09/1.32      (![X20 : $i]:
% 1.09/1.32         (~ (v2_funct_1 @ X20)
% 1.09/1.32          | ((k5_relat_1 @ (k2_funct_1 @ X20) @ X20)
% 1.09/1.32              = (k6_partfun1 @ (k2_relat_1 @ X20)))
% 1.09/1.32          | ~ (v1_funct_1 @ X20)
% 1.09/1.32          | ~ (v1_relat_1 @ X20))),
% 1.09/1.32      inference('demod', [status(thm)], ['27', '28'])).
% 1.09/1.32  thf('32', plain,
% 1.09/1.32      (![X20 : $i]:
% 1.09/1.32         (~ (v2_funct_1 @ X20)
% 1.09/1.32          | ((k5_relat_1 @ (k2_funct_1 @ X20) @ X20)
% 1.09/1.32              = (k6_partfun1 @ (k2_relat_1 @ X20)))
% 1.09/1.32          | ~ (v1_funct_1 @ X20)
% 1.09/1.32          | ~ (v1_relat_1 @ X20))),
% 1.09/1.32      inference('demod', [status(thm)], ['27', '28'])).
% 1.09/1.32  thf('33', plain,
% 1.09/1.32      (![X20 : $i]:
% 1.09/1.32         (~ (v2_funct_1 @ X20)
% 1.09/1.32          | ((k5_relat_1 @ (k2_funct_1 @ X20) @ X20)
% 1.09/1.32              = (k6_partfun1 @ (k2_relat_1 @ X20)))
% 1.09/1.32          | ~ (v1_funct_1 @ X20)
% 1.09/1.32          | ~ (v1_relat_1 @ X20))),
% 1.09/1.32      inference('demod', [status(thm)], ['27', '28'])).
% 1.09/1.32  thf('34', plain,
% 1.09/1.32      (![X16 : $i]:
% 1.09/1.32         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 1.09/1.32          | ~ (v1_funct_1 @ X16)
% 1.09/1.32          | ~ (v1_relat_1 @ X16))),
% 1.09/1.32      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.09/1.32  thf('35', plain,
% 1.09/1.32      (![X16 : $i]:
% 1.09/1.32         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 1.09/1.32          | ~ (v1_funct_1 @ X16)
% 1.09/1.32          | ~ (v1_relat_1 @ X16))),
% 1.09/1.32      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.09/1.32  thf(t55_funct_1, axiom,
% 1.09/1.32    (![A:$i]:
% 1.09/1.32     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.09/1.32       ( ( v2_funct_1 @ A ) =>
% 1.09/1.32         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.09/1.32           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.09/1.32  thf('36', plain,
% 1.09/1.32      (![X19 : $i]:
% 1.09/1.32         (~ (v2_funct_1 @ X19)
% 1.09/1.32          | ((k2_relat_1 @ X19) = (k1_relat_1 @ (k2_funct_1 @ X19)))
% 1.09/1.32          | ~ (v1_funct_1 @ X19)
% 1.09/1.32          | ~ (v1_relat_1 @ X19))),
% 1.09/1.32      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.09/1.32  thf('37', plain,
% 1.09/1.32      (![X16 : $i]:
% 1.09/1.32         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 1.09/1.32          | ~ (v1_funct_1 @ X16)
% 1.09/1.32          | ~ (v1_relat_1 @ X16))),
% 1.09/1.32      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.09/1.32  thf('38', plain,
% 1.09/1.32      (![X16 : $i]:
% 1.09/1.32         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 1.09/1.32          | ~ (v1_funct_1 @ X16)
% 1.09/1.32          | ~ (v1_relat_1 @ X16))),
% 1.09/1.32      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.09/1.32  thf('39', plain,
% 1.09/1.32      (![X16 : $i]:
% 1.09/1.32         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 1.09/1.32          | ~ (v1_funct_1 @ X16)
% 1.09/1.32          | ~ (v1_relat_1 @ X16))),
% 1.09/1.32      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.09/1.32  thf('40', plain,
% 1.09/1.32      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.09/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.32  thf(redefinition_k2_relset_1, axiom,
% 1.09/1.32    (![A:$i,B:$i,C:$i]:
% 1.09/1.32     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.09/1.32       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.09/1.32  thf('41', plain,
% 1.09/1.32      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.09/1.32         (((k2_relset_1 @ X28 @ X29 @ X27) = (k2_relat_1 @ X27))
% 1.09/1.32          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 1.09/1.32      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.09/1.32  thf('42', plain,
% 1.09/1.32      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.09/1.32      inference('sup-', [status(thm)], ['40', '41'])).
% 1.09/1.32  thf('43', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.09/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.32  thf('44', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.09/1.32      inference('sup+', [status(thm)], ['42', '43'])).
% 1.09/1.32  thf('45', plain,
% 1.09/1.32      (![X16 : $i]:
% 1.09/1.32         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 1.09/1.32          | ~ (v1_funct_1 @ X16)
% 1.09/1.32          | ~ (v1_relat_1 @ X16))),
% 1.09/1.32      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.09/1.32  thf('46', plain,
% 1.09/1.32      (![X19 : $i]:
% 1.09/1.32         (~ (v2_funct_1 @ X19)
% 1.09/1.32          | ((k2_relat_1 @ X19) = (k1_relat_1 @ (k2_funct_1 @ X19)))
% 1.09/1.32          | ~ (v1_funct_1 @ X19)
% 1.09/1.32          | ~ (v1_relat_1 @ X19))),
% 1.09/1.32      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.09/1.32  thf('47', plain,
% 1.09/1.32      (![X34 : $i]:
% 1.09/1.32         (m1_subset_1 @ (k6_partfun1 @ X34) @ 
% 1.09/1.32          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))),
% 1.09/1.32      inference('demod', [status(thm)], ['21', '22'])).
% 1.09/1.32  thf(cc2_relset_1, axiom,
% 1.09/1.32    (![A:$i,B:$i,C:$i]:
% 1.09/1.32     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.09/1.32       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.09/1.32  thf('48', plain,
% 1.09/1.32      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.09/1.32         ((v4_relat_1 @ X24 @ X25)
% 1.09/1.32          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 1.09/1.32      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.09/1.32  thf('49', plain, (![X0 : $i]: (v4_relat_1 @ (k6_partfun1 @ X0) @ X0)),
% 1.09/1.32      inference('sup-', [status(thm)], ['47', '48'])).
% 1.09/1.32  thf(d18_relat_1, axiom,
% 1.09/1.32    (![A:$i,B:$i]:
% 1.09/1.32     ( ( v1_relat_1 @ B ) =>
% 1.09/1.32       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.09/1.32  thf('50', plain,
% 1.09/1.32      (![X0 : $i, X1 : $i]:
% 1.09/1.32         (~ (v4_relat_1 @ X0 @ X1)
% 1.09/1.32          | (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 1.09/1.32          | ~ (v1_relat_1 @ X0))),
% 1.09/1.32      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.09/1.32  thf('51', plain,
% 1.09/1.32      (![X0 : $i]:
% 1.09/1.32         (~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 1.09/1.32          | (r1_tarski @ (k1_relat_1 @ (k6_partfun1 @ X0)) @ X0))),
% 1.09/1.32      inference('sup-', [status(thm)], ['49', '50'])).
% 1.09/1.32  thf(fc4_funct_1, axiom,
% 1.09/1.32    (![A:$i]:
% 1.09/1.32     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.09/1.32       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.09/1.32  thf('52', plain, (![X17 : $i]: (v1_relat_1 @ (k6_relat_1 @ X17))),
% 1.09/1.32      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.09/1.32  thf('53', plain, (![X47 : $i]: ((k6_partfun1 @ X47) = (k6_relat_1 @ X47))),
% 1.09/1.32      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.09/1.32  thf('54', plain, (![X17 : $i]: (v1_relat_1 @ (k6_partfun1 @ X17))),
% 1.09/1.32      inference('demod', [status(thm)], ['52', '53'])).
% 1.09/1.32  thf(t71_relat_1, axiom,
% 1.09/1.32    (![A:$i]:
% 1.09/1.32     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.09/1.32       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.09/1.32  thf('55', plain, (![X9 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X9)) = (X9))),
% 1.09/1.32      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.09/1.32  thf('56', plain, (![X47 : $i]: ((k6_partfun1 @ X47) = (k6_relat_1 @ X47))),
% 1.09/1.32      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.09/1.32  thf('57', plain, (![X9 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X9)) = (X9))),
% 1.09/1.32      inference('demod', [status(thm)], ['55', '56'])).
% 1.09/1.32  thf('58', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.09/1.32      inference('demod', [status(thm)], ['51', '54', '57'])).
% 1.09/1.32  thf('59', plain,
% 1.09/1.32      (![X0 : $i, X1 : $i]:
% 1.09/1.32         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 1.09/1.32          | (v4_relat_1 @ X0 @ X1)
% 1.09/1.32          | ~ (v1_relat_1 @ X0))),
% 1.09/1.32      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.09/1.32  thf('60', plain,
% 1.09/1.32      (![X0 : $i]:
% 1.09/1.32         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 1.09/1.32      inference('sup-', [status(thm)], ['58', '59'])).
% 1.09/1.32  thf('61', plain,
% 1.09/1.32      (![X0 : $i]:
% 1.09/1.32         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.09/1.32          | ~ (v1_relat_1 @ X0)
% 1.09/1.32          | ~ (v1_funct_1 @ X0)
% 1.09/1.32          | ~ (v2_funct_1 @ X0)
% 1.09/1.32          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.09/1.32      inference('sup+', [status(thm)], ['46', '60'])).
% 1.09/1.32  thf('62', plain,
% 1.09/1.32      (![X0 : $i]:
% 1.09/1.32         (~ (v1_relat_1 @ X0)
% 1.09/1.32          | ~ (v1_funct_1 @ X0)
% 1.09/1.32          | ~ (v2_funct_1 @ X0)
% 1.09/1.32          | ~ (v1_funct_1 @ X0)
% 1.09/1.32          | ~ (v1_relat_1 @ X0)
% 1.09/1.32          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 1.09/1.32      inference('sup-', [status(thm)], ['45', '61'])).
% 1.09/1.32  thf('63', plain,
% 1.09/1.32      (![X0 : $i]:
% 1.09/1.32         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.09/1.32          | ~ (v2_funct_1 @ X0)
% 1.09/1.32          | ~ (v1_funct_1 @ X0)
% 1.09/1.32          | ~ (v1_relat_1 @ X0))),
% 1.09/1.32      inference('simplify', [status(thm)], ['62'])).
% 1.09/1.32  thf('64', plain,
% 1.09/1.32      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)
% 1.09/1.32        | ~ (v1_relat_1 @ sk_C)
% 1.09/1.32        | ~ (v1_funct_1 @ sk_C)
% 1.09/1.32        | ~ (v2_funct_1 @ sk_C))),
% 1.09/1.32      inference('sup+', [status(thm)], ['44', '63'])).
% 1.09/1.32  thf('65', plain,
% 1.09/1.32      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.09/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.32  thf(cc1_relset_1, axiom,
% 1.09/1.32    (![A:$i,B:$i,C:$i]:
% 1.09/1.32     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.09/1.32       ( v1_relat_1 @ C ) ))).
% 1.09/1.32  thf('66', plain,
% 1.09/1.32      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.09/1.32         ((v1_relat_1 @ X21)
% 1.09/1.32          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 1.09/1.32      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.09/1.32  thf('67', plain, ((v1_relat_1 @ sk_C)),
% 1.09/1.32      inference('sup-', [status(thm)], ['65', '66'])).
% 1.09/1.32  thf('68', plain, ((v1_funct_1 @ sk_C)),
% 1.09/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.32  thf('69', plain, ((v2_funct_1 @ sk_C)),
% 1.09/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.32  thf('70', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)),
% 1.09/1.32      inference('demod', [status(thm)], ['64', '67', '68', '69'])).
% 1.09/1.32  thf('71', plain,
% 1.09/1.32      (![X0 : $i, X1 : $i]:
% 1.09/1.32         (~ (v4_relat_1 @ X0 @ X1)
% 1.09/1.32          | (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 1.09/1.32          | ~ (v1_relat_1 @ X0))),
% 1.09/1.32      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.09/1.32  thf('72', plain,
% 1.09/1.32      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.09/1.32        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 1.09/1.32      inference('sup-', [status(thm)], ['70', '71'])).
% 1.09/1.32  thf('73', plain,
% 1.09/1.32      ((~ (v1_relat_1 @ sk_C)
% 1.09/1.32        | ~ (v1_funct_1 @ sk_C)
% 1.09/1.32        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 1.09/1.32      inference('sup-', [status(thm)], ['39', '72'])).
% 1.09/1.32  thf('74', plain, ((v1_relat_1 @ sk_C)),
% 1.09/1.32      inference('sup-', [status(thm)], ['65', '66'])).
% 1.09/1.32  thf('75', plain, ((v1_funct_1 @ sk_C)),
% 1.09/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.32  thf('76', plain, ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B)),
% 1.09/1.32      inference('demod', [status(thm)], ['73', '74', '75'])).
% 1.09/1.32  thf(t77_relat_1, axiom,
% 1.09/1.32    (![A:$i,B:$i]:
% 1.09/1.32     ( ( v1_relat_1 @ B ) =>
% 1.09/1.32       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 1.09/1.32         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 1.09/1.32  thf('77', plain,
% 1.09/1.32      (![X11 : $i, X12 : $i]:
% 1.09/1.32         (~ (r1_tarski @ (k1_relat_1 @ X11) @ X12)
% 1.09/1.32          | ((k5_relat_1 @ (k6_relat_1 @ X12) @ X11) = (X11))
% 1.09/1.32          | ~ (v1_relat_1 @ X11))),
% 1.09/1.32      inference('cnf', [status(esa)], [t77_relat_1])).
% 1.09/1.32  thf('78', plain, (![X47 : $i]: ((k6_partfun1 @ X47) = (k6_relat_1 @ X47))),
% 1.09/1.32      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.09/1.32  thf('79', plain,
% 1.09/1.32      (![X11 : $i, X12 : $i]:
% 1.09/1.32         (~ (r1_tarski @ (k1_relat_1 @ X11) @ X12)
% 1.09/1.32          | ((k5_relat_1 @ (k6_partfun1 @ X12) @ X11) = (X11))
% 1.09/1.32          | ~ (v1_relat_1 @ X11))),
% 1.09/1.32      inference('demod', [status(thm)], ['77', '78'])).
% 1.09/1.32  thf('80', plain,
% 1.09/1.32      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.09/1.32        | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.09/1.32            = (k2_funct_1 @ sk_C)))),
% 1.09/1.32      inference('sup-', [status(thm)], ['76', '79'])).
% 1.09/1.32  thf('81', plain,
% 1.09/1.32      ((~ (v1_relat_1 @ sk_C)
% 1.09/1.32        | ~ (v1_funct_1 @ sk_C)
% 1.09/1.32        | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.09/1.32            = (k2_funct_1 @ sk_C)))),
% 1.09/1.32      inference('sup-', [status(thm)], ['38', '80'])).
% 1.09/1.32  thf('82', plain, ((v1_relat_1 @ sk_C)),
% 1.09/1.32      inference('sup-', [status(thm)], ['65', '66'])).
% 1.09/1.32  thf('83', plain, ((v1_funct_1 @ sk_C)),
% 1.09/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.32  thf('84', plain,
% 1.09/1.32      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.09/1.32         = (k2_funct_1 @ sk_C))),
% 1.09/1.32      inference('demod', [status(thm)], ['81', '82', '83'])).
% 1.09/1.32  thf(t182_relat_1, axiom,
% 1.09/1.32    (![A:$i]:
% 1.09/1.32     ( ( v1_relat_1 @ A ) =>
% 1.09/1.32       ( ![B:$i]:
% 1.09/1.32         ( ( v1_relat_1 @ B ) =>
% 1.09/1.32           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 1.09/1.32             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 1.09/1.32  thf('85', plain,
% 1.09/1.32      (![X4 : $i, X5 : $i]:
% 1.09/1.32         (~ (v1_relat_1 @ X4)
% 1.09/1.32          | ((k1_relat_1 @ (k5_relat_1 @ X5 @ X4))
% 1.09/1.32              = (k10_relat_1 @ X5 @ (k1_relat_1 @ X4)))
% 1.09/1.32          | ~ (v1_relat_1 @ X5))),
% 1.09/1.32      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.09/1.32  thf('86', plain,
% 1.09/1.32      ((((k1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.09/1.32          = (k10_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.09/1.32             (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 1.09/1.32        | ~ (v1_relat_1 @ (k6_partfun1 @ sk_B))
% 1.09/1.32        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.09/1.32      inference('sup+', [status(thm)], ['84', '85'])).
% 1.09/1.32  thf('87', plain, (![X17 : $i]: (v1_relat_1 @ (k6_partfun1 @ X17))),
% 1.09/1.32      inference('demod', [status(thm)], ['52', '53'])).
% 1.09/1.32  thf('88', plain,
% 1.09/1.32      ((((k1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.09/1.32          = (k10_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.09/1.32             (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 1.09/1.32        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.09/1.32      inference('demod', [status(thm)], ['86', '87'])).
% 1.09/1.32  thf('89', plain,
% 1.09/1.32      ((~ (v1_relat_1 @ sk_C)
% 1.09/1.32        | ~ (v1_funct_1 @ sk_C)
% 1.09/1.32        | ((k1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.09/1.32            = (k10_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.09/1.32               (k1_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 1.09/1.32      inference('sup-', [status(thm)], ['37', '88'])).
% 1.09/1.32  thf('90', plain, ((v1_relat_1 @ sk_C)),
% 1.09/1.32      inference('sup-', [status(thm)], ['65', '66'])).
% 1.09/1.32  thf('91', plain, ((v1_funct_1 @ sk_C)),
% 1.09/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.32  thf('92', plain,
% 1.09/1.32      (((k1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.09/1.32         = (k10_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.09/1.32            (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.09/1.32      inference('demod', [status(thm)], ['89', '90', '91'])).
% 1.09/1.32  thf('93', plain,
% 1.09/1.32      ((((k1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.09/1.32          = (k10_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_relat_1 @ sk_C)))
% 1.09/1.32        | ~ (v1_relat_1 @ sk_C)
% 1.09/1.32        | ~ (v1_funct_1 @ sk_C)
% 1.09/1.32        | ~ (v2_funct_1 @ sk_C))),
% 1.09/1.32      inference('sup+', [status(thm)], ['36', '92'])).
% 1.09/1.32  thf('94', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.09/1.32      inference('sup+', [status(thm)], ['42', '43'])).
% 1.09/1.32  thf('95', plain, (![X10 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 1.09/1.32      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.09/1.32  thf('96', plain, (![X47 : $i]: ((k6_partfun1 @ X47) = (k6_relat_1 @ X47))),
% 1.09/1.32      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.09/1.32  thf('97', plain, (![X10 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X10)) = (X10))),
% 1.09/1.32      inference('demod', [status(thm)], ['95', '96'])).
% 1.09/1.32  thf(t80_relat_1, axiom,
% 1.09/1.32    (![A:$i]:
% 1.09/1.32     ( ( v1_relat_1 @ A ) =>
% 1.09/1.32       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 1.09/1.32  thf('98', plain,
% 1.09/1.32      (![X15 : $i]:
% 1.09/1.32         (((k5_relat_1 @ X15 @ (k6_relat_1 @ (k2_relat_1 @ X15))) = (X15))
% 1.09/1.32          | ~ (v1_relat_1 @ X15))),
% 1.09/1.32      inference('cnf', [status(esa)], [t80_relat_1])).
% 1.09/1.32  thf('99', plain, (![X47 : $i]: ((k6_partfun1 @ X47) = (k6_relat_1 @ X47))),
% 1.09/1.32      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.09/1.32  thf('100', plain,
% 1.09/1.32      (![X15 : $i]:
% 1.09/1.32         (((k5_relat_1 @ X15 @ (k6_partfun1 @ (k2_relat_1 @ X15))) = (X15))
% 1.09/1.32          | ~ (v1_relat_1 @ X15))),
% 1.09/1.32      inference('demod', [status(thm)], ['98', '99'])).
% 1.09/1.32  thf('101', plain,
% 1.09/1.32      (![X0 : $i]:
% 1.09/1.32         (((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 1.09/1.32            = (k6_partfun1 @ X0))
% 1.09/1.32          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 1.09/1.32      inference('sup+', [status(thm)], ['97', '100'])).
% 1.09/1.32  thf('102', plain, (![X17 : $i]: (v1_relat_1 @ (k6_partfun1 @ X17))),
% 1.09/1.32      inference('demod', [status(thm)], ['52', '53'])).
% 1.09/1.32  thf('103', plain,
% 1.09/1.32      (![X0 : $i]:
% 1.09/1.32         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 1.09/1.32           = (k6_partfun1 @ X0))),
% 1.09/1.32      inference('demod', [status(thm)], ['101', '102'])).
% 1.09/1.32  thf('104', plain,
% 1.09/1.32      (![X4 : $i, X5 : $i]:
% 1.09/1.32         (~ (v1_relat_1 @ X4)
% 1.09/1.32          | ((k1_relat_1 @ (k5_relat_1 @ X5 @ X4))
% 1.09/1.32              = (k10_relat_1 @ X5 @ (k1_relat_1 @ X4)))
% 1.09/1.32          | ~ (v1_relat_1 @ X5))),
% 1.09/1.32      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.09/1.32  thf('105', plain,
% 1.09/1.32      (![X0 : $i]:
% 1.09/1.32         (((k1_relat_1 @ (k6_partfun1 @ X0))
% 1.09/1.32            = (k10_relat_1 @ (k6_partfun1 @ X0) @ 
% 1.09/1.32               (k1_relat_1 @ (k6_partfun1 @ X0))))
% 1.09/1.32          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 1.09/1.32          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 1.09/1.32      inference('sup+', [status(thm)], ['103', '104'])).
% 1.09/1.32  thf('106', plain, (![X9 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X9)) = (X9))),
% 1.09/1.32      inference('demod', [status(thm)], ['55', '56'])).
% 1.09/1.32  thf('107', plain, (![X9 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X9)) = (X9))),
% 1.09/1.32      inference('demod', [status(thm)], ['55', '56'])).
% 1.09/1.32  thf('108', plain, (![X17 : $i]: (v1_relat_1 @ (k6_partfun1 @ X17))),
% 1.09/1.32      inference('demod', [status(thm)], ['52', '53'])).
% 1.09/1.32  thf('109', plain, (![X17 : $i]: (v1_relat_1 @ (k6_partfun1 @ X17))),
% 1.09/1.32      inference('demod', [status(thm)], ['52', '53'])).
% 1.09/1.32  thf('110', plain,
% 1.09/1.32      (![X0 : $i]: ((X0) = (k10_relat_1 @ (k6_partfun1 @ X0) @ X0))),
% 1.09/1.32      inference('demod', [status(thm)], ['105', '106', '107', '108', '109'])).
% 1.09/1.32  thf('111', plain, ((v1_relat_1 @ sk_C)),
% 1.09/1.32      inference('sup-', [status(thm)], ['65', '66'])).
% 1.09/1.32  thf('112', plain, ((v1_funct_1 @ sk_C)),
% 1.09/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.32  thf('113', plain, ((v2_funct_1 @ sk_C)),
% 1.09/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.32  thf('114', plain, (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_B))),
% 1.09/1.32      inference('demod', [status(thm)],
% 1.09/1.32                ['93', '94', '110', '111', '112', '113'])).
% 1.09/1.32  thf(t167_relat_1, axiom,
% 1.09/1.32    (![A:$i,B:$i]:
% 1.09/1.32     ( ( v1_relat_1 @ B ) =>
% 1.09/1.32       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 1.09/1.32  thf('115', plain,
% 1.09/1.32      (![X2 : $i, X3 : $i]:
% 1.09/1.32         ((r1_tarski @ (k10_relat_1 @ X2 @ X3) @ (k1_relat_1 @ X2))
% 1.09/1.32          | ~ (v1_relat_1 @ X2))),
% 1.09/1.32      inference('cnf', [status(esa)], [t167_relat_1])).
% 1.09/1.32  thf('116', plain,
% 1.09/1.32      (![X0 : $i]:
% 1.09/1.32         ((r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ sk_C) @ X0) @ sk_B)
% 1.09/1.32          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.09/1.32      inference('sup+', [status(thm)], ['114', '115'])).
% 1.09/1.32  thf('117', plain,
% 1.09/1.32      (![X0 : $i]:
% 1.09/1.32         (~ (v1_relat_1 @ sk_C)
% 1.09/1.32          | ~ (v1_funct_1 @ sk_C)
% 1.09/1.32          | (r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ sk_C) @ X0) @ sk_B))),
% 1.09/1.32      inference('sup-', [status(thm)], ['35', '116'])).
% 1.09/1.32  thf('118', plain, ((v1_relat_1 @ sk_C)),
% 1.09/1.32      inference('sup-', [status(thm)], ['65', '66'])).
% 1.09/1.32  thf('119', plain, ((v1_funct_1 @ sk_C)),
% 1.09/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.32  thf('120', plain,
% 1.09/1.32      (![X0 : $i]:
% 1.09/1.32         (r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ sk_C) @ X0) @ sk_B)),
% 1.09/1.32      inference('demod', [status(thm)], ['117', '118', '119'])).
% 1.09/1.32  thf('121', plain,
% 1.09/1.32      (![X4 : $i, X5 : $i]:
% 1.09/1.32         (~ (v1_relat_1 @ X4)
% 1.09/1.32          | ((k1_relat_1 @ (k5_relat_1 @ X5 @ X4))
% 1.09/1.32              = (k10_relat_1 @ X5 @ (k1_relat_1 @ X4)))
% 1.09/1.32          | ~ (v1_relat_1 @ X5))),
% 1.09/1.32      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.09/1.32  thf('122', plain,
% 1.09/1.32      (![X0 : $i, X1 : $i]:
% 1.09/1.32         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 1.09/1.32          | (v4_relat_1 @ X0 @ X1)
% 1.09/1.32          | ~ (v1_relat_1 @ X0))),
% 1.09/1.32      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.09/1.32  thf('123', plain,
% 1.09/1.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.09/1.32         (~ (r1_tarski @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)) @ X2)
% 1.09/1.32          | ~ (v1_relat_1 @ X1)
% 1.09/1.32          | ~ (v1_relat_1 @ X0)
% 1.09/1.32          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 1.09/1.32          | (v4_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2))),
% 1.09/1.32      inference('sup-', [status(thm)], ['121', '122'])).
% 1.09/1.32  thf('124', plain,
% 1.09/1.32      (![X0 : $i]:
% 1.09/1.32         ((v4_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0) @ sk_B)
% 1.09/1.32          | ~ (v1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))
% 1.09/1.32          | ~ (v1_relat_1 @ X0)
% 1.09/1.32          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.09/1.32      inference('sup-', [status(thm)], ['120', '123'])).
% 1.09/1.32  thf('125', plain,
% 1.09/1.32      (![X0 : $i]:
% 1.09/1.32         (~ (v1_relat_1 @ sk_C)
% 1.09/1.32          | ~ (v1_funct_1 @ sk_C)
% 1.09/1.32          | ~ (v1_relat_1 @ X0)
% 1.09/1.32          | ~ (v1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))
% 1.09/1.32          | (v4_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0) @ sk_B))),
% 1.09/1.32      inference('sup-', [status(thm)], ['34', '124'])).
% 1.09/1.32  thf('126', plain, ((v1_relat_1 @ sk_C)),
% 1.09/1.32      inference('sup-', [status(thm)], ['65', '66'])).
% 1.09/1.32  thf('127', plain, ((v1_funct_1 @ sk_C)),
% 1.09/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.32  thf('128', plain,
% 1.09/1.32      (![X0 : $i]:
% 1.09/1.32         (~ (v1_relat_1 @ X0)
% 1.09/1.32          | ~ (v1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))
% 1.09/1.32          | (v4_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0) @ sk_B))),
% 1.09/1.32      inference('demod', [status(thm)], ['125', '126', '127'])).
% 1.09/1.32  thf('129', plain,
% 1.09/1.32      ((~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 1.09/1.32        | ~ (v1_relat_1 @ sk_C)
% 1.09/1.32        | ~ (v1_funct_1 @ sk_C)
% 1.09/1.32        | ~ (v2_funct_1 @ sk_C)
% 1.09/1.32        | (v4_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) @ sk_B)
% 1.09/1.32        | ~ (v1_relat_1 @ sk_C))),
% 1.09/1.32      inference('sup-', [status(thm)], ['33', '128'])).
% 1.09/1.32  thf('130', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.09/1.32      inference('sup+', [status(thm)], ['42', '43'])).
% 1.09/1.32  thf('131', plain, (![X17 : $i]: (v1_relat_1 @ (k6_partfun1 @ X17))),
% 1.09/1.32      inference('demod', [status(thm)], ['52', '53'])).
% 1.09/1.32  thf('132', plain, ((v1_relat_1 @ sk_C)),
% 1.09/1.32      inference('sup-', [status(thm)], ['65', '66'])).
% 1.09/1.32  thf('133', plain, ((v1_funct_1 @ sk_C)),
% 1.09/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.32  thf('134', plain, ((v2_funct_1 @ sk_C)),
% 1.09/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.32  thf('135', plain, ((v1_relat_1 @ sk_C)),
% 1.09/1.32      inference('sup-', [status(thm)], ['65', '66'])).
% 1.09/1.32  thf('136', plain,
% 1.09/1.32      ((v4_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) @ sk_B)),
% 1.09/1.32      inference('demod', [status(thm)],
% 1.09/1.32                ['129', '130', '131', '132', '133', '134', '135'])).
% 1.09/1.32  thf('137', plain,
% 1.09/1.32      (![X0 : $i, X1 : $i]:
% 1.09/1.32         (~ (v4_relat_1 @ X0 @ X1)
% 1.09/1.32          | (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 1.09/1.32          | ~ (v1_relat_1 @ X0))),
% 1.09/1.32      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.09/1.32  thf('138', plain,
% 1.09/1.32      ((~ (v1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))
% 1.09/1.32        | (r1_tarski @ 
% 1.09/1.32           (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)) @ sk_B))),
% 1.09/1.32      inference('sup-', [status(thm)], ['136', '137'])).
% 1.09/1.32  thf('139', plain,
% 1.09/1.32      ((~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 1.09/1.32        | ~ (v1_relat_1 @ sk_C)
% 1.09/1.32        | ~ (v1_funct_1 @ sk_C)
% 1.09/1.32        | ~ (v2_funct_1 @ sk_C)
% 1.09/1.32        | (r1_tarski @ 
% 1.09/1.32           (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)) @ sk_B))),
% 1.09/1.32      inference('sup-', [status(thm)], ['32', '138'])).
% 1.09/1.32  thf('140', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.09/1.32      inference('sup+', [status(thm)], ['42', '43'])).
% 1.09/1.32  thf('141', plain, (![X17 : $i]: (v1_relat_1 @ (k6_partfun1 @ X17))),
% 1.09/1.32      inference('demod', [status(thm)], ['52', '53'])).
% 1.09/1.32  thf('142', plain, ((v1_relat_1 @ sk_C)),
% 1.09/1.32      inference('sup-', [status(thm)], ['65', '66'])).
% 1.09/1.32  thf('143', plain, ((v1_funct_1 @ sk_C)),
% 1.09/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.32  thf('144', plain, ((v2_funct_1 @ sk_C)),
% 1.09/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.32  thf('145', plain,
% 1.09/1.32      ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)) @ 
% 1.09/1.32        sk_B)),
% 1.09/1.32      inference('demod', [status(thm)],
% 1.09/1.32                ['139', '140', '141', '142', '143', '144'])).
% 1.09/1.32  thf('146', plain, (![X9 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X9)) = (X9))),
% 1.09/1.32      inference('demod', [status(thm)], ['55', '56'])).
% 1.09/1.32  thf('147', plain,
% 1.09/1.32      (![X11 : $i, X12 : $i]:
% 1.09/1.32         (~ (r1_tarski @ (k1_relat_1 @ X11) @ X12)
% 1.09/1.32          | ((k5_relat_1 @ (k6_partfun1 @ X12) @ X11) = (X11))
% 1.09/1.32          | ~ (v1_relat_1 @ X11))),
% 1.09/1.32      inference('demod', [status(thm)], ['77', '78'])).
% 1.09/1.32  thf('148', plain,
% 1.09/1.32      (![X0 : $i, X1 : $i]:
% 1.09/1.32         (~ (r1_tarski @ X0 @ X1)
% 1.09/1.32          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 1.09/1.32          | ((k5_relat_1 @ (k6_partfun1 @ X1) @ (k6_partfun1 @ X0))
% 1.09/1.32              = (k6_partfun1 @ X0)))),
% 1.09/1.32      inference('sup-', [status(thm)], ['146', '147'])).
% 1.09/1.32  thf('149', plain, (![X17 : $i]: (v1_relat_1 @ (k6_partfun1 @ X17))),
% 1.09/1.32      inference('demod', [status(thm)], ['52', '53'])).
% 1.09/1.32  thf('150', plain,
% 1.09/1.32      (![X0 : $i, X1 : $i]:
% 1.09/1.32         (~ (r1_tarski @ X0 @ X1)
% 1.09/1.32          | ((k5_relat_1 @ (k6_partfun1 @ X1) @ (k6_partfun1 @ X0))
% 1.09/1.32              = (k6_partfun1 @ X0)))),
% 1.09/1.32      inference('demod', [status(thm)], ['148', '149'])).
% 1.09/1.32  thf('151', plain,
% 1.09/1.32      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.09/1.32         (k6_partfun1 @ 
% 1.09/1.32          (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))))
% 1.09/1.32         = (k6_partfun1 @ 
% 1.09/1.32            (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))))),
% 1.09/1.32      inference('sup-', [status(thm)], ['145', '150'])).
% 1.09/1.32  thf('152', plain,
% 1.09/1.32      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.09/1.32          (k6_partfun1 @ (k1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)))))
% 1.09/1.32          = (k6_partfun1 @ 
% 1.09/1.32             (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))))
% 1.09/1.32        | ~ (v1_relat_1 @ sk_C)
% 1.09/1.32        | ~ (v1_funct_1 @ sk_C)
% 1.09/1.32        | ~ (v2_funct_1 @ sk_C))),
% 1.09/1.32      inference('sup+', [status(thm)], ['31', '151'])).
% 1.09/1.32  thf('153', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.09/1.32      inference('sup+', [status(thm)], ['42', '43'])).
% 1.09/1.32  thf('154', plain, (![X9 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X9)) = (X9))),
% 1.09/1.32      inference('demod', [status(thm)], ['55', '56'])).
% 1.09/1.32  thf('155', plain,
% 1.09/1.32      (![X0 : $i]:
% 1.09/1.32         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 1.09/1.32           = (k6_partfun1 @ X0))),
% 1.09/1.32      inference('demod', [status(thm)], ['101', '102'])).
% 1.09/1.32  thf('156', plain, ((v1_relat_1 @ sk_C)),
% 1.09/1.32      inference('sup-', [status(thm)], ['65', '66'])).
% 1.09/1.32  thf('157', plain, ((v1_funct_1 @ sk_C)),
% 1.09/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.32  thf('158', plain, ((v2_funct_1 @ sk_C)),
% 1.09/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.32  thf('159', plain,
% 1.09/1.32      (((k6_partfun1 @ sk_B)
% 1.09/1.32         = (k6_partfun1 @ 
% 1.09/1.32            (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))))),
% 1.09/1.32      inference('demod', [status(thm)],
% 1.09/1.32                ['152', '153', '154', '155', '156', '157', '158'])).
% 1.09/1.32  thf('160', plain, (![X9 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X9)) = (X9))),
% 1.09/1.32      inference('demod', [status(thm)], ['55', '56'])).
% 1.09/1.32  thf('161', plain,
% 1.09/1.32      (((k1_relat_1 @ (k6_partfun1 @ sk_B))
% 1.09/1.32         = (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)))),
% 1.09/1.32      inference('sup+', [status(thm)], ['159', '160'])).
% 1.09/1.32  thf('162', plain, (![X9 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X9)) = (X9))),
% 1.09/1.32      inference('demod', [status(thm)], ['55', '56'])).
% 1.09/1.32  thf('163', plain,
% 1.09/1.32      (((sk_B) = (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)))),
% 1.09/1.32      inference('demod', [status(thm)], ['161', '162'])).
% 1.09/1.32  thf('164', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.09/1.32      inference('demod', [status(thm)], ['51', '54', '57'])).
% 1.09/1.32  thf('165', plain,
% 1.09/1.32      (![X11 : $i, X12 : $i]:
% 1.09/1.32         (~ (r1_tarski @ (k1_relat_1 @ X11) @ X12)
% 1.09/1.32          | ((k5_relat_1 @ (k6_partfun1 @ X12) @ X11) = (X11))
% 1.09/1.32          | ~ (v1_relat_1 @ X11))),
% 1.09/1.32      inference('demod', [status(thm)], ['77', '78'])).
% 1.09/1.32  thf('166', plain,
% 1.09/1.32      (![X0 : $i]:
% 1.09/1.32         (~ (v1_relat_1 @ X0)
% 1.09/1.32          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 1.09/1.32      inference('sup-', [status(thm)], ['164', '165'])).
% 1.09/1.32  thf('167', plain,
% 1.09/1.32      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.09/1.32          (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))
% 1.09/1.32          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))
% 1.09/1.32        | ~ (v1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)))),
% 1.09/1.32      inference('sup+', [status(thm)], ['163', '166'])).
% 1.09/1.32  thf('168', plain,
% 1.09/1.32      ((~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 1.09/1.32        | ~ (v1_relat_1 @ sk_C)
% 1.09/1.32        | ~ (v1_funct_1 @ sk_C)
% 1.09/1.32        | ~ (v2_funct_1 @ sk_C)
% 1.09/1.32        | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.09/1.32            (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))
% 1.09/1.32            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)))),
% 1.09/1.32      inference('sup-', [status(thm)], ['30', '167'])).
% 1.09/1.32  thf('169', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.09/1.32      inference('sup+', [status(thm)], ['42', '43'])).
% 1.09/1.32  thf('170', plain, (![X17 : $i]: (v1_relat_1 @ (k6_partfun1 @ X17))),
% 1.09/1.32      inference('demod', [status(thm)], ['52', '53'])).
% 1.09/1.32  thf('171', plain, ((v1_relat_1 @ sk_C)),
% 1.09/1.32      inference('sup-', [status(thm)], ['65', '66'])).
% 1.09/1.32  thf('172', plain, ((v1_funct_1 @ sk_C)),
% 1.09/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.32  thf('173', plain, ((v2_funct_1 @ sk_C)),
% 1.09/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.32  thf('174', plain,
% 1.09/1.32      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.09/1.32         (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))
% 1.09/1.32         = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))),
% 1.09/1.32      inference('demod', [status(thm)],
% 1.09/1.32                ['168', '169', '170', '171', '172', '173'])).
% 1.09/1.32  thf('175', plain,
% 1.09/1.32      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.09/1.32          (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 1.09/1.32          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))
% 1.09/1.32        | ~ (v1_relat_1 @ sk_C)
% 1.09/1.32        | ~ (v1_funct_1 @ sk_C)
% 1.09/1.32        | ~ (v2_funct_1 @ sk_C))),
% 1.09/1.32      inference('sup+', [status(thm)], ['29', '174'])).
% 1.09/1.32  thf('176', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.09/1.32      inference('sup+', [status(thm)], ['42', '43'])).
% 1.09/1.32  thf('177', plain,
% 1.09/1.32      (![X0 : $i]:
% 1.09/1.32         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 1.09/1.32           = (k6_partfun1 @ X0))),
% 1.09/1.32      inference('demod', [status(thm)], ['101', '102'])).
% 1.09/1.32  thf('178', plain, ((v1_relat_1 @ sk_C)),
% 1.09/1.32      inference('sup-', [status(thm)], ['65', '66'])).
% 1.09/1.32  thf('179', plain, ((v1_funct_1 @ sk_C)),
% 1.09/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.32  thf('180', plain, ((v2_funct_1 @ sk_C)),
% 1.09/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.32  thf('181', plain,
% 1.09/1.32      (((k6_partfun1 @ sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))),
% 1.09/1.32      inference('demod', [status(thm)],
% 1.09/1.32                ['175', '176', '177', '178', '179', '180'])).
% 1.09/1.32  thf(t55_relat_1, axiom,
% 1.09/1.32    (![A:$i]:
% 1.09/1.32     ( ( v1_relat_1 @ A ) =>
% 1.09/1.32       ( ![B:$i]:
% 1.09/1.32         ( ( v1_relat_1 @ B ) =>
% 1.09/1.32           ( ![C:$i]:
% 1.09/1.32             ( ( v1_relat_1 @ C ) =>
% 1.09/1.32               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 1.09/1.32                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 1.09/1.32  thf('182', plain,
% 1.09/1.32      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.09/1.32         (~ (v1_relat_1 @ X6)
% 1.09/1.32          | ((k5_relat_1 @ (k5_relat_1 @ X7 @ X6) @ X8)
% 1.09/1.32              = (k5_relat_1 @ X7 @ (k5_relat_1 @ X6 @ X8)))
% 1.09/1.32          | ~ (v1_relat_1 @ X8)
% 1.09/1.32          | ~ (v1_relat_1 @ X7))),
% 1.09/1.32      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.09/1.32  thf('183', plain,
% 1.09/1.32      (![X0 : $i]:
% 1.09/1.32         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.09/1.32            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 1.09/1.32          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.09/1.32          | ~ (v1_relat_1 @ X0)
% 1.09/1.32          | ~ (v1_relat_1 @ sk_C))),
% 1.09/1.32      inference('sup+', [status(thm)], ['181', '182'])).
% 1.09/1.32  thf('184', plain, ((v1_relat_1 @ sk_C)),
% 1.09/1.32      inference('sup-', [status(thm)], ['65', '66'])).
% 1.09/1.32  thf('185', plain,
% 1.09/1.32      (![X0 : $i]:
% 1.09/1.32         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.09/1.32            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 1.09/1.32          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.09/1.32          | ~ (v1_relat_1 @ X0))),
% 1.09/1.32      inference('demod', [status(thm)], ['183', '184'])).
% 1.09/1.32  thf('186', plain,
% 1.09/1.32      (![X0 : $i]:
% 1.09/1.32         (~ (v1_relat_1 @ sk_C)
% 1.09/1.32          | ~ (v1_funct_1 @ sk_C)
% 1.09/1.32          | ~ (v1_relat_1 @ X0)
% 1.09/1.32          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.09/1.32              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 1.09/1.32      inference('sup-', [status(thm)], ['26', '185'])).
% 1.09/1.32  thf('187', plain, ((v1_relat_1 @ sk_C)),
% 1.09/1.32      inference('sup-', [status(thm)], ['65', '66'])).
% 1.09/1.32  thf('188', plain, ((v1_funct_1 @ sk_C)),
% 1.09/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.32  thf('189', plain,
% 1.09/1.32      (![X0 : $i]:
% 1.09/1.32         (~ (v1_relat_1 @ X0)
% 1.09/1.32          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.09/1.32              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 1.09/1.32      inference('demod', [status(thm)], ['186', '187', '188'])).
% 1.09/1.32  thf('190', plain,
% 1.09/1.32      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 1.09/1.32          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 1.09/1.32        | ~ (v1_relat_1 @ sk_D))),
% 1.09/1.32      inference('sup+', [status(thm)], ['25', '189'])).
% 1.09/1.32  thf('191', plain,
% 1.09/1.32      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.09/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.32  thf('192', plain,
% 1.09/1.32      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.09/1.32         ((v4_relat_1 @ X24 @ X25)
% 1.09/1.32          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 1.09/1.32      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.09/1.32  thf('193', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 1.09/1.32      inference('sup-', [status(thm)], ['191', '192'])).
% 1.09/1.32  thf('194', plain,
% 1.09/1.32      (![X0 : $i, X1 : $i]:
% 1.09/1.32         (~ (v4_relat_1 @ X0 @ X1)
% 1.09/1.32          | (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 1.09/1.32          | ~ (v1_relat_1 @ X0))),
% 1.09/1.32      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.09/1.32  thf('195', plain,
% 1.09/1.32      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B))),
% 1.09/1.32      inference('sup-', [status(thm)], ['193', '194'])).
% 1.09/1.32  thf('196', plain,
% 1.09/1.32      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.09/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.32  thf('197', plain,
% 1.09/1.32      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.09/1.32         ((v1_relat_1 @ X21)
% 1.09/1.32          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 1.09/1.32      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.09/1.32  thf('198', plain, ((v1_relat_1 @ sk_D)),
% 1.09/1.32      inference('sup-', [status(thm)], ['196', '197'])).
% 1.09/1.32  thf('199', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B)),
% 1.09/1.32      inference('demod', [status(thm)], ['195', '198'])).
% 1.09/1.32  thf('200', plain,
% 1.09/1.32      (![X11 : $i, X12 : $i]:
% 1.09/1.32         (~ (r1_tarski @ (k1_relat_1 @ X11) @ X12)
% 1.09/1.32          | ((k5_relat_1 @ (k6_partfun1 @ X12) @ X11) = (X11))
% 1.09/1.32          | ~ (v1_relat_1 @ X11))),
% 1.09/1.32      inference('demod', [status(thm)], ['77', '78'])).
% 1.09/1.32  thf('201', plain,
% 1.09/1.32      ((~ (v1_relat_1 @ sk_D)
% 1.09/1.32        | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D)))),
% 1.09/1.32      inference('sup-', [status(thm)], ['199', '200'])).
% 1.09/1.32  thf('202', plain, ((v1_relat_1 @ sk_D)),
% 1.09/1.32      inference('sup-', [status(thm)], ['196', '197'])).
% 1.09/1.32  thf('203', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))),
% 1.09/1.32      inference('demod', [status(thm)], ['201', '202'])).
% 1.09/1.32  thf('204', plain,
% 1.09/1.32      (![X16 : $i]:
% 1.09/1.32         ((v1_relat_1 @ (k2_funct_1 @ X16))
% 1.09/1.32          | ~ (v1_funct_1 @ X16)
% 1.09/1.32          | ~ (v1_relat_1 @ X16))),
% 1.09/1.32      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.09/1.32  thf('205', plain,
% 1.09/1.32      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.09/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.32  thf('206', plain,
% 1.09/1.32      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.09/1.32         ((v4_relat_1 @ X24 @ X25)
% 1.09/1.32          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 1.09/1.32      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.09/1.32  thf('207', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 1.09/1.32      inference('sup-', [status(thm)], ['205', '206'])).
% 1.09/1.32  thf('208', plain,
% 1.09/1.32      (![X0 : $i, X1 : $i]:
% 1.09/1.32         (~ (v4_relat_1 @ X0 @ X1)
% 1.09/1.32          | (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 1.09/1.32          | ~ (v1_relat_1 @ X0))),
% 1.09/1.32      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.09/1.32  thf('209', plain,
% 1.09/1.32      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 1.09/1.32      inference('sup-', [status(thm)], ['207', '208'])).
% 1.09/1.32  thf('210', plain, ((v1_relat_1 @ sk_C)),
% 1.09/1.32      inference('sup-', [status(thm)], ['65', '66'])).
% 1.09/1.32  thf('211', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 1.09/1.32      inference('demod', [status(thm)], ['209', '210'])).
% 1.09/1.32  thf('212', plain,
% 1.09/1.32      (![X19 : $i]:
% 1.09/1.32         (~ (v2_funct_1 @ X19)
% 1.09/1.32          | ((k1_relat_1 @ X19) = (k2_relat_1 @ (k2_funct_1 @ X19)))
% 1.09/1.32          | ~ (v1_funct_1 @ X19)
% 1.09/1.32          | ~ (v1_relat_1 @ X19))),
% 1.09/1.32      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.09/1.32  thf(t79_relat_1, axiom,
% 1.09/1.32    (![A:$i,B:$i]:
% 1.09/1.32     ( ( v1_relat_1 @ B ) =>
% 1.09/1.32       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 1.09/1.32         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 1.09/1.32  thf('213', plain,
% 1.09/1.32      (![X13 : $i, X14 : $i]:
% 1.09/1.32         (~ (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 1.09/1.32          | ((k5_relat_1 @ X13 @ (k6_relat_1 @ X14)) = (X13))
% 1.09/1.32          | ~ (v1_relat_1 @ X13))),
% 1.09/1.32      inference('cnf', [status(esa)], [t79_relat_1])).
% 1.09/1.32  thf('214', plain, (![X47 : $i]: ((k6_partfun1 @ X47) = (k6_relat_1 @ X47))),
% 1.09/1.32      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.09/1.32  thf('215', plain,
% 1.09/1.32      (![X13 : $i, X14 : $i]:
% 1.09/1.32         (~ (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 1.09/1.32          | ((k5_relat_1 @ X13 @ (k6_partfun1 @ X14)) = (X13))
% 1.09/1.32          | ~ (v1_relat_1 @ X13))),
% 1.09/1.32      inference('demod', [status(thm)], ['213', '214'])).
% 1.09/1.32  thf('216', plain,
% 1.09/1.32      (![X0 : $i, X1 : $i]:
% 1.09/1.32         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 1.09/1.32          | ~ (v1_relat_1 @ X0)
% 1.09/1.32          | ~ (v1_funct_1 @ X0)
% 1.09/1.32          | ~ (v2_funct_1 @ X0)
% 1.09/1.32          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.09/1.32          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ X1))
% 1.09/1.32              = (k2_funct_1 @ X0)))),
% 1.09/1.32      inference('sup-', [status(thm)], ['212', '215'])).
% 1.09/1.32  thf('217', plain,
% 1.09/1.32      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 1.09/1.32          = (k2_funct_1 @ sk_C))
% 1.09/1.32        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.09/1.32        | ~ (v2_funct_1 @ sk_C)
% 1.09/1.32        | ~ (v1_funct_1 @ sk_C)
% 1.09/1.32        | ~ (v1_relat_1 @ sk_C))),
% 1.09/1.32      inference('sup-', [status(thm)], ['211', '216'])).
% 1.09/1.32  thf('218', plain, ((v2_funct_1 @ sk_C)),
% 1.09/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.32  thf('219', plain, ((v1_funct_1 @ sk_C)),
% 1.09/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.32  thf('220', plain, ((v1_relat_1 @ sk_C)),
% 1.09/1.32      inference('sup-', [status(thm)], ['65', '66'])).
% 1.09/1.32  thf('221', plain,
% 1.09/1.32      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 1.09/1.32          = (k2_funct_1 @ sk_C))
% 1.09/1.32        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.09/1.32      inference('demod', [status(thm)], ['217', '218', '219', '220'])).
% 1.09/1.32  thf('222', plain,
% 1.09/1.32      ((~ (v1_relat_1 @ sk_C)
% 1.09/1.32        | ~ (v1_funct_1 @ sk_C)
% 1.09/1.32        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 1.09/1.32            = (k2_funct_1 @ sk_C)))),
% 1.09/1.32      inference('sup-', [status(thm)], ['204', '221'])).
% 1.09/1.32  thf('223', plain, ((v1_relat_1 @ sk_C)),
% 1.09/1.32      inference('sup-', [status(thm)], ['65', '66'])).
% 1.09/1.32  thf('224', plain, ((v1_funct_1 @ sk_C)),
% 1.09/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.32  thf('225', plain,
% 1.09/1.32      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 1.09/1.32         = (k2_funct_1 @ sk_C))),
% 1.09/1.32      inference('demod', [status(thm)], ['222', '223', '224'])).
% 1.09/1.32  thf('226', plain, ((v1_relat_1 @ sk_D)),
% 1.09/1.32      inference('sup-', [status(thm)], ['196', '197'])).
% 1.09/1.32  thf('227', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 1.09/1.32      inference('demod', [status(thm)], ['190', '203', '225', '226'])).
% 1.09/1.32  thf('228', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.09/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.09/1.32  thf('229', plain, ($false),
% 1.09/1.32      inference('simplify_reflect-', [status(thm)], ['227', '228'])).
% 1.09/1.32  
% 1.09/1.32  % SZS output end Refutation
% 1.09/1.32  
% 1.09/1.33  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

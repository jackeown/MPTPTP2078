%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7Z6usY0Of7

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:12 EST 2020

% Result     : Theorem 44.73s
% Output     : Refutation 44.73s
% Verified   : 
% Statistics : Number of formulae       :  275 ( 873 expanded)
%              Number of leaves         :   47 ( 287 expanded)
%              Depth                    :   26
%              Number of atoms          : 2295 (15350 expanded)
%              Number of equality atoms :  144 (1013 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

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
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ( ( k1_partfun1 @ X45 @ X46 @ X48 @ X49 @ X44 @ X47 )
        = ( k5_relat_1 @ X44 @ X47 ) ) ) ),
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
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X43 ) ) ) ) ),
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

thf('20',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('21',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('22',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( X33 = X36 )
      | ~ ( r2_relset_1 @ X34 @ X35 @ X33 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','23'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('25',plain,(
    ! [X37: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

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
    ! [X37: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['24','27'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('29',plain,(
    ! [X24: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
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

thf('30',plain,(
    ! [X26: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X26 ) @ X26 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('31',plain,(
    ! [X50: $i] :
      ( ( k6_partfun1 @ X50 )
      = ( k6_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('32',plain,(
    ! [X26: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X26 ) @ X26 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X26: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X26 ) @ X26 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('34',plain,(
    ! [X24: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('35',plain,(
    ! [X24: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('36',plain,(
    ! [X26: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X26 ) @ X26 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('37',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) ) @ ( k2_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('38',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('41',plain,(
    ! [X19: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('42',plain,(
    ! [X50: $i] :
      ( ( k6_partfun1 @ X50 )
      = ( k6_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('43',plain,(
    ! [X19: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X19 ) )
      = X19 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('45',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['40','43','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['35','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('51',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k2_relset_1 @ X31 @ X32 @ X30 )
        = ( k2_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('52',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) ) @ ( k2_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ sk_C ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('58',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('60',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('61',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ sk_C ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['56','61'])).

thf('63',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ sk_C ) ) )
      | ( sk_B
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_B
      = ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['49','64'])).

thf('66',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['52','53'])).

thf('67',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('68',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('69',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( sk_B
      = ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['65','66','67','68','69','70'])).

thf('72',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B
      = ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['34','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('74',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( sk_B
    = ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('76',plain,(
    ! [X23: $i] :
      ( ( ( k5_relat_1 @ X23 @ ( k6_relat_1 @ ( k2_relat_1 @ X23 ) ) )
        = X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('77',plain,(
    ! [X50: $i] :
      ( ( k6_partfun1 @ X50 )
      = ( k6_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('78',plain,(
    ! [X23: $i] :
      ( ( ( k5_relat_1 @ X23 @ ( k6_partfun1 @ ( k2_relat_1 @ X23 ) ) )
        = X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( ( k5_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) @ ( k6_partfun1 @ sk_B ) )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['75','78'])).

thf('80',plain,
    ( ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) @ ( k6_partfun1 @ sk_B ) )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['33','79'])).

thf('81',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['52','53'])).

thf('82',plain,(
    ! [X37: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('83',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('88',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( k5_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) @ ( k6_partfun1 @ sk_B ) )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['80','81','86','87','88','89'])).

thf('91',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) @ ( k6_partfun1 @ sk_B ) )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['32','90'])).

thf('92',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['52','53'])).

thf('93',plain,(
    ! [X19: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X19 ) )
      = X19 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('94',plain,(
    ! [X23: $i] :
      ( ( ( k5_relat_1 @ X23 @ ( k6_partfun1 @ ( k2_relat_1 @ X23 ) ) )
        = X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('99',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( k6_partfun1 @ sk_B )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['91','92','97','98','99','100'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('102',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X16 @ X15 ) @ X17 )
        = ( k5_relat_1 @ X16 @ ( k5_relat_1 @ X15 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['29','105'])).

thf('107',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('108',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['28','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('112',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v4_relat_1 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('113',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['111','112'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('114',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('115',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['113','114'])).

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
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('120',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['115','120'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('122',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X21 ) @ X22 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X22 ) @ X21 )
        = X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('123',plain,(
    ! [X50: $i] :
      ( ( k6_partfun1 @ X50 )
      = ( k6_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('124',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X21 ) @ X22 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X22 ) @ X21 )
        = X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = sk_D ) ),
    inference('sup-',[status(thm)],['121','124'])).

thf('126',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['118','119'])).

thf('127',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X24: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
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

thf('129',plain,(
    ! [X25: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k1_relat_1 @ X25 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('130',plain,(
    ! [X24: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('131',plain,(
    ! [X24: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('132',plain,(
    ! [X26: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k5_relat_1 @ X26 @ ( k2_funct_1 @ X26 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('133',plain,(
    ! [X50: $i] :
      ( ( k6_partfun1 @ X50 )
      = ( k6_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('134',plain,(
    ! [X26: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k5_relat_1 @ X26 @ ( k2_funct_1 @ X26 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v4_relat_1 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('137',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('139',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('141',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X21 ) @ X22 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X22 ) @ X21 )
        = X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('143',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_C )
      = sk_C ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('145',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X16 @ X15 ) @ X17 )
        = ( k5_relat_1 @ X16 @ ( k5_relat_1 @ X15 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('149',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['147','148','149'])).

thf('151',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['134','150'])).

thf('152',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['139','140'])).

thf('153',plain,(
    ! [X18: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('154',plain,(
    ! [X50: $i] :
      ( ( k6_partfun1 @ X50 )
      = ( k6_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('155',plain,(
    ! [X18: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X18 ) )
      = X18 ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X21 ) @ X22 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X22 ) @ X21 )
        = X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['152','159'])).

thf('161',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('162',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['151','160','161','162','163'])).

thf('165',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['131','164'])).

thf('166',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('167',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['165','166','167'])).

thf('169',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) ) @ ( k2_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('170',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X19: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X19 ) )
      = X19 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('172',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('173',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['170','171','172'])).

thf('174',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['130','173'])).

thf('175',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('176',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['174','175','176'])).

thf('178',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('179',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['129','179'])).

thf('181',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('182',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('183',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['180','181','182','183','184'])).

thf('186',plain,(
    ! [X23: $i] :
      ( ( ( k5_relat_1 @ X23 @ ( k6_partfun1 @ ( k2_relat_1 @ X23 ) ) )
        = X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('187',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['185','186'])).

thf('188',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['128','187'])).

thf('189',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('190',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['188','189','190'])).

thf('192',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('193',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('194',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X21 ) @ X22 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X22 ) @ X21 )
        = X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('195',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X16 @ X15 ) @ X17 )
        = ( k5_relat_1 @ X16 @ ( k5_relat_1 @ X15 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('197',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['195','196'])).

thf('198',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('199',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['197','198'])).

thf('200',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['199'])).

thf('201',plain,
    ( ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['192','200'])).

thf('202',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('203',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['152','159'])).

thf(t72_relat_1,axiom,(
    ! [A: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('204',plain,(
    ! [X20: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X20 ) )
      = ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('205',plain,(
    ! [X50: $i] :
      ( ( k6_partfun1 @ X50 )
      = ( k6_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('206',plain,(
    ! [X50: $i] :
      ( ( k6_partfun1 @ X50 )
      = ( k6_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('207',plain,(
    ! [X20: $i] :
      ( ( k4_relat_1 @ ( k6_partfun1 @ X20 ) )
      = ( k6_partfun1 @ X20 ) ) ),
    inference(demod,[status(thm)],['204','205','206'])).

thf('208',plain,(
    ! [X20: $i] :
      ( ( k4_relat_1 @ ( k6_partfun1 @ X20 ) )
      = ( k6_partfun1 @ X20 ) ) ),
    inference(demod,[status(thm)],['204','205','206'])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('209',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X13 ) @ ( k4_relat_1 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('210',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['208','209'])).

thf('211',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('212',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['210','211'])).

thf('213',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X1 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['207','212'])).

thf('214',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('215',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X1 ) ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ ( k6_partfun1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['213','214'])).

thf('216',plain,
    ( ( k4_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['203','215'])).

thf('217',plain,(
    ! [X20: $i] :
      ( ( k4_relat_1 @ ( k6_partfun1 @ X20 ) )
      = ( k6_partfun1 @ X20 ) ) ),
    inference(demod,[status(thm)],['204','205','206'])).

thf('218',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
    = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['216','217'])).

thf('219',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('220',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['118','119'])).

thf('221',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['201','202','218','219','220'])).

thf('222',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['191','221'])).

thf('223',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['118','119'])).

thf('224',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['110','127','222','223'])).

thf('225',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['224','225'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7Z6usY0Of7
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:05:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.22/0.36  % Python version: Python 3.6.8
% 0.22/0.36  % Running in FO mode
% 44.73/44.94  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 44.73/44.94  % Solved by: fo/fo7.sh
% 44.73/44.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 44.73/44.94  % done 21437 iterations in 44.472s
% 44.73/44.94  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 44.73/44.94  % SZS output start Refutation
% 44.73/44.94  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 44.73/44.94  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 44.73/44.94  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 44.73/44.94  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 44.73/44.94  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 44.73/44.94  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 44.73/44.94  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 44.73/44.94  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 44.73/44.94  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 44.73/44.94  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 44.73/44.94  thf(sk_A_type, type, sk_A: $i).
% 44.73/44.94  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 44.73/44.94  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 44.73/44.94  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 44.73/44.94  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 44.73/44.94  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 44.73/44.94  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 44.73/44.94  thf(sk_D_type, type, sk_D: $i).
% 44.73/44.94  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 44.73/44.94  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 44.73/44.94  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 44.73/44.94  thf(sk_C_type, type, sk_C: $i).
% 44.73/44.94  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 44.73/44.94  thf(sk_B_type, type, sk_B: $i).
% 44.73/44.94  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 44.73/44.94  thf(t36_funct_2, conjecture,
% 44.73/44.94    (![A:$i,B:$i,C:$i]:
% 44.73/44.94     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 44.73/44.94         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 44.73/44.94       ( ![D:$i]:
% 44.73/44.94         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 44.73/44.94             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 44.73/44.94           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 44.73/44.94               ( r2_relset_1 @
% 44.73/44.94                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 44.73/44.94                 ( k6_partfun1 @ A ) ) & 
% 44.73/44.94               ( v2_funct_1 @ C ) ) =>
% 44.73/44.94             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 44.73/44.94               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 44.73/44.94  thf(zf_stmt_0, negated_conjecture,
% 44.73/44.94    (~( ![A:$i,B:$i,C:$i]:
% 44.73/44.94        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 44.73/44.94            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 44.73/44.94          ( ![D:$i]:
% 44.73/44.94            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 44.73/44.94                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 44.73/44.94              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 44.73/44.94                  ( r2_relset_1 @
% 44.73/44.94                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 44.73/44.94                    ( k6_partfun1 @ A ) ) & 
% 44.73/44.94                  ( v2_funct_1 @ C ) ) =>
% 44.73/44.94                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 44.73/44.94                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 44.73/44.94    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 44.73/44.94  thf('0', plain,
% 44.73/44.94      ((r2_relset_1 @ sk_A @ sk_A @ 
% 44.73/44.94        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 44.73/44.94        (k6_partfun1 @ sk_A))),
% 44.73/44.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.73/44.94  thf('1', plain,
% 44.73/44.94      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 44.73/44.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.73/44.94  thf('2', plain,
% 44.73/44.94      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 44.73/44.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.73/44.94  thf(redefinition_k1_partfun1, axiom,
% 44.73/44.94    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 44.73/44.94     ( ( ( v1_funct_1 @ E ) & 
% 44.73/44.94         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 44.73/44.94         ( v1_funct_1 @ F ) & 
% 44.73/44.94         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 44.73/44.94       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 44.73/44.94  thf('3', plain,
% 44.73/44.94      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 44.73/44.94         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 44.73/44.94          | ~ (v1_funct_1 @ X44)
% 44.73/44.94          | ~ (v1_funct_1 @ X47)
% 44.73/44.94          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 44.73/44.94          | ((k1_partfun1 @ X45 @ X46 @ X48 @ X49 @ X44 @ X47)
% 44.73/44.94              = (k5_relat_1 @ X44 @ X47)))),
% 44.73/44.94      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 44.73/44.94  thf('4', plain,
% 44.73/44.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.73/44.94         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 44.73/44.94            = (k5_relat_1 @ sk_C @ X0))
% 44.73/44.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 44.73/44.94          | ~ (v1_funct_1 @ X0)
% 44.73/44.94          | ~ (v1_funct_1 @ sk_C))),
% 44.73/44.94      inference('sup-', [status(thm)], ['2', '3'])).
% 44.73/44.94  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 44.73/44.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.73/44.94  thf('6', plain,
% 44.73/44.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.73/44.94         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 44.73/44.94            = (k5_relat_1 @ sk_C @ X0))
% 44.73/44.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 44.73/44.94          | ~ (v1_funct_1 @ X0))),
% 44.73/44.94      inference('demod', [status(thm)], ['4', '5'])).
% 44.73/44.94  thf('7', plain,
% 44.73/44.94      ((~ (v1_funct_1 @ sk_D)
% 44.73/44.94        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 44.73/44.94            = (k5_relat_1 @ sk_C @ sk_D)))),
% 44.73/44.94      inference('sup-', [status(thm)], ['1', '6'])).
% 44.73/44.94  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 44.73/44.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.73/44.94  thf('9', plain,
% 44.73/44.94      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 44.73/44.94         = (k5_relat_1 @ sk_C @ sk_D))),
% 44.73/44.94      inference('demod', [status(thm)], ['7', '8'])).
% 44.73/44.94  thf('10', plain,
% 44.73/44.94      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 44.73/44.94        (k6_partfun1 @ sk_A))),
% 44.73/44.94      inference('demod', [status(thm)], ['0', '9'])).
% 44.73/44.94  thf('11', plain,
% 44.73/44.94      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 44.73/44.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.73/44.94  thf('12', plain,
% 44.73/44.94      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 44.73/44.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.73/44.94  thf(dt_k1_partfun1, axiom,
% 44.73/44.94    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 44.73/44.94     ( ( ( v1_funct_1 @ E ) & 
% 44.73/44.94         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 44.73/44.94         ( v1_funct_1 @ F ) & 
% 44.73/44.94         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 44.73/44.94       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 44.73/44.94         ( m1_subset_1 @
% 44.73/44.94           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 44.73/44.94           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 44.73/44.94  thf('13', plain,
% 44.73/44.94      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 44.73/44.94         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 44.73/44.94          | ~ (v1_funct_1 @ X38)
% 44.73/44.94          | ~ (v1_funct_1 @ X41)
% 44.73/44.94          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 44.73/44.94          | (m1_subset_1 @ (k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41) @ 
% 44.73/44.94             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X43))))),
% 44.73/44.94      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 44.73/44.94  thf('14', plain,
% 44.73/44.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.73/44.94         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 44.73/44.94           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 44.73/44.94          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 44.73/44.94          | ~ (v1_funct_1 @ X1)
% 44.73/44.94          | ~ (v1_funct_1 @ sk_C))),
% 44.73/44.94      inference('sup-', [status(thm)], ['12', '13'])).
% 44.73/44.94  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 44.73/44.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.73/44.94  thf('16', plain,
% 44.73/44.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.73/44.94         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 44.73/44.94           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 44.73/44.94          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 44.73/44.94          | ~ (v1_funct_1 @ X1))),
% 44.73/44.94      inference('demod', [status(thm)], ['14', '15'])).
% 44.73/44.94  thf('17', plain,
% 44.73/44.94      ((~ (v1_funct_1 @ sk_D)
% 44.73/44.94        | (m1_subset_1 @ 
% 44.73/44.94           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 44.73/44.94           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 44.73/44.94      inference('sup-', [status(thm)], ['11', '16'])).
% 44.73/44.94  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 44.73/44.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.73/44.94  thf('19', plain,
% 44.73/44.94      ((m1_subset_1 @ 
% 44.73/44.94        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 44.73/44.94        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 44.73/44.94      inference('demod', [status(thm)], ['17', '18'])).
% 44.73/44.94  thf('20', plain,
% 44.73/44.94      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 44.73/44.94         = (k5_relat_1 @ sk_C @ sk_D))),
% 44.73/44.94      inference('demod', [status(thm)], ['7', '8'])).
% 44.73/44.94  thf('21', plain,
% 44.73/44.94      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 44.73/44.94        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 44.73/44.94      inference('demod', [status(thm)], ['19', '20'])).
% 44.73/44.94  thf(redefinition_r2_relset_1, axiom,
% 44.73/44.94    (![A:$i,B:$i,C:$i,D:$i]:
% 44.73/44.94     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 44.73/44.94         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 44.73/44.94       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 44.73/44.94  thf('22', plain,
% 44.73/44.94      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 44.73/44.94         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 44.73/44.94          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 44.73/44.94          | ((X33) = (X36))
% 44.73/44.94          | ~ (r2_relset_1 @ X34 @ X35 @ X33 @ X36))),
% 44.73/44.94      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 44.73/44.94  thf('23', plain,
% 44.73/44.94      (![X0 : $i]:
% 44.73/44.94         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 44.73/44.94          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 44.73/44.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 44.73/44.94      inference('sup-', [status(thm)], ['21', '22'])).
% 44.73/44.94  thf('24', plain,
% 44.73/44.94      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 44.73/44.94           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 44.73/44.94        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 44.73/44.94      inference('sup-', [status(thm)], ['10', '23'])).
% 44.73/44.94  thf(t29_relset_1, axiom,
% 44.73/44.94    (![A:$i]:
% 44.73/44.94     ( m1_subset_1 @
% 44.73/44.94       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 44.73/44.94  thf('25', plain,
% 44.73/44.94      (![X37 : $i]:
% 44.73/44.94         (m1_subset_1 @ (k6_relat_1 @ X37) @ 
% 44.73/44.94          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))),
% 44.73/44.94      inference('cnf', [status(esa)], [t29_relset_1])).
% 44.73/44.94  thf(redefinition_k6_partfun1, axiom,
% 44.73/44.94    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 44.73/44.94  thf('26', plain, (![X50 : $i]: ((k6_partfun1 @ X50) = (k6_relat_1 @ X50))),
% 44.73/44.94      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 44.73/44.94  thf('27', plain,
% 44.73/44.94      (![X37 : $i]:
% 44.73/44.94         (m1_subset_1 @ (k6_partfun1 @ X37) @ 
% 44.73/44.94          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))),
% 44.73/44.94      inference('demod', [status(thm)], ['25', '26'])).
% 44.73/44.94  thf('28', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 44.73/44.94      inference('demod', [status(thm)], ['24', '27'])).
% 44.73/44.94  thf(dt_k2_funct_1, axiom,
% 44.73/44.94    (![A:$i]:
% 44.73/44.94     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 44.73/44.94       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 44.73/44.94         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 44.73/44.94  thf('29', plain,
% 44.73/44.94      (![X24 : $i]:
% 44.73/44.94         ((v1_relat_1 @ (k2_funct_1 @ X24))
% 44.73/44.94          | ~ (v1_funct_1 @ X24)
% 44.73/44.94          | ~ (v1_relat_1 @ X24))),
% 44.73/44.94      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 44.73/44.94  thf(t61_funct_1, axiom,
% 44.73/44.94    (![A:$i]:
% 44.73/44.94     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 44.73/44.94       ( ( v2_funct_1 @ A ) =>
% 44.73/44.94         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 44.73/44.94             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 44.73/44.94           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 44.73/44.94             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 44.73/44.94  thf('30', plain,
% 44.73/44.94      (![X26 : $i]:
% 44.73/44.94         (~ (v2_funct_1 @ X26)
% 44.73/44.94          | ((k5_relat_1 @ (k2_funct_1 @ X26) @ X26)
% 44.73/44.94              = (k6_relat_1 @ (k2_relat_1 @ X26)))
% 44.73/44.94          | ~ (v1_funct_1 @ X26)
% 44.73/44.94          | ~ (v1_relat_1 @ X26))),
% 44.73/44.94      inference('cnf', [status(esa)], [t61_funct_1])).
% 44.73/44.94  thf('31', plain, (![X50 : $i]: ((k6_partfun1 @ X50) = (k6_relat_1 @ X50))),
% 44.73/44.94      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 44.73/44.94  thf('32', plain,
% 44.73/44.94      (![X26 : $i]:
% 44.73/44.94         (~ (v2_funct_1 @ X26)
% 44.73/44.94          | ((k5_relat_1 @ (k2_funct_1 @ X26) @ X26)
% 44.73/44.94              = (k6_partfun1 @ (k2_relat_1 @ X26)))
% 44.73/44.94          | ~ (v1_funct_1 @ X26)
% 44.73/44.94          | ~ (v1_relat_1 @ X26))),
% 44.73/44.94      inference('demod', [status(thm)], ['30', '31'])).
% 44.73/44.94  thf('33', plain,
% 44.73/44.94      (![X26 : $i]:
% 44.73/44.94         (~ (v2_funct_1 @ X26)
% 44.73/44.94          | ((k5_relat_1 @ (k2_funct_1 @ X26) @ X26)
% 44.73/44.94              = (k6_partfun1 @ (k2_relat_1 @ X26)))
% 44.73/44.94          | ~ (v1_funct_1 @ X26)
% 44.73/44.94          | ~ (v1_relat_1 @ X26))),
% 44.73/44.94      inference('demod', [status(thm)], ['30', '31'])).
% 44.73/44.94  thf('34', plain,
% 44.73/44.94      (![X24 : $i]:
% 44.73/44.94         ((v1_relat_1 @ (k2_funct_1 @ X24))
% 44.73/44.94          | ~ (v1_funct_1 @ X24)
% 44.73/44.94          | ~ (v1_relat_1 @ X24))),
% 44.73/44.94      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 44.73/44.94  thf('35', plain,
% 44.73/44.94      (![X24 : $i]:
% 44.73/44.94         ((v1_relat_1 @ (k2_funct_1 @ X24))
% 44.73/44.94          | ~ (v1_funct_1 @ X24)
% 44.73/44.94          | ~ (v1_relat_1 @ X24))),
% 44.73/44.94      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 44.73/44.94  thf('36', plain,
% 44.73/44.94      (![X26 : $i]:
% 44.73/44.94         (~ (v2_funct_1 @ X26)
% 44.73/44.94          | ((k5_relat_1 @ (k2_funct_1 @ X26) @ X26)
% 44.73/44.94              = (k6_partfun1 @ (k2_relat_1 @ X26)))
% 44.73/44.94          | ~ (v1_funct_1 @ X26)
% 44.73/44.94          | ~ (v1_relat_1 @ X26))),
% 44.73/44.94      inference('demod', [status(thm)], ['30', '31'])).
% 44.73/44.94  thf(t45_relat_1, axiom,
% 44.73/44.94    (![A:$i]:
% 44.73/44.94     ( ( v1_relat_1 @ A ) =>
% 44.73/44.94       ( ![B:$i]:
% 44.73/44.94         ( ( v1_relat_1 @ B ) =>
% 44.73/44.94           ( r1_tarski @
% 44.73/44.94             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 44.73/44.94  thf('37', plain,
% 44.73/44.94      (![X11 : $i, X12 : $i]:
% 44.73/44.94         (~ (v1_relat_1 @ X11)
% 44.73/44.94          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X12 @ X11)) @ 
% 44.73/44.94             (k2_relat_1 @ X11))
% 44.73/44.94          | ~ (v1_relat_1 @ X12))),
% 44.73/44.94      inference('cnf', [status(esa)], [t45_relat_1])).
% 44.73/44.94  thf(d10_xboole_0, axiom,
% 44.73/44.94    (![A:$i,B:$i]:
% 44.73/44.94     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 44.73/44.94  thf('38', plain,
% 44.73/44.94      (![X0 : $i, X2 : $i]:
% 44.73/44.94         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 44.73/44.94      inference('cnf', [status(esa)], [d10_xboole_0])).
% 44.73/44.94  thf('39', plain,
% 44.73/44.94      (![X0 : $i, X1 : $i]:
% 44.73/44.94         (~ (v1_relat_1 @ X1)
% 44.73/44.94          | ~ (v1_relat_1 @ X0)
% 44.73/44.94          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 44.73/44.94               (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 44.73/44.94          | ((k2_relat_1 @ X0) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 44.73/44.94      inference('sup-', [status(thm)], ['37', '38'])).
% 44.73/44.94  thf('40', plain,
% 44.73/44.94      (![X0 : $i]:
% 44.73/44.94         (~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 44.73/44.94             (k2_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0))))
% 44.73/44.94          | ~ (v1_relat_1 @ X0)
% 44.73/44.94          | ~ (v1_funct_1 @ X0)
% 44.73/44.94          | ~ (v2_funct_1 @ X0)
% 44.73/44.94          | ((k2_relat_1 @ X0)
% 44.73/44.94              = (k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0)))
% 44.73/44.94          | ~ (v1_relat_1 @ X0)
% 44.73/44.94          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 44.73/44.94      inference('sup-', [status(thm)], ['36', '39'])).
% 44.73/44.94  thf(t71_relat_1, axiom,
% 44.73/44.94    (![A:$i]:
% 44.73/44.94     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 44.73/44.94       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 44.73/44.94  thf('41', plain, (![X19 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X19)) = (X19))),
% 44.73/44.94      inference('cnf', [status(esa)], [t71_relat_1])).
% 44.73/44.94  thf('42', plain, (![X50 : $i]: ((k6_partfun1 @ X50) = (k6_relat_1 @ X50))),
% 44.73/44.94      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 44.73/44.94  thf('43', plain, (![X19 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X19)) = (X19))),
% 44.73/44.94      inference('demod', [status(thm)], ['41', '42'])).
% 44.73/44.94  thf('44', plain,
% 44.73/44.94      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 44.73/44.94      inference('cnf', [status(esa)], [d10_xboole_0])).
% 44.73/44.94  thf('45', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 44.73/44.94      inference('simplify', [status(thm)], ['44'])).
% 44.73/44.94  thf('46', plain,
% 44.73/44.94      (![X0 : $i]:
% 44.73/44.94         (~ (v1_relat_1 @ X0)
% 44.73/44.94          | ~ (v1_funct_1 @ X0)
% 44.73/44.94          | ~ (v2_funct_1 @ X0)
% 44.73/44.94          | ((k2_relat_1 @ X0)
% 44.73/44.94              = (k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0)))
% 44.73/44.94          | ~ (v1_relat_1 @ X0)
% 44.73/44.94          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 44.73/44.94      inference('demod', [status(thm)], ['40', '43', '45'])).
% 44.73/44.94  thf('47', plain,
% 44.73/44.94      (![X0 : $i]:
% 44.73/44.94         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 44.73/44.94          | ((k2_relat_1 @ X0)
% 44.73/44.94              = (k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0)))
% 44.73/44.94          | ~ (v2_funct_1 @ X0)
% 44.73/44.94          | ~ (v1_funct_1 @ X0)
% 44.73/44.94          | ~ (v1_relat_1 @ X0))),
% 44.73/44.94      inference('simplify', [status(thm)], ['46'])).
% 44.73/44.94  thf('48', plain,
% 44.73/44.94      (![X0 : $i]:
% 44.73/44.94         (~ (v1_relat_1 @ X0)
% 44.73/44.94          | ~ (v1_funct_1 @ X0)
% 44.73/44.94          | ~ (v1_relat_1 @ X0)
% 44.73/44.94          | ~ (v1_funct_1 @ X0)
% 44.73/44.94          | ~ (v2_funct_1 @ X0)
% 44.73/44.94          | ((k2_relat_1 @ X0)
% 44.73/44.94              = (k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))))),
% 44.73/44.94      inference('sup-', [status(thm)], ['35', '47'])).
% 44.73/44.94  thf('49', plain,
% 44.73/44.94      (![X0 : $i]:
% 44.73/44.94         (((k2_relat_1 @ X0)
% 44.73/44.94            = (k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0)))
% 44.73/44.94          | ~ (v2_funct_1 @ X0)
% 44.73/44.94          | ~ (v1_funct_1 @ X0)
% 44.73/44.94          | ~ (v1_relat_1 @ X0))),
% 44.73/44.94      inference('simplify', [status(thm)], ['48'])).
% 44.73/44.94  thf('50', plain,
% 44.73/44.94      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 44.73/44.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.73/44.94  thf(redefinition_k2_relset_1, axiom,
% 44.73/44.94    (![A:$i,B:$i,C:$i]:
% 44.73/44.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 44.73/44.94       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 44.73/44.94  thf('51', plain,
% 44.73/44.94      (![X30 : $i, X31 : $i, X32 : $i]:
% 44.73/44.94         (((k2_relset_1 @ X31 @ X32 @ X30) = (k2_relat_1 @ X30))
% 44.73/44.94          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 44.73/44.94      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 44.73/44.94  thf('52', plain,
% 44.73/44.94      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 44.73/44.94      inference('sup-', [status(thm)], ['50', '51'])).
% 44.73/44.94  thf('53', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 44.73/44.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.73/44.94  thf('54', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 44.73/44.94      inference('sup+', [status(thm)], ['52', '53'])).
% 44.73/44.94  thf('55', plain,
% 44.73/44.94      (![X11 : $i, X12 : $i]:
% 44.73/44.94         (~ (v1_relat_1 @ X11)
% 44.73/44.94          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X12 @ X11)) @ 
% 44.73/44.94             (k2_relat_1 @ X11))
% 44.73/44.94          | ~ (v1_relat_1 @ X12))),
% 44.73/44.94      inference('cnf', [status(esa)], [t45_relat_1])).
% 44.73/44.94  thf('56', plain,
% 44.73/44.94      (![X0 : $i]:
% 44.73/44.94         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ sk_C)) @ sk_B)
% 44.73/44.94          | ~ (v1_relat_1 @ X0)
% 44.73/44.94          | ~ (v1_relat_1 @ sk_C))),
% 44.73/44.94      inference('sup+', [status(thm)], ['54', '55'])).
% 44.73/44.94  thf('57', plain,
% 44.73/44.94      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 44.73/44.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.73/44.94  thf(cc2_relat_1, axiom,
% 44.73/44.94    (![A:$i]:
% 44.73/44.94     ( ( v1_relat_1 @ A ) =>
% 44.73/44.94       ( ![B:$i]:
% 44.73/44.94         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 44.73/44.94  thf('58', plain,
% 44.73/44.94      (![X3 : $i, X4 : $i]:
% 44.73/44.94         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 44.73/44.94          | (v1_relat_1 @ X3)
% 44.73/44.94          | ~ (v1_relat_1 @ X4))),
% 44.73/44.94      inference('cnf', [status(esa)], [cc2_relat_1])).
% 44.73/44.94  thf('59', plain,
% 44.73/44.94      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 44.73/44.94      inference('sup-', [status(thm)], ['57', '58'])).
% 44.73/44.94  thf(fc6_relat_1, axiom,
% 44.73/44.94    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 44.73/44.94  thf('60', plain,
% 44.73/44.94      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 44.73/44.94      inference('cnf', [status(esa)], [fc6_relat_1])).
% 44.73/44.94  thf('61', plain, ((v1_relat_1 @ sk_C)),
% 44.73/44.94      inference('demod', [status(thm)], ['59', '60'])).
% 44.73/44.94  thf('62', plain,
% 44.73/44.94      (![X0 : $i]:
% 44.73/44.94         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ sk_C)) @ sk_B)
% 44.73/44.94          | ~ (v1_relat_1 @ X0))),
% 44.73/44.94      inference('demod', [status(thm)], ['56', '61'])).
% 44.73/44.94  thf('63', plain,
% 44.73/44.94      (![X0 : $i, X2 : $i]:
% 44.73/44.94         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 44.73/44.94      inference('cnf', [status(esa)], [d10_xboole_0])).
% 44.73/44.94  thf('64', plain,
% 44.73/44.94      (![X0 : $i]:
% 44.73/44.94         (~ (v1_relat_1 @ X0)
% 44.73/44.94          | ~ (r1_tarski @ sk_B @ (k2_relat_1 @ (k5_relat_1 @ X0 @ sk_C)))
% 44.73/44.94          | ((sk_B) = (k2_relat_1 @ (k5_relat_1 @ X0 @ sk_C))))),
% 44.73/44.94      inference('sup-', [status(thm)], ['62', '63'])).
% 44.73/44.94  thf('65', plain,
% 44.73/44.94      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C))
% 44.73/44.94        | ~ (v1_relat_1 @ sk_C)
% 44.73/44.94        | ~ (v1_funct_1 @ sk_C)
% 44.73/44.94        | ~ (v2_funct_1 @ sk_C)
% 44.73/44.94        | ((sk_B) = (k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)))
% 44.73/44.94        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 44.73/44.94      inference('sup-', [status(thm)], ['49', '64'])).
% 44.73/44.94  thf('66', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 44.73/44.94      inference('sup+', [status(thm)], ['52', '53'])).
% 44.73/44.94  thf('67', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 44.73/44.94      inference('simplify', [status(thm)], ['44'])).
% 44.73/44.94  thf('68', plain, ((v1_relat_1 @ sk_C)),
% 44.73/44.94      inference('demod', [status(thm)], ['59', '60'])).
% 44.73/44.94  thf('69', plain, ((v1_funct_1 @ sk_C)),
% 44.73/44.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.73/44.94  thf('70', plain, ((v2_funct_1 @ sk_C)),
% 44.73/44.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.73/44.95  thf('71', plain,
% 44.73/44.95      ((((sk_B) = (k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)))
% 44.73/44.95        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 44.73/44.95      inference('demod', [status(thm)], ['65', '66', '67', '68', '69', '70'])).
% 44.73/44.95  thf('72', plain,
% 44.73/44.95      ((~ (v1_relat_1 @ sk_C)
% 44.73/44.95        | ~ (v1_funct_1 @ sk_C)
% 44.73/44.95        | ((sk_B) = (k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))))),
% 44.73/44.95      inference('sup-', [status(thm)], ['34', '71'])).
% 44.73/44.95  thf('73', plain, ((v1_relat_1 @ sk_C)),
% 44.73/44.95      inference('demod', [status(thm)], ['59', '60'])).
% 44.73/44.95  thf('74', plain, ((v1_funct_1 @ sk_C)),
% 44.73/44.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.73/44.95  thf('75', plain,
% 44.73/44.95      (((sk_B) = (k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)))),
% 44.73/44.95      inference('demod', [status(thm)], ['72', '73', '74'])).
% 44.73/44.95  thf(t80_relat_1, axiom,
% 44.73/44.95    (![A:$i]:
% 44.73/44.95     ( ( v1_relat_1 @ A ) =>
% 44.73/44.95       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 44.73/44.95  thf('76', plain,
% 44.73/44.95      (![X23 : $i]:
% 44.73/44.95         (((k5_relat_1 @ X23 @ (k6_relat_1 @ (k2_relat_1 @ X23))) = (X23))
% 44.73/44.95          | ~ (v1_relat_1 @ X23))),
% 44.73/44.95      inference('cnf', [status(esa)], [t80_relat_1])).
% 44.73/44.95  thf('77', plain, (![X50 : $i]: ((k6_partfun1 @ X50) = (k6_relat_1 @ X50))),
% 44.73/44.95      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 44.73/44.95  thf('78', plain,
% 44.73/44.95      (![X23 : $i]:
% 44.73/44.95         (((k5_relat_1 @ X23 @ (k6_partfun1 @ (k2_relat_1 @ X23))) = (X23))
% 44.73/44.95          | ~ (v1_relat_1 @ X23))),
% 44.73/44.95      inference('demod', [status(thm)], ['76', '77'])).
% 44.73/44.95  thf('79', plain,
% 44.73/44.95      ((((k5_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) @ 
% 44.73/44.95          (k6_partfun1 @ sk_B)) = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))
% 44.73/44.95        | ~ (v1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)))),
% 44.73/44.95      inference('sup+', [status(thm)], ['75', '78'])).
% 44.73/44.95  thf('80', plain,
% 44.73/44.95      ((~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 44.73/44.95        | ~ (v1_relat_1 @ sk_C)
% 44.73/44.95        | ~ (v1_funct_1 @ sk_C)
% 44.73/44.95        | ~ (v2_funct_1 @ sk_C)
% 44.73/44.95        | ((k5_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) @ 
% 44.73/44.95            (k6_partfun1 @ sk_B)) = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)))),
% 44.73/44.95      inference('sup-', [status(thm)], ['33', '79'])).
% 44.73/44.95  thf('81', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 44.73/44.95      inference('sup+', [status(thm)], ['52', '53'])).
% 44.73/44.95  thf('82', plain,
% 44.73/44.95      (![X37 : $i]:
% 44.73/44.95         (m1_subset_1 @ (k6_partfun1 @ X37) @ 
% 44.73/44.95          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))),
% 44.73/44.95      inference('demod', [status(thm)], ['25', '26'])).
% 44.73/44.95  thf('83', plain,
% 44.73/44.95      (![X3 : $i, X4 : $i]:
% 44.73/44.95         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 44.73/44.95          | (v1_relat_1 @ X3)
% 44.73/44.95          | ~ (v1_relat_1 @ X4))),
% 44.73/44.95      inference('cnf', [status(esa)], [cc2_relat_1])).
% 44.73/44.95  thf('84', plain,
% 44.73/44.95      (![X0 : $i]:
% 44.73/44.95         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X0))
% 44.73/44.95          | (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 44.73/44.95      inference('sup-', [status(thm)], ['82', '83'])).
% 44.73/44.95  thf('85', plain,
% 44.73/44.95      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 44.73/44.95      inference('cnf', [status(esa)], [fc6_relat_1])).
% 44.73/44.95  thf('86', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 44.73/44.95      inference('demod', [status(thm)], ['84', '85'])).
% 44.73/44.95  thf('87', plain, ((v1_relat_1 @ sk_C)),
% 44.73/44.95      inference('demod', [status(thm)], ['59', '60'])).
% 44.73/44.95  thf('88', plain, ((v1_funct_1 @ sk_C)),
% 44.73/44.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.73/44.95  thf('89', plain, ((v2_funct_1 @ sk_C)),
% 44.73/44.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.73/44.95  thf('90', plain,
% 44.73/44.95      (((k5_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) @ 
% 44.73/44.95         (k6_partfun1 @ sk_B)) = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))),
% 44.73/44.95      inference('demod', [status(thm)], ['80', '81', '86', '87', '88', '89'])).
% 44.73/44.95  thf('91', plain,
% 44.73/44.95      ((((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)) @ 
% 44.73/44.95          (k6_partfun1 @ sk_B)) = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))
% 44.73/44.95        | ~ (v1_relat_1 @ sk_C)
% 44.73/44.95        | ~ (v1_funct_1 @ sk_C)
% 44.73/44.95        | ~ (v2_funct_1 @ sk_C))),
% 44.73/44.95      inference('sup+', [status(thm)], ['32', '90'])).
% 44.73/44.95  thf('92', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 44.73/44.95      inference('sup+', [status(thm)], ['52', '53'])).
% 44.73/44.95  thf('93', plain, (![X19 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X19)) = (X19))),
% 44.73/44.95      inference('demod', [status(thm)], ['41', '42'])).
% 44.73/44.95  thf('94', plain,
% 44.73/44.95      (![X23 : $i]:
% 44.73/44.95         (((k5_relat_1 @ X23 @ (k6_partfun1 @ (k2_relat_1 @ X23))) = (X23))
% 44.73/44.95          | ~ (v1_relat_1 @ X23))),
% 44.73/44.95      inference('demod', [status(thm)], ['76', '77'])).
% 44.73/44.95  thf('95', plain,
% 44.73/44.95      (![X0 : $i]:
% 44.73/44.95         (((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 44.73/44.95            = (k6_partfun1 @ X0))
% 44.73/44.95          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 44.73/44.95      inference('sup+', [status(thm)], ['93', '94'])).
% 44.73/44.95  thf('96', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 44.73/44.95      inference('demod', [status(thm)], ['84', '85'])).
% 44.73/44.95  thf('97', plain,
% 44.73/44.95      (![X0 : $i]:
% 44.73/44.95         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 44.73/44.95           = (k6_partfun1 @ X0))),
% 44.73/44.95      inference('demod', [status(thm)], ['95', '96'])).
% 44.73/44.95  thf('98', plain, ((v1_relat_1 @ sk_C)),
% 44.73/44.95      inference('demod', [status(thm)], ['59', '60'])).
% 44.73/44.95  thf('99', plain, ((v1_funct_1 @ sk_C)),
% 44.73/44.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.73/44.95  thf('100', plain, ((v2_funct_1 @ sk_C)),
% 44.73/44.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.73/44.95  thf('101', plain,
% 44.73/44.95      (((k6_partfun1 @ sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))),
% 44.73/44.95      inference('demod', [status(thm)], ['91', '92', '97', '98', '99', '100'])).
% 44.73/44.95  thf(t55_relat_1, axiom,
% 44.73/44.95    (![A:$i]:
% 44.73/44.95     ( ( v1_relat_1 @ A ) =>
% 44.73/44.95       ( ![B:$i]:
% 44.73/44.95         ( ( v1_relat_1 @ B ) =>
% 44.73/44.95           ( ![C:$i]:
% 44.73/44.95             ( ( v1_relat_1 @ C ) =>
% 44.73/44.95               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 44.73/44.95                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 44.73/44.95  thf('102', plain,
% 44.73/44.95      (![X15 : $i, X16 : $i, X17 : $i]:
% 44.73/44.95         (~ (v1_relat_1 @ X15)
% 44.73/44.95          | ((k5_relat_1 @ (k5_relat_1 @ X16 @ X15) @ X17)
% 44.73/44.95              = (k5_relat_1 @ X16 @ (k5_relat_1 @ X15 @ X17)))
% 44.73/44.95          | ~ (v1_relat_1 @ X17)
% 44.73/44.95          | ~ (v1_relat_1 @ X16))),
% 44.73/44.95      inference('cnf', [status(esa)], [t55_relat_1])).
% 44.73/44.95  thf('103', plain,
% 44.73/44.95      (![X0 : $i]:
% 44.73/44.95         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 44.73/44.95            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 44.73/44.95          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 44.73/44.95          | ~ (v1_relat_1 @ X0)
% 44.73/44.95          | ~ (v1_relat_1 @ sk_C))),
% 44.73/44.95      inference('sup+', [status(thm)], ['101', '102'])).
% 44.73/44.95  thf('104', plain, ((v1_relat_1 @ sk_C)),
% 44.73/44.95      inference('demod', [status(thm)], ['59', '60'])).
% 44.73/44.95  thf('105', plain,
% 44.73/44.95      (![X0 : $i]:
% 44.73/44.95         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 44.73/44.95            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 44.73/44.95          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 44.73/44.95          | ~ (v1_relat_1 @ X0))),
% 44.73/44.95      inference('demod', [status(thm)], ['103', '104'])).
% 44.73/44.95  thf('106', plain,
% 44.73/44.95      (![X0 : $i]:
% 44.73/44.95         (~ (v1_relat_1 @ sk_C)
% 44.73/44.95          | ~ (v1_funct_1 @ sk_C)
% 44.73/44.95          | ~ (v1_relat_1 @ X0)
% 44.73/44.95          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 44.73/44.95              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 44.73/44.95      inference('sup-', [status(thm)], ['29', '105'])).
% 44.73/44.95  thf('107', plain, ((v1_relat_1 @ sk_C)),
% 44.73/44.95      inference('demod', [status(thm)], ['59', '60'])).
% 44.73/44.95  thf('108', plain, ((v1_funct_1 @ sk_C)),
% 44.73/44.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.73/44.95  thf('109', plain,
% 44.73/44.95      (![X0 : $i]:
% 44.73/44.95         (~ (v1_relat_1 @ X0)
% 44.73/44.95          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 44.73/44.95              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 44.73/44.95      inference('demod', [status(thm)], ['106', '107', '108'])).
% 44.73/44.95  thf('110', plain,
% 44.73/44.95      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 44.73/44.95          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 44.73/44.95        | ~ (v1_relat_1 @ sk_D))),
% 44.73/44.95      inference('sup+', [status(thm)], ['28', '109'])).
% 44.73/44.95  thf('111', plain,
% 44.73/44.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 44.73/44.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.73/44.95  thf(cc2_relset_1, axiom,
% 44.73/44.95    (![A:$i,B:$i,C:$i]:
% 44.73/44.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 44.73/44.95       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 44.73/44.95  thf('112', plain,
% 44.73/44.95      (![X27 : $i, X28 : $i, X29 : $i]:
% 44.73/44.95         ((v4_relat_1 @ X27 @ X28)
% 44.73/44.95          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 44.73/44.95      inference('cnf', [status(esa)], [cc2_relset_1])).
% 44.73/44.95  thf('113', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 44.73/44.95      inference('sup-', [status(thm)], ['111', '112'])).
% 44.73/44.95  thf(d18_relat_1, axiom,
% 44.73/44.95    (![A:$i,B:$i]:
% 44.73/44.95     ( ( v1_relat_1 @ B ) =>
% 44.73/44.95       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 44.73/44.95  thf('114', plain,
% 44.73/44.95      (![X5 : $i, X6 : $i]:
% 44.73/44.95         (~ (v4_relat_1 @ X5 @ X6)
% 44.73/44.95          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 44.73/44.95          | ~ (v1_relat_1 @ X5))),
% 44.73/44.95      inference('cnf', [status(esa)], [d18_relat_1])).
% 44.73/44.95  thf('115', plain,
% 44.73/44.95      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B))),
% 44.73/44.95      inference('sup-', [status(thm)], ['113', '114'])).
% 44.73/44.95  thf('116', plain,
% 44.73/44.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 44.73/44.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.73/44.95  thf('117', plain,
% 44.73/44.95      (![X3 : $i, X4 : $i]:
% 44.73/44.95         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 44.73/44.95          | (v1_relat_1 @ X3)
% 44.73/44.95          | ~ (v1_relat_1 @ X4))),
% 44.73/44.95      inference('cnf', [status(esa)], [cc2_relat_1])).
% 44.73/44.95  thf('118', plain,
% 44.73/44.95      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 44.73/44.95      inference('sup-', [status(thm)], ['116', '117'])).
% 44.73/44.95  thf('119', plain,
% 44.73/44.95      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 44.73/44.95      inference('cnf', [status(esa)], [fc6_relat_1])).
% 44.73/44.95  thf('120', plain, ((v1_relat_1 @ sk_D)),
% 44.73/44.95      inference('demod', [status(thm)], ['118', '119'])).
% 44.73/44.95  thf('121', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B)),
% 44.73/44.95      inference('demod', [status(thm)], ['115', '120'])).
% 44.73/44.95  thf(t77_relat_1, axiom,
% 44.73/44.95    (![A:$i,B:$i]:
% 44.73/44.95     ( ( v1_relat_1 @ B ) =>
% 44.73/44.95       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 44.73/44.95         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 44.73/44.95  thf('122', plain,
% 44.73/44.95      (![X21 : $i, X22 : $i]:
% 44.73/44.95         (~ (r1_tarski @ (k1_relat_1 @ X21) @ X22)
% 44.73/44.95          | ((k5_relat_1 @ (k6_relat_1 @ X22) @ X21) = (X21))
% 44.73/44.95          | ~ (v1_relat_1 @ X21))),
% 44.73/44.95      inference('cnf', [status(esa)], [t77_relat_1])).
% 44.73/44.95  thf('123', plain, (![X50 : $i]: ((k6_partfun1 @ X50) = (k6_relat_1 @ X50))),
% 44.73/44.95      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 44.73/44.95  thf('124', plain,
% 44.73/44.95      (![X21 : $i, X22 : $i]:
% 44.73/44.95         (~ (r1_tarski @ (k1_relat_1 @ X21) @ X22)
% 44.73/44.95          | ((k5_relat_1 @ (k6_partfun1 @ X22) @ X21) = (X21))
% 44.73/44.95          | ~ (v1_relat_1 @ X21))),
% 44.73/44.95      inference('demod', [status(thm)], ['122', '123'])).
% 44.73/44.95  thf('125', plain,
% 44.73/44.95      ((~ (v1_relat_1 @ sk_D)
% 44.73/44.95        | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D)))),
% 44.73/44.95      inference('sup-', [status(thm)], ['121', '124'])).
% 44.73/44.95  thf('126', plain, ((v1_relat_1 @ sk_D)),
% 44.73/44.95      inference('demod', [status(thm)], ['118', '119'])).
% 44.73/44.95  thf('127', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))),
% 44.73/44.95      inference('demod', [status(thm)], ['125', '126'])).
% 44.73/44.95  thf('128', plain,
% 44.73/44.95      (![X24 : $i]:
% 44.73/44.95         ((v1_relat_1 @ (k2_funct_1 @ X24))
% 44.73/44.95          | ~ (v1_funct_1 @ X24)
% 44.73/44.95          | ~ (v1_relat_1 @ X24))),
% 44.73/44.95      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 44.73/44.95  thf(t55_funct_1, axiom,
% 44.73/44.95    (![A:$i]:
% 44.73/44.95     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 44.73/44.95       ( ( v2_funct_1 @ A ) =>
% 44.73/44.95         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 44.73/44.95           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 44.73/44.95  thf('129', plain,
% 44.73/44.95      (![X25 : $i]:
% 44.73/44.95         (~ (v2_funct_1 @ X25)
% 44.73/44.95          | ((k1_relat_1 @ X25) = (k2_relat_1 @ (k2_funct_1 @ X25)))
% 44.73/44.95          | ~ (v1_funct_1 @ X25)
% 44.73/44.95          | ~ (v1_relat_1 @ X25))),
% 44.73/44.95      inference('cnf', [status(esa)], [t55_funct_1])).
% 44.73/44.95  thf('130', plain,
% 44.73/44.95      (![X24 : $i]:
% 44.73/44.95         ((v1_relat_1 @ (k2_funct_1 @ X24))
% 44.73/44.95          | ~ (v1_funct_1 @ X24)
% 44.73/44.95          | ~ (v1_relat_1 @ X24))),
% 44.73/44.95      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 44.73/44.95  thf('131', plain,
% 44.73/44.95      (![X24 : $i]:
% 44.73/44.95         ((v1_relat_1 @ (k2_funct_1 @ X24))
% 44.73/44.95          | ~ (v1_funct_1 @ X24)
% 44.73/44.95          | ~ (v1_relat_1 @ X24))),
% 44.73/44.95      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 44.73/44.95  thf('132', plain,
% 44.73/44.95      (![X26 : $i]:
% 44.73/44.95         (~ (v2_funct_1 @ X26)
% 44.73/44.95          | ((k5_relat_1 @ X26 @ (k2_funct_1 @ X26))
% 44.73/44.95              = (k6_relat_1 @ (k1_relat_1 @ X26)))
% 44.73/44.95          | ~ (v1_funct_1 @ X26)
% 44.73/44.95          | ~ (v1_relat_1 @ X26))),
% 44.73/44.95      inference('cnf', [status(esa)], [t61_funct_1])).
% 44.73/44.95  thf('133', plain, (![X50 : $i]: ((k6_partfun1 @ X50) = (k6_relat_1 @ X50))),
% 44.73/44.95      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 44.73/44.95  thf('134', plain,
% 44.73/44.95      (![X26 : $i]:
% 44.73/44.95         (~ (v2_funct_1 @ X26)
% 44.73/44.95          | ((k5_relat_1 @ X26 @ (k2_funct_1 @ X26))
% 44.73/44.95              = (k6_partfun1 @ (k1_relat_1 @ X26)))
% 44.73/44.95          | ~ (v1_funct_1 @ X26)
% 44.73/44.95          | ~ (v1_relat_1 @ X26))),
% 44.73/44.95      inference('demod', [status(thm)], ['132', '133'])).
% 44.73/44.95  thf('135', plain,
% 44.73/44.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 44.73/44.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.73/44.95  thf('136', plain,
% 44.73/44.95      (![X27 : $i, X28 : $i, X29 : $i]:
% 44.73/44.95         ((v4_relat_1 @ X27 @ X28)
% 44.73/44.95          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 44.73/44.95      inference('cnf', [status(esa)], [cc2_relset_1])).
% 44.73/44.95  thf('137', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 44.73/44.95      inference('sup-', [status(thm)], ['135', '136'])).
% 44.73/44.95  thf('138', plain,
% 44.73/44.95      (![X5 : $i, X6 : $i]:
% 44.73/44.95         (~ (v4_relat_1 @ X5 @ X6)
% 44.73/44.95          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 44.73/44.95          | ~ (v1_relat_1 @ X5))),
% 44.73/44.95      inference('cnf', [status(esa)], [d18_relat_1])).
% 44.73/44.95  thf('139', plain,
% 44.73/44.95      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 44.73/44.95      inference('sup-', [status(thm)], ['137', '138'])).
% 44.73/44.95  thf('140', plain, ((v1_relat_1 @ sk_C)),
% 44.73/44.95      inference('demod', [status(thm)], ['59', '60'])).
% 44.73/44.95  thf('141', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 44.73/44.95      inference('demod', [status(thm)], ['139', '140'])).
% 44.73/44.95  thf('142', plain,
% 44.73/44.95      (![X21 : $i, X22 : $i]:
% 44.73/44.95         (~ (r1_tarski @ (k1_relat_1 @ X21) @ X22)
% 44.73/44.95          | ((k5_relat_1 @ (k6_partfun1 @ X22) @ X21) = (X21))
% 44.73/44.95          | ~ (v1_relat_1 @ X21))),
% 44.73/44.95      inference('demod', [status(thm)], ['122', '123'])).
% 44.73/44.95  thf('143', plain,
% 44.73/44.95      ((~ (v1_relat_1 @ sk_C)
% 44.73/44.95        | ((k5_relat_1 @ (k6_partfun1 @ sk_A) @ sk_C) = (sk_C)))),
% 44.73/44.95      inference('sup-', [status(thm)], ['141', '142'])).
% 44.73/44.95  thf('144', plain, ((v1_relat_1 @ sk_C)),
% 44.73/44.95      inference('demod', [status(thm)], ['59', '60'])).
% 44.73/44.95  thf('145', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_A) @ sk_C) = (sk_C))),
% 44.73/44.95      inference('demod', [status(thm)], ['143', '144'])).
% 44.73/44.95  thf('146', plain,
% 44.73/44.95      (![X15 : $i, X16 : $i, X17 : $i]:
% 44.73/44.95         (~ (v1_relat_1 @ X15)
% 44.73/44.95          | ((k5_relat_1 @ (k5_relat_1 @ X16 @ X15) @ X17)
% 44.73/44.95              = (k5_relat_1 @ X16 @ (k5_relat_1 @ X15 @ X17)))
% 44.73/44.95          | ~ (v1_relat_1 @ X17)
% 44.73/44.95          | ~ (v1_relat_1 @ X16))),
% 44.73/44.95      inference('cnf', [status(esa)], [t55_relat_1])).
% 44.73/44.95  thf('147', plain,
% 44.73/44.95      (![X0 : $i]:
% 44.73/44.95         (((k5_relat_1 @ sk_C @ X0)
% 44.73/44.95            = (k5_relat_1 @ (k6_partfun1 @ sk_A) @ (k5_relat_1 @ sk_C @ X0)))
% 44.73/44.95          | ~ (v1_relat_1 @ (k6_partfun1 @ sk_A))
% 44.73/44.95          | ~ (v1_relat_1 @ X0)
% 44.73/44.95          | ~ (v1_relat_1 @ sk_C))),
% 44.73/44.95      inference('sup+', [status(thm)], ['145', '146'])).
% 44.73/44.95  thf('148', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 44.73/44.95      inference('demod', [status(thm)], ['84', '85'])).
% 44.73/44.95  thf('149', plain, ((v1_relat_1 @ sk_C)),
% 44.73/44.95      inference('demod', [status(thm)], ['59', '60'])).
% 44.73/44.95  thf('150', plain,
% 44.73/44.95      (![X0 : $i]:
% 44.73/44.95         (((k5_relat_1 @ sk_C @ X0)
% 44.73/44.95            = (k5_relat_1 @ (k6_partfun1 @ sk_A) @ (k5_relat_1 @ sk_C @ X0)))
% 44.73/44.95          | ~ (v1_relat_1 @ X0))),
% 44.73/44.95      inference('demod', [status(thm)], ['147', '148', '149'])).
% 44.73/44.95  thf('151', plain,
% 44.73/44.95      ((((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 44.73/44.95          = (k5_relat_1 @ (k6_partfun1 @ sk_A) @ 
% 44.73/44.95             (k6_partfun1 @ (k1_relat_1 @ sk_C))))
% 44.73/44.95        | ~ (v1_relat_1 @ sk_C)
% 44.73/44.95        | ~ (v1_funct_1 @ sk_C)
% 44.73/44.95        | ~ (v2_funct_1 @ sk_C)
% 44.73/44.95        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 44.73/44.95      inference('sup+', [status(thm)], ['134', '150'])).
% 44.73/44.95  thf('152', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 44.73/44.95      inference('demod', [status(thm)], ['139', '140'])).
% 44.73/44.95  thf('153', plain, (![X18 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X18)) = (X18))),
% 44.73/44.95      inference('cnf', [status(esa)], [t71_relat_1])).
% 44.73/44.95  thf('154', plain, (![X50 : $i]: ((k6_partfun1 @ X50) = (k6_relat_1 @ X50))),
% 44.73/44.95      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 44.73/44.95  thf('155', plain,
% 44.73/44.95      (![X18 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X18)) = (X18))),
% 44.73/44.95      inference('demod', [status(thm)], ['153', '154'])).
% 44.73/44.95  thf('156', plain,
% 44.73/44.95      (![X21 : $i, X22 : $i]:
% 44.73/44.95         (~ (r1_tarski @ (k1_relat_1 @ X21) @ X22)
% 44.73/44.95          | ((k5_relat_1 @ (k6_partfun1 @ X22) @ X21) = (X21))
% 44.73/44.95          | ~ (v1_relat_1 @ X21))),
% 44.73/44.95      inference('demod', [status(thm)], ['122', '123'])).
% 44.73/44.95  thf('157', plain,
% 44.73/44.95      (![X0 : $i, X1 : $i]:
% 44.73/44.95         (~ (r1_tarski @ X0 @ X1)
% 44.73/44.95          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 44.73/44.95          | ((k5_relat_1 @ (k6_partfun1 @ X1) @ (k6_partfun1 @ X0))
% 44.73/44.95              = (k6_partfun1 @ X0)))),
% 44.73/44.95      inference('sup-', [status(thm)], ['155', '156'])).
% 44.73/44.95  thf('158', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 44.73/44.95      inference('demod', [status(thm)], ['84', '85'])).
% 44.73/44.95  thf('159', plain,
% 44.73/44.95      (![X0 : $i, X1 : $i]:
% 44.73/44.95         (~ (r1_tarski @ X0 @ X1)
% 44.73/44.95          | ((k5_relat_1 @ (k6_partfun1 @ X1) @ (k6_partfun1 @ X0))
% 44.73/44.95              = (k6_partfun1 @ X0)))),
% 44.73/44.95      inference('demod', [status(thm)], ['157', '158'])).
% 44.73/44.95  thf('160', plain,
% 44.73/44.95      (((k5_relat_1 @ (k6_partfun1 @ sk_A) @ 
% 44.73/44.95         (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 44.73/44.95         = (k6_partfun1 @ (k1_relat_1 @ sk_C)))),
% 44.73/44.95      inference('sup-', [status(thm)], ['152', '159'])).
% 44.73/44.95  thf('161', plain, ((v1_relat_1 @ sk_C)),
% 44.73/44.95      inference('demod', [status(thm)], ['59', '60'])).
% 44.73/44.95  thf('162', plain, ((v1_funct_1 @ sk_C)),
% 44.73/44.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.73/44.95  thf('163', plain, ((v2_funct_1 @ sk_C)),
% 44.73/44.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.73/44.95  thf('164', plain,
% 44.73/44.95      ((((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 44.73/44.95          = (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 44.73/44.95        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 44.73/44.95      inference('demod', [status(thm)], ['151', '160', '161', '162', '163'])).
% 44.73/44.95  thf('165', plain,
% 44.73/44.95      ((~ (v1_relat_1 @ sk_C)
% 44.73/44.95        | ~ (v1_funct_1 @ sk_C)
% 44.73/44.95        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 44.73/44.95            = (k6_partfun1 @ (k1_relat_1 @ sk_C))))),
% 44.73/44.95      inference('sup-', [status(thm)], ['131', '164'])).
% 44.73/44.95  thf('166', plain, ((v1_relat_1 @ sk_C)),
% 44.73/44.95      inference('demod', [status(thm)], ['59', '60'])).
% 44.73/44.95  thf('167', plain, ((v1_funct_1 @ sk_C)),
% 44.73/44.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.73/44.95  thf('168', plain,
% 44.73/44.95      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 44.73/44.95         = (k6_partfun1 @ (k1_relat_1 @ sk_C)))),
% 44.73/44.95      inference('demod', [status(thm)], ['165', '166', '167'])).
% 44.73/44.95  thf('169', plain,
% 44.73/44.95      (![X11 : $i, X12 : $i]:
% 44.73/44.95         (~ (v1_relat_1 @ X11)
% 44.73/44.95          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X12 @ X11)) @ 
% 44.73/44.95             (k2_relat_1 @ X11))
% 44.73/44.95          | ~ (v1_relat_1 @ X12))),
% 44.73/44.95      inference('cnf', [status(esa)], [t45_relat_1])).
% 44.73/44.95  thf('170', plain,
% 44.73/44.95      (((r1_tarski @ (k2_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C))) @ 
% 44.73/44.95         (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 44.73/44.95        | ~ (v1_relat_1 @ sk_C)
% 44.73/44.95        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 44.73/44.95      inference('sup+', [status(thm)], ['168', '169'])).
% 44.73/44.95  thf('171', plain,
% 44.73/44.95      (![X19 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X19)) = (X19))),
% 44.73/44.95      inference('demod', [status(thm)], ['41', '42'])).
% 44.73/44.95  thf('172', plain, ((v1_relat_1 @ sk_C)),
% 44.73/44.95      inference('demod', [status(thm)], ['59', '60'])).
% 44.73/44.95  thf('173', plain,
% 44.73/44.95      (((r1_tarski @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 44.73/44.95        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 44.73/44.95      inference('demod', [status(thm)], ['170', '171', '172'])).
% 44.73/44.95  thf('174', plain,
% 44.73/44.95      ((~ (v1_relat_1 @ sk_C)
% 44.73/44.95        | ~ (v1_funct_1 @ sk_C)
% 44.73/44.95        | (r1_tarski @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 44.73/44.95      inference('sup-', [status(thm)], ['130', '173'])).
% 44.73/44.95  thf('175', plain, ((v1_relat_1 @ sk_C)),
% 44.73/44.95      inference('demod', [status(thm)], ['59', '60'])).
% 44.73/44.95  thf('176', plain, ((v1_funct_1 @ sk_C)),
% 44.73/44.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.73/44.95  thf('177', plain,
% 44.73/44.95      ((r1_tarski @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 44.73/44.95      inference('demod', [status(thm)], ['174', '175', '176'])).
% 44.73/44.95  thf('178', plain,
% 44.73/44.95      (![X0 : $i, X2 : $i]:
% 44.73/44.95         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 44.73/44.95      inference('cnf', [status(esa)], [d10_xboole_0])).
% 44.73/44.95  thf('179', plain,
% 44.73/44.95      ((~ (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (k1_relat_1 @ sk_C))
% 44.73/44.95        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C)))),
% 44.73/44.95      inference('sup-', [status(thm)], ['177', '178'])).
% 44.73/44.95  thf('180', plain,
% 44.73/44.95      ((~ (r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))
% 44.73/44.95        | ~ (v1_relat_1 @ sk_C)
% 44.73/44.95        | ~ (v1_funct_1 @ sk_C)
% 44.73/44.95        | ~ (v2_funct_1 @ sk_C)
% 44.73/44.95        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C)))),
% 44.73/44.95      inference('sup-', [status(thm)], ['129', '179'])).
% 44.73/44.95  thf('181', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 44.73/44.95      inference('simplify', [status(thm)], ['44'])).
% 44.73/44.95  thf('182', plain, ((v1_relat_1 @ sk_C)),
% 44.73/44.95      inference('demod', [status(thm)], ['59', '60'])).
% 44.73/44.95  thf('183', plain, ((v1_funct_1 @ sk_C)),
% 44.73/44.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.73/44.95  thf('184', plain, ((v2_funct_1 @ sk_C)),
% 44.73/44.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.73/44.95  thf('185', plain,
% 44.73/44.95      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 44.73/44.95      inference('demod', [status(thm)], ['180', '181', '182', '183', '184'])).
% 44.73/44.95  thf('186', plain,
% 44.73/44.95      (![X23 : $i]:
% 44.73/44.95         (((k5_relat_1 @ X23 @ (k6_partfun1 @ (k2_relat_1 @ X23))) = (X23))
% 44.73/44.95          | ~ (v1_relat_1 @ X23))),
% 44.73/44.95      inference('demod', [status(thm)], ['76', '77'])).
% 44.73/44.95  thf('187', plain,
% 44.73/44.95      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 44.73/44.95          (k6_partfun1 @ (k1_relat_1 @ sk_C))) = (k2_funct_1 @ sk_C))
% 44.73/44.95        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 44.73/44.95      inference('sup+', [status(thm)], ['185', '186'])).
% 44.73/44.95  thf('188', plain,
% 44.73/44.95      ((~ (v1_relat_1 @ sk_C)
% 44.73/44.95        | ~ (v1_funct_1 @ sk_C)
% 44.73/44.95        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 44.73/44.95            (k6_partfun1 @ (k1_relat_1 @ sk_C))) = (k2_funct_1 @ sk_C)))),
% 44.73/44.95      inference('sup-', [status(thm)], ['128', '187'])).
% 44.73/44.95  thf('189', plain, ((v1_relat_1 @ sk_C)),
% 44.73/44.95      inference('demod', [status(thm)], ['59', '60'])).
% 44.73/44.95  thf('190', plain, ((v1_funct_1 @ sk_C)),
% 44.73/44.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.73/44.95  thf('191', plain,
% 44.73/44.95      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 44.73/44.95         = (k2_funct_1 @ sk_C))),
% 44.73/44.95      inference('demod', [status(thm)], ['188', '189', '190'])).
% 44.73/44.95  thf('192', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 44.73/44.95      inference('demod', [status(thm)], ['24', '27'])).
% 44.73/44.95  thf('193', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 44.73/44.95      inference('simplify', [status(thm)], ['44'])).
% 44.73/44.95  thf('194', plain,
% 44.73/44.95      (![X21 : $i, X22 : $i]:
% 44.73/44.95         (~ (r1_tarski @ (k1_relat_1 @ X21) @ X22)
% 44.73/44.95          | ((k5_relat_1 @ (k6_partfun1 @ X22) @ X21) = (X21))
% 44.73/44.95          | ~ (v1_relat_1 @ X21))),
% 44.73/44.95      inference('demod', [status(thm)], ['122', '123'])).
% 44.73/44.95  thf('195', plain,
% 44.73/44.95      (![X0 : $i]:
% 44.73/44.95         (~ (v1_relat_1 @ X0)
% 44.73/44.95          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 44.73/44.95      inference('sup-', [status(thm)], ['193', '194'])).
% 44.73/44.95  thf('196', plain,
% 44.73/44.95      (![X15 : $i, X16 : $i, X17 : $i]:
% 44.73/44.95         (~ (v1_relat_1 @ X15)
% 44.73/44.95          | ((k5_relat_1 @ (k5_relat_1 @ X16 @ X15) @ X17)
% 44.73/44.95              = (k5_relat_1 @ X16 @ (k5_relat_1 @ X15 @ X17)))
% 44.73/44.95          | ~ (v1_relat_1 @ X17)
% 44.73/44.95          | ~ (v1_relat_1 @ X16))),
% 44.73/44.95      inference('cnf', [status(esa)], [t55_relat_1])).
% 44.73/44.95  thf('197', plain,
% 44.73/44.95      (![X0 : $i, X1 : $i]:
% 44.73/44.95         (((k5_relat_1 @ X0 @ X1)
% 44.73/44.95            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 44.73/44.95               (k5_relat_1 @ X0 @ X1)))
% 44.73/44.95          | ~ (v1_relat_1 @ X0)
% 44.73/44.95          | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 44.73/44.95          | ~ (v1_relat_1 @ X1)
% 44.73/44.95          | ~ (v1_relat_1 @ X0))),
% 44.73/44.95      inference('sup+', [status(thm)], ['195', '196'])).
% 44.73/44.95  thf('198', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 44.73/44.95      inference('demod', [status(thm)], ['84', '85'])).
% 44.73/44.95  thf('199', plain,
% 44.73/44.95      (![X0 : $i, X1 : $i]:
% 44.73/44.95         (((k5_relat_1 @ X0 @ X1)
% 44.73/44.95            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 44.73/44.95               (k5_relat_1 @ X0 @ X1)))
% 44.73/44.95          | ~ (v1_relat_1 @ X0)
% 44.73/44.95          | ~ (v1_relat_1 @ X1)
% 44.73/44.95          | ~ (v1_relat_1 @ X0))),
% 44.73/44.95      inference('demod', [status(thm)], ['197', '198'])).
% 44.73/44.95  thf('200', plain,
% 44.73/44.95      (![X0 : $i, X1 : $i]:
% 44.73/44.95         (~ (v1_relat_1 @ X1)
% 44.73/44.95          | ~ (v1_relat_1 @ X0)
% 44.73/44.95          | ((k5_relat_1 @ X0 @ X1)
% 44.73/44.95              = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 44.73/44.95                 (k5_relat_1 @ X0 @ X1))))),
% 44.73/44.95      inference('simplify', [status(thm)], ['199'])).
% 44.73/44.95  thf('201', plain,
% 44.73/44.95      ((((k5_relat_1 @ sk_C @ sk_D)
% 44.73/44.95          = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ 
% 44.73/44.95             (k6_partfun1 @ sk_A)))
% 44.73/44.95        | ~ (v1_relat_1 @ sk_C)
% 44.73/44.95        | ~ (v1_relat_1 @ sk_D))),
% 44.73/44.95      inference('sup+', [status(thm)], ['192', '200'])).
% 44.73/44.95  thf('202', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 44.73/44.95      inference('demod', [status(thm)], ['24', '27'])).
% 44.73/44.95  thf('203', plain,
% 44.73/44.95      (((k5_relat_1 @ (k6_partfun1 @ sk_A) @ 
% 44.73/44.95         (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 44.73/44.95         = (k6_partfun1 @ (k1_relat_1 @ sk_C)))),
% 44.73/44.95      inference('sup-', [status(thm)], ['152', '159'])).
% 44.73/44.95  thf(t72_relat_1, axiom,
% 44.73/44.95    (![A:$i]: ( ( k4_relat_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 44.73/44.95  thf('204', plain,
% 44.73/44.95      (![X20 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X20)) = (k6_relat_1 @ X20))),
% 44.73/44.95      inference('cnf', [status(esa)], [t72_relat_1])).
% 44.73/44.95  thf('205', plain, (![X50 : $i]: ((k6_partfun1 @ X50) = (k6_relat_1 @ X50))),
% 44.73/44.95      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 44.73/44.95  thf('206', plain, (![X50 : $i]: ((k6_partfun1 @ X50) = (k6_relat_1 @ X50))),
% 44.73/44.95      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 44.73/44.95  thf('207', plain,
% 44.73/44.95      (![X20 : $i]: ((k4_relat_1 @ (k6_partfun1 @ X20)) = (k6_partfun1 @ X20))),
% 44.73/44.95      inference('demod', [status(thm)], ['204', '205', '206'])).
% 44.73/44.95  thf('208', plain,
% 44.73/44.95      (![X20 : $i]: ((k4_relat_1 @ (k6_partfun1 @ X20)) = (k6_partfun1 @ X20))),
% 44.73/44.95      inference('demod', [status(thm)], ['204', '205', '206'])).
% 44.73/44.95  thf(t54_relat_1, axiom,
% 44.73/44.95    (![A:$i]:
% 44.73/44.95     ( ( v1_relat_1 @ A ) =>
% 44.73/44.95       ( ![B:$i]:
% 44.73/44.95         ( ( v1_relat_1 @ B ) =>
% 44.73/44.95           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 44.73/44.95             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 44.73/44.95  thf('209', plain,
% 44.73/44.95      (![X13 : $i, X14 : $i]:
% 44.73/44.95         (~ (v1_relat_1 @ X13)
% 44.73/44.95          | ((k4_relat_1 @ (k5_relat_1 @ X14 @ X13))
% 44.73/44.95              = (k5_relat_1 @ (k4_relat_1 @ X13) @ (k4_relat_1 @ X14)))
% 44.73/44.95          | ~ (v1_relat_1 @ X14))),
% 44.73/44.95      inference('cnf', [status(esa)], [t54_relat_1])).
% 44.73/44.95  thf('210', plain,
% 44.73/44.95      (![X0 : $i, X1 : $i]:
% 44.73/44.95         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0)))
% 44.73/44.95            = (k5_relat_1 @ (k6_partfun1 @ X0) @ (k4_relat_1 @ X1)))
% 44.73/44.95          | ~ (v1_relat_1 @ X1)
% 44.73/44.95          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 44.73/44.95      inference('sup+', [status(thm)], ['208', '209'])).
% 44.73/44.95  thf('211', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 44.73/44.95      inference('demod', [status(thm)], ['84', '85'])).
% 44.73/44.95  thf('212', plain,
% 44.73/44.95      (![X0 : $i, X1 : $i]:
% 44.73/44.95         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0)))
% 44.73/44.95            = (k5_relat_1 @ (k6_partfun1 @ X0) @ (k4_relat_1 @ X1)))
% 44.73/44.95          | ~ (v1_relat_1 @ X1))),
% 44.73/44.95      inference('demod', [status(thm)], ['210', '211'])).
% 44.73/44.95  thf('213', plain,
% 44.73/44.95      (![X0 : $i, X1 : $i]:
% 44.73/44.95         (((k4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X1)))
% 44.73/44.95            = (k5_relat_1 @ (k6_partfun1 @ X1) @ (k6_partfun1 @ X0)))
% 44.73/44.95          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 44.73/44.95      inference('sup+', [status(thm)], ['207', '212'])).
% 44.73/44.95  thf('214', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 44.73/44.95      inference('demod', [status(thm)], ['84', '85'])).
% 44.73/44.95  thf('215', plain,
% 44.73/44.95      (![X0 : $i, X1 : $i]:
% 44.73/44.95         ((k4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X1)))
% 44.73/44.95           = (k5_relat_1 @ (k6_partfun1 @ X1) @ (k6_partfun1 @ X0)))),
% 44.73/44.95      inference('demod', [status(thm)], ['213', '214'])).
% 44.73/44.95  thf('216', plain,
% 44.73/44.95      (((k4_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 44.73/44.95         = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ 
% 44.73/44.95            (k6_partfun1 @ sk_A)))),
% 44.73/44.95      inference('sup+', [status(thm)], ['203', '215'])).
% 44.73/44.95  thf('217', plain,
% 44.73/44.95      (![X20 : $i]: ((k4_relat_1 @ (k6_partfun1 @ X20)) = (k6_partfun1 @ X20))),
% 44.73/44.95      inference('demod', [status(thm)], ['204', '205', '206'])).
% 44.73/44.95  thf('218', plain,
% 44.73/44.95      (((k6_partfun1 @ (k1_relat_1 @ sk_C))
% 44.73/44.95         = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ 
% 44.73/44.95            (k6_partfun1 @ sk_A)))),
% 44.73/44.95      inference('demod', [status(thm)], ['216', '217'])).
% 44.73/44.95  thf('219', plain, ((v1_relat_1 @ sk_C)),
% 44.73/44.95      inference('demod', [status(thm)], ['59', '60'])).
% 44.73/44.95  thf('220', plain, ((v1_relat_1 @ sk_D)),
% 44.73/44.95      inference('demod', [status(thm)], ['118', '119'])).
% 44.73/44.95  thf('221', plain,
% 44.73/44.95      (((k6_partfun1 @ sk_A) = (k6_partfun1 @ (k1_relat_1 @ sk_C)))),
% 44.73/44.95      inference('demod', [status(thm)], ['201', '202', '218', '219', '220'])).
% 44.73/44.95  thf('222', plain,
% 44.73/44.95      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 44.73/44.95         = (k2_funct_1 @ sk_C))),
% 44.73/44.95      inference('demod', [status(thm)], ['191', '221'])).
% 44.73/44.95  thf('223', plain, ((v1_relat_1 @ sk_D)),
% 44.73/44.95      inference('demod', [status(thm)], ['118', '119'])).
% 44.73/44.95  thf('224', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 44.73/44.95      inference('demod', [status(thm)], ['110', '127', '222', '223'])).
% 44.73/44.95  thf('225', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 44.73/44.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.73/44.95  thf('226', plain, ($false),
% 44.73/44.95      inference('simplify_reflect-', [status(thm)], ['224', '225'])).
% 44.73/44.95  
% 44.73/44.95  % SZS output end Refutation
% 44.73/44.95  
% 44.80/44.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

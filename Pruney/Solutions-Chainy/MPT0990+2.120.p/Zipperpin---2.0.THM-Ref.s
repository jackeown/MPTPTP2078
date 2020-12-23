%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.V9XSHjLAun

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:15 EST 2020

% Result     : Theorem 2.03s
% Output     : Refutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :  277 (1385 expanded)
%              Number of leaves         :   50 ( 460 expanded)
%              Depth                    :   22
%              Number of atoms          : 2308 (20639 expanded)
%              Number of equality atoms :  164 (1393 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X51: $i,X52: $i,X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X53 ) ) )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_funct_1 @ X54 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X56 ) ) )
      | ( ( k1_partfun1 @ X52 @ X53 @ X55 @ X56 @ X51 @ X54 )
        = ( k5_relat_1 @ X51 @ X54 ) ) ) ),
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
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X46 @ X47 @ X49 @ X50 @ X45 @ X48 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X50 ) ) ) ) ),
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
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( X40 = X43 )
      | ~ ( r2_relset_1 @ X41 @ X42 @ X40 @ X43 ) ) ),
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
    ! [X44: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X44 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('22',plain,(
    ! [X57: $i] :
      ( ( k6_partfun1 @ X57 )
      = ( k6_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('23',plain,(
    ! [X44: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X44 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X44 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['6','7','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('27',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('29',plain,(
    ! [X6: $i,X7: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('30',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['28','29'])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('31',plain,(
    ! [X26: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k2_funct_1 @ X26 )
        = ( k4_relat_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('32',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('36',plain,(
    ! [X33: $i] :
      ( ~ ( v2_funct_1 @ X33 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X33 ) @ X33 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('37',plain,(
    ! [X57: $i] :
      ( ( k6_partfun1 @ X57 )
      = ( k6_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('38',plain,(
    ! [X33: $i] :
      ( ~ ( v2_funct_1 @ X33 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X33 ) @ X33 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('41',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k2_relset_1 @ X38 @ X39 @ X37 )
        = ( k2_relat_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
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
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['28','29'])).

thf('46',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['39','44','45','46','47'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('49',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X18 @ X17 ) @ X19 )
        = ( k5_relat_1 @ X18 @ ( k5_relat_1 @ X17 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('52',plain,(
    ! [X27: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X27 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('53',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['28','29'])).

thf('55',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['28','29'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','56','57'])).

thf('59',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['25','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('61',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v4_relat_1 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('62',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['60','61'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('63',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11
        = ( k7_relat_1 @ X11 @ X12 ) )
      | ~ ( v4_relat_1 @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('64',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('67',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X6: $i,X7: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('69',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['64','69'])).

thf('71',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['64','69'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('72',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k9_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('73',plain,(
    ! [X23: $i] :
      ( ( ( k5_relat_1 @ X23 @ ( k6_relat_1 @ ( k2_relat_1 @ X23 ) ) )
        = X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('74',plain,(
    ! [X57: $i] :
      ( ( k6_partfun1 @ X57 )
      = ( k6_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('75',plain,(
    ! [X23: $i] :
      ( ( ( k5_relat_1 @ X23 @ ( k6_partfun1 @ ( k2_relat_1 @ X23 ) ) )
        = X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k6_partfun1 @ ( k9_relat_1 @ X1 @ X0 ) ) )
        = ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['72','75'])).

thf('77',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k5_relat_1 @ ( k7_relat_1 @ sk_D @ sk_B ) @ ( k6_partfun1 @ ( k9_relat_1 @ sk_D @ sk_B ) ) )
      = ( k7_relat_1 @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['71','76'])).

thf('78',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['67','68'])).

thf('79',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['67','68'])).

thf('80',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['64','69'])).

thf('81',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['64','69'])).

thf('82',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k9_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('83',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k9_relat_1 @ sk_D @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['67','68'])).

thf('85',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k9_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['64','69'])).

thf('87',plain,
    ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
    = sk_D ),
    inference(demod,[status(thm)],['77','78','79','80','85','86'])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('88',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k7_relat_1 @ X25 @ X24 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X24 ) @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('89',plain,(
    ! [X57: $i] :
      ( ( k6_partfun1 @ X57 )
      = ( k6_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('90',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k7_relat_1 @ X25 @ X24 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X24 ) @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X18 @ X17 ) @ X19 )
        = ( k5_relat_1 @ X18 @ ( k5_relat_1 @ X17 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X44: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X44 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X44 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('94',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X6: $i,X7: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('97',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['92','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ sk_D ) )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) ) ),
    inference('sup+',[status(thm)],['87','99'])).

thf('101',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['67','68'])).

thf('102',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,
    ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
    = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D ) ),
    inference('sup+',[status(thm)],['70','103'])).

thf('105',plain,
    ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
    = sk_D ),
    inference(demod,[status(thm)],['77','78','79','80','85','86'])).

thf('106',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = sk_D ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k7_relat_1 @ X25 @ X24 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X24 ) @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('108',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k7_relat_1 @ X25 @ X24 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X24 ) @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('109',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v4_relat_1 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('111',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11
        = ( k7_relat_1 @ X11 @ X12 ) )
      | ~ ( v4_relat_1 @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('113',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['28','29'])).

thf('115',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k7_relat_1 @ X25 @ X24 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X24 ) @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('117',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['42','43'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('118',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) ) @ ( k2_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ sk_C ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['28','29'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ sk_C ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('122',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ sk_C ) ) )
      | ( sk_B
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ( sk_B
        = ( k2_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ sk_C ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['116','123'])).

thf('125',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['28','29'])).

thf('126',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) ) )
      | ( sk_B
        = ( k2_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('128',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C ) )
    | ( sk_B
      = ( k2_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['115','127'])).

thf('129',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['42','43'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('131',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,
    ( sk_B
    = ( k2_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['128','129','131'])).

thf('133',plain,(
    ! [X23: $i] :
      ( ( ( k5_relat_1 @ X23 @ ( k6_partfun1 @ ( k2_relat_1 @ X23 ) ) )
        = X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('134',plain,
    ( ( ( k5_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ ( k6_partfun1 @ sk_B ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,
    ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ ( k6_partfun1 @ sk_B ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['108','134'])).

thf('136',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('137',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['28','29'])).

thf('138',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['28','29'])).

thf('139',plain,
    ( ( k5_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ ( k6_partfun1 @ sk_B ) )
    = ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_C ) ),
    inference(demod,[status(thm)],['135','136','137','138'])).

thf('140',plain,
    ( ( ( k5_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k6_partfun1 @ sk_B ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['107','139'])).

thf('141',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('142',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['42','43'])).

thf('143',plain,(
    ! [X23: $i] :
      ( ( ( k5_relat_1 @ X23 @ ( k6_partfun1 @ ( k2_relat_1 @ X23 ) ) )
        = X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('144',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['142','143'])).

thf('145',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['28','29'])).

thf('146',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['28','29'])).

thf('148',plain,
    ( sk_C
    = ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_C ) ),
    inference(demod,[status(thm)],['140','141','146','147'])).

thf(t72_relat_1,axiom,(
    ! [A: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('149',plain,(
    ! [X22: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X22 ) )
      = ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('150',plain,(
    ! [X57: $i] :
      ( ( k6_partfun1 @ X57 )
      = ( k6_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('151',plain,(
    ! [X57: $i] :
      ( ( k6_partfun1 @ X57 )
      = ( k6_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('152',plain,(
    ! [X22: $i] :
      ( ( k4_relat_1 @ ( k6_partfun1 @ X22 ) )
      = ( k6_partfun1 @ X22 ) ) ),
    inference(demod,[status(thm)],['149','150','151'])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('153',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X16 @ X15 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X15 ) @ ( k4_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('157',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('158',plain,(
    ! [X33: $i] :
      ( ~ ( v2_funct_1 @ X33 )
      | ( ( k5_relat_1 @ X33 @ ( k2_funct_1 @ X33 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('159',plain,(
    ! [X57: $i] :
      ( ( k6_partfun1 @ X57 )
      = ( k6_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('160',plain,(
    ! [X33: $i] :
      ( ~ ( v2_funct_1 @ X33 )
      | ( ( k5_relat_1 @ X33 @ ( k2_funct_1 @ X33 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(demod,[status(thm)],['158','159'])).

thf('161',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['157','160'])).

thf('162',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['28','29'])).

thf('163',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['161','162','163','164'])).

thf('166',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X18 @ X17 ) @ X19 )
        = ( k5_relat_1 @ X18 @ ( k5_relat_1 @ X17 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ X0 )
        = ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['165','166'])).

thf('168',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['28','29'])).

thf('169',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ X0 )
        = ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['167','168','169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ ( k6_partfun1 @ X0 ) )
        = ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ sk_C ) ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['156','170'])).

thf('172',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k7_relat_1 @ X25 @ X24 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X24 ) @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('173',plain,(
    ! [X22: $i] :
      ( ( k4_relat_1 @ ( k6_partfun1 @ X22 ) )
      = ( k6_partfun1 @ X22 ) ) ),
    inference(demod,[status(thm)],['149','150','151'])).

thf('174',plain,(
    ! [X22: $i] :
      ( ( k4_relat_1 @ ( k6_partfun1 @ X22 ) )
      = ( k6_partfun1 @ X22 ) ) ),
    inference(demod,[status(thm)],['149','150','151'])).

thf('175',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X16 @ X15 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X15 ) @ ( k4_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X1 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['173','178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('181',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X1 ) ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ ( k6_partfun1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['179','180'])).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_partfun1 @ X1 ) @ X0 ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['172','181'])).

thf('183',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('184',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_partfun1 @ X1 ) @ X0 ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ ( k6_partfun1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['182','183'])).

thf('185',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k7_relat_1 @ X25 @ X24 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X24 ) @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('186',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_partfun1 @ X1 ) @ X0 ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ ( k6_partfun1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['182','183'])).

thf('187',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
        = ( k7_relat_1 @ ( k6_partfun1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['185','186'])).

thf('188',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('189',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
      = ( k7_relat_1 @ ( k6_partfun1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['187','188'])).

thf('190',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ ( k6_partfun1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['184','189'])).

thf('191',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['28','29'])).

thf('192',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k1_relat_1 @ sk_C ) )
      = ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['171','190','191','192'])).

thf('194',plain,
    ( ( k7_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
    = ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['148','193'])).

thf('195',plain,
    ( ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['161','162','163','164'])).

thf('196',plain,
    ( ( k7_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['194','195'])).

thf('197',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 )
      = ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ ( k6_partfun1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['184','189'])).

thf('198',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('199',plain,(
    ! [X32: $i] :
      ( ~ ( v2_funct_1 @ X32 )
      | ( ( k1_relat_1 @ X32 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('200',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['198','199'])).

thf('201',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['28','29'])).

thf('202',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['200','201','202','203'])).

thf('205',plain,(
    ! [X23: $i] :
      ( ( ( k5_relat_1 @ X23 @ ( k6_partfun1 @ ( k2_relat_1 @ X23 ) ) )
        = X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('206',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['204','205'])).

thf('207',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('208',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['206','207'])).

thf('209',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X18 @ X17 ) @ X19 )
        = ( k5_relat_1 @ X18 @ ( k5_relat_1 @ X17 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('210',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup+',[status(thm)],['208','209'])).

thf('211',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('212',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('213',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['210','211','212'])).

thf('214',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_partfun1 @ X0 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k7_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k1_relat_1 @ sk_C ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['197','213'])).

thf('215',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('216',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_partfun1 @ X0 ) )
      = ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k7_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['214','215'])).

thf('217',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
    = ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['196','216'])).

thf('218',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['206','207'])).

thf('219',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['217','218'])).

thf('220',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['67','68'])).

thf('221',plain,
    ( sk_D
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['59','106','219','220'])).

thf('222',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('224',plain,(
    sk_D
 != ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['222','223'])).

thf('225',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['221','224'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.V9XSHjLAun
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:27:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.03/2.23  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.03/2.23  % Solved by: fo/fo7.sh
% 2.03/2.23  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.03/2.23  % done 2577 iterations in 1.779s
% 2.03/2.23  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.03/2.23  % SZS output start Refutation
% 2.03/2.23  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.03/2.23  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.03/2.23  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.03/2.23  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.03/2.23  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.03/2.23  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.03/2.23  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 2.03/2.23  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.03/2.23  thf(sk_A_type, type, sk_A: $i).
% 2.03/2.23  thf(sk_D_type, type, sk_D: $i).
% 2.03/2.23  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.03/2.23  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.03/2.23  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.03/2.23  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.03/2.23  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.03/2.23  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.03/2.23  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.03/2.23  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.03/2.23  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 2.03/2.23  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.03/2.23  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 2.03/2.23  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.03/2.23  thf(sk_B_type, type, sk_B: $i).
% 2.03/2.23  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.03/2.23  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.03/2.23  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 2.03/2.23  thf(sk_C_type, type, sk_C: $i).
% 2.03/2.23  thf(t36_funct_2, conjecture,
% 2.03/2.23    (![A:$i,B:$i,C:$i]:
% 2.03/2.23     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.03/2.23         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.03/2.23       ( ![D:$i]:
% 2.03/2.23         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.03/2.23             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.03/2.23           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 2.03/2.23               ( r2_relset_1 @
% 2.03/2.23                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.03/2.23                 ( k6_partfun1 @ A ) ) & 
% 2.03/2.23               ( v2_funct_1 @ C ) ) =>
% 2.03/2.23             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.03/2.23               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 2.03/2.23  thf(zf_stmt_0, negated_conjecture,
% 2.03/2.23    (~( ![A:$i,B:$i,C:$i]:
% 2.03/2.23        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.03/2.23            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.03/2.23          ( ![D:$i]:
% 2.03/2.23            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.03/2.23                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.03/2.23              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 2.03/2.23                  ( r2_relset_1 @
% 2.03/2.23                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.03/2.23                    ( k6_partfun1 @ A ) ) & 
% 2.03/2.23                  ( v2_funct_1 @ C ) ) =>
% 2.03/2.23                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.03/2.23                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 2.03/2.23    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 2.03/2.23  thf('0', plain,
% 2.03/2.23      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.03/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.23  thf('1', plain,
% 2.03/2.23      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.03/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.23  thf(redefinition_k1_partfun1, axiom,
% 2.03/2.23    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.03/2.23     ( ( ( v1_funct_1 @ E ) & 
% 2.03/2.23         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.03/2.23         ( v1_funct_1 @ F ) & 
% 2.03/2.23         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.03/2.23       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.03/2.23  thf('2', plain,
% 2.03/2.23      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 2.03/2.23         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X53)))
% 2.03/2.23          | ~ (v1_funct_1 @ X51)
% 2.03/2.23          | ~ (v1_funct_1 @ X54)
% 2.03/2.23          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X56)))
% 2.03/2.23          | ((k1_partfun1 @ X52 @ X53 @ X55 @ X56 @ X51 @ X54)
% 2.03/2.23              = (k5_relat_1 @ X51 @ X54)))),
% 2.03/2.23      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 2.03/2.23  thf('3', plain,
% 2.03/2.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.03/2.23         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.03/2.23            = (k5_relat_1 @ sk_C @ X0))
% 2.03/2.23          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.03/2.23          | ~ (v1_funct_1 @ X0)
% 2.03/2.23          | ~ (v1_funct_1 @ sk_C))),
% 2.03/2.23      inference('sup-', [status(thm)], ['1', '2'])).
% 2.03/2.23  thf('4', plain, ((v1_funct_1 @ sk_C)),
% 2.03/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.23  thf('5', plain,
% 2.03/2.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.03/2.23         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.03/2.23            = (k5_relat_1 @ sk_C @ X0))
% 2.03/2.23          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.03/2.23          | ~ (v1_funct_1 @ X0))),
% 2.03/2.23      inference('demod', [status(thm)], ['3', '4'])).
% 2.03/2.23  thf('6', plain,
% 2.03/2.23      ((~ (v1_funct_1 @ sk_D)
% 2.03/2.23        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.03/2.23            = (k5_relat_1 @ sk_C @ sk_D)))),
% 2.03/2.23      inference('sup-', [status(thm)], ['0', '5'])).
% 2.03/2.23  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 2.03/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.23  thf('8', plain,
% 2.03/2.23      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.03/2.23        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.03/2.23        (k6_partfun1 @ sk_A))),
% 2.03/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.23  thf('9', plain,
% 2.03/2.23      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.03/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.23  thf('10', plain,
% 2.03/2.23      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.03/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.23  thf(dt_k1_partfun1, axiom,
% 2.03/2.23    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.03/2.23     ( ( ( v1_funct_1 @ E ) & 
% 2.03/2.23         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.03/2.23         ( v1_funct_1 @ F ) & 
% 2.03/2.23         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.03/2.23       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.03/2.23         ( m1_subset_1 @
% 2.03/2.23           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.03/2.23           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 2.03/2.23  thf('11', plain,
% 2.03/2.23      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 2.03/2.23         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 2.03/2.23          | ~ (v1_funct_1 @ X45)
% 2.03/2.23          | ~ (v1_funct_1 @ X48)
% 2.03/2.23          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 2.03/2.23          | (m1_subset_1 @ (k1_partfun1 @ X46 @ X47 @ X49 @ X50 @ X45 @ X48) @ 
% 2.03/2.23             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X50))))),
% 2.03/2.23      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 2.03/2.23  thf('12', plain,
% 2.03/2.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.03/2.23         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.03/2.23           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.03/2.23          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.03/2.23          | ~ (v1_funct_1 @ X1)
% 2.03/2.23          | ~ (v1_funct_1 @ sk_C))),
% 2.03/2.23      inference('sup-', [status(thm)], ['10', '11'])).
% 2.03/2.23  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 2.03/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.23  thf('14', plain,
% 2.03/2.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.03/2.23         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.03/2.23           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.03/2.23          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.03/2.23          | ~ (v1_funct_1 @ X1))),
% 2.03/2.23      inference('demod', [status(thm)], ['12', '13'])).
% 2.03/2.23  thf('15', plain,
% 2.03/2.23      ((~ (v1_funct_1 @ sk_D)
% 2.03/2.23        | (m1_subset_1 @ 
% 2.03/2.23           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.03/2.23           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.03/2.23      inference('sup-', [status(thm)], ['9', '14'])).
% 2.03/2.23  thf('16', plain, ((v1_funct_1 @ sk_D)),
% 2.03/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.23  thf('17', plain,
% 2.03/2.23      ((m1_subset_1 @ 
% 2.03/2.23        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.03/2.23        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.03/2.23      inference('demod', [status(thm)], ['15', '16'])).
% 2.03/2.23  thf(redefinition_r2_relset_1, axiom,
% 2.03/2.23    (![A:$i,B:$i,C:$i,D:$i]:
% 2.03/2.23     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.03/2.23         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.03/2.23       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.03/2.23  thf('18', plain,
% 2.03/2.23      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 2.03/2.23         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 2.03/2.23          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 2.03/2.23          | ((X40) = (X43))
% 2.03/2.23          | ~ (r2_relset_1 @ X41 @ X42 @ X40 @ X43))),
% 2.03/2.23      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.03/2.23  thf('19', plain,
% 2.03/2.23      (![X0 : $i]:
% 2.03/2.23         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.03/2.23             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 2.03/2.23          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 2.03/2.23          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.03/2.23      inference('sup-', [status(thm)], ['17', '18'])).
% 2.03/2.23  thf('20', plain,
% 2.03/2.23      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 2.03/2.23           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 2.03/2.23        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.03/2.23            = (k6_partfun1 @ sk_A)))),
% 2.03/2.23      inference('sup-', [status(thm)], ['8', '19'])).
% 2.03/2.23  thf(t29_relset_1, axiom,
% 2.03/2.23    (![A:$i]:
% 2.03/2.23     ( m1_subset_1 @
% 2.03/2.23       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 2.03/2.23  thf('21', plain,
% 2.03/2.23      (![X44 : $i]:
% 2.03/2.23         (m1_subset_1 @ (k6_relat_1 @ X44) @ 
% 2.03/2.23          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X44)))),
% 2.03/2.23      inference('cnf', [status(esa)], [t29_relset_1])).
% 2.03/2.23  thf(redefinition_k6_partfun1, axiom,
% 2.03/2.23    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 2.03/2.23  thf('22', plain, (![X57 : $i]: ((k6_partfun1 @ X57) = (k6_relat_1 @ X57))),
% 2.03/2.23      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.03/2.23  thf('23', plain,
% 2.03/2.23      (![X44 : $i]:
% 2.03/2.23         (m1_subset_1 @ (k6_partfun1 @ X44) @ 
% 2.03/2.23          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X44)))),
% 2.03/2.23      inference('demod', [status(thm)], ['21', '22'])).
% 2.03/2.23  thf('24', plain,
% 2.03/2.23      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.03/2.23         = (k6_partfun1 @ sk_A))),
% 2.03/2.23      inference('demod', [status(thm)], ['20', '23'])).
% 2.03/2.23  thf('25', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 2.03/2.23      inference('demod', [status(thm)], ['6', '7', '24'])).
% 2.03/2.23  thf('26', plain,
% 2.03/2.23      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.03/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.23  thf(cc2_relat_1, axiom,
% 2.03/2.23    (![A:$i]:
% 2.03/2.23     ( ( v1_relat_1 @ A ) =>
% 2.03/2.23       ( ![B:$i]:
% 2.03/2.23         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.03/2.23  thf('27', plain,
% 2.03/2.23      (![X3 : $i, X4 : $i]:
% 2.03/2.23         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 2.03/2.23          | (v1_relat_1 @ X3)
% 2.03/2.23          | ~ (v1_relat_1 @ X4))),
% 2.03/2.23      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.03/2.23  thf('28', plain,
% 2.03/2.23      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 2.03/2.23      inference('sup-', [status(thm)], ['26', '27'])).
% 2.03/2.23  thf(fc6_relat_1, axiom,
% 2.03/2.23    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.03/2.23  thf('29', plain,
% 2.03/2.23      (![X6 : $i, X7 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X6 @ X7))),
% 2.03/2.23      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.03/2.23  thf('30', plain, ((v1_relat_1 @ sk_C)),
% 2.03/2.23      inference('demod', [status(thm)], ['28', '29'])).
% 2.03/2.23  thf(d9_funct_1, axiom,
% 2.03/2.23    (![A:$i]:
% 2.03/2.23     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.03/2.23       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 2.03/2.23  thf('31', plain,
% 2.03/2.23      (![X26 : $i]:
% 2.03/2.23         (~ (v2_funct_1 @ X26)
% 2.03/2.23          | ((k2_funct_1 @ X26) = (k4_relat_1 @ X26))
% 2.03/2.23          | ~ (v1_funct_1 @ X26)
% 2.03/2.23          | ~ (v1_relat_1 @ X26))),
% 2.03/2.23      inference('cnf', [status(esa)], [d9_funct_1])).
% 2.03/2.23  thf('32', plain,
% 2.03/2.23      ((~ (v1_funct_1 @ sk_C)
% 2.03/2.23        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 2.03/2.23        | ~ (v2_funct_1 @ sk_C))),
% 2.03/2.23      inference('sup-', [status(thm)], ['30', '31'])).
% 2.03/2.23  thf('33', plain, ((v1_funct_1 @ sk_C)),
% 2.03/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.23  thf('34', plain, ((v2_funct_1 @ sk_C)),
% 2.03/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.23  thf('35', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 2.03/2.23      inference('demod', [status(thm)], ['32', '33', '34'])).
% 2.03/2.23  thf(t61_funct_1, axiom,
% 2.03/2.23    (![A:$i]:
% 2.03/2.23     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.03/2.23       ( ( v2_funct_1 @ A ) =>
% 2.03/2.23         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 2.03/2.23             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 2.03/2.23           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 2.03/2.23             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 2.03/2.23  thf('36', plain,
% 2.03/2.23      (![X33 : $i]:
% 2.03/2.23         (~ (v2_funct_1 @ X33)
% 2.03/2.23          | ((k5_relat_1 @ (k2_funct_1 @ X33) @ X33)
% 2.03/2.23              = (k6_relat_1 @ (k2_relat_1 @ X33)))
% 2.03/2.23          | ~ (v1_funct_1 @ X33)
% 2.03/2.23          | ~ (v1_relat_1 @ X33))),
% 2.03/2.23      inference('cnf', [status(esa)], [t61_funct_1])).
% 2.03/2.23  thf('37', plain, (![X57 : $i]: ((k6_partfun1 @ X57) = (k6_relat_1 @ X57))),
% 2.03/2.23      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.03/2.23  thf('38', plain,
% 2.03/2.23      (![X33 : $i]:
% 2.03/2.23         (~ (v2_funct_1 @ X33)
% 2.03/2.23          | ((k5_relat_1 @ (k2_funct_1 @ X33) @ X33)
% 2.03/2.23              = (k6_partfun1 @ (k2_relat_1 @ X33)))
% 2.03/2.23          | ~ (v1_funct_1 @ X33)
% 2.03/2.23          | ~ (v1_relat_1 @ X33))),
% 2.03/2.23      inference('demod', [status(thm)], ['36', '37'])).
% 2.03/2.24  thf('39', plain,
% 2.03/2.24      ((((k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C)
% 2.03/2.24          = (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 2.03/2.24        | ~ (v1_relat_1 @ sk_C)
% 2.03/2.24        | ~ (v1_funct_1 @ sk_C)
% 2.03/2.24        | ~ (v2_funct_1 @ sk_C))),
% 2.03/2.24      inference('sup+', [status(thm)], ['35', '38'])).
% 2.03/2.24  thf('40', plain,
% 2.03/2.24      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.03/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.24  thf(redefinition_k2_relset_1, axiom,
% 2.03/2.24    (![A:$i,B:$i,C:$i]:
% 2.03/2.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.03/2.24       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.03/2.24  thf('41', plain,
% 2.03/2.24      (![X37 : $i, X38 : $i, X39 : $i]:
% 2.03/2.24         (((k2_relset_1 @ X38 @ X39 @ X37) = (k2_relat_1 @ X37))
% 2.03/2.24          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 2.03/2.24      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.03/2.24  thf('42', plain,
% 2.03/2.24      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 2.03/2.24      inference('sup-', [status(thm)], ['40', '41'])).
% 2.03/2.24  thf('43', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.03/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.24  thf('44', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.03/2.24      inference('sup+', [status(thm)], ['42', '43'])).
% 2.03/2.24  thf('45', plain, ((v1_relat_1 @ sk_C)),
% 2.03/2.24      inference('demod', [status(thm)], ['28', '29'])).
% 2.03/2.24  thf('46', plain, ((v1_funct_1 @ sk_C)),
% 2.03/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.24  thf('47', plain, ((v2_funct_1 @ sk_C)),
% 2.03/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.24  thf('48', plain,
% 2.03/2.24      (((k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 2.03/2.24      inference('demod', [status(thm)], ['39', '44', '45', '46', '47'])).
% 2.03/2.24  thf(t55_relat_1, axiom,
% 2.03/2.24    (![A:$i]:
% 2.03/2.24     ( ( v1_relat_1 @ A ) =>
% 2.03/2.24       ( ![B:$i]:
% 2.03/2.24         ( ( v1_relat_1 @ B ) =>
% 2.03/2.24           ( ![C:$i]:
% 2.03/2.24             ( ( v1_relat_1 @ C ) =>
% 2.03/2.24               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 2.03/2.24                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 2.03/2.24  thf('49', plain,
% 2.03/2.24      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.03/2.24         (~ (v1_relat_1 @ X17)
% 2.03/2.24          | ((k5_relat_1 @ (k5_relat_1 @ X18 @ X17) @ X19)
% 2.03/2.24              = (k5_relat_1 @ X18 @ (k5_relat_1 @ X17 @ X19)))
% 2.03/2.24          | ~ (v1_relat_1 @ X19)
% 2.03/2.24          | ~ (v1_relat_1 @ X18))),
% 2.03/2.24      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.03/2.24  thf('50', plain,
% 2.03/2.24      (![X0 : $i]:
% 2.03/2.24         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 2.03/2.24            = (k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 2.03/2.24          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 2.03/2.24          | ~ (v1_relat_1 @ X0)
% 2.03/2.24          | ~ (v1_relat_1 @ sk_C))),
% 2.03/2.24      inference('sup+', [status(thm)], ['48', '49'])).
% 2.03/2.24  thf('51', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 2.03/2.24      inference('demod', [status(thm)], ['32', '33', '34'])).
% 2.03/2.24  thf(dt_k2_funct_1, axiom,
% 2.03/2.24    (![A:$i]:
% 2.03/2.24     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.03/2.24       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 2.03/2.24         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 2.03/2.24  thf('52', plain,
% 2.03/2.24      (![X27 : $i]:
% 2.03/2.24         ((v1_relat_1 @ (k2_funct_1 @ X27))
% 2.03/2.24          | ~ (v1_funct_1 @ X27)
% 2.03/2.24          | ~ (v1_relat_1 @ X27))),
% 2.03/2.24      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.03/2.24  thf('53', plain,
% 2.03/2.24      (((v1_relat_1 @ (k4_relat_1 @ sk_C))
% 2.03/2.24        | ~ (v1_relat_1 @ sk_C)
% 2.03/2.24        | ~ (v1_funct_1 @ sk_C))),
% 2.03/2.24      inference('sup+', [status(thm)], ['51', '52'])).
% 2.03/2.24  thf('54', plain, ((v1_relat_1 @ sk_C)),
% 2.03/2.24      inference('demod', [status(thm)], ['28', '29'])).
% 2.03/2.24  thf('55', plain, ((v1_funct_1 @ sk_C)),
% 2.03/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.24  thf('56', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 2.03/2.24      inference('demod', [status(thm)], ['53', '54', '55'])).
% 2.03/2.24  thf('57', plain, ((v1_relat_1 @ sk_C)),
% 2.03/2.24      inference('demod', [status(thm)], ['28', '29'])).
% 2.03/2.24  thf('58', plain,
% 2.03/2.24      (![X0 : $i]:
% 2.03/2.24         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 2.03/2.24            = (k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 2.03/2.24          | ~ (v1_relat_1 @ X0))),
% 2.03/2.24      inference('demod', [status(thm)], ['50', '56', '57'])).
% 2.03/2.24  thf('59', plain,
% 2.03/2.24      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 2.03/2.24          = (k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 2.03/2.24        | ~ (v1_relat_1 @ sk_D))),
% 2.03/2.24      inference('sup+', [status(thm)], ['25', '58'])).
% 2.03/2.24  thf('60', plain,
% 2.03/2.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.03/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.24  thf(cc2_relset_1, axiom,
% 2.03/2.24    (![A:$i,B:$i,C:$i]:
% 2.03/2.24     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.03/2.24       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.03/2.24  thf('61', plain,
% 2.03/2.24      (![X34 : $i, X35 : $i, X36 : $i]:
% 2.03/2.24         ((v4_relat_1 @ X34 @ X35)
% 2.03/2.24          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 2.03/2.24      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.03/2.24  thf('62', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 2.03/2.24      inference('sup-', [status(thm)], ['60', '61'])).
% 2.03/2.24  thf(t209_relat_1, axiom,
% 2.03/2.24    (![A:$i,B:$i]:
% 2.03/2.24     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 2.03/2.24       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 2.03/2.24  thf('63', plain,
% 2.03/2.24      (![X11 : $i, X12 : $i]:
% 2.03/2.24         (((X11) = (k7_relat_1 @ X11 @ X12))
% 2.03/2.24          | ~ (v4_relat_1 @ X11 @ X12)
% 2.03/2.24          | ~ (v1_relat_1 @ X11))),
% 2.03/2.24      inference('cnf', [status(esa)], [t209_relat_1])).
% 2.03/2.24  thf('64', plain,
% 2.03/2.24      ((~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ sk_B)))),
% 2.03/2.24      inference('sup-', [status(thm)], ['62', '63'])).
% 2.03/2.24  thf('65', plain,
% 2.03/2.24      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.03/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.24  thf('66', plain,
% 2.03/2.24      (![X3 : $i, X4 : $i]:
% 2.03/2.24         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 2.03/2.24          | (v1_relat_1 @ X3)
% 2.03/2.24          | ~ (v1_relat_1 @ X4))),
% 2.03/2.24      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.03/2.24  thf('67', plain,
% 2.03/2.24      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 2.03/2.24      inference('sup-', [status(thm)], ['65', '66'])).
% 2.03/2.24  thf('68', plain,
% 2.03/2.24      (![X6 : $i, X7 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X6 @ X7))),
% 2.03/2.24      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.03/2.24  thf('69', plain, ((v1_relat_1 @ sk_D)),
% 2.03/2.24      inference('demod', [status(thm)], ['67', '68'])).
% 2.03/2.24  thf('70', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_B))),
% 2.03/2.24      inference('demod', [status(thm)], ['64', '69'])).
% 2.03/2.24  thf('71', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_B))),
% 2.03/2.24      inference('demod', [status(thm)], ['64', '69'])).
% 2.03/2.24  thf(t148_relat_1, axiom,
% 2.03/2.24    (![A:$i,B:$i]:
% 2.03/2.24     ( ( v1_relat_1 @ B ) =>
% 2.03/2.24       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 2.03/2.24  thf('72', plain,
% 2.03/2.24      (![X9 : $i, X10 : $i]:
% 2.03/2.24         (((k2_relat_1 @ (k7_relat_1 @ X9 @ X10)) = (k9_relat_1 @ X9 @ X10))
% 2.03/2.24          | ~ (v1_relat_1 @ X9))),
% 2.03/2.24      inference('cnf', [status(esa)], [t148_relat_1])).
% 2.03/2.24  thf(t80_relat_1, axiom,
% 2.03/2.24    (![A:$i]:
% 2.03/2.24     ( ( v1_relat_1 @ A ) =>
% 2.03/2.24       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 2.03/2.24  thf('73', plain,
% 2.03/2.24      (![X23 : $i]:
% 2.03/2.24         (((k5_relat_1 @ X23 @ (k6_relat_1 @ (k2_relat_1 @ X23))) = (X23))
% 2.03/2.24          | ~ (v1_relat_1 @ X23))),
% 2.03/2.24      inference('cnf', [status(esa)], [t80_relat_1])).
% 2.03/2.24  thf('74', plain, (![X57 : $i]: ((k6_partfun1 @ X57) = (k6_relat_1 @ X57))),
% 2.03/2.24      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.03/2.24  thf('75', plain,
% 2.03/2.24      (![X23 : $i]:
% 2.03/2.24         (((k5_relat_1 @ X23 @ (k6_partfun1 @ (k2_relat_1 @ X23))) = (X23))
% 2.03/2.24          | ~ (v1_relat_1 @ X23))),
% 2.03/2.24      inference('demod', [status(thm)], ['73', '74'])).
% 2.03/2.24  thf('76', plain,
% 2.03/2.24      (![X0 : $i, X1 : $i]:
% 2.03/2.24         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 2.03/2.24            (k6_partfun1 @ (k9_relat_1 @ X1 @ X0))) = (k7_relat_1 @ X1 @ X0))
% 2.03/2.24          | ~ (v1_relat_1 @ X1)
% 2.03/2.24          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 2.03/2.24      inference('sup+', [status(thm)], ['72', '75'])).
% 2.03/2.24  thf('77', plain,
% 2.03/2.24      ((~ (v1_relat_1 @ sk_D)
% 2.03/2.24        | ~ (v1_relat_1 @ sk_D)
% 2.03/2.24        | ((k5_relat_1 @ (k7_relat_1 @ sk_D @ sk_B) @ 
% 2.03/2.24            (k6_partfun1 @ (k9_relat_1 @ sk_D @ sk_B)))
% 2.03/2.24            = (k7_relat_1 @ sk_D @ sk_B)))),
% 2.03/2.24      inference('sup-', [status(thm)], ['71', '76'])).
% 2.03/2.24  thf('78', plain, ((v1_relat_1 @ sk_D)),
% 2.03/2.24      inference('demod', [status(thm)], ['67', '68'])).
% 2.03/2.24  thf('79', plain, ((v1_relat_1 @ sk_D)),
% 2.03/2.24      inference('demod', [status(thm)], ['67', '68'])).
% 2.03/2.24  thf('80', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_B))),
% 2.03/2.24      inference('demod', [status(thm)], ['64', '69'])).
% 2.03/2.24  thf('81', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_B))),
% 2.03/2.24      inference('demod', [status(thm)], ['64', '69'])).
% 2.03/2.24  thf('82', plain,
% 2.03/2.24      (![X9 : $i, X10 : $i]:
% 2.03/2.24         (((k2_relat_1 @ (k7_relat_1 @ X9 @ X10)) = (k9_relat_1 @ X9 @ X10))
% 2.03/2.24          | ~ (v1_relat_1 @ X9))),
% 2.03/2.24      inference('cnf', [status(esa)], [t148_relat_1])).
% 2.03/2.24  thf('83', plain,
% 2.03/2.24      ((((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ sk_B))
% 2.03/2.24        | ~ (v1_relat_1 @ sk_D))),
% 2.03/2.24      inference('sup+', [status(thm)], ['81', '82'])).
% 2.03/2.24  thf('84', plain, ((v1_relat_1 @ sk_D)),
% 2.03/2.24      inference('demod', [status(thm)], ['67', '68'])).
% 2.03/2.24  thf('85', plain, (((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ sk_B))),
% 2.03/2.24      inference('demod', [status(thm)], ['83', '84'])).
% 2.03/2.24  thf('86', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_B))),
% 2.03/2.24      inference('demod', [status(thm)], ['64', '69'])).
% 2.03/2.24  thf('87', plain,
% 2.03/2.24      (((k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D))) = (sk_D))),
% 2.03/2.24      inference('demod', [status(thm)], ['77', '78', '79', '80', '85', '86'])).
% 2.03/2.24  thf(t94_relat_1, axiom,
% 2.03/2.24    (![A:$i,B:$i]:
% 2.03/2.24     ( ( v1_relat_1 @ B ) =>
% 2.03/2.24       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 2.03/2.24  thf('88', plain,
% 2.03/2.24      (![X24 : $i, X25 : $i]:
% 2.03/2.24         (((k7_relat_1 @ X25 @ X24) = (k5_relat_1 @ (k6_relat_1 @ X24) @ X25))
% 2.03/2.24          | ~ (v1_relat_1 @ X25))),
% 2.03/2.24      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.03/2.24  thf('89', plain, (![X57 : $i]: ((k6_partfun1 @ X57) = (k6_relat_1 @ X57))),
% 2.03/2.24      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.03/2.24  thf('90', plain,
% 2.03/2.24      (![X24 : $i, X25 : $i]:
% 2.03/2.24         (((k7_relat_1 @ X25 @ X24) = (k5_relat_1 @ (k6_partfun1 @ X24) @ X25))
% 2.03/2.24          | ~ (v1_relat_1 @ X25))),
% 2.03/2.24      inference('demod', [status(thm)], ['88', '89'])).
% 2.03/2.24  thf('91', plain,
% 2.03/2.24      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.03/2.24         (~ (v1_relat_1 @ X17)
% 2.03/2.24          | ((k5_relat_1 @ (k5_relat_1 @ X18 @ X17) @ X19)
% 2.03/2.24              = (k5_relat_1 @ X18 @ (k5_relat_1 @ X17 @ X19)))
% 2.03/2.24          | ~ (v1_relat_1 @ X19)
% 2.03/2.24          | ~ (v1_relat_1 @ X18))),
% 2.03/2.24      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.03/2.24  thf('92', plain,
% 2.03/2.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.03/2.24         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 2.03/2.24            = (k5_relat_1 @ (k6_partfun1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 2.03/2.24          | ~ (v1_relat_1 @ X1)
% 2.03/2.24          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 2.03/2.24          | ~ (v1_relat_1 @ X2)
% 2.03/2.24          | ~ (v1_relat_1 @ X1))),
% 2.03/2.24      inference('sup+', [status(thm)], ['90', '91'])).
% 2.03/2.24  thf('93', plain,
% 2.03/2.24      (![X44 : $i]:
% 2.03/2.24         (m1_subset_1 @ (k6_partfun1 @ X44) @ 
% 2.03/2.24          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X44)))),
% 2.03/2.24      inference('demod', [status(thm)], ['21', '22'])).
% 2.03/2.24  thf('94', plain,
% 2.03/2.24      (![X3 : $i, X4 : $i]:
% 2.03/2.24         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 2.03/2.24          | (v1_relat_1 @ X3)
% 2.03/2.24          | ~ (v1_relat_1 @ X4))),
% 2.03/2.24      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.03/2.24  thf('95', plain,
% 2.03/2.24      (![X0 : $i]:
% 2.03/2.24         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X0))
% 2.03/2.24          | (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 2.03/2.24      inference('sup-', [status(thm)], ['93', '94'])).
% 2.03/2.24  thf('96', plain,
% 2.03/2.24      (![X6 : $i, X7 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X6 @ X7))),
% 2.03/2.24      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.03/2.24  thf('97', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 2.03/2.24      inference('demod', [status(thm)], ['95', '96'])).
% 2.03/2.24  thf('98', plain,
% 2.03/2.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.03/2.24         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 2.03/2.24            = (k5_relat_1 @ (k6_partfun1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 2.03/2.24          | ~ (v1_relat_1 @ X1)
% 2.03/2.24          | ~ (v1_relat_1 @ X2)
% 2.03/2.24          | ~ (v1_relat_1 @ X1))),
% 2.03/2.24      inference('demod', [status(thm)], ['92', '97'])).
% 2.03/2.24  thf('99', plain,
% 2.03/2.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.03/2.24         (~ (v1_relat_1 @ X2)
% 2.03/2.24          | ~ (v1_relat_1 @ X1)
% 2.03/2.24          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 2.03/2.24              = (k5_relat_1 @ (k6_partfun1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 2.03/2.24      inference('simplify', [status(thm)], ['98'])).
% 2.03/2.24  thf('100', plain,
% 2.03/2.24      (![X0 : $i]:
% 2.03/2.24         (((k5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 2.03/2.24            (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 2.03/2.24            = (k5_relat_1 @ (k6_partfun1 @ X0) @ sk_D))
% 2.03/2.24          | ~ (v1_relat_1 @ sk_D)
% 2.03/2.24          | ~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_D))))),
% 2.03/2.24      inference('sup+', [status(thm)], ['87', '99'])).
% 2.03/2.24  thf('101', plain, ((v1_relat_1 @ sk_D)),
% 2.03/2.24      inference('demod', [status(thm)], ['67', '68'])).
% 2.03/2.24  thf('102', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 2.03/2.24      inference('demod', [status(thm)], ['95', '96'])).
% 2.03/2.24  thf('103', plain,
% 2.03/2.24      (![X0 : $i]:
% 2.03/2.24         ((k5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 2.03/2.24           (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 2.03/2.24           = (k5_relat_1 @ (k6_partfun1 @ X0) @ sk_D))),
% 2.03/2.24      inference('demod', [status(thm)], ['100', '101', '102'])).
% 2.03/2.24  thf('104', plain,
% 2.03/2.24      (((k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 2.03/2.24         = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D))),
% 2.03/2.24      inference('sup+', [status(thm)], ['70', '103'])).
% 2.03/2.24  thf('105', plain,
% 2.03/2.24      (((k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D))) = (sk_D))),
% 2.03/2.24      inference('demod', [status(thm)], ['77', '78', '79', '80', '85', '86'])).
% 2.03/2.24  thf('106', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))),
% 2.03/2.24      inference('sup+', [status(thm)], ['104', '105'])).
% 2.03/2.24  thf('107', plain,
% 2.03/2.24      (![X24 : $i, X25 : $i]:
% 2.03/2.24         (((k7_relat_1 @ X25 @ X24) = (k5_relat_1 @ (k6_partfun1 @ X24) @ X25))
% 2.03/2.24          | ~ (v1_relat_1 @ X25))),
% 2.03/2.24      inference('demod', [status(thm)], ['88', '89'])).
% 2.03/2.24  thf('108', plain,
% 2.03/2.24      (![X24 : $i, X25 : $i]:
% 2.03/2.24         (((k7_relat_1 @ X25 @ X24) = (k5_relat_1 @ (k6_partfun1 @ X24) @ X25))
% 2.03/2.24          | ~ (v1_relat_1 @ X25))),
% 2.03/2.24      inference('demod', [status(thm)], ['88', '89'])).
% 2.03/2.24  thf('109', plain,
% 2.03/2.24      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.03/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.24  thf('110', plain,
% 2.03/2.24      (![X34 : $i, X35 : $i, X36 : $i]:
% 2.03/2.24         ((v4_relat_1 @ X34 @ X35)
% 2.03/2.24          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 2.03/2.24      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.03/2.24  thf('111', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 2.03/2.24      inference('sup-', [status(thm)], ['109', '110'])).
% 2.03/2.24  thf('112', plain,
% 2.03/2.24      (![X11 : $i, X12 : $i]:
% 2.03/2.24         (((X11) = (k7_relat_1 @ X11 @ X12))
% 2.03/2.24          | ~ (v4_relat_1 @ X11 @ X12)
% 2.03/2.24          | ~ (v1_relat_1 @ X11))),
% 2.03/2.24      inference('cnf', [status(esa)], [t209_relat_1])).
% 2.03/2.24  thf('113', plain,
% 2.03/2.24      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 2.03/2.24      inference('sup-', [status(thm)], ['111', '112'])).
% 2.03/2.24  thf('114', plain, ((v1_relat_1 @ sk_C)),
% 2.03/2.24      inference('demod', [status(thm)], ['28', '29'])).
% 2.03/2.24  thf('115', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 2.03/2.24      inference('demod', [status(thm)], ['113', '114'])).
% 2.03/2.24  thf('116', plain,
% 2.03/2.24      (![X24 : $i, X25 : $i]:
% 2.03/2.24         (((k7_relat_1 @ X25 @ X24) = (k5_relat_1 @ (k6_partfun1 @ X24) @ X25))
% 2.03/2.24          | ~ (v1_relat_1 @ X25))),
% 2.03/2.24      inference('demod', [status(thm)], ['88', '89'])).
% 2.03/2.24  thf('117', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.03/2.24      inference('sup+', [status(thm)], ['42', '43'])).
% 2.03/2.24  thf(t45_relat_1, axiom,
% 2.03/2.24    (![A:$i]:
% 2.03/2.24     ( ( v1_relat_1 @ A ) =>
% 2.03/2.24       ( ![B:$i]:
% 2.03/2.24         ( ( v1_relat_1 @ B ) =>
% 2.03/2.24           ( r1_tarski @
% 2.03/2.24             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 2.03/2.24  thf('118', plain,
% 2.03/2.24      (![X13 : $i, X14 : $i]:
% 2.03/2.24         (~ (v1_relat_1 @ X13)
% 2.03/2.24          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X14 @ X13)) @ 
% 2.03/2.24             (k2_relat_1 @ X13))
% 2.03/2.24          | ~ (v1_relat_1 @ X14))),
% 2.03/2.24      inference('cnf', [status(esa)], [t45_relat_1])).
% 2.03/2.24  thf('119', plain,
% 2.03/2.24      (![X0 : $i]:
% 2.03/2.24         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ sk_C)) @ sk_B)
% 2.03/2.24          | ~ (v1_relat_1 @ X0)
% 2.03/2.24          | ~ (v1_relat_1 @ sk_C))),
% 2.03/2.24      inference('sup+', [status(thm)], ['117', '118'])).
% 2.03/2.24  thf('120', plain, ((v1_relat_1 @ sk_C)),
% 2.03/2.24      inference('demod', [status(thm)], ['28', '29'])).
% 2.03/2.24  thf('121', plain,
% 2.03/2.24      (![X0 : $i]:
% 2.03/2.24         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ sk_C)) @ sk_B)
% 2.03/2.24          | ~ (v1_relat_1 @ X0))),
% 2.03/2.24      inference('demod', [status(thm)], ['119', '120'])).
% 2.03/2.24  thf(d10_xboole_0, axiom,
% 2.03/2.24    (![A:$i,B:$i]:
% 2.03/2.24     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.03/2.24  thf('122', plain,
% 2.03/2.24      (![X0 : $i, X2 : $i]:
% 2.03/2.24         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.03/2.24      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.03/2.24  thf('123', plain,
% 2.03/2.24      (![X0 : $i]:
% 2.03/2.24         (~ (v1_relat_1 @ X0)
% 2.03/2.24          | ~ (r1_tarski @ sk_B @ (k2_relat_1 @ (k5_relat_1 @ X0 @ sk_C)))
% 2.03/2.24          | ((sk_B) = (k2_relat_1 @ (k5_relat_1 @ X0 @ sk_C))))),
% 2.03/2.24      inference('sup-', [status(thm)], ['121', '122'])).
% 2.03/2.24  thf('124', plain,
% 2.03/2.24      (![X0 : $i]:
% 2.03/2.24         (~ (r1_tarski @ sk_B @ (k2_relat_1 @ (k7_relat_1 @ sk_C @ X0)))
% 2.03/2.24          | ~ (v1_relat_1 @ sk_C)
% 2.03/2.24          | ((sk_B) = (k2_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ sk_C)))
% 2.03/2.24          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 2.03/2.24      inference('sup-', [status(thm)], ['116', '123'])).
% 2.03/2.24  thf('125', plain, ((v1_relat_1 @ sk_C)),
% 2.03/2.24      inference('demod', [status(thm)], ['28', '29'])).
% 2.03/2.24  thf('126', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 2.03/2.24      inference('demod', [status(thm)], ['95', '96'])).
% 2.03/2.24  thf('127', plain,
% 2.03/2.24      (![X0 : $i]:
% 2.03/2.24         (~ (r1_tarski @ sk_B @ (k2_relat_1 @ (k7_relat_1 @ sk_C @ X0)))
% 2.03/2.24          | ((sk_B) = (k2_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ sk_C))))),
% 2.03/2.24      inference('demod', [status(thm)], ['124', '125', '126'])).
% 2.03/2.24  thf('128', plain,
% 2.03/2.24      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C))
% 2.03/2.24        | ((sk_B) = (k2_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ sk_A) @ sk_C))))),
% 2.03/2.24      inference('sup-', [status(thm)], ['115', '127'])).
% 2.03/2.24  thf('129', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.03/2.24      inference('sup+', [status(thm)], ['42', '43'])).
% 2.03/2.24  thf('130', plain,
% 2.03/2.24      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 2.03/2.24      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.03/2.24  thf('131', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.03/2.24      inference('simplify', [status(thm)], ['130'])).
% 2.03/2.24  thf('132', plain,
% 2.03/2.24      (((sk_B) = (k2_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ sk_A) @ sk_C)))),
% 2.03/2.24      inference('demod', [status(thm)], ['128', '129', '131'])).
% 2.03/2.24  thf('133', plain,
% 2.03/2.24      (![X23 : $i]:
% 2.03/2.24         (((k5_relat_1 @ X23 @ (k6_partfun1 @ (k2_relat_1 @ X23))) = (X23))
% 2.03/2.24          | ~ (v1_relat_1 @ X23))),
% 2.03/2.24      inference('demod', [status(thm)], ['73', '74'])).
% 2.03/2.24  thf('134', plain,
% 2.03/2.24      ((((k5_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ sk_A) @ sk_C) @ 
% 2.03/2.24          (k6_partfun1 @ sk_B)) = (k5_relat_1 @ (k6_partfun1 @ sk_A) @ sk_C))
% 2.03/2.24        | ~ (v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ sk_A) @ sk_C)))),
% 2.03/2.24      inference('sup+', [status(thm)], ['132', '133'])).
% 2.03/2.24  thf('135', plain,
% 2.03/2.24      ((~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A))
% 2.03/2.24        | ~ (v1_relat_1 @ sk_C)
% 2.03/2.24        | ((k5_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ sk_A) @ sk_C) @ 
% 2.03/2.24            (k6_partfun1 @ sk_B)) = (k5_relat_1 @ (k6_partfun1 @ sk_A) @ sk_C)))),
% 2.03/2.24      inference('sup-', [status(thm)], ['108', '134'])).
% 2.03/2.24  thf('136', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 2.03/2.24      inference('demod', [status(thm)], ['113', '114'])).
% 2.03/2.24  thf('137', plain, ((v1_relat_1 @ sk_C)),
% 2.03/2.24      inference('demod', [status(thm)], ['28', '29'])).
% 2.03/2.24  thf('138', plain, ((v1_relat_1 @ sk_C)),
% 2.03/2.24      inference('demod', [status(thm)], ['28', '29'])).
% 2.03/2.24  thf('139', plain,
% 2.03/2.24      (((k5_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ sk_A) @ sk_C) @ 
% 2.03/2.24         (k6_partfun1 @ sk_B)) = (k5_relat_1 @ (k6_partfun1 @ sk_A) @ sk_C))),
% 2.03/2.24      inference('demod', [status(thm)], ['135', '136', '137', '138'])).
% 2.03/2.24  thf('140', plain,
% 2.03/2.24      ((((k5_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ (k6_partfun1 @ sk_B))
% 2.03/2.24          = (k5_relat_1 @ (k6_partfun1 @ sk_A) @ sk_C))
% 2.03/2.24        | ~ (v1_relat_1 @ sk_C))),
% 2.03/2.24      inference('sup+', [status(thm)], ['107', '139'])).
% 2.03/2.24  thf('141', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 2.03/2.24      inference('demod', [status(thm)], ['113', '114'])).
% 2.03/2.24  thf('142', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.03/2.24      inference('sup+', [status(thm)], ['42', '43'])).
% 2.03/2.24  thf('143', plain,
% 2.03/2.24      (![X23 : $i]:
% 2.03/2.24         (((k5_relat_1 @ X23 @ (k6_partfun1 @ (k2_relat_1 @ X23))) = (X23))
% 2.03/2.24          | ~ (v1_relat_1 @ X23))),
% 2.03/2.24      inference('demod', [status(thm)], ['73', '74'])).
% 2.03/2.24  thf('144', plain,
% 2.03/2.24      ((((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))
% 2.03/2.24        | ~ (v1_relat_1 @ sk_C))),
% 2.03/2.24      inference('sup+', [status(thm)], ['142', '143'])).
% 2.03/2.24  thf('145', plain, ((v1_relat_1 @ sk_C)),
% 2.03/2.24      inference('demod', [status(thm)], ['28', '29'])).
% 2.03/2.24  thf('146', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 2.03/2.24      inference('demod', [status(thm)], ['144', '145'])).
% 2.03/2.24  thf('147', plain, ((v1_relat_1 @ sk_C)),
% 2.03/2.24      inference('demod', [status(thm)], ['28', '29'])).
% 2.03/2.24  thf('148', plain, (((sk_C) = (k5_relat_1 @ (k6_partfun1 @ sk_A) @ sk_C))),
% 2.03/2.24      inference('demod', [status(thm)], ['140', '141', '146', '147'])).
% 2.03/2.24  thf(t72_relat_1, axiom,
% 2.03/2.24    (![A:$i]: ( ( k4_relat_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 2.03/2.24  thf('149', plain,
% 2.03/2.24      (![X22 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X22)) = (k6_relat_1 @ X22))),
% 2.03/2.24      inference('cnf', [status(esa)], [t72_relat_1])).
% 2.03/2.24  thf('150', plain, (![X57 : $i]: ((k6_partfun1 @ X57) = (k6_relat_1 @ X57))),
% 2.03/2.24      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.03/2.24  thf('151', plain, (![X57 : $i]: ((k6_partfun1 @ X57) = (k6_relat_1 @ X57))),
% 2.03/2.24      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.03/2.24  thf('152', plain,
% 2.03/2.24      (![X22 : $i]: ((k4_relat_1 @ (k6_partfun1 @ X22)) = (k6_partfun1 @ X22))),
% 2.03/2.24      inference('demod', [status(thm)], ['149', '150', '151'])).
% 2.03/2.24  thf(t54_relat_1, axiom,
% 2.03/2.24    (![A:$i]:
% 2.03/2.24     ( ( v1_relat_1 @ A ) =>
% 2.03/2.24       ( ![B:$i]:
% 2.03/2.24         ( ( v1_relat_1 @ B ) =>
% 2.03/2.24           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 2.03/2.24             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 2.03/2.24  thf('153', plain,
% 2.03/2.24      (![X15 : $i, X16 : $i]:
% 2.03/2.24         (~ (v1_relat_1 @ X15)
% 2.03/2.24          | ((k4_relat_1 @ (k5_relat_1 @ X16 @ X15))
% 2.03/2.24              = (k5_relat_1 @ (k4_relat_1 @ X15) @ (k4_relat_1 @ X16)))
% 2.03/2.24          | ~ (v1_relat_1 @ X16))),
% 2.03/2.24      inference('cnf', [status(esa)], [t54_relat_1])).
% 2.03/2.24  thf('154', plain,
% 2.03/2.24      (![X0 : $i, X1 : $i]:
% 2.03/2.24         (((k4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 2.03/2.24            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_partfun1 @ X0)))
% 2.03/2.24          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 2.03/2.24          | ~ (v1_relat_1 @ X1))),
% 2.03/2.24      inference('sup+', [status(thm)], ['152', '153'])).
% 2.03/2.24  thf('155', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 2.03/2.24      inference('demod', [status(thm)], ['95', '96'])).
% 2.03/2.24  thf('156', plain,
% 2.03/2.24      (![X0 : $i, X1 : $i]:
% 2.03/2.24         (((k4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 2.03/2.24            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_partfun1 @ X0)))
% 2.03/2.24          | ~ (v1_relat_1 @ X1))),
% 2.03/2.24      inference('demod', [status(thm)], ['154', '155'])).
% 2.03/2.24  thf('157', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 2.03/2.24      inference('demod', [status(thm)], ['32', '33', '34'])).
% 2.03/2.24  thf('158', plain,
% 2.03/2.24      (![X33 : $i]:
% 2.03/2.24         (~ (v2_funct_1 @ X33)
% 2.03/2.24          | ((k5_relat_1 @ X33 @ (k2_funct_1 @ X33))
% 2.03/2.24              = (k6_relat_1 @ (k1_relat_1 @ X33)))
% 2.03/2.24          | ~ (v1_funct_1 @ X33)
% 2.03/2.24          | ~ (v1_relat_1 @ X33))),
% 2.03/2.24      inference('cnf', [status(esa)], [t61_funct_1])).
% 2.03/2.24  thf('159', plain, (![X57 : $i]: ((k6_partfun1 @ X57) = (k6_relat_1 @ X57))),
% 2.03/2.24      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.03/2.24  thf('160', plain,
% 2.03/2.24      (![X33 : $i]:
% 2.03/2.24         (~ (v2_funct_1 @ X33)
% 2.03/2.24          | ((k5_relat_1 @ X33 @ (k2_funct_1 @ X33))
% 2.03/2.24              = (k6_partfun1 @ (k1_relat_1 @ X33)))
% 2.03/2.24          | ~ (v1_funct_1 @ X33)
% 2.03/2.24          | ~ (v1_relat_1 @ X33))),
% 2.03/2.24      inference('demod', [status(thm)], ['158', '159'])).
% 2.03/2.24  thf('161', plain,
% 2.03/2.24      ((((k5_relat_1 @ sk_C @ (k4_relat_1 @ sk_C))
% 2.03/2.24          = (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 2.03/2.24        | ~ (v1_relat_1 @ sk_C)
% 2.03/2.24        | ~ (v1_funct_1 @ sk_C)
% 2.03/2.24        | ~ (v2_funct_1 @ sk_C))),
% 2.03/2.24      inference('sup+', [status(thm)], ['157', '160'])).
% 2.03/2.24  thf('162', plain, ((v1_relat_1 @ sk_C)),
% 2.03/2.24      inference('demod', [status(thm)], ['28', '29'])).
% 2.03/2.24  thf('163', plain, ((v1_funct_1 @ sk_C)),
% 2.03/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.24  thf('164', plain, ((v2_funct_1 @ sk_C)),
% 2.03/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.24  thf('165', plain,
% 2.03/2.24      (((k5_relat_1 @ sk_C @ (k4_relat_1 @ sk_C))
% 2.03/2.24         = (k6_partfun1 @ (k1_relat_1 @ sk_C)))),
% 2.03/2.24      inference('demod', [status(thm)], ['161', '162', '163', '164'])).
% 2.03/2.24  thf('166', plain,
% 2.03/2.24      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.03/2.24         (~ (v1_relat_1 @ X17)
% 2.03/2.24          | ((k5_relat_1 @ (k5_relat_1 @ X18 @ X17) @ X19)
% 2.03/2.24              = (k5_relat_1 @ X18 @ (k5_relat_1 @ X17 @ X19)))
% 2.03/2.24          | ~ (v1_relat_1 @ X19)
% 2.03/2.24          | ~ (v1_relat_1 @ X18))),
% 2.03/2.24      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.03/2.24  thf('167', plain,
% 2.03/2.24      (![X0 : $i]:
% 2.03/2.24         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ X0)
% 2.03/2.24            = (k5_relat_1 @ sk_C @ (k5_relat_1 @ (k4_relat_1 @ sk_C) @ X0)))
% 2.03/2.24          | ~ (v1_relat_1 @ sk_C)
% 2.03/2.24          | ~ (v1_relat_1 @ X0)
% 2.03/2.24          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 2.03/2.24      inference('sup+', [status(thm)], ['165', '166'])).
% 2.03/2.24  thf('168', plain, ((v1_relat_1 @ sk_C)),
% 2.03/2.24      inference('demod', [status(thm)], ['28', '29'])).
% 2.03/2.24  thf('169', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 2.03/2.24      inference('demod', [status(thm)], ['53', '54', '55'])).
% 2.03/2.24  thf('170', plain,
% 2.03/2.24      (![X0 : $i]:
% 2.03/2.24         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ X0)
% 2.03/2.24            = (k5_relat_1 @ sk_C @ (k5_relat_1 @ (k4_relat_1 @ sk_C) @ X0)))
% 2.03/2.24          | ~ (v1_relat_1 @ X0))),
% 2.03/2.24      inference('demod', [status(thm)], ['167', '168', '169'])).
% 2.03/2.24  thf('171', plain,
% 2.03/2.24      (![X0 : $i]:
% 2.03/2.24         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ 
% 2.03/2.24            (k6_partfun1 @ X0))
% 2.03/2.24            = (k5_relat_1 @ sk_C @ 
% 2.03/2.24               (k4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ sk_C))))
% 2.03/2.24          | ~ (v1_relat_1 @ sk_C)
% 2.03/2.24          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 2.03/2.24      inference('sup+', [status(thm)], ['156', '170'])).
% 2.03/2.24  thf('172', plain,
% 2.03/2.24      (![X24 : $i, X25 : $i]:
% 2.03/2.24         (((k7_relat_1 @ X25 @ X24) = (k5_relat_1 @ (k6_partfun1 @ X24) @ X25))
% 2.03/2.24          | ~ (v1_relat_1 @ X25))),
% 2.03/2.24      inference('demod', [status(thm)], ['88', '89'])).
% 2.03/2.24  thf('173', plain,
% 2.03/2.24      (![X22 : $i]: ((k4_relat_1 @ (k6_partfun1 @ X22)) = (k6_partfun1 @ X22))),
% 2.03/2.24      inference('demod', [status(thm)], ['149', '150', '151'])).
% 2.03/2.24  thf('174', plain,
% 2.03/2.24      (![X22 : $i]: ((k4_relat_1 @ (k6_partfun1 @ X22)) = (k6_partfun1 @ X22))),
% 2.03/2.24      inference('demod', [status(thm)], ['149', '150', '151'])).
% 2.03/2.24  thf('175', plain,
% 2.03/2.24      (![X15 : $i, X16 : $i]:
% 2.03/2.24         (~ (v1_relat_1 @ X15)
% 2.03/2.24          | ((k4_relat_1 @ (k5_relat_1 @ X16 @ X15))
% 2.03/2.24              = (k5_relat_1 @ (k4_relat_1 @ X15) @ (k4_relat_1 @ X16)))
% 2.03/2.24          | ~ (v1_relat_1 @ X16))),
% 2.03/2.24      inference('cnf', [status(esa)], [t54_relat_1])).
% 2.03/2.24  thf('176', plain,
% 2.03/2.24      (![X0 : $i, X1 : $i]:
% 2.03/2.24         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0)))
% 2.03/2.24            = (k5_relat_1 @ (k6_partfun1 @ X0) @ (k4_relat_1 @ X1)))
% 2.03/2.24          | ~ (v1_relat_1 @ X1)
% 2.03/2.24          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 2.03/2.24      inference('sup+', [status(thm)], ['174', '175'])).
% 2.03/2.24  thf('177', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 2.03/2.24      inference('demod', [status(thm)], ['95', '96'])).
% 2.03/2.24  thf('178', plain,
% 2.03/2.24      (![X0 : $i, X1 : $i]:
% 2.03/2.24         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0)))
% 2.03/2.24            = (k5_relat_1 @ (k6_partfun1 @ X0) @ (k4_relat_1 @ X1)))
% 2.03/2.24          | ~ (v1_relat_1 @ X1))),
% 2.03/2.24      inference('demod', [status(thm)], ['176', '177'])).
% 2.03/2.24  thf('179', plain,
% 2.03/2.24      (![X0 : $i, X1 : $i]:
% 2.03/2.24         (((k4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X1)))
% 2.03/2.24            = (k5_relat_1 @ (k6_partfun1 @ X1) @ (k6_partfun1 @ X0)))
% 2.03/2.24          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 2.03/2.24      inference('sup+', [status(thm)], ['173', '178'])).
% 2.03/2.24  thf('180', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 2.03/2.24      inference('demod', [status(thm)], ['95', '96'])).
% 2.03/2.24  thf('181', plain,
% 2.03/2.24      (![X0 : $i, X1 : $i]:
% 2.03/2.24         ((k4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X1)))
% 2.03/2.24           = (k5_relat_1 @ (k6_partfun1 @ X1) @ (k6_partfun1 @ X0)))),
% 2.03/2.24      inference('demod', [status(thm)], ['179', '180'])).
% 2.03/2.24  thf('182', plain,
% 2.03/2.24      (![X0 : $i, X1 : $i]:
% 2.03/2.24         (((k4_relat_1 @ (k7_relat_1 @ (k6_partfun1 @ X1) @ X0))
% 2.03/2.24            = (k5_relat_1 @ (k6_partfun1 @ X1) @ (k6_partfun1 @ X0)))
% 2.03/2.24          | ~ (v1_relat_1 @ (k6_partfun1 @ X1)))),
% 2.03/2.24      inference('sup+', [status(thm)], ['172', '181'])).
% 2.03/2.24  thf('183', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 2.03/2.24      inference('demod', [status(thm)], ['95', '96'])).
% 2.03/2.24  thf('184', plain,
% 2.03/2.24      (![X0 : $i, X1 : $i]:
% 2.03/2.24         ((k4_relat_1 @ (k7_relat_1 @ (k6_partfun1 @ X1) @ X0))
% 2.03/2.24           = (k5_relat_1 @ (k6_partfun1 @ X1) @ (k6_partfun1 @ X0)))),
% 2.03/2.24      inference('demod', [status(thm)], ['182', '183'])).
% 2.03/2.24  thf('185', plain,
% 2.03/2.24      (![X24 : $i, X25 : $i]:
% 2.03/2.24         (((k7_relat_1 @ X25 @ X24) = (k5_relat_1 @ (k6_partfun1 @ X24) @ X25))
% 2.03/2.24          | ~ (v1_relat_1 @ X25))),
% 2.03/2.24      inference('demod', [status(thm)], ['88', '89'])).
% 2.03/2.24  thf('186', plain,
% 2.03/2.24      (![X0 : $i, X1 : $i]:
% 2.03/2.24         ((k4_relat_1 @ (k7_relat_1 @ (k6_partfun1 @ X1) @ X0))
% 2.03/2.24           = (k5_relat_1 @ (k6_partfun1 @ X1) @ (k6_partfun1 @ X0)))),
% 2.03/2.24      inference('demod', [status(thm)], ['182', '183'])).
% 2.03/2.24  thf('187', plain,
% 2.03/2.24      (![X0 : $i, X1 : $i]:
% 2.03/2.24         (((k4_relat_1 @ (k7_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 2.03/2.24            = (k7_relat_1 @ (k6_partfun1 @ X1) @ X0))
% 2.03/2.24          | ~ (v1_relat_1 @ (k6_partfun1 @ X1)))),
% 2.03/2.24      inference('sup+', [status(thm)], ['185', '186'])).
% 2.03/2.24  thf('188', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 2.03/2.24      inference('demod', [status(thm)], ['95', '96'])).
% 2.03/2.24  thf('189', plain,
% 2.03/2.24      (![X0 : $i, X1 : $i]:
% 2.03/2.24         ((k4_relat_1 @ (k7_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 2.03/2.24           = (k7_relat_1 @ (k6_partfun1 @ X1) @ X0))),
% 2.03/2.24      inference('demod', [status(thm)], ['187', '188'])).
% 2.03/2.24  thf('190', plain,
% 2.03/2.24      (![X0 : $i, X1 : $i]:
% 2.03/2.24         ((k7_relat_1 @ (k6_partfun1 @ X0) @ X1)
% 2.03/2.24           = (k5_relat_1 @ (k6_partfun1 @ X1) @ (k6_partfun1 @ X0)))),
% 2.03/2.24      inference('demod', [status(thm)], ['184', '189'])).
% 2.03/2.24  thf('191', plain, ((v1_relat_1 @ sk_C)),
% 2.03/2.24      inference('demod', [status(thm)], ['28', '29'])).
% 2.03/2.24  thf('192', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 2.03/2.24      inference('demod', [status(thm)], ['95', '96'])).
% 2.03/2.24  thf('193', plain,
% 2.03/2.24      (![X0 : $i]:
% 2.03/2.24         ((k7_relat_1 @ (k6_partfun1 @ X0) @ (k1_relat_1 @ sk_C))
% 2.03/2.24           = (k5_relat_1 @ sk_C @ 
% 2.03/2.24              (k4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ sk_C))))),
% 2.03/2.24      inference('demod', [status(thm)], ['171', '190', '191', '192'])).
% 2.03/2.24  thf('194', plain,
% 2.03/2.24      (((k7_relat_1 @ (k6_partfun1 @ sk_A) @ (k1_relat_1 @ sk_C))
% 2.03/2.24         = (k5_relat_1 @ sk_C @ (k4_relat_1 @ sk_C)))),
% 2.03/2.24      inference('sup+', [status(thm)], ['148', '193'])).
% 2.03/2.24  thf('195', plain,
% 2.03/2.24      (((k5_relat_1 @ sk_C @ (k4_relat_1 @ sk_C))
% 2.03/2.24         = (k6_partfun1 @ (k1_relat_1 @ sk_C)))),
% 2.03/2.24      inference('demod', [status(thm)], ['161', '162', '163', '164'])).
% 2.03/2.24  thf('196', plain,
% 2.03/2.24      (((k7_relat_1 @ (k6_partfun1 @ sk_A) @ (k1_relat_1 @ sk_C))
% 2.03/2.24         = (k6_partfun1 @ (k1_relat_1 @ sk_C)))),
% 2.03/2.24      inference('sup+', [status(thm)], ['194', '195'])).
% 2.03/2.24  thf('197', plain,
% 2.03/2.24      (![X0 : $i, X1 : $i]:
% 2.03/2.24         ((k7_relat_1 @ (k6_partfun1 @ X0) @ X1)
% 2.03/2.24           = (k5_relat_1 @ (k6_partfun1 @ X1) @ (k6_partfun1 @ X0)))),
% 2.03/2.24      inference('demod', [status(thm)], ['184', '189'])).
% 2.03/2.24  thf('198', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 2.03/2.24      inference('demod', [status(thm)], ['32', '33', '34'])).
% 2.03/2.24  thf(t55_funct_1, axiom,
% 2.03/2.24    (![A:$i]:
% 2.03/2.24     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.03/2.24       ( ( v2_funct_1 @ A ) =>
% 2.03/2.24         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 2.03/2.24           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 2.03/2.24  thf('199', plain,
% 2.03/2.24      (![X32 : $i]:
% 2.03/2.24         (~ (v2_funct_1 @ X32)
% 2.03/2.24          | ((k1_relat_1 @ X32) = (k2_relat_1 @ (k2_funct_1 @ X32)))
% 2.03/2.24          | ~ (v1_funct_1 @ X32)
% 2.03/2.24          | ~ (v1_relat_1 @ X32))),
% 2.03/2.24      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.03/2.24  thf('200', plain,
% 2.03/2.24      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 2.03/2.24        | ~ (v1_relat_1 @ sk_C)
% 2.03/2.24        | ~ (v1_funct_1 @ sk_C)
% 2.03/2.24        | ~ (v2_funct_1 @ sk_C))),
% 2.03/2.24      inference('sup+', [status(thm)], ['198', '199'])).
% 2.03/2.24  thf('201', plain, ((v1_relat_1 @ sk_C)),
% 2.03/2.24      inference('demod', [status(thm)], ['28', '29'])).
% 2.03/2.24  thf('202', plain, ((v1_funct_1 @ sk_C)),
% 2.03/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.24  thf('203', plain, ((v2_funct_1 @ sk_C)),
% 2.03/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.24  thf('204', plain,
% 2.03/2.24      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 2.03/2.24      inference('demod', [status(thm)], ['200', '201', '202', '203'])).
% 2.03/2.24  thf('205', plain,
% 2.03/2.24      (![X23 : $i]:
% 2.03/2.24         (((k5_relat_1 @ X23 @ (k6_partfun1 @ (k2_relat_1 @ X23))) = (X23))
% 2.03/2.24          | ~ (v1_relat_1 @ X23))),
% 2.03/2.24      inference('demod', [status(thm)], ['73', '74'])).
% 2.03/2.24  thf('206', plain,
% 2.03/2.24      ((((k5_relat_1 @ (k4_relat_1 @ sk_C) @ 
% 2.03/2.24          (k6_partfun1 @ (k1_relat_1 @ sk_C))) = (k4_relat_1 @ sk_C))
% 2.03/2.24        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 2.03/2.24      inference('sup+', [status(thm)], ['204', '205'])).
% 2.03/2.24  thf('207', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 2.03/2.24      inference('demod', [status(thm)], ['53', '54', '55'])).
% 2.03/2.24  thf('208', plain,
% 2.03/2.24      (((k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 2.03/2.24         = (k4_relat_1 @ sk_C))),
% 2.03/2.24      inference('demod', [status(thm)], ['206', '207'])).
% 2.03/2.24  thf('209', plain,
% 2.03/2.24      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.03/2.24         (~ (v1_relat_1 @ X17)
% 2.03/2.24          | ((k5_relat_1 @ (k5_relat_1 @ X18 @ X17) @ X19)
% 2.03/2.24              = (k5_relat_1 @ X18 @ (k5_relat_1 @ X17 @ X19)))
% 2.03/2.24          | ~ (v1_relat_1 @ X19)
% 2.03/2.24          | ~ (v1_relat_1 @ X18))),
% 2.03/2.24      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.03/2.24  thf('210', plain,
% 2.03/2.24      (![X0 : $i]:
% 2.03/2.24         (((k5_relat_1 @ (k4_relat_1 @ sk_C) @ X0)
% 2.03/2.24            = (k5_relat_1 @ (k4_relat_1 @ sk_C) @ 
% 2.03/2.24               (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ X0)))
% 2.03/2.24          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 2.03/2.24          | ~ (v1_relat_1 @ X0)
% 2.03/2.24          | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C))))),
% 2.03/2.24      inference('sup+', [status(thm)], ['208', '209'])).
% 2.03/2.24  thf('211', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 2.03/2.24      inference('demod', [status(thm)], ['53', '54', '55'])).
% 2.03/2.24  thf('212', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 2.03/2.24      inference('demod', [status(thm)], ['95', '96'])).
% 2.03/2.24  thf('213', plain,
% 2.03/2.24      (![X0 : $i]:
% 2.03/2.24         (((k5_relat_1 @ (k4_relat_1 @ sk_C) @ X0)
% 2.03/2.24            = (k5_relat_1 @ (k4_relat_1 @ sk_C) @ 
% 2.03/2.24               (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ X0)))
% 2.03/2.24          | ~ (v1_relat_1 @ X0))),
% 2.03/2.24      inference('demod', [status(thm)], ['210', '211', '212'])).
% 2.03/2.24  thf('214', plain,
% 2.03/2.24      (![X0 : $i]:
% 2.03/2.24         (((k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_partfun1 @ X0))
% 2.03/2.24            = (k5_relat_1 @ (k4_relat_1 @ sk_C) @ 
% 2.03/2.24               (k7_relat_1 @ (k6_partfun1 @ X0) @ (k1_relat_1 @ sk_C))))
% 2.03/2.24          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 2.03/2.24      inference('sup+', [status(thm)], ['197', '213'])).
% 2.03/2.24  thf('215', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 2.03/2.24      inference('demod', [status(thm)], ['95', '96'])).
% 2.03/2.24  thf('216', plain,
% 2.03/2.24      (![X0 : $i]:
% 2.03/2.24         ((k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_partfun1 @ X0))
% 2.03/2.24           = (k5_relat_1 @ (k4_relat_1 @ sk_C) @ 
% 2.03/2.24              (k7_relat_1 @ (k6_partfun1 @ X0) @ (k1_relat_1 @ sk_C))))),
% 2.03/2.24      inference('demod', [status(thm)], ['214', '215'])).
% 2.03/2.24  thf('217', plain,
% 2.03/2.24      (((k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 2.03/2.24         = (k5_relat_1 @ (k4_relat_1 @ sk_C) @ 
% 2.03/2.24            (k6_partfun1 @ (k1_relat_1 @ sk_C))))),
% 2.03/2.24      inference('sup+', [status(thm)], ['196', '216'])).
% 2.03/2.24  thf('218', plain,
% 2.03/2.24      (((k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 2.03/2.24         = (k4_relat_1 @ sk_C))),
% 2.03/2.24      inference('demod', [status(thm)], ['206', '207'])).
% 2.03/2.24  thf('219', plain,
% 2.03/2.24      (((k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 2.03/2.24         = (k4_relat_1 @ sk_C))),
% 2.03/2.24      inference('sup+', [status(thm)], ['217', '218'])).
% 2.03/2.24  thf('220', plain, ((v1_relat_1 @ sk_D)),
% 2.03/2.24      inference('demod', [status(thm)], ['67', '68'])).
% 2.03/2.24  thf('221', plain, (((sk_D) = (k4_relat_1 @ sk_C))),
% 2.03/2.24      inference('demod', [status(thm)], ['59', '106', '219', '220'])).
% 2.03/2.24  thf('222', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 2.03/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.24  thf('223', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 2.03/2.24      inference('demod', [status(thm)], ['32', '33', '34'])).
% 2.03/2.24  thf('224', plain, (((sk_D) != (k4_relat_1 @ sk_C))),
% 2.03/2.24      inference('demod', [status(thm)], ['222', '223'])).
% 2.03/2.24  thf('225', plain, ($false),
% 2.03/2.24      inference('simplify_reflect-', [status(thm)], ['221', '224'])).
% 2.03/2.24  
% 2.03/2.24  % SZS output end Refutation
% 2.03/2.24  
% 2.03/2.24  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

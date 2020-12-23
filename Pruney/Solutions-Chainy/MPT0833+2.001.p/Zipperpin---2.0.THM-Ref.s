%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.x4uASjaX6a

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:33 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   74 (  89 expanded)
%              Number of leaves         :   30 (  39 expanded)
%              Depth                    :   15
%              Number of atoms          :  492 ( 732 expanded)
%              Number of equality atoms :   29 (  32 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_relset_1_type,type,(
    k6_relset_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(t36_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( r1_tarski @ B @ C )
       => ( r2_relset_1 @ A @ B @ ( k6_relset_1 @ A @ B @ C @ D ) @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
       => ( ( r1_tarski @ B @ C )
         => ( r2_relset_1 @ A @ B @ ( k6_relset_1 @ A @ B @ C @ D ) @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_relset_1])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k6_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k6_relset_1 @ A @ B @ C @ D )
        = ( k8_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( ( k6_relset_1 @ X45 @ X46 @ X43 @ X44 )
        = ( k8_relat_1 @ X43 @ X44 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k6_relset_1 @ sk_A @ sk_B @ X0 @ sk_D )
      = ( k8_relat_1 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k8_relat_1 @ sk_C @ sk_D ) @ sk_D ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X37 @ X38 @ X39 ) @ ( k1_zfmisc_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('7',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('9',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) @ sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( ( k2_relset_1 @ X41 @ X42 @ X40 )
        = ( k2_relat_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('12',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['9','12'])).

thf(t37_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('15',plain,
    ( ( k4_xboole_0 @ ( k2_relat_1 @ sk_D ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t117_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ C @ B )
     => ( ( k4_xboole_0 @ A @ C )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) )
      | ~ ( r1_tarski @ X2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t117_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ sk_B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_C @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('20',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ ( k4_xboole_0 @ X0 @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_relat_1 @ sk_D ) @ sk_C ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['15','22'])).

thf('24',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('25',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ sk_D ) @ sk_C ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ sk_D ) @ sk_C ) @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['25'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('27',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('28',plain,
    ( ( k4_xboole_0 @ ( k2_relat_1 @ sk_D ) @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('30',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference(simplify,[status(thm)],['30'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('32',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X32 ) @ X33 )
      | ( ( k8_relat_1 @ X33 @ X32 )
        = X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k8_relat_1 @ sk_C @ sk_D )
      = sk_D ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('35',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v1_relat_1 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('36',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k8_relat_1 @ sk_C @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('39',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ( r2_relset_1 @ X48 @ X49 @ X47 @ X50 )
      | ( X47 != X50 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('40',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( r2_relset_1 @ X48 @ X49 @ X50 @ X50 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['4','37','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.x4uASjaX6a
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:43:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.55  % Solved by: fo/fo7.sh
% 0.36/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.55  % done 274 iterations in 0.106s
% 0.36/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.55  % SZS output start Refutation
% 0.36/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.36/0.55  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.36/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.55  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.36/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.55  thf(k6_relset_1_type, type, k6_relset_1: $i > $i > $i > $i > $i).
% 0.36/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.36/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.55  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.36/0.55  thf(t36_relset_1, conjecture,
% 0.36/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.55       ( ( r1_tarski @ B @ C ) =>
% 0.36/0.55         ( r2_relset_1 @ A @ B @ ( k6_relset_1 @ A @ B @ C @ D ) @ D ) ) ))).
% 0.36/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.55    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.55        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.55          ( ( r1_tarski @ B @ C ) =>
% 0.36/0.55            ( r2_relset_1 @ A @ B @ ( k6_relset_1 @ A @ B @ C @ D ) @ D ) ) ) )),
% 0.36/0.55    inference('cnf.neg', [status(esa)], [t36_relset_1])).
% 0.36/0.55  thf('0', plain,
% 0.36/0.55      (~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.36/0.55          (k6_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('1', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(redefinition_k6_relset_1, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.55       ( ( k6_relset_1 @ A @ B @ C @ D ) = ( k8_relat_1 @ C @ D ) ) ))).
% 0.36/0.55  thf('2', plain,
% 0.36/0.55      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.36/0.55         (((k6_relset_1 @ X45 @ X46 @ X43 @ X44) = (k8_relat_1 @ X43 @ X44))
% 0.36/0.55          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46))))),
% 0.36/0.55      inference('cnf', [status(esa)], [redefinition_k6_relset_1])).
% 0.36/0.55  thf('3', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((k6_relset_1 @ sk_A @ sk_B @ X0 @ sk_D) = (k8_relat_1 @ X0 @ sk_D))),
% 0.36/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.55  thf('4', plain,
% 0.36/0.55      (~ (r2_relset_1 @ sk_A @ sk_B @ (k8_relat_1 @ sk_C @ sk_D) @ sk_D)),
% 0.36/0.55      inference('demod', [status(thm)], ['0', '3'])).
% 0.36/0.55  thf('5', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(dt_k2_relset_1, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.55       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.36/0.55  thf('6', plain,
% 0.36/0.55      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.36/0.55         ((m1_subset_1 @ (k2_relset_1 @ X37 @ X38 @ X39) @ (k1_zfmisc_1 @ X38))
% 0.36/0.55          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.36/0.55  thf('7', plain,
% 0.36/0.55      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_D) @ (k1_zfmisc_1 @ sk_B))),
% 0.36/0.55      inference('sup-', [status(thm)], ['5', '6'])).
% 0.36/0.55  thf(t3_subset, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.55  thf('8', plain,
% 0.36/0.55      (![X20 : $i, X21 : $i]:
% 0.36/0.55         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 0.36/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.55  thf('9', plain, ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B @ sk_D) @ sk_B)),
% 0.36/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.55  thf('10', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(redefinition_k2_relset_1, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.55       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.36/0.55  thf('11', plain,
% 0.36/0.55      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.36/0.55         (((k2_relset_1 @ X41 @ X42 @ X40) = (k2_relat_1 @ X40))
% 0.36/0.55          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42))))),
% 0.36/0.55      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.36/0.55  thf('12', plain,
% 0.36/0.55      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.36/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.36/0.55  thf('13', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 0.36/0.55      inference('demod', [status(thm)], ['9', '12'])).
% 0.36/0.55  thf(t37_xboole_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.55  thf('14', plain,
% 0.36/0.55      (![X3 : $i, X5 : $i]:
% 0.36/0.55         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.36/0.55      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.36/0.55  thf('15', plain,
% 0.36/0.55      (((k4_xboole_0 @ (k2_relat_1 @ sk_D) @ sk_B) = (k1_xboole_0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.36/0.55  thf('16', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(t117_xboole_1, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( r1_tarski @ C @ B ) =>
% 0.36/0.55       ( ( k4_xboole_0 @ A @ C ) =
% 0.36/0.55         ( k2_xboole_0 @
% 0.36/0.55           ( k4_xboole_0 @ A @ B ) @ 
% 0.36/0.55           ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) ) ))).
% 0.36/0.55  thf('17', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.55         (((k4_xboole_0 @ X0 @ X2)
% 0.36/0.55            = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 0.36/0.55               (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))))
% 0.36/0.55          | ~ (r1_tarski @ X2 @ X1))),
% 0.36/0.55      inference('cnf', [status(esa)], [t117_xboole_1])).
% 0.36/0.55  thf('18', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((k4_xboole_0 @ X0 @ sk_B)
% 0.36/0.55           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ 
% 0.36/0.55              (k3_xboole_0 @ X0 @ (k4_xboole_0 @ sk_C @ sk_B))))),
% 0.36/0.55      inference('sup-', [status(thm)], ['16', '17'])).
% 0.36/0.55  thf(t7_xboole_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.36/0.55  thf('19', plain,
% 0.36/0.55      (![X13 : $i, X14 : $i]: (r1_tarski @ X13 @ (k2_xboole_0 @ X13 @ X14))),
% 0.36/0.55      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.36/0.55  thf('20', plain,
% 0.36/0.55      (![X3 : $i, X5 : $i]:
% 0.36/0.55         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.36/0.55      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.36/0.55  thf('21', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['19', '20'])).
% 0.36/0.55  thf('22', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ (k4_xboole_0 @ X0 @ sk_B))
% 0.36/0.55           = (k1_xboole_0))),
% 0.36/0.55      inference('sup+', [status(thm)], ['18', '21'])).
% 0.36/0.55  thf('23', plain,
% 0.36/0.55      (((k4_xboole_0 @ (k4_xboole_0 @ (k2_relat_1 @ sk_D) @ sk_C) @ k1_xboole_0)
% 0.36/0.55         = (k1_xboole_0))),
% 0.36/0.55      inference('sup+', [status(thm)], ['15', '22'])).
% 0.36/0.55  thf('24', plain,
% 0.36/0.55      (![X3 : $i, X4 : $i]:
% 0.36/0.55         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.36/0.55      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.36/0.55  thf('25', plain,
% 0.36/0.55      ((((k1_xboole_0) != (k1_xboole_0))
% 0.36/0.55        | (r1_tarski @ (k4_xboole_0 @ (k2_relat_1 @ sk_D) @ sk_C) @ k1_xboole_0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['23', '24'])).
% 0.36/0.55  thf('26', plain,
% 0.36/0.55      ((r1_tarski @ (k4_xboole_0 @ (k2_relat_1 @ sk_D) @ sk_C) @ k1_xboole_0)),
% 0.36/0.55      inference('simplify', [status(thm)], ['25'])).
% 0.36/0.55  thf(t3_xboole_1, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.36/0.55  thf('27', plain,
% 0.36/0.55      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ k1_xboole_0))),
% 0.36/0.55      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.36/0.55  thf('28', plain,
% 0.36/0.55      (((k4_xboole_0 @ (k2_relat_1 @ sk_D) @ sk_C) = (k1_xboole_0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.36/0.55  thf('29', plain,
% 0.36/0.55      (![X3 : $i, X4 : $i]:
% 0.36/0.55         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.36/0.55      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.36/0.55  thf('30', plain,
% 0.36/0.55      ((((k1_xboole_0) != (k1_xboole_0))
% 0.36/0.55        | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C))),
% 0.36/0.55      inference('sup-', [status(thm)], ['28', '29'])).
% 0.36/0.55  thf('31', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 0.36/0.55      inference('simplify', [status(thm)], ['30'])).
% 0.36/0.55  thf(t125_relat_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( v1_relat_1 @ B ) =>
% 0.36/0.55       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.36/0.55         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.36/0.55  thf('32', plain,
% 0.36/0.55      (![X32 : $i, X33 : $i]:
% 0.36/0.55         (~ (r1_tarski @ (k2_relat_1 @ X32) @ X33)
% 0.36/0.55          | ((k8_relat_1 @ X33 @ X32) = (X32))
% 0.36/0.55          | ~ (v1_relat_1 @ X32))),
% 0.36/0.55      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.36/0.55  thf('33', plain,
% 0.36/0.55      ((~ (v1_relat_1 @ sk_D) | ((k8_relat_1 @ sk_C @ sk_D) = (sk_D)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['31', '32'])).
% 0.36/0.55  thf('34', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(cc1_relset_1, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.55       ( v1_relat_1 @ C ) ))).
% 0.36/0.55  thf('35', plain,
% 0.36/0.55      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.36/0.55         ((v1_relat_1 @ X34)
% 0.36/0.55          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.36/0.55      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.36/0.55  thf('36', plain, ((v1_relat_1 @ sk_D)),
% 0.36/0.55      inference('sup-', [status(thm)], ['34', '35'])).
% 0.36/0.55  thf('37', plain, (((k8_relat_1 @ sk_C @ sk_D) = (sk_D))),
% 0.36/0.55      inference('demod', [status(thm)], ['33', '36'])).
% 0.36/0.55  thf('38', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(redefinition_r2_relset_1, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.55     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.36/0.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.55       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.36/0.55  thf('39', plain,
% 0.36/0.55      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 0.36/0.55          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 0.36/0.55          | (r2_relset_1 @ X48 @ X49 @ X47 @ X50)
% 0.36/0.55          | ((X47) != (X50)))),
% 0.36/0.55      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.36/0.55  thf('40', plain,
% 0.36/0.55      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.36/0.55         ((r2_relset_1 @ X48 @ X49 @ X50 @ X50)
% 0.36/0.55          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49))))),
% 0.36/0.55      inference('simplify', [status(thm)], ['39'])).
% 0.36/0.55  thf('41', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D)),
% 0.36/0.55      inference('sup-', [status(thm)], ['38', '40'])).
% 0.36/0.55  thf('42', plain, ($false),
% 0.36/0.55      inference('demod', [status(thm)], ['4', '37', '41'])).
% 0.36/0.55  
% 0.36/0.55  % SZS output end Refutation
% 0.36/0.55  
% 0.36/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

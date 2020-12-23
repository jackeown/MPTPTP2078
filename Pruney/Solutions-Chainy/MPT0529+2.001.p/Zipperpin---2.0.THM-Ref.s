%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KfW6oG1aBR

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:39 EST 2020

% Result     : Theorem 0.72s
% Output     : Refutation 0.72s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 100 expanded)
%              Number of leaves         :   31 (  42 expanded)
%              Depth                    :   14
%              Number of atoms          :  543 ( 689 expanded)
%              Number of equality atoms :   36 (  48 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('0',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_tarski @ X9 @ X8 )
      = ( k2_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X37 @ X38 ) )
      = ( k3_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X37 @ X38 ) )
      = ( k3_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t129_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) )
          = ( k8_relat_1 @ A @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) )
            = ( k8_relat_1 @ A @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t129_relat_1])).

thf('5',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t119_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('6',plain,(
    ! [X47: $i,X48: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X48 @ X47 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X47 ) @ X48 ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('7',plain,(
    ! [X54: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X54 ) )
      = X54 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t118_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X45: $i,X46: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X45 @ X46 ) ) @ ( k2_relat_1 @ X46 ) )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t118_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('10',plain,(
    ! [X44: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ ( k2_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X54: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X54 ) )
      = X54 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('14',plain,(
    ! [X44: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('16',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['5','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['4','20'])).

thf('22',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X47: $i,X48: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X48 @ X47 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X47 ) @ X48 ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('26',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('29',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X51 ) @ X52 )
      | ( ( k8_relat_1 @ X52 @ X51 )
        = X51 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k8_relat_1 @ ( k2_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 ) @ X1 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ ( k2_xboole_0 @ ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 ) @ X2 ) @ ( k8_relat_1 @ X0 @ X1 ) )
        = ( k8_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['24','30'])).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('32',plain,(
    ! [X49: $i,X50: $i] :
      ( ( ( k8_relat_1 @ X50 @ X49 )
        = ( k5_relat_1 @ X49 @ ( k6_relat_1 @ X50 ) ) )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('33',plain,(
    ! [X55: $i,X56: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X55 @ ( k6_relat_1 @ X56 ) ) @ X55 )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('34',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_xboole_0 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('37',plain,(
    ! [X39: $i,X41: $i] :
      ( ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X41 ) )
      | ~ ( r1_tarski @ X39 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('39',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X43 ) )
      | ( v1_relat_1 @ X42 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k8_relat_1 @ ( k2_xboole_0 @ ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 ) @ X2 ) @ ( k8_relat_1 @ X0 @ X1 ) )
        = ( k8_relat_1 @ X0 @ X1 ) ) ) ),
    inference(clc,[status(thm)],['31','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ X0 ) )
        = ( k8_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','45'])).

thf('47',plain,(
    ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
 != ( k8_relat_1 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( ( k8_relat_1 @ sk_A @ sk_C )
     != ( k8_relat_1 @ sk_A @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ( k8_relat_1 @ sk_A @ sk_C )
 != ( k8_relat_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    $false ),
    inference(simplify,[status(thm)],['50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KfW6oG1aBR
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:03:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.72/0.89  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.72/0.89  % Solved by: fo/fo7.sh
% 0.72/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.72/0.89  % done 1237 iterations in 0.434s
% 0.72/0.89  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.72/0.89  % SZS output start Refutation
% 0.72/0.89  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.72/0.89  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.72/0.89  thf(sk_B_type, type, sk_B: $i).
% 0.72/0.89  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.72/0.89  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.72/0.89  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.72/0.89  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.72/0.89  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.72/0.89  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.72/0.89  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.72/0.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.72/0.89  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.72/0.89  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.72/0.89  thf(sk_C_type, type, sk_C: $i).
% 0.72/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.72/0.89  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.72/0.89  thf(commutativity_k2_tarski, axiom,
% 0.72/0.89    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.72/0.89  thf('0', plain,
% 0.72/0.89      (![X8 : $i, X9 : $i]: ((k2_tarski @ X9 @ X8) = (k2_tarski @ X8 @ X9))),
% 0.72/0.89      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.72/0.89  thf(t12_setfam_1, axiom,
% 0.72/0.89    (![A:$i,B:$i]:
% 0.72/0.89     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.72/0.89  thf('1', plain,
% 0.72/0.89      (![X37 : $i, X38 : $i]:
% 0.72/0.89         ((k1_setfam_1 @ (k2_tarski @ X37 @ X38)) = (k3_xboole_0 @ X37 @ X38))),
% 0.72/0.89      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.72/0.89  thf('2', plain,
% 0.72/0.89      (![X0 : $i, X1 : $i]:
% 0.72/0.89         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.72/0.89      inference('sup+', [status(thm)], ['0', '1'])).
% 0.72/0.89  thf('3', plain,
% 0.72/0.89      (![X37 : $i, X38 : $i]:
% 0.72/0.89         ((k1_setfam_1 @ (k2_tarski @ X37 @ X38)) = (k3_xboole_0 @ X37 @ X38))),
% 0.72/0.89      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.72/0.89  thf('4', plain,
% 0.72/0.89      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.72/0.89      inference('sup+', [status(thm)], ['2', '3'])).
% 0.72/0.89  thf(t129_relat_1, conjecture,
% 0.72/0.89    (![A:$i,B:$i,C:$i]:
% 0.72/0.89     ( ( v1_relat_1 @ C ) =>
% 0.72/0.89       ( ( r1_tarski @ A @ B ) =>
% 0.72/0.89         ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) = ( k8_relat_1 @ A @ C ) ) ) ))).
% 0.72/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.72/0.89    (~( ![A:$i,B:$i,C:$i]:
% 0.72/0.89        ( ( v1_relat_1 @ C ) =>
% 0.72/0.89          ( ( r1_tarski @ A @ B ) =>
% 0.72/0.89            ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) =
% 0.72/0.89              ( k8_relat_1 @ A @ C ) ) ) ) )),
% 0.72/0.89    inference('cnf.neg', [status(esa)], [t129_relat_1])).
% 0.72/0.89  thf('5', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.89  thf(t119_relat_1, axiom,
% 0.72/0.89    (![A:$i,B:$i]:
% 0.72/0.89     ( ( v1_relat_1 @ B ) =>
% 0.72/0.89       ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) =
% 0.72/0.89         ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.72/0.89  thf('6', plain,
% 0.72/0.89      (![X47 : $i, X48 : $i]:
% 0.72/0.89         (((k2_relat_1 @ (k8_relat_1 @ X48 @ X47))
% 0.72/0.89            = (k3_xboole_0 @ (k2_relat_1 @ X47) @ X48))
% 0.72/0.89          | ~ (v1_relat_1 @ X47))),
% 0.72/0.89      inference('cnf', [status(esa)], [t119_relat_1])).
% 0.72/0.89  thf(t71_relat_1, axiom,
% 0.72/0.89    (![A:$i]:
% 0.72/0.89     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.72/0.89       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.72/0.89  thf('7', plain, (![X54 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X54)) = (X54))),
% 0.72/0.89      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.72/0.89  thf(t118_relat_1, axiom,
% 0.72/0.89    (![A:$i,B:$i]:
% 0.72/0.89     ( ( v1_relat_1 @ B ) =>
% 0.72/0.89       ( r1_tarski @
% 0.72/0.89         ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ))).
% 0.72/0.89  thf('8', plain,
% 0.72/0.89      (![X45 : $i, X46 : $i]:
% 0.72/0.89         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X45 @ X46)) @ 
% 0.72/0.89           (k2_relat_1 @ X46))
% 0.72/0.89          | ~ (v1_relat_1 @ X46))),
% 0.72/0.89      inference('cnf', [status(esa)], [t118_relat_1])).
% 0.72/0.89  thf('9', plain,
% 0.72/0.89      (![X0 : $i, X1 : $i]:
% 0.72/0.89         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.72/0.89           X0)
% 0.72/0.89          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.72/0.89      inference('sup+', [status(thm)], ['7', '8'])).
% 0.72/0.89  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.72/0.89  thf('10', plain, (![X44 : $i]: (v1_relat_1 @ (k6_relat_1 @ X44))),
% 0.72/0.89      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.72/0.89  thf('11', plain,
% 0.72/0.89      (![X0 : $i, X1 : $i]:
% 0.72/0.89         (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ X0)),
% 0.72/0.89      inference('demod', [status(thm)], ['9', '10'])).
% 0.72/0.89  thf('12', plain,
% 0.72/0.89      (![X0 : $i, X1 : $i]:
% 0.72/0.89         ((r1_tarski @ (k3_xboole_0 @ (k2_relat_1 @ (k6_relat_1 @ X1)) @ X0) @ 
% 0.72/0.89           X1)
% 0.72/0.89          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.72/0.89      inference('sup+', [status(thm)], ['6', '11'])).
% 0.72/0.89  thf('13', plain, (![X54 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X54)) = (X54))),
% 0.72/0.89      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.72/0.89  thf('14', plain, (![X44 : $i]: (v1_relat_1 @ (k6_relat_1 @ X44))),
% 0.72/0.89      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.72/0.89  thf('15', plain,
% 0.72/0.89      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.72/0.89      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.72/0.89  thf(t12_xboole_1, axiom,
% 0.72/0.89    (![A:$i,B:$i]:
% 0.72/0.89     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.72/0.89  thf('16', plain,
% 0.72/0.89      (![X6 : $i, X7 : $i]:
% 0.72/0.89         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.72/0.89      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.72/0.89  thf('17', plain,
% 0.72/0.89      (![X0 : $i, X1 : $i]:
% 0.72/0.89         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.72/0.89      inference('sup-', [status(thm)], ['15', '16'])).
% 0.72/0.89  thf(t11_xboole_1, axiom,
% 0.72/0.89    (![A:$i,B:$i,C:$i]:
% 0.72/0.89     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.72/0.89  thf('18', plain,
% 0.72/0.89      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.72/0.89         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 0.72/0.89      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.72/0.89  thf('19', plain,
% 0.72/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.89         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ (k3_xboole_0 @ X0 @ X2) @ X1))),
% 0.72/0.89      inference('sup-', [status(thm)], ['17', '18'])).
% 0.72/0.89  thf('20', plain,
% 0.72/0.89      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ sk_B)),
% 0.72/0.89      inference('sup-', [status(thm)], ['5', '19'])).
% 0.72/0.89  thf('21', plain,
% 0.72/0.89      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ sk_B)),
% 0.72/0.90      inference('sup+', [status(thm)], ['4', '20'])).
% 0.72/0.90  thf('22', plain,
% 0.72/0.90      (![X6 : $i, X7 : $i]:
% 0.72/0.90         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.72/0.90      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.72/0.90  thf('23', plain,
% 0.72/0.90      (![X0 : $i]: ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ sk_A) @ sk_B) = (sk_B))),
% 0.72/0.90      inference('sup-', [status(thm)], ['21', '22'])).
% 0.72/0.90  thf('24', plain,
% 0.72/0.90      (![X47 : $i, X48 : $i]:
% 0.72/0.90         (((k2_relat_1 @ (k8_relat_1 @ X48 @ X47))
% 0.72/0.90            = (k3_xboole_0 @ (k2_relat_1 @ X47) @ X48))
% 0.72/0.90          | ~ (v1_relat_1 @ X47))),
% 0.72/0.90      inference('cnf', [status(esa)], [t119_relat_1])).
% 0.72/0.90  thf(d10_xboole_0, axiom,
% 0.72/0.90    (![A:$i,B:$i]:
% 0.72/0.90     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.72/0.90  thf('25', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.72/0.90      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.72/0.90  thf('26', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.72/0.90      inference('simplify', [status(thm)], ['25'])).
% 0.72/0.90  thf('27', plain,
% 0.72/0.90      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.72/0.90         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 0.72/0.90      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.72/0.90  thf('28', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.72/0.90      inference('sup-', [status(thm)], ['26', '27'])).
% 0.72/0.90  thf(t125_relat_1, axiom,
% 0.72/0.90    (![A:$i,B:$i]:
% 0.72/0.90     ( ( v1_relat_1 @ B ) =>
% 0.72/0.90       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.72/0.90         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.72/0.90  thf('29', plain,
% 0.72/0.90      (![X51 : $i, X52 : $i]:
% 0.72/0.90         (~ (r1_tarski @ (k2_relat_1 @ X51) @ X52)
% 0.72/0.90          | ((k8_relat_1 @ X52 @ X51) = (X51))
% 0.72/0.90          | ~ (v1_relat_1 @ X51))),
% 0.72/0.90      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.72/0.90  thf('30', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         (~ (v1_relat_1 @ X1)
% 0.72/0.90          | ((k8_relat_1 @ (k2_xboole_0 @ (k2_relat_1 @ X1) @ X0) @ X1) = (X1)))),
% 0.72/0.90      inference('sup-', [status(thm)], ['28', '29'])).
% 0.72/0.90  thf('31', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.90         (((k8_relat_1 @ 
% 0.72/0.90            (k2_xboole_0 @ (k3_xboole_0 @ (k2_relat_1 @ X1) @ X0) @ X2) @ 
% 0.72/0.90            (k8_relat_1 @ X0 @ X1)) = (k8_relat_1 @ X0 @ X1))
% 0.72/0.90          | ~ (v1_relat_1 @ X1)
% 0.72/0.90          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ X1)))),
% 0.72/0.90      inference('sup+', [status(thm)], ['24', '30'])).
% 0.72/0.90  thf(t123_relat_1, axiom,
% 0.72/0.90    (![A:$i,B:$i]:
% 0.72/0.90     ( ( v1_relat_1 @ B ) =>
% 0.72/0.90       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.72/0.90  thf('32', plain,
% 0.72/0.90      (![X49 : $i, X50 : $i]:
% 0.72/0.90         (((k8_relat_1 @ X50 @ X49) = (k5_relat_1 @ X49 @ (k6_relat_1 @ X50)))
% 0.72/0.90          | ~ (v1_relat_1 @ X49))),
% 0.72/0.90      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.72/0.90  thf(t76_relat_1, axiom,
% 0.72/0.90    (![A:$i,B:$i]:
% 0.72/0.90     ( ( v1_relat_1 @ B ) =>
% 0.72/0.90       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 0.72/0.90         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 0.72/0.90  thf('33', plain,
% 0.72/0.90      (![X55 : $i, X56 : $i]:
% 0.72/0.90         ((r1_tarski @ (k5_relat_1 @ X55 @ (k6_relat_1 @ X56)) @ X55)
% 0.72/0.90          | ~ (v1_relat_1 @ X55))),
% 0.72/0.90      inference('cnf', [status(esa)], [t76_relat_1])).
% 0.72/0.90  thf('34', plain,
% 0.72/0.90      (![X6 : $i, X7 : $i]:
% 0.72/0.90         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.72/0.90      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.72/0.90  thf('35', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         (~ (v1_relat_1 @ X0)
% 0.72/0.90          | ((k2_xboole_0 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)) @ X0) = (X0)))),
% 0.72/0.90      inference('sup-', [status(thm)], ['33', '34'])).
% 0.72/0.90  thf('36', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.72/0.90      inference('sup-', [status(thm)], ['26', '27'])).
% 0.72/0.90  thf(t3_subset, axiom,
% 0.72/0.90    (![A:$i,B:$i]:
% 0.72/0.90     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.72/0.90  thf('37', plain,
% 0.72/0.90      (![X39 : $i, X41 : $i]:
% 0.72/0.90         ((m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X41)) | ~ (r1_tarski @ X39 @ X41))),
% 0.72/0.90      inference('cnf', [status(esa)], [t3_subset])).
% 0.72/0.90  thf('38', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.72/0.90      inference('sup-', [status(thm)], ['36', '37'])).
% 0.72/0.90  thf(cc2_relat_1, axiom,
% 0.72/0.90    (![A:$i]:
% 0.72/0.90     ( ( v1_relat_1 @ A ) =>
% 0.72/0.90       ( ![B:$i]:
% 0.72/0.90         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.72/0.90  thf('39', plain,
% 0.72/0.90      (![X42 : $i, X43 : $i]:
% 0.72/0.90         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X43))
% 0.72/0.90          | (v1_relat_1 @ X42)
% 0.72/0.90          | ~ (v1_relat_1 @ X43))),
% 0.72/0.90      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.72/0.90  thf('40', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         (~ (v1_relat_1 @ (k2_xboole_0 @ X1 @ X0)) | (v1_relat_1 @ X1))),
% 0.72/0.90      inference('sup-', [status(thm)], ['38', '39'])).
% 0.72/0.90  thf('41', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         (~ (v1_relat_1 @ X0)
% 0.72/0.90          | ~ (v1_relat_1 @ X0)
% 0.72/0.90          | (v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1))))),
% 0.72/0.90      inference('sup-', [status(thm)], ['35', '40'])).
% 0.72/0.90  thf('42', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         ((v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ X1)))
% 0.72/0.90          | ~ (v1_relat_1 @ X0))),
% 0.72/0.90      inference('simplify', [status(thm)], ['41'])).
% 0.72/0.90  thf('43', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         ((v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.72/0.90          | ~ (v1_relat_1 @ X0)
% 0.72/0.90          | ~ (v1_relat_1 @ X0))),
% 0.72/0.90      inference('sup+', [status(thm)], ['32', '42'])).
% 0.72/0.90  thf('44', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 0.72/0.90      inference('simplify', [status(thm)], ['43'])).
% 0.72/0.90  thf('45', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.90         (~ (v1_relat_1 @ X1)
% 0.72/0.90          | ((k8_relat_1 @ 
% 0.72/0.90              (k2_xboole_0 @ (k3_xboole_0 @ (k2_relat_1 @ X1) @ X0) @ X2) @ 
% 0.72/0.90              (k8_relat_1 @ X0 @ X1)) = (k8_relat_1 @ X0 @ X1)))),
% 0.72/0.90      inference('clc', [status(thm)], ['31', '44'])).
% 0.72/0.90  thf('46', plain,
% 0.72/0.90      (![X0 : $i]:
% 0.72/0.90         (((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ X0))
% 0.72/0.90            = (k8_relat_1 @ sk_A @ X0))
% 0.72/0.90          | ~ (v1_relat_1 @ X0))),
% 0.72/0.90      inference('sup+', [status(thm)], ['23', '45'])).
% 0.72/0.90  thf('47', plain,
% 0.72/0.90      (((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ sk_C))
% 0.72/0.90         != (k8_relat_1 @ sk_A @ sk_C))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('48', plain,
% 0.72/0.90      ((((k8_relat_1 @ sk_A @ sk_C) != (k8_relat_1 @ sk_A @ sk_C))
% 0.72/0.90        | ~ (v1_relat_1 @ sk_C))),
% 0.72/0.90      inference('sup-', [status(thm)], ['46', '47'])).
% 0.72/0.90  thf('49', plain, ((v1_relat_1 @ sk_C)),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('50', plain,
% 0.72/0.90      (((k8_relat_1 @ sk_A @ sk_C) != (k8_relat_1 @ sk_A @ sk_C))),
% 0.72/0.90      inference('demod', [status(thm)], ['48', '49'])).
% 0.72/0.90  thf('51', plain, ($false), inference('simplify', [status(thm)], ['50'])).
% 0.72/0.90  
% 0.72/0.90  % SZS output end Refutation
% 0.72/0.90  
% 0.72/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

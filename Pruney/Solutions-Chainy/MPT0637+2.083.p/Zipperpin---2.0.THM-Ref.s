%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ODzp8gLtr9

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 (  67 expanded)
%              Number of leaves         :   20 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :  385 ( 443 expanded)
%              Number of equality atoms :   32 (  39 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k7_relat_1 @ X21 @ X20 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X20 ) @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t43_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_funct_1])).

thf('1',plain,(
    ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
     != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X7: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('4',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('5',plain,(
    ! [X18: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t192_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k7_relat_1 @ X16 @ X17 )
        = ( k7_relat_1 @ X16 @ ( k3_xboole_0 @ ( k1_relat_1 @ X16 ) @ X17 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X7: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t119_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X11 @ X10 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X10 ) @ X11 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf('11',plain,(
    ! [X19: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t118_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X8 @ X9 ) ) @ ( k2_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t118_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X7: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ ( k2_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X19: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('18',plain,(
    ! [X7: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    ! [X19: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('21',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ( ( k8_relat_1 @ X15 @ X14 )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X7: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('25',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k8_relat_1 @ X13 @ X12 )
        = ( k5_relat_1 @ X12 @ ( k6_relat_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('26',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k7_relat_1 @ X21 @ X20 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X20 ) @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X7: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('29',plain,(
    ! [X7: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['19','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','32'])).

thf('34',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['4','33'])).

thf('35',plain,(
    $false ),
    inference(simplify,[status(thm)],['34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ODzp8gLtr9
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:26:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 88 iterations in 0.047s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.21/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.55  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.55  thf(t94_relat_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ B ) =>
% 0.21/0.55       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.21/0.55  thf('0', plain,
% 0.21/0.55      (![X20 : $i, X21 : $i]:
% 0.21/0.55         (((k7_relat_1 @ X21 @ X20) = (k5_relat_1 @ (k6_relat_1 @ X20) @ X21))
% 0.21/0.55          | ~ (v1_relat_1 @ X21))),
% 0.21/0.55      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.21/0.55  thf(t43_funct_1, conjecture,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.21/0.55       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i,B:$i]:
% 0.21/0.55        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.21/0.55          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 0.21/0.55  thf('1', plain,
% 0.21/0.55      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.21/0.55         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      ((((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.21/0.55          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 0.21/0.55        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.55  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.21/0.55  thf('3', plain, (![X7 : $i]: (v1_relat_1 @ (k6_relat_1 @ X7))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.55  thf('4', plain,
% 0.21/0.55      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.21/0.55         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.55      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.55  thf(t71_relat_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.21/0.55       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.55  thf('5', plain, (![X18 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X18)) = (X18))),
% 0.21/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.55  thf(t192_relat_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ B ) =>
% 0.21/0.55       ( ( k7_relat_1 @ B @ A ) =
% 0.21/0.55         ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 0.21/0.55  thf('6', plain,
% 0.21/0.55      (![X16 : $i, X17 : $i]:
% 0.21/0.55         (((k7_relat_1 @ X16 @ X17)
% 0.21/0.55            = (k7_relat_1 @ X16 @ (k3_xboole_0 @ (k1_relat_1 @ X16) @ X17)))
% 0.21/0.55          | ~ (v1_relat_1 @ X16))),
% 0.21/0.55      inference('cnf', [status(esa)], [t192_relat_1])).
% 0.21/0.55  thf('7', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.21/0.55            = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))
% 0.21/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.55  thf('8', plain, (![X7 : $i]: (v1_relat_1 @ (k6_relat_1 @ X7))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.55  thf('9', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.21/0.55           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.21/0.55      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.55  thf(t119_relat_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ B ) =>
% 0.21/0.55       ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) =
% 0.21/0.55         ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.55  thf('10', plain,
% 0.21/0.55      (![X10 : $i, X11 : $i]:
% 0.21/0.55         (((k2_relat_1 @ (k8_relat_1 @ X11 @ X10))
% 0.21/0.55            = (k3_xboole_0 @ (k2_relat_1 @ X10) @ X11))
% 0.21/0.55          | ~ (v1_relat_1 @ X10))),
% 0.21/0.55      inference('cnf', [status(esa)], [t119_relat_1])).
% 0.21/0.55  thf('11', plain, (![X19 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X19)) = (X19))),
% 0.21/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.55  thf(t118_relat_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ B ) =>
% 0.21/0.55       ( r1_tarski @
% 0.21/0.55         ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ))).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      (![X8 : $i, X9 : $i]:
% 0.21/0.55         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X8 @ X9)) @ 
% 0.21/0.55           (k2_relat_1 @ X9))
% 0.21/0.55          | ~ (v1_relat_1 @ X9))),
% 0.21/0.55      inference('cnf', [status(esa)], [t118_relat_1])).
% 0.21/0.55  thf('13', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ 
% 0.21/0.55           X0)
% 0.21/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['11', '12'])).
% 0.21/0.55  thf('14', plain, (![X7 : $i]: (v1_relat_1 @ (k6_relat_1 @ X7))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.55  thf('15', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0))) @ X0)),
% 0.21/0.55      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.55  thf('16', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r1_tarski @ (k3_xboole_0 @ (k2_relat_1 @ (k6_relat_1 @ X1)) @ X0) @ 
% 0.21/0.55           X1)
% 0.21/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['10', '15'])).
% 0.21/0.55  thf('17', plain, (![X19 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X19)) = (X19))),
% 0.21/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.55  thf('18', plain, (![X7 : $i]: (v1_relat_1 @ (k6_relat_1 @ X7))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.55  thf('19', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.21/0.55      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.21/0.55  thf('20', plain, (![X19 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X19)) = (X19))),
% 0.21/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.55  thf(t125_relat_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ B ) =>
% 0.21/0.55       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.21/0.55         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.21/0.55  thf('21', plain,
% 0.21/0.55      (![X14 : $i, X15 : $i]:
% 0.21/0.55         (~ (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 0.21/0.55          | ((k8_relat_1 @ X15 @ X14) = (X14))
% 0.21/0.55          | ~ (v1_relat_1 @ X14))),
% 0.21/0.55      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.21/0.55  thf('22', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.21/0.55          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.55  thf('23', plain, (![X7 : $i]: (v1_relat_1 @ (k6_relat_1 @ X7))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.55  thf('24', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.55          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0)))),
% 0.21/0.55      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.55  thf(t123_relat_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ B ) =>
% 0.21/0.55       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.21/0.55  thf('25', plain,
% 0.21/0.55      (![X12 : $i, X13 : $i]:
% 0.21/0.55         (((k8_relat_1 @ X13 @ X12) = (k5_relat_1 @ X12 @ (k6_relat_1 @ X13)))
% 0.21/0.55          | ~ (v1_relat_1 @ X12))),
% 0.21/0.55      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.21/0.55  thf('26', plain,
% 0.21/0.55      (![X20 : $i, X21 : $i]:
% 0.21/0.55         (((k7_relat_1 @ X21 @ X20) = (k5_relat_1 @ (k6_relat_1 @ X20) @ X21))
% 0.21/0.55          | ~ (v1_relat_1 @ X21))),
% 0.21/0.55      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.21/0.55  thf('27', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.21/0.55            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.21/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.21/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['25', '26'])).
% 0.21/0.55  thf('28', plain, (![X7 : $i]: (v1_relat_1 @ (k6_relat_1 @ X7))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.55  thf('29', plain, (![X7 : $i]: (v1_relat_1 @ (k6_relat_1 @ X7))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.55  thf('30', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.21/0.55           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.21/0.55      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.21/0.55  thf('31', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.55          | ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0) = (k6_relat_1 @ X0)))),
% 0.21/0.55      inference('demod', [status(thm)], ['24', '30'])).
% 0.21/0.55  thf('32', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 0.21/0.55           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['19', '31'])).
% 0.21/0.55  thf('33', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.21/0.55           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['9', '32'])).
% 0.21/0.55  thf('34', plain,
% 0.21/0.55      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.21/0.55         != (k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 0.21/0.55      inference('demod', [status(thm)], ['4', '33'])).
% 0.21/0.55  thf('35', plain, ($false), inference('simplify', [status(thm)], ['34'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

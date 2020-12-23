%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5rqdJ2jIIE

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   55 (  81 expanded)
%              Number of leaves         :   20 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :  377 ( 557 expanded)
%              Number of equality atoms :   34 (  48 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k8_relat_1 @ X17 @ X16 )
        = ( k5_relat_1 @ X16 @ ( k6_relat_1 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

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
    ( ( ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
     != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('4',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('7',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X18 ) @ X19 )
      | ( ( k8_relat_1 @ X19 @ X18 )
        = X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ ( k2_relat_1 @ X0 ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k8_relat_1 @ X17 @ X16 )
        = ( k5_relat_1 @ X16 @ ( k6_relat_1 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('10',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k7_relat_1 @ X23 @ X22 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X22 ) @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('13',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) @ X15 )
        = ( k7_relat_1 @ X13 @ ( k3_xboole_0 @ X14 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('18',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) @ X2 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k8_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('22',plain,(
    ! [X21: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('23',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('24',plain,(
    ! [X21: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('25',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X18 ) @ X19 )
      | ( ( k8_relat_1 @ X19 @ X18 )
        = X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['20','21','22','29','30'])).

thf('32',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','31'])).

thf('33',plain,(
    $false ),
    inference(simplify,[status(thm)],['32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5rqdJ2jIIE
% 0.16/0.35  % Computer   : n005.cluster.edu
% 0.16/0.35  % Model      : x86_64 x86_64
% 0.16/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.35  % Memory     : 8042.1875MB
% 0.16/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.35  % CPULimit   : 60
% 0.16/0.35  % DateTime   : Tue Dec  1 09:25:48 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.36  % Running portfolio for 600 s
% 0.16/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.36  % Number of cores: 8
% 0.16/0.36  % Python version: Python 3.6.8
% 0.16/0.36  % Running in FO mode
% 0.22/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.46  % Solved by: fo/fo7.sh
% 0.22/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.46  % done 39 iterations in 0.021s
% 0.22/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.46  % SZS output start Refutation
% 0.22/0.46  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.46  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.22/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.46  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.46  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.22/0.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.46  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.22/0.46  thf(t123_relat_1, axiom,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( v1_relat_1 @ B ) =>
% 0.22/0.46       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.22/0.46  thf('0', plain,
% 0.22/0.46      (![X16 : $i, X17 : $i]:
% 0.22/0.46         (((k8_relat_1 @ X17 @ X16) = (k5_relat_1 @ X16 @ (k6_relat_1 @ X17)))
% 0.22/0.46          | ~ (v1_relat_1 @ X16))),
% 0.22/0.46      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.22/0.46  thf(t43_funct_1, conjecture,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.22/0.46       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.46    (~( ![A:$i,B:$i]:
% 0.22/0.46        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.22/0.46          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.22/0.46    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 0.22/0.46  thf('1', plain,
% 0.22/0.46      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.22/0.46         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('2', plain,
% 0.22/0.46      ((((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.22/0.46          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 0.22/0.46        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 0.22/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.46  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.22/0.46  thf('3', plain, (![X12 : $i]: (v1_relat_1 @ (k6_relat_1 @ X12))),
% 0.22/0.46      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.46  thf('4', plain,
% 0.22/0.46      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.22/0.46         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.46      inference('demod', [status(thm)], ['2', '3'])).
% 0.22/0.46  thf(d10_xboole_0, axiom,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.46  thf('5', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.22/0.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.46  thf('6', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.46      inference('simplify', [status(thm)], ['5'])).
% 0.22/0.46  thf(t125_relat_1, axiom,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( v1_relat_1 @ B ) =>
% 0.22/0.46       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.22/0.46         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.22/0.46  thf('7', plain,
% 0.22/0.46      (![X18 : $i, X19 : $i]:
% 0.22/0.46         (~ (r1_tarski @ (k2_relat_1 @ X18) @ X19)
% 0.22/0.46          | ((k8_relat_1 @ X19 @ X18) = (X18))
% 0.22/0.46          | ~ (v1_relat_1 @ X18))),
% 0.22/0.46      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.22/0.46  thf('8', plain,
% 0.22/0.46      (![X0 : $i]:
% 0.22/0.46         (~ (v1_relat_1 @ X0) | ((k8_relat_1 @ (k2_relat_1 @ X0) @ X0) = (X0)))),
% 0.22/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.46  thf('9', plain,
% 0.22/0.46      (![X16 : $i, X17 : $i]:
% 0.22/0.46         (((k8_relat_1 @ X17 @ X16) = (k5_relat_1 @ X16 @ (k6_relat_1 @ X17)))
% 0.22/0.46          | ~ (v1_relat_1 @ X16))),
% 0.22/0.46      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.22/0.46  thf(t94_relat_1, axiom,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( v1_relat_1 @ B ) =>
% 0.22/0.46       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.22/0.46  thf('10', plain,
% 0.22/0.46      (![X22 : $i, X23 : $i]:
% 0.22/0.46         (((k7_relat_1 @ X23 @ X22) = (k5_relat_1 @ (k6_relat_1 @ X22) @ X23))
% 0.22/0.46          | ~ (v1_relat_1 @ X23))),
% 0.22/0.46      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.22/0.46  thf('11', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.22/0.46            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.22/0.46          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.22/0.46          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.22/0.46      inference('sup+', [status(thm)], ['9', '10'])).
% 0.22/0.46  thf('12', plain, (![X12 : $i]: (v1_relat_1 @ (k6_relat_1 @ X12))),
% 0.22/0.46      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.46  thf('13', plain, (![X12 : $i]: (v1_relat_1 @ (k6_relat_1 @ X12))),
% 0.22/0.46      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.46  thf('14', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.22/0.46           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.22/0.46      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.22/0.46  thf(t100_relat_1, axiom,
% 0.22/0.46    (![A:$i,B:$i,C:$i]:
% 0.22/0.46     ( ( v1_relat_1 @ C ) =>
% 0.22/0.46       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.22/0.46         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.22/0.46  thf('15', plain,
% 0.22/0.46      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.46         (((k7_relat_1 @ (k7_relat_1 @ X13 @ X14) @ X15)
% 0.22/0.46            = (k7_relat_1 @ X13 @ (k3_xboole_0 @ X14 @ X15)))
% 0.22/0.46          | ~ (v1_relat_1 @ X13))),
% 0.22/0.46      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.22/0.46  thf('16', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.46         (((k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 0.22/0.46            = (k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X0 @ X2)))
% 0.22/0.46          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.22/0.46      inference('sup+', [status(thm)], ['14', '15'])).
% 0.22/0.46  thf('17', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.22/0.46           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.22/0.46      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.22/0.46  thf('18', plain, (![X12 : $i]: (v1_relat_1 @ (k6_relat_1 @ X12))),
% 0.22/0.46      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.46  thf('19', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.46         ((k7_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) @ X2)
% 0.22/0.46           = (k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X2))))),
% 0.22/0.46      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.22/0.46  thf('20', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.22/0.46            = (k8_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0)) @ 
% 0.22/0.46               (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))))
% 0.22/0.46          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.22/0.46      inference('sup+', [status(thm)], ['8', '19'])).
% 0.22/0.46  thf('21', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.22/0.46           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.22/0.46      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.22/0.46  thf(t71_relat_1, axiom,
% 0.22/0.46    (![A:$i]:
% 0.22/0.46     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.22/0.46       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.22/0.46  thf('22', plain, (![X21 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 0.22/0.46      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.46  thf(t17_xboole_1, axiom,
% 0.22/0.46    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.22/0.46  thf('23', plain,
% 0.22/0.46      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 0.22/0.46      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.22/0.46  thf('24', plain, (![X21 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 0.22/0.46      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.46  thf('25', plain,
% 0.22/0.46      (![X18 : $i, X19 : $i]:
% 0.22/0.46         (~ (r1_tarski @ (k2_relat_1 @ X18) @ X19)
% 0.22/0.46          | ((k8_relat_1 @ X19 @ X18) = (X18))
% 0.22/0.46          | ~ (v1_relat_1 @ X18))),
% 0.22/0.46      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.22/0.46  thf('26', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         (~ (r1_tarski @ X0 @ X1)
% 0.22/0.46          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.22/0.46          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0)))),
% 0.22/0.46      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.46  thf('27', plain, (![X12 : $i]: (v1_relat_1 @ (k6_relat_1 @ X12))),
% 0.22/0.46      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.46  thf('28', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         (~ (r1_tarski @ X0 @ X1)
% 0.22/0.46          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0)))),
% 0.22/0.46      inference('demod', [status(thm)], ['26', '27'])).
% 0.22/0.46  thf('29', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         ((k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 0.22/0.46           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.22/0.46      inference('sup-', [status(thm)], ['23', '28'])).
% 0.22/0.46  thf('30', plain, (![X12 : $i]: (v1_relat_1 @ (k6_relat_1 @ X12))),
% 0.22/0.46      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.46  thf('31', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.22/0.46           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.22/0.46      inference('demod', [status(thm)], ['20', '21', '22', '29', '30'])).
% 0.22/0.46  thf('32', plain,
% 0.22/0.46      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.22/0.46         != (k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B)))),
% 0.22/0.46      inference('demod', [status(thm)], ['4', '31'])).
% 0.22/0.46  thf('33', plain, ($false), inference('simplify', [status(thm)], ['32'])).
% 0.22/0.46  
% 0.22/0.46  % SZS output end Refutation
% 0.22/0.46  
% 0.22/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

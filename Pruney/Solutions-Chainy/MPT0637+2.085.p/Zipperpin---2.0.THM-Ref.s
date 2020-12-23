%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jTqJqlGZY0

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:08 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   48 (  63 expanded)
%              Number of leaves         :   19 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :  317 ( 416 expanded)
%              Number of equality atoms :   29 (  37 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k8_relat_1 @ X6 @ X5 )
        = ( k5_relat_1 @ X5 @ ( k6_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
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
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('4',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('5',plain,(
    ! [X11: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t192_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k7_relat_1 @ X9 @ X10 )
        = ( k7_relat_1 @ X9 @ ( k3_xboole_0 @ ( k1_relat_1 @ X9 ) @ X10 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k8_relat_1 @ X6 @ X5 )
        = ( k5_relat_1 @ X5 @ ( k6_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k7_relat_1 @ X14 @ X13 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X13 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('14',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['9','15','16'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('19',plain,(
    ! [X12: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('20',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X7 ) @ X8 )
      | ( ( k8_relat_1 @ X8 @ X7 )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','24'])).

thf('26',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','25'])).

thf('27',plain,(
    $false ),
    inference(simplify,[status(thm)],['26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jTqJqlGZY0
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 14:53:11 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.22/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.46  % Solved by: fo/fo7.sh
% 0.22/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.46  % done 18 iterations in 0.015s
% 0.22/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.46  % SZS output start Refutation
% 0.22/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.46  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.22/0.46  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.46  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.22/0.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.46  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.22/0.46  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.46  thf(t123_relat_1, axiom,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( v1_relat_1 @ B ) =>
% 0.22/0.46       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.22/0.46  thf('0', plain,
% 0.22/0.46      (![X5 : $i, X6 : $i]:
% 0.22/0.46         (((k8_relat_1 @ X6 @ X5) = (k5_relat_1 @ X5 @ (k6_relat_1 @ X6)))
% 0.22/0.46          | ~ (v1_relat_1 @ X5))),
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
% 0.22/0.46  thf('3', plain, (![X4 : $i]: (v1_relat_1 @ (k6_relat_1 @ X4))),
% 0.22/0.46      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.46  thf('4', plain,
% 0.22/0.46      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.22/0.46         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.46      inference('demod', [status(thm)], ['2', '3'])).
% 0.22/0.46  thf(t71_relat_1, axiom,
% 0.22/0.46    (![A:$i]:
% 0.22/0.46     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.22/0.46       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.22/0.46  thf('5', plain, (![X11 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X11)) = (X11))),
% 0.22/0.46      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.46  thf(t192_relat_1, axiom,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( v1_relat_1 @ B ) =>
% 0.22/0.46       ( ( k7_relat_1 @ B @ A ) =
% 0.22/0.46         ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 0.22/0.46  thf('6', plain,
% 0.22/0.46      (![X9 : $i, X10 : $i]:
% 0.22/0.46         (((k7_relat_1 @ X9 @ X10)
% 0.22/0.46            = (k7_relat_1 @ X9 @ (k3_xboole_0 @ (k1_relat_1 @ X9) @ X10)))
% 0.22/0.46          | ~ (v1_relat_1 @ X9))),
% 0.22/0.46      inference('cnf', [status(esa)], [t192_relat_1])).
% 0.22/0.46  thf('7', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.22/0.46            = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))
% 0.22/0.46          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.22/0.46      inference('sup+', [status(thm)], ['5', '6'])).
% 0.22/0.46  thf('8', plain, (![X4 : $i]: (v1_relat_1 @ (k6_relat_1 @ X4))),
% 0.22/0.46      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.46  thf('9', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.22/0.46           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.22/0.46      inference('demod', [status(thm)], ['7', '8'])).
% 0.22/0.46  thf('10', plain,
% 0.22/0.46      (![X5 : $i, X6 : $i]:
% 0.22/0.46         (((k8_relat_1 @ X6 @ X5) = (k5_relat_1 @ X5 @ (k6_relat_1 @ X6)))
% 0.22/0.46          | ~ (v1_relat_1 @ X5))),
% 0.22/0.46      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.22/0.46  thf(t94_relat_1, axiom,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( v1_relat_1 @ B ) =>
% 0.22/0.46       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.22/0.46  thf('11', plain,
% 0.22/0.46      (![X13 : $i, X14 : $i]:
% 0.22/0.46         (((k7_relat_1 @ X14 @ X13) = (k5_relat_1 @ (k6_relat_1 @ X13) @ X14))
% 0.22/0.46          | ~ (v1_relat_1 @ X14))),
% 0.22/0.46      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.22/0.46  thf('12', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.22/0.46            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.22/0.46          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.22/0.46          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.22/0.46      inference('sup+', [status(thm)], ['10', '11'])).
% 0.22/0.46  thf('13', plain, (![X4 : $i]: (v1_relat_1 @ (k6_relat_1 @ X4))),
% 0.22/0.46      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.46  thf('14', plain, (![X4 : $i]: (v1_relat_1 @ (k6_relat_1 @ X4))),
% 0.22/0.46      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.46  thf('15', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.22/0.46           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.22/0.46      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.22/0.46  thf('16', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.22/0.46           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.22/0.46      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.22/0.46  thf('17', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.22/0.46           = (k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))))),
% 0.22/0.46      inference('demod', [status(thm)], ['9', '15', '16'])).
% 0.22/0.46  thf(t17_xboole_1, axiom,
% 0.22/0.46    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.22/0.46  thf('18', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.22/0.46      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.22/0.46  thf('19', plain, (![X12 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X12)) = (X12))),
% 0.22/0.46      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.46  thf(t125_relat_1, axiom,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( v1_relat_1 @ B ) =>
% 0.22/0.46       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.22/0.46         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.22/0.46  thf('20', plain,
% 0.22/0.46      (![X7 : $i, X8 : $i]:
% 0.22/0.46         (~ (r1_tarski @ (k2_relat_1 @ X7) @ X8)
% 0.22/0.46          | ((k8_relat_1 @ X8 @ X7) = (X7))
% 0.22/0.46          | ~ (v1_relat_1 @ X7))),
% 0.22/0.46      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.22/0.46  thf('21', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         (~ (r1_tarski @ X0 @ X1)
% 0.22/0.46          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.22/0.46          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0)))),
% 0.22/0.46      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.46  thf('22', plain, (![X4 : $i]: (v1_relat_1 @ (k6_relat_1 @ X4))),
% 0.22/0.46      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.46  thf('23', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         (~ (r1_tarski @ X0 @ X1)
% 0.22/0.46          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0)))),
% 0.22/0.46      inference('demod', [status(thm)], ['21', '22'])).
% 0.22/0.46  thf('24', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         ((k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 0.22/0.46           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.22/0.46      inference('sup-', [status(thm)], ['18', '23'])).
% 0.22/0.46  thf('25', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.22/0.46           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.22/0.46      inference('sup+', [status(thm)], ['17', '24'])).
% 0.22/0.46  thf('26', plain,
% 0.22/0.46      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.22/0.46         != (k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B)))),
% 0.22/0.46      inference('demod', [status(thm)], ['4', '25'])).
% 0.22/0.46  thf('27', plain, ($false), inference('simplify', [status(thm)], ['26'])).
% 0.22/0.46  
% 0.22/0.46  % SZS output end Refutation
% 0.22/0.46  
% 0.22/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

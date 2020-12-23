%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VeR7tDR6qm

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:31 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   45 (  50 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :   11
%              Number of atoms          :  268 ( 310 expanded)
%              Number of equality atoms :   24 (  29 expanded)
%              Maximal formula depth    :    8 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X10: $i] :
      ( ( ( k3_relat_1 @ X10 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X10 ) @ ( k2_relat_1 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X3 @ ( k2_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X11 ) @ X12 )
      | ( ( k8_relat_1 @ X12 @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ ( k3_relat_1 @ X0 ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ ( k3_relat_1 @ X0 ) @ X0 )
        = X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X10: $i] :
      ( ( ( k3_relat_1 @ X10 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X10 ) @ ( k2_relat_1 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ( ( k7_relat_1 @ X13 @ X14 )
        = X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k3_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ X0 @ ( k3_relat_1 @ X0 ) )
        = X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t18_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_wellord1 @ B @ A )
        = ( k8_relat_1 @ A @ ( k7_relat_1 @ B @ A ) ) ) ) )).

thf('15',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_wellord1 @ X16 @ X15 )
        = ( k8_relat_1 @ X15 @ ( k7_relat_1 @ X16 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t18_wellord1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k2_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
        = ( k8_relat_1 @ ( k3_relat_1 @ X0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
        = ( k8_relat_1 @ ( k3_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t30_wellord1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k2_wellord1 @ A @ ( k3_relat_1 @ A ) )
        = A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( k2_wellord1 @ A @ ( k3_relat_1 @ A ) )
          = A ) ) ),
    inference('cnf.neg',[status(esa)],[t30_wellord1])).

thf('18',plain,(
    ( k2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( k8_relat_1 @ ( k3_relat_1 @ sk_A ) @ sk_A )
     != sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ( k8_relat_1 @ ( k3_relat_1 @ sk_A ) @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    $false ),
    inference(simplify,[status(thm)],['24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VeR7tDR6qm
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:06:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 24 iterations in 0.016s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.47  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.20/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.47  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.20/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.47  thf(d6_relat_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ A ) =>
% 0.20/0.47       ( ( k3_relat_1 @ A ) =
% 0.20/0.47         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      (![X10 : $i]:
% 0.20/0.47         (((k3_relat_1 @ X10)
% 0.20/0.47            = (k2_xboole_0 @ (k1_relat_1 @ X10) @ (k2_relat_1 @ X10)))
% 0.20/0.47          | ~ (v1_relat_1 @ X10))),
% 0.20/0.47      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.20/0.47  thf(d10_xboole_0, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.47  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.47      inference('simplify', [status(thm)], ['1'])).
% 0.20/0.47  thf(t10_xboole_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.47         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ X3 @ (k2_xboole_0 @ X5 @ X4)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((r1_tarski @ (k2_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 0.20/0.47          | ~ (v1_relat_1 @ X0))),
% 0.20/0.47      inference('sup+', [status(thm)], ['0', '4'])).
% 0.20/0.47  thf(t125_relat_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ B ) =>
% 0.20/0.47       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.20/0.47         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (![X11 : $i, X12 : $i]:
% 0.20/0.47         (~ (r1_tarski @ (k2_relat_1 @ X11) @ X12)
% 0.20/0.47          | ((k8_relat_1 @ X12 @ X11) = (X11))
% 0.20/0.47          | ~ (v1_relat_1 @ X11))),
% 0.20/0.47      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ X0)
% 0.20/0.47          | ((k8_relat_1 @ (k3_relat_1 @ X0) @ X0) = (X0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (((k8_relat_1 @ (k3_relat_1 @ X0) @ X0) = (X0)) | ~ (v1_relat_1 @ X0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X10 : $i]:
% 0.20/0.47         (((k3_relat_1 @ X10)
% 0.20/0.47            = (k2_xboole_0 @ (k1_relat_1 @ X10) @ (k2_relat_1 @ X10)))
% 0.20/0.47          | ~ (v1_relat_1 @ X10))),
% 0.20/0.47      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.20/0.47  thf(t7_xboole_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 0.20/0.47      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 0.20/0.47          | ~ (v1_relat_1 @ X0))),
% 0.20/0.47      inference('sup+', [status(thm)], ['9', '10'])).
% 0.20/0.47  thf(t97_relat_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ B ) =>
% 0.20/0.47       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.20/0.47         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (![X13 : $i, X14 : $i]:
% 0.20/0.47         (~ (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 0.20/0.47          | ((k7_relat_1 @ X13 @ X14) = (X13))
% 0.20/0.47          | ~ (v1_relat_1 @ X13))),
% 0.20/0.47      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ X0)
% 0.20/0.47          | ((k7_relat_1 @ X0 @ (k3_relat_1 @ X0)) = (X0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (((k7_relat_1 @ X0 @ (k3_relat_1 @ X0)) = (X0)) | ~ (v1_relat_1 @ X0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.47  thf(t18_wellord1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ B ) =>
% 0.20/0.47       ( ( k2_wellord1 @ B @ A ) = ( k8_relat_1 @ A @ ( k7_relat_1 @ B @ A ) ) ) ))).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X15 : $i, X16 : $i]:
% 0.20/0.47         (((k2_wellord1 @ X16 @ X15)
% 0.20/0.47            = (k8_relat_1 @ X15 @ (k7_relat_1 @ X16 @ X15)))
% 0.20/0.47          | ~ (v1_relat_1 @ X16))),
% 0.20/0.47      inference('cnf', [status(esa)], [t18_wellord1])).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (((k2_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.20/0.47            = (k8_relat_1 @ (k3_relat_1 @ X0) @ X0))
% 0.20/0.47          | ~ (v1_relat_1 @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ X0))),
% 0.20/0.47      inference('sup+', [status(thm)], ['14', '15'])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X0)
% 0.20/0.47          | ((k2_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.20/0.47              = (k8_relat_1 @ (k3_relat_1 @ X0) @ X0)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.47  thf(t30_wellord1, conjecture,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ A ) =>
% 0.20/0.47       ( ( k2_wellord1 @ A @ ( k3_relat_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i]:
% 0.20/0.47        ( ( v1_relat_1 @ A ) =>
% 0.20/0.47          ( ( k2_wellord1 @ A @ ( k3_relat_1 @ A ) ) = ( A ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t30_wellord1])).
% 0.20/0.47  thf('18', plain, (((k2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A)) != (sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      ((((k8_relat_1 @ (k3_relat_1 @ sk_A) @ sk_A) != (sk_A))
% 0.20/0.47        | ~ (v1_relat_1 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.47  thf('20', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('21', plain, (((k8_relat_1 @ (k3_relat_1 @ sk_A) @ sk_A) != (sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.47  thf('22', plain, ((((sk_A) != (sk_A)) | ~ (v1_relat_1 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['8', '21'])).
% 0.20/0.47  thf('23', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('24', plain, (((sk_A) != (sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.47  thf('25', plain, ($false), inference('simplify', [status(thm)], ['24'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

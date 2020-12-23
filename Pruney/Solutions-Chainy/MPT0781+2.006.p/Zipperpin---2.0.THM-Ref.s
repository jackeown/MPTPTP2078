%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ugx1QHRt0O

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:31 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   43 (  49 expanded)
%              Number of leaves         :   17 (  21 expanded)
%              Depth                    :   11
%              Number of atoms          :  253 ( 300 expanded)
%              Number of equality atoms :   24 (  29 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( ( ( k3_relat_1 @ X4 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X4 ) @ ( k2_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','3'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ( ( k8_relat_1 @ X6 @ X5 )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ ( k3_relat_1 @ X0 ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ ( k3_relat_1 @ X0 ) @ X0 )
        = X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X4: $i] :
      ( ( ( k3_relat_1 @ X4 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X4 ) @ ( k2_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X7 ) @ X8 )
      | ( ( k7_relat_1 @ X7 @ X8 )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k3_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ X0 @ ( k3_relat_1 @ X0 ) )
        = X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t18_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_wellord1 @ B @ A )
        = ( k8_relat_1 @ A @ ( k7_relat_1 @ B @ A ) ) ) ) )).

thf('14',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_wellord1 @ X10 @ X9 )
        = ( k8_relat_1 @ X9 @ ( k7_relat_1 @ X10 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t18_wellord1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k2_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
        = ( k8_relat_1 @ ( k3_relat_1 @ X0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
        = ( k8_relat_1 @ ( k3_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

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

thf('17',plain,(
    ( k2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( k8_relat_1 @ ( k3_relat_1 @ sk_A ) @ sk_A )
     != sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ( k8_relat_1 @ ( k3_relat_1 @ sk_A ) @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    $false ),
    inference(simplify,[status(thm)],['23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ugx1QHRt0O
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:21:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 19 iterations in 0.015s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.48  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.22/0.48  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.48  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.22/0.48  thf(d6_relat_1, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( v1_relat_1 @ A ) =>
% 0.22/0.48       ( ( k3_relat_1 @ A ) =
% 0.22/0.48         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.22/0.48  thf('0', plain,
% 0.22/0.48      (![X4 : $i]:
% 0.22/0.48         (((k3_relat_1 @ X4)
% 0.22/0.48            = (k2_xboole_0 @ (k1_relat_1 @ X4) @ (k2_relat_1 @ X4)))
% 0.22/0.48          | ~ (v1_relat_1 @ X4))),
% 0.22/0.48      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.22/0.48  thf(commutativity_k2_xboole_0, axiom,
% 0.22/0.48    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.22/0.48  thf('1', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.48      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.22/0.48  thf(t7_xboole_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.48  thf('2', plain,
% 0.22/0.48      (![X2 : $i, X3 : $i]: (r1_tarski @ X2 @ (k2_xboole_0 @ X2 @ X3))),
% 0.22/0.48      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.22/0.48  thf('3', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.22/0.48      inference('sup+', [status(thm)], ['1', '2'])).
% 0.22/0.48  thf('4', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((r1_tarski @ (k2_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 0.22/0.48          | ~ (v1_relat_1 @ X0))),
% 0.22/0.48      inference('sup+', [status(thm)], ['0', '3'])).
% 0.22/0.48  thf(t125_relat_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( v1_relat_1 @ B ) =>
% 0.22/0.48       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.22/0.48         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.22/0.48  thf('5', plain,
% 0.22/0.48      (![X5 : $i, X6 : $i]:
% 0.22/0.48         (~ (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 0.22/0.48          | ((k8_relat_1 @ X6 @ X5) = (X5))
% 0.22/0.48          | ~ (v1_relat_1 @ X5))),
% 0.22/0.48      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.22/0.48  thf('6', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (v1_relat_1 @ X0)
% 0.22/0.48          | ~ (v1_relat_1 @ X0)
% 0.22/0.48          | ((k8_relat_1 @ (k3_relat_1 @ X0) @ X0) = (X0)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.48  thf('7', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (((k8_relat_1 @ (k3_relat_1 @ X0) @ X0) = (X0)) | ~ (v1_relat_1 @ X0))),
% 0.22/0.48      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.48  thf('8', plain,
% 0.22/0.48      (![X4 : $i]:
% 0.22/0.48         (((k3_relat_1 @ X4)
% 0.22/0.48            = (k2_xboole_0 @ (k1_relat_1 @ X4) @ (k2_relat_1 @ X4)))
% 0.22/0.48          | ~ (v1_relat_1 @ X4))),
% 0.22/0.48      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.22/0.48  thf('9', plain,
% 0.22/0.48      (![X2 : $i, X3 : $i]: (r1_tarski @ X2 @ (k2_xboole_0 @ X2 @ X3))),
% 0.22/0.48      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.22/0.48  thf('10', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 0.22/0.48          | ~ (v1_relat_1 @ X0))),
% 0.22/0.48      inference('sup+', [status(thm)], ['8', '9'])).
% 0.22/0.48  thf(t97_relat_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( v1_relat_1 @ B ) =>
% 0.22/0.48       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.22/0.48         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.22/0.48  thf('11', plain,
% 0.22/0.48      (![X7 : $i, X8 : $i]:
% 0.22/0.48         (~ (r1_tarski @ (k1_relat_1 @ X7) @ X8)
% 0.22/0.48          | ((k7_relat_1 @ X7 @ X8) = (X7))
% 0.22/0.48          | ~ (v1_relat_1 @ X7))),
% 0.22/0.48      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.22/0.48  thf('12', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (v1_relat_1 @ X0)
% 0.22/0.48          | ~ (v1_relat_1 @ X0)
% 0.22/0.48          | ((k7_relat_1 @ X0 @ (k3_relat_1 @ X0)) = (X0)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.48  thf('13', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (((k7_relat_1 @ X0 @ (k3_relat_1 @ X0)) = (X0)) | ~ (v1_relat_1 @ X0))),
% 0.22/0.48      inference('simplify', [status(thm)], ['12'])).
% 0.22/0.48  thf(t18_wellord1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( v1_relat_1 @ B ) =>
% 0.22/0.48       ( ( k2_wellord1 @ B @ A ) = ( k8_relat_1 @ A @ ( k7_relat_1 @ B @ A ) ) ) ))).
% 0.22/0.48  thf('14', plain,
% 0.22/0.48      (![X9 : $i, X10 : $i]:
% 0.22/0.48         (((k2_wellord1 @ X10 @ X9)
% 0.22/0.48            = (k8_relat_1 @ X9 @ (k7_relat_1 @ X10 @ X9)))
% 0.22/0.48          | ~ (v1_relat_1 @ X10))),
% 0.22/0.48      inference('cnf', [status(esa)], [t18_wellord1])).
% 0.22/0.48  thf('15', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (((k2_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.22/0.48            = (k8_relat_1 @ (k3_relat_1 @ X0) @ X0))
% 0.22/0.48          | ~ (v1_relat_1 @ X0)
% 0.22/0.48          | ~ (v1_relat_1 @ X0))),
% 0.22/0.48      inference('sup+', [status(thm)], ['13', '14'])).
% 0.22/0.48  thf('16', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (v1_relat_1 @ X0)
% 0.22/0.48          | ((k2_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.22/0.48              = (k8_relat_1 @ (k3_relat_1 @ X0) @ X0)))),
% 0.22/0.48      inference('simplify', [status(thm)], ['15'])).
% 0.22/0.48  thf(t30_wellord1, conjecture,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( v1_relat_1 @ A ) =>
% 0.22/0.48       ( ( k2_wellord1 @ A @ ( k3_relat_1 @ A ) ) = ( A ) ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i]:
% 0.22/0.48        ( ( v1_relat_1 @ A ) =>
% 0.22/0.48          ( ( k2_wellord1 @ A @ ( k3_relat_1 @ A ) ) = ( A ) ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t30_wellord1])).
% 0.22/0.48  thf('17', plain, (((k2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A)) != (sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('18', plain,
% 0.22/0.48      ((((k8_relat_1 @ (k3_relat_1 @ sk_A) @ sk_A) != (sk_A))
% 0.22/0.48        | ~ (v1_relat_1 @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.48  thf('19', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('20', plain, (((k8_relat_1 @ (k3_relat_1 @ sk_A) @ sk_A) != (sk_A))),
% 0.22/0.48      inference('demod', [status(thm)], ['18', '19'])).
% 0.22/0.48  thf('21', plain, ((((sk_A) != (sk_A)) | ~ (v1_relat_1 @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['7', '20'])).
% 0.22/0.48  thf('22', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('23', plain, (((sk_A) != (sk_A))),
% 0.22/0.48      inference('demod', [status(thm)], ['21', '22'])).
% 0.22/0.48  thf('24', plain, ($false), inference('simplify', [status(thm)], ['23'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

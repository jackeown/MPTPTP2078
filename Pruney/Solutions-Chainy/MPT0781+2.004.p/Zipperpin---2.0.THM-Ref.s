%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ob2ar4UlvF

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:30 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   44 (  52 expanded)
%              Number of leaves         :   17 (  22 expanded)
%              Depth                    :   12
%              Number of atoms          :  272 ( 334 expanded)
%              Number of equality atoms :   26 (  33 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X20: $i] :
      ( ( ( k3_relat_1 @ X20 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X20 ) @ ( k2_relat_1 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
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

thf('2',plain,(
    ! [X20: $i] :
      ( ( ( k3_relat_1 @ X20 )
        = ( k2_xboole_0 @ ( k2_relat_1 @ X20 ) @ ( k1_relat_1 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('7',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X28 ) @ X29 )
      | ( ( k7_relat_1 @ X28 @ X29 )
        = X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k3_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ X0 @ ( k3_relat_1 @ X0 ) )
        = X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X20: $i] :
      ( ( ( k3_relat_1 @ X20 )
        = ( k2_xboole_0 @ ( k2_relat_1 @ X20 ) @ ( k1_relat_1 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('11',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('13',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X24 ) @ X25 )
      | ( ( k8_relat_1 @ X25 @ X24 )
        = X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ ( k3_relat_1 @ X0 ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ ( k3_relat_1 @ X0 ) @ X0 )
        = X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t17_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_wellord1 @ B @ A )
        = ( k7_relat_1 @ ( k8_relat_1 @ A @ B ) @ A ) ) ) )).

thf('16',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k2_wellord1 @ X31 @ X30 )
        = ( k7_relat_1 @ ( k8_relat_1 @ X30 @ X31 ) @ X30 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t17_wellord1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k2_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
        = ( k7_relat_1 @ X0 @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
        = ( k7_relat_1 @ X0 @ ( k3_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k2_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
        = X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

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

thf('21',plain,(
    ( k2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

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
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ob2ar4UlvF
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:23:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.56  % Solved by: fo/fo7.sh
% 0.35/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.56  % done 209 iterations in 0.095s
% 0.35/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.56  % SZS output start Refutation
% 0.35/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.56  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.35/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.56  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.35/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.35/0.56  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.35/0.56  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.35/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.35/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.35/0.56  thf(d6_relat_1, axiom,
% 0.35/0.56    (![A:$i]:
% 0.35/0.56     ( ( v1_relat_1 @ A ) =>
% 0.35/0.56       ( ( k3_relat_1 @ A ) =
% 0.35/0.56         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.35/0.56  thf('0', plain,
% 0.35/0.56      (![X20 : $i]:
% 0.35/0.56         (((k3_relat_1 @ X20)
% 0.35/0.56            = (k2_xboole_0 @ (k1_relat_1 @ X20) @ (k2_relat_1 @ X20)))
% 0.35/0.56          | ~ (v1_relat_1 @ X20))),
% 0.35/0.56      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.35/0.56  thf(commutativity_k2_xboole_0, axiom,
% 0.35/0.56    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.35/0.56  thf('1', plain,
% 0.35/0.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.35/0.56      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.35/0.56  thf('2', plain,
% 0.35/0.56      (![X20 : $i]:
% 0.35/0.56         (((k3_relat_1 @ X20)
% 0.35/0.56            = (k2_xboole_0 @ (k2_relat_1 @ X20) @ (k1_relat_1 @ X20)))
% 0.35/0.56          | ~ (v1_relat_1 @ X20))),
% 0.35/0.56      inference('demod', [status(thm)], ['0', '1'])).
% 0.35/0.56  thf('3', plain,
% 0.35/0.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.35/0.56      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.35/0.56  thf(t7_xboole_1, axiom,
% 0.35/0.56    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.35/0.56  thf('4', plain,
% 0.35/0.56      (![X16 : $i, X17 : $i]: (r1_tarski @ X16 @ (k2_xboole_0 @ X16 @ X17))),
% 0.35/0.56      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.35/0.56  thf('5', plain,
% 0.35/0.56      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.35/0.56      inference('sup+', [status(thm)], ['3', '4'])).
% 0.35/0.56  thf('6', plain,
% 0.35/0.56      (![X0 : $i]:
% 0.35/0.56         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 0.35/0.56          | ~ (v1_relat_1 @ X0))),
% 0.35/0.56      inference('sup+', [status(thm)], ['2', '5'])).
% 0.35/0.56  thf(t97_relat_1, axiom,
% 0.35/0.56    (![A:$i,B:$i]:
% 0.35/0.56     ( ( v1_relat_1 @ B ) =>
% 0.35/0.56       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.35/0.56         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.35/0.56  thf('7', plain,
% 0.35/0.56      (![X28 : $i, X29 : $i]:
% 0.35/0.56         (~ (r1_tarski @ (k1_relat_1 @ X28) @ X29)
% 0.35/0.56          | ((k7_relat_1 @ X28 @ X29) = (X28))
% 0.35/0.56          | ~ (v1_relat_1 @ X28))),
% 0.35/0.56      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.35/0.56  thf('8', plain,
% 0.35/0.56      (![X0 : $i]:
% 0.35/0.56         (~ (v1_relat_1 @ X0)
% 0.35/0.56          | ~ (v1_relat_1 @ X0)
% 0.35/0.56          | ((k7_relat_1 @ X0 @ (k3_relat_1 @ X0)) = (X0)))),
% 0.35/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.35/0.56  thf('9', plain,
% 0.35/0.56      (![X0 : $i]:
% 0.35/0.56         (((k7_relat_1 @ X0 @ (k3_relat_1 @ X0)) = (X0)) | ~ (v1_relat_1 @ X0))),
% 0.35/0.56      inference('simplify', [status(thm)], ['8'])).
% 0.35/0.56  thf('10', plain,
% 0.35/0.56      (![X20 : $i]:
% 0.35/0.56         (((k3_relat_1 @ X20)
% 0.35/0.56            = (k2_xboole_0 @ (k2_relat_1 @ X20) @ (k1_relat_1 @ X20)))
% 0.35/0.56          | ~ (v1_relat_1 @ X20))),
% 0.35/0.56      inference('demod', [status(thm)], ['0', '1'])).
% 0.35/0.56  thf('11', plain,
% 0.35/0.56      (![X16 : $i, X17 : $i]: (r1_tarski @ X16 @ (k2_xboole_0 @ X16 @ X17))),
% 0.35/0.56      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.35/0.56  thf('12', plain,
% 0.35/0.56      (![X0 : $i]:
% 0.35/0.56         ((r1_tarski @ (k2_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 0.35/0.56          | ~ (v1_relat_1 @ X0))),
% 0.35/0.56      inference('sup+', [status(thm)], ['10', '11'])).
% 0.35/0.56  thf(t125_relat_1, axiom,
% 0.35/0.56    (![A:$i,B:$i]:
% 0.35/0.56     ( ( v1_relat_1 @ B ) =>
% 0.35/0.56       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.35/0.56         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.35/0.56  thf('13', plain,
% 0.35/0.56      (![X24 : $i, X25 : $i]:
% 0.35/0.56         (~ (r1_tarski @ (k2_relat_1 @ X24) @ X25)
% 0.35/0.56          | ((k8_relat_1 @ X25 @ X24) = (X24))
% 0.35/0.56          | ~ (v1_relat_1 @ X24))),
% 0.35/0.56      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.35/0.56  thf('14', plain,
% 0.35/0.56      (![X0 : $i]:
% 0.35/0.56         (~ (v1_relat_1 @ X0)
% 0.35/0.56          | ~ (v1_relat_1 @ X0)
% 0.35/0.56          | ((k8_relat_1 @ (k3_relat_1 @ X0) @ X0) = (X0)))),
% 0.35/0.56      inference('sup-', [status(thm)], ['12', '13'])).
% 0.35/0.56  thf('15', plain,
% 0.35/0.56      (![X0 : $i]:
% 0.35/0.56         (((k8_relat_1 @ (k3_relat_1 @ X0) @ X0) = (X0)) | ~ (v1_relat_1 @ X0))),
% 0.35/0.56      inference('simplify', [status(thm)], ['14'])).
% 0.35/0.56  thf(t17_wellord1, axiom,
% 0.35/0.56    (![A:$i,B:$i]:
% 0.35/0.56     ( ( v1_relat_1 @ B ) =>
% 0.35/0.56       ( ( k2_wellord1 @ B @ A ) = ( k7_relat_1 @ ( k8_relat_1 @ A @ B ) @ A ) ) ))).
% 0.35/0.56  thf('16', plain,
% 0.35/0.56      (![X30 : $i, X31 : $i]:
% 0.35/0.56         (((k2_wellord1 @ X31 @ X30)
% 0.35/0.56            = (k7_relat_1 @ (k8_relat_1 @ X30 @ X31) @ X30))
% 0.35/0.56          | ~ (v1_relat_1 @ X31))),
% 0.35/0.56      inference('cnf', [status(esa)], [t17_wellord1])).
% 0.35/0.56  thf('17', plain,
% 0.35/0.56      (![X0 : $i]:
% 0.35/0.56         (((k2_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.35/0.56            = (k7_relat_1 @ X0 @ (k3_relat_1 @ X0)))
% 0.35/0.56          | ~ (v1_relat_1 @ X0)
% 0.35/0.56          | ~ (v1_relat_1 @ X0))),
% 0.35/0.56      inference('sup+', [status(thm)], ['15', '16'])).
% 0.35/0.56  thf('18', plain,
% 0.35/0.56      (![X0 : $i]:
% 0.35/0.56         (~ (v1_relat_1 @ X0)
% 0.35/0.56          | ((k2_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.35/0.56              = (k7_relat_1 @ X0 @ (k3_relat_1 @ X0))))),
% 0.35/0.56      inference('simplify', [status(thm)], ['17'])).
% 0.35/0.56  thf('19', plain,
% 0.35/0.56      (![X0 : $i]:
% 0.35/0.56         (((k2_wellord1 @ X0 @ (k3_relat_1 @ X0)) = (X0))
% 0.35/0.56          | ~ (v1_relat_1 @ X0)
% 0.35/0.56          | ~ (v1_relat_1 @ X0))),
% 0.35/0.56      inference('sup+', [status(thm)], ['9', '18'])).
% 0.35/0.56  thf('20', plain,
% 0.35/0.56      (![X0 : $i]:
% 0.35/0.56         (~ (v1_relat_1 @ X0) | ((k2_wellord1 @ X0 @ (k3_relat_1 @ X0)) = (X0)))),
% 0.35/0.56      inference('simplify', [status(thm)], ['19'])).
% 0.35/0.56  thf(t30_wellord1, conjecture,
% 0.35/0.56    (![A:$i]:
% 0.35/0.56     ( ( v1_relat_1 @ A ) =>
% 0.35/0.56       ( ( k2_wellord1 @ A @ ( k3_relat_1 @ A ) ) = ( A ) ) ))).
% 0.35/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.56    (~( ![A:$i]:
% 0.35/0.56        ( ( v1_relat_1 @ A ) =>
% 0.35/0.56          ( ( k2_wellord1 @ A @ ( k3_relat_1 @ A ) ) = ( A ) ) ) )),
% 0.35/0.56    inference('cnf.neg', [status(esa)], [t30_wellord1])).
% 0.35/0.56  thf('21', plain, (((k2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A)) != (sk_A))),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('22', plain, ((((sk_A) != (sk_A)) | ~ (v1_relat_1 @ sk_A))),
% 0.35/0.56      inference('sup-', [status(thm)], ['20', '21'])).
% 0.35/0.56  thf('23', plain, ((v1_relat_1 @ sk_A)),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('24', plain, (((sk_A) != (sk_A))),
% 0.35/0.56      inference('demod', [status(thm)], ['22', '23'])).
% 0.35/0.56  thf('25', plain, ($false), inference('simplify', [status(thm)], ['24'])).
% 0.35/0.56  
% 0.35/0.56  % SZS output end Refutation
% 0.35/0.56  
% 0.35/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

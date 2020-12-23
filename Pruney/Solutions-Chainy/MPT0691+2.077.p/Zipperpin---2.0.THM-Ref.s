%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hVS57aoRpc

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:28 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   47 (  53 expanded)
%              Number of leaves         :   22 (  25 expanded)
%              Depth                    :   11
%              Number of atoms          :  326 ( 404 expanded)
%              Number of equality atoms :   24 (  24 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t146_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
         => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t146_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X13 @ ( k1_relat_1 @ X14 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X14 @ X13 ) )
        = X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('3',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['3','4'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X16 @ X15 ) @ X17 )
        = ( k3_xboole_0 @ X15 @ ( k10_relat_1 @ X16 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) )
        = ( k9_relat_1 @ X10 @ X11 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X12: $i] :
      ( ( ( k10_relat_1 @ X12 @ ( k2_relat_1 @ X12 ) )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) )
        = ( k5_xboole_0 @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ X0 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( k5_xboole_0 @ sk_A @ sk_A )
     != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['5','17'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('19',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('20',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['0','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hVS57aoRpc
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:35:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 38 iterations in 0.019s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.47  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.47  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.47  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.47  thf(t146_funct_1, conjecture,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ B ) =>
% 0.20/0.47       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.47         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i]:
% 0.20/0.47        ( ( v1_relat_1 @ B ) =>
% 0.20/0.47          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.47            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('1', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t91_relat_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ B ) =>
% 0.20/0.47       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.47         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X13 : $i, X14 : $i]:
% 0.20/0.47         (~ (r1_tarski @ X13 @ (k1_relat_1 @ X14))
% 0.20/0.47          | ((k1_relat_1 @ (k7_relat_1 @ X14 @ X13)) = (X13))
% 0.20/0.47          | ~ (v1_relat_1 @ X14))),
% 0.20/0.47      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.47        | ((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.47  thf('4', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('5', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.47  thf(t139_funct_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ C ) =>
% 0.20/0.47       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.20/0.47         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.47         (((k10_relat_1 @ (k7_relat_1 @ X16 @ X15) @ X17)
% 0.20/0.47            = (k3_xboole_0 @ X15 @ (k10_relat_1 @ X16 @ X17)))
% 0.20/0.47          | ~ (v1_relat_1 @ X16))),
% 0.20/0.47      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.20/0.47  thf(t148_relat_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ B ) =>
% 0.20/0.47       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (![X10 : $i, X11 : $i]:
% 0.20/0.47         (((k2_relat_1 @ (k7_relat_1 @ X10 @ X11)) = (k9_relat_1 @ X10 @ X11))
% 0.20/0.47          | ~ (v1_relat_1 @ X10))),
% 0.20/0.47      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.47  thf(t169_relat_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ A ) =>
% 0.20/0.47       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X12 : $i]:
% 0.20/0.47         (((k10_relat_1 @ X12 @ (k2_relat_1 @ X12)) = (k1_relat_1 @ X12))
% 0.20/0.47          | ~ (v1_relat_1 @ X12))),
% 0.20/0.47      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.20/0.47            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.20/0.47          | ~ (v1_relat_1 @ X1)
% 0.20/0.47          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.20/0.47      inference('sup+', [status(thm)], ['7', '8'])).
% 0.20/0.47  thf(dt_k7_relat_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X8 : $i, X9 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X8) | (v1_relat_1 @ (k7_relat_1 @ X8 @ X9)))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X1)
% 0.20/0.47          | ((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.20/0.47              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.20/0.47      inference('clc', [status(thm)], ['9', '10'])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (((k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)))
% 0.20/0.47            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.20/0.47          | ~ (v1_relat_1 @ X1)
% 0.20/0.47          | ~ (v1_relat_1 @ X1))),
% 0.20/0.47      inference('sup+', [status(thm)], ['6', '11'])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X1)
% 0.20/0.47          | ((k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)))
% 0.20/0.47              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.20/0.47      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.47  thf(t100_xboole_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i]:
% 0.20/0.47         ((k4_xboole_0 @ X3 @ X4)
% 0.20/0.47           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (((k4_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)))
% 0.20/0.47            = (k5_xboole_0 @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 0.20/0.47          | ~ (v1_relat_1 @ X1))),
% 0.20/0.47      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.47  thf(l32_xboole_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 0.20/0.47      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (((k5_xboole_0 @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.20/0.47            != (k1_xboole_0))
% 0.20/0.47          | ~ (v1_relat_1 @ X1)
% 0.20/0.47          | (r1_tarski @ X0 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      ((((k5_xboole_0 @ sk_A @ sk_A) != (k1_xboole_0))
% 0.20/0.47        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.20/0.47        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['5', '17'])).
% 0.20/0.47  thf(t92_xboole_1, axiom,
% 0.20/0.47    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.47  thf('19', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ X5) = (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.47  thf('20', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.47        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 0.20/0.47      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.47  thf('23', plain, ($false), inference('demod', [status(thm)], ['0', '22'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

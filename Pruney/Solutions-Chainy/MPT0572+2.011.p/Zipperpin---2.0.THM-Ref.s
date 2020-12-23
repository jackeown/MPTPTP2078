%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xI0DbqWcp0

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:15 EST 2020

% Result     : Theorem 4.57s
% Output     : Refutation 4.57s
% Verified   : 
% Statistics : Number of formulae       :   50 (  68 expanded)
%              Number of leaves         :   17 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :  395 ( 564 expanded)
%              Number of equality atoms :   19 (  31 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['0','3'])).

thf(t45_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( B
        = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X8
        = ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) ) )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('8',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('9',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['6','11'])).

thf(t175_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('13',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k10_relat_1 @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ X20 @ X21 ) @ ( k10_relat_1 @ X20 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t175_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ X1 ) @ ( k10_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k10_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('18',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X8
        = ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) ) )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ X1 ) @ ( k10_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k10_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('24',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ ( k3_xboole_0 @ ( k10_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ~ ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k10_relat_1 @ X1 @ X2 ) @ ( k10_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k10_relat_1 @ X1 @ X2 ) @ ( k10_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf(t176_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( r1_tarski @ ( k10_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( r1_tarski @ ( k10_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t176_relat_1])).

thf('28',plain,(
    ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['29','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xI0DbqWcp0
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:40:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 4.57/4.83  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.57/4.83  % Solved by: fo/fo7.sh
% 4.57/4.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.57/4.83  % done 3461 iterations in 4.371s
% 4.57/4.83  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.57/4.83  % SZS output start Refutation
% 4.57/4.83  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.57/4.83  thf(sk_B_type, type, sk_B: $i).
% 4.57/4.83  thf(sk_C_type, type, sk_C: $i).
% 4.57/4.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.57/4.83  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.57/4.83  thf(sk_A_type, type, sk_A: $i).
% 4.57/4.83  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 4.57/4.83  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.57/4.83  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.57/4.83  thf(commutativity_k3_xboole_0, axiom,
% 4.57/4.83    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 4.57/4.83  thf('0', plain,
% 4.57/4.83      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.57/4.83      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.57/4.83  thf(t48_xboole_1, axiom,
% 4.57/4.83    (![A:$i,B:$i]:
% 4.57/4.83     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 4.57/4.83  thf('1', plain,
% 4.57/4.83      (![X9 : $i, X10 : $i]:
% 4.57/4.83         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 4.57/4.83           = (k3_xboole_0 @ X9 @ X10))),
% 4.57/4.83      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.57/4.83  thf(t36_xboole_1, axiom,
% 4.57/4.83    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 4.57/4.83  thf('2', plain,
% 4.57/4.83      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 4.57/4.83      inference('cnf', [status(esa)], [t36_xboole_1])).
% 4.57/4.83  thf('3', plain,
% 4.57/4.83      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 4.57/4.83      inference('sup+', [status(thm)], ['1', '2'])).
% 4.57/4.83  thf('4', plain,
% 4.57/4.83      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 4.57/4.83      inference('sup+', [status(thm)], ['0', '3'])).
% 4.57/4.83  thf(t45_xboole_1, axiom,
% 4.57/4.83    (![A:$i,B:$i]:
% 4.57/4.83     ( ( r1_tarski @ A @ B ) =>
% 4.57/4.83       ( ( B ) = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ))).
% 4.57/4.83  thf('5', plain,
% 4.57/4.83      (![X7 : $i, X8 : $i]:
% 4.57/4.83         (((X8) = (k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7)))
% 4.57/4.83          | ~ (r1_tarski @ X7 @ X8))),
% 4.57/4.83      inference('cnf', [status(esa)], [t45_xboole_1])).
% 4.57/4.83  thf('6', plain,
% 4.57/4.83      (![X0 : $i, X1 : $i]:
% 4.57/4.83         ((X0)
% 4.57/4.83           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 4.57/4.83              (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))))),
% 4.57/4.83      inference('sup-', [status(thm)], ['4', '5'])).
% 4.57/4.83  thf('7', plain,
% 4.57/4.83      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.57/4.83      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.57/4.83  thf('8', plain,
% 4.57/4.83      (![X9 : $i, X10 : $i]:
% 4.57/4.83         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 4.57/4.83           = (k3_xboole_0 @ X9 @ X10))),
% 4.57/4.83      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.57/4.83  thf('9', plain,
% 4.57/4.83      (![X9 : $i, X10 : $i]:
% 4.57/4.83         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 4.57/4.83           = (k3_xboole_0 @ X9 @ X10))),
% 4.57/4.83      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.57/4.83  thf('10', plain,
% 4.57/4.83      (![X0 : $i, X1 : $i]:
% 4.57/4.83         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 4.57/4.83           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 4.57/4.83      inference('sup+', [status(thm)], ['8', '9'])).
% 4.57/4.83  thf('11', plain,
% 4.57/4.83      (![X0 : $i, X1 : $i]:
% 4.57/4.83         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 4.57/4.83           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 4.57/4.83      inference('sup+', [status(thm)], ['7', '10'])).
% 4.57/4.83  thf('12', plain,
% 4.57/4.83      (![X0 : $i, X1 : $i]:
% 4.57/4.83         ((X0)
% 4.57/4.83           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 4.57/4.83              (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))))),
% 4.57/4.83      inference('demod', [status(thm)], ['6', '11'])).
% 4.57/4.83  thf(t175_relat_1, axiom,
% 4.57/4.83    (![A:$i,B:$i,C:$i]:
% 4.57/4.83     ( ( v1_relat_1 @ C ) =>
% 4.57/4.83       ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 4.57/4.83         ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 4.57/4.83  thf('13', plain,
% 4.57/4.83      (![X20 : $i, X21 : $i, X22 : $i]:
% 4.57/4.83         (((k10_relat_1 @ X20 @ (k2_xboole_0 @ X21 @ X22))
% 4.57/4.83            = (k2_xboole_0 @ (k10_relat_1 @ X20 @ X21) @ 
% 4.57/4.83               (k10_relat_1 @ X20 @ X22)))
% 4.57/4.83          | ~ (v1_relat_1 @ X20))),
% 4.57/4.83      inference('cnf', [status(esa)], [t175_relat_1])).
% 4.57/4.83  thf(t7_xboole_1, axiom,
% 4.57/4.83    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 4.57/4.83  thf('14', plain,
% 4.57/4.83      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 4.57/4.83      inference('cnf', [status(esa)], [t7_xboole_1])).
% 4.57/4.83  thf('15', plain,
% 4.57/4.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.57/4.83         ((r1_tarski @ (k10_relat_1 @ X2 @ X1) @ 
% 4.57/4.83           (k10_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 4.57/4.83          | ~ (v1_relat_1 @ X2))),
% 4.57/4.83      inference('sup+', [status(thm)], ['13', '14'])).
% 4.57/4.83  thf('16', plain,
% 4.57/4.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.57/4.83         ((r1_tarski @ (k10_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 4.57/4.83           (k10_relat_1 @ X2 @ X0))
% 4.57/4.83          | ~ (v1_relat_1 @ X2))),
% 4.57/4.83      inference('sup+', [status(thm)], ['12', '15'])).
% 4.57/4.83  thf('17', plain,
% 4.57/4.83      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 4.57/4.83      inference('sup+', [status(thm)], ['1', '2'])).
% 4.57/4.83  thf('18', plain,
% 4.57/4.83      (![X7 : $i, X8 : $i]:
% 4.57/4.83         (((X8) = (k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7)))
% 4.57/4.83          | ~ (r1_tarski @ X7 @ X8))),
% 4.57/4.83      inference('cnf', [status(esa)], [t45_xboole_1])).
% 4.57/4.83  thf('19', plain,
% 4.57/4.83      (![X0 : $i, X1 : $i]:
% 4.57/4.83         ((X0)
% 4.57/4.83           = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ 
% 4.57/4.83              (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))))),
% 4.57/4.83      inference('sup-', [status(thm)], ['17', '18'])).
% 4.57/4.83  thf('20', plain,
% 4.57/4.83      (![X0 : $i, X1 : $i]:
% 4.57/4.83         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 4.57/4.83           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 4.57/4.83      inference('sup+', [status(thm)], ['8', '9'])).
% 4.57/4.83  thf('21', plain,
% 4.57/4.83      (![X0 : $i, X1 : $i]:
% 4.57/4.83         ((X0)
% 4.57/4.83           = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ 
% 4.57/4.83              (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))))),
% 4.57/4.83      inference('demod', [status(thm)], ['19', '20'])).
% 4.57/4.83  thf('22', plain,
% 4.57/4.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.57/4.83         ((r1_tarski @ (k10_relat_1 @ X2 @ X1) @ 
% 4.57/4.83           (k10_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 4.57/4.83          | ~ (v1_relat_1 @ X2))),
% 4.57/4.83      inference('sup+', [status(thm)], ['13', '14'])).
% 4.57/4.83  thf('23', plain,
% 4.57/4.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.57/4.83         ((r1_tarski @ (k10_relat_1 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 4.57/4.83           (k10_relat_1 @ X2 @ X0))
% 4.57/4.83          | ~ (v1_relat_1 @ X2))),
% 4.57/4.83      inference('sup+', [status(thm)], ['21', '22'])).
% 4.57/4.83  thf(t19_xboole_1, axiom,
% 4.57/4.83    (![A:$i,B:$i,C:$i]:
% 4.57/4.83     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 4.57/4.83       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 4.57/4.83  thf('24', plain,
% 4.57/4.83      (![X2 : $i, X3 : $i, X4 : $i]:
% 4.57/4.83         (~ (r1_tarski @ X2 @ X3)
% 4.57/4.83          | ~ (r1_tarski @ X2 @ X4)
% 4.57/4.83          | (r1_tarski @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 4.57/4.83      inference('cnf', [status(esa)], [t19_xboole_1])).
% 4.57/4.83  thf('25', plain,
% 4.57/4.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.57/4.83         (~ (v1_relat_1 @ X1)
% 4.57/4.83          | (r1_tarski @ (k10_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ 
% 4.57/4.83             (k3_xboole_0 @ (k10_relat_1 @ X1 @ X0) @ X3))
% 4.57/4.83          | ~ (r1_tarski @ (k10_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ X3))),
% 4.57/4.83      inference('sup-', [status(thm)], ['23', '24'])).
% 4.57/4.83  thf('26', plain,
% 4.57/4.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.57/4.83         (~ (v1_relat_1 @ X1)
% 4.57/4.83          | (r1_tarski @ (k10_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 4.57/4.83             (k3_xboole_0 @ (k10_relat_1 @ X1 @ X2) @ (k10_relat_1 @ X1 @ X0)))
% 4.57/4.83          | ~ (v1_relat_1 @ X1))),
% 4.57/4.83      inference('sup-', [status(thm)], ['16', '25'])).
% 4.57/4.83  thf('27', plain,
% 4.57/4.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.57/4.83         ((r1_tarski @ (k10_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 4.57/4.83           (k3_xboole_0 @ (k10_relat_1 @ X1 @ X2) @ (k10_relat_1 @ X1 @ X0)))
% 4.57/4.83          | ~ (v1_relat_1 @ X1))),
% 4.57/4.83      inference('simplify', [status(thm)], ['26'])).
% 4.57/4.83  thf(t176_relat_1, conjecture,
% 4.57/4.83    (![A:$i,B:$i,C:$i]:
% 4.57/4.83     ( ( v1_relat_1 @ C ) =>
% 4.57/4.83       ( r1_tarski @
% 4.57/4.83         ( k10_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 4.57/4.83         ( k3_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 4.57/4.83  thf(zf_stmt_0, negated_conjecture,
% 4.57/4.83    (~( ![A:$i,B:$i,C:$i]:
% 4.57/4.83        ( ( v1_relat_1 @ C ) =>
% 4.57/4.83          ( r1_tarski @
% 4.57/4.83            ( k10_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 4.57/4.83            ( k3_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )),
% 4.57/4.83    inference('cnf.neg', [status(esa)], [t176_relat_1])).
% 4.57/4.83  thf('28', plain,
% 4.57/4.83      (~ (r1_tarski @ (k10_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 4.57/4.83          (k3_xboole_0 @ (k10_relat_1 @ sk_C @ sk_A) @ 
% 4.57/4.83           (k10_relat_1 @ sk_C @ sk_B)))),
% 4.57/4.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.57/4.83  thf('29', plain, (~ (v1_relat_1 @ sk_C)),
% 4.57/4.83      inference('sup-', [status(thm)], ['27', '28'])).
% 4.57/4.83  thf('30', plain, ((v1_relat_1 @ sk_C)),
% 4.57/4.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.57/4.83  thf('31', plain, ($false), inference('demod', [status(thm)], ['29', '30'])).
% 4.57/4.83  
% 4.57/4.83  % SZS output end Refutation
% 4.57/4.83  
% 4.57/4.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

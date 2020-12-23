%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZODpCy04nv

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:50 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   33 (  44 expanded)
%              Number of leaves         :   10 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :  278 ( 369 expanded)
%              Number of equality atoms :   27 (  38 expanded)
%              Maximal formula depth    :   10 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t111_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
        = ( k3_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t111_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_C @ sk_B ) )
 != ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('4',plain,(
    ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k3_xboole_0 @ sk_B @ sk_C ) )
 != ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','1','2','3'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('6',plain,(
    ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) )
 != ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k3_xboole_0 @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('15',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','16','17','18'])).

thf('20',plain,(
    ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) )
 != ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['6','19'])).

thf('21',plain,(
    $false ),
    inference(simplify,[status(thm)],['20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZODpCy04nv
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:21:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.46/0.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.64  % Solved by: fo/fo7.sh
% 0.46/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.64  % done 163 iterations in 0.199s
% 0.46/0.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.64  % SZS output start Refutation
% 0.46/0.64  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.64  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.64  thf(t111_xboole_1, conjecture,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 0.46/0.64       ( k3_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 0.46/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.64    (~( ![A:$i,B:$i,C:$i]:
% 0.46/0.64        ( ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 0.46/0.64          ( k3_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ B ) ) )),
% 0.46/0.64    inference('cnf.neg', [status(esa)], [t111_xboole_1])).
% 0.46/0.64  thf('0', plain,
% 0.46/0.64      (((k4_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 0.46/0.64         (k3_xboole_0 @ sk_C @ sk_B))
% 0.46/0.64         != (k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(commutativity_k3_xboole_0, axiom,
% 0.46/0.64    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.46/0.64  thf('1', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.64  thf('2', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.64  thf('3', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.64  thf('4', plain,
% 0.46/0.64      (((k4_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ 
% 0.46/0.64         (k3_xboole_0 @ sk_B @ sk_C))
% 0.46/0.64         != (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 0.46/0.64      inference('demod', [status(thm)], ['0', '1', '2', '3'])).
% 0.46/0.64  thf(t49_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.46/0.64       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.46/0.64  thf('5', plain,
% 0.46/0.64      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.64         ((k3_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X12))
% 0.46/0.64           = (k4_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12))),
% 0.46/0.64      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.46/0.64  thf('6', plain,
% 0.46/0.64      (((k3_xboole_0 @ sk_B @ 
% 0.46/0.64         (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))
% 0.46/0.64         != (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 0.46/0.64      inference('demod', [status(thm)], ['4', '5'])).
% 0.46/0.64  thf(t16_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.46/0.64       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.46/0.64  thf('7', plain,
% 0.46/0.64      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.46/0.64         ((k3_xboole_0 @ (k3_xboole_0 @ X4 @ X5) @ X6)
% 0.46/0.64           = (k3_xboole_0 @ X4 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.46/0.64  thf('8', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.64  thf('9', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 0.46/0.64           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['7', '8'])).
% 0.46/0.64  thf('10', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.64  thf(t47_xboole_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.46/0.64  thf('11', plain,
% 0.46/0.64      (![X8 : $i, X9 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9))
% 0.46/0.64           = (k4_xboole_0 @ X8 @ X9))),
% 0.46/0.64      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.46/0.64  thf('12', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.46/0.64           = (k4_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('sup+', [status(thm)], ['10', '11'])).
% 0.46/0.64  thf('13', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ 
% 0.46/0.64           (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.46/0.64           = (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['9', '12'])).
% 0.46/0.64  thf('14', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.64  thf('15', plain,
% 0.46/0.64      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.64         ((k3_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X12))
% 0.46/0.64           = (k4_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12))),
% 0.46/0.64      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.46/0.64  thf('16', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.46/0.64           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 0.46/0.64      inference('sup+', [status(thm)], ['14', '15'])).
% 0.46/0.64  thf('17', plain,
% 0.46/0.64      (![X8 : $i, X9 : $i]:
% 0.46/0.64         ((k4_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9))
% 0.46/0.64           = (k4_xboole_0 @ X8 @ X9))),
% 0.46/0.64      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.46/0.64  thf('18', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.46/0.64           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 0.46/0.64      inference('sup+', [status(thm)], ['14', '15'])).
% 0.46/0.64  thf('19', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.46/0.64           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X0)))),
% 0.46/0.64      inference('demod', [status(thm)], ['13', '16', '17', '18'])).
% 0.46/0.64  thf('20', plain,
% 0.46/0.64      (((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))
% 0.46/0.64         != (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 0.46/0.64      inference('demod', [status(thm)], ['6', '19'])).
% 0.46/0.64  thf('21', plain, ($false), inference('simplify', [status(thm)], ['20'])).
% 0.46/0.64  
% 0.46/0.64  % SZS output end Refutation
% 0.46/0.64  
% 0.46/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

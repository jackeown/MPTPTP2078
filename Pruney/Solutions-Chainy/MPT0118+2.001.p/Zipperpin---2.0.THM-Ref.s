%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.z0xsXywIt5

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:49 EST 2020

% Result     : Theorem 5.49s
% Output     : Refutation 5.49s
% Verified   : 
% Statistics : Number of formulae       :   42 (  65 expanded)
%              Number of leaves         :   12 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :  354 ( 559 expanded)
%              Number of equality atoms :   35 (  58 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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

thf('7',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('8',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k3_xboole_0 @ X7 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['7','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('17',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('20',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k3_xboole_0 @ X7 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['15','18','21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('25',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) )
 != ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['6','23','26'])).

thf('28',plain,(
    $false ),
    inference(simplify,[status(thm)],['27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.z0xsXywIt5
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:07:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 5.49/5.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.49/5.67  % Solved by: fo/fo7.sh
% 5.49/5.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.49/5.67  % done 1489 iterations in 5.239s
% 5.49/5.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.49/5.67  % SZS output start Refutation
% 5.49/5.67  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 5.49/5.67  thf(sk_B_type, type, sk_B: $i).
% 5.49/5.67  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 5.49/5.67  thf(sk_A_type, type, sk_A: $i).
% 5.49/5.67  thf(sk_C_type, type, sk_C: $i).
% 5.49/5.67  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 5.49/5.67  thf(t111_xboole_1, conjecture,
% 5.49/5.67    (![A:$i,B:$i,C:$i]:
% 5.49/5.67     ( ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 5.49/5.67       ( k3_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 5.49/5.67  thf(zf_stmt_0, negated_conjecture,
% 5.49/5.67    (~( ![A:$i,B:$i,C:$i]:
% 5.49/5.67        ( ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 5.49/5.67          ( k3_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ B ) ) )),
% 5.49/5.67    inference('cnf.neg', [status(esa)], [t111_xboole_1])).
% 5.49/5.67  thf('0', plain,
% 5.49/5.67      (((k4_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 5.49/5.67         (k3_xboole_0 @ sk_C @ sk_B))
% 5.49/5.67         != (k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B))),
% 5.49/5.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.49/5.67  thf(commutativity_k3_xboole_0, axiom,
% 5.49/5.67    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 5.49/5.67  thf('1', plain,
% 5.49/5.67      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.49/5.67      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.49/5.67  thf('2', plain,
% 5.49/5.67      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.49/5.67      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.49/5.67  thf('3', plain,
% 5.49/5.67      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.49/5.67      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.49/5.67  thf('4', plain,
% 5.49/5.67      (((k4_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ 
% 5.49/5.67         (k3_xboole_0 @ sk_B @ sk_C))
% 5.49/5.67         != (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 5.49/5.67      inference('demod', [status(thm)], ['0', '1', '2', '3'])).
% 5.49/5.67  thf(t49_xboole_1, axiom,
% 5.49/5.67    (![A:$i,B:$i,C:$i]:
% 5.49/5.67     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 5.49/5.67       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 5.49/5.67  thf('5', plain,
% 5.49/5.67      (![X10 : $i, X11 : $i, X12 : $i]:
% 5.49/5.67         ((k3_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X12))
% 5.49/5.67           = (k4_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12))),
% 5.49/5.67      inference('cnf', [status(esa)], [t49_xboole_1])).
% 5.49/5.67  thf('6', plain,
% 5.49/5.67      (((k3_xboole_0 @ sk_B @ 
% 5.49/5.67         (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))
% 5.49/5.67         != (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 5.49/5.67      inference('demod', [status(thm)], ['4', '5'])).
% 5.49/5.67  thf('7', plain,
% 5.49/5.67      (![X10 : $i, X11 : $i, X12 : $i]:
% 5.49/5.67         ((k3_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X12))
% 5.49/5.67           = (k4_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12))),
% 5.49/5.67      inference('cnf', [status(esa)], [t49_xboole_1])).
% 5.49/5.67  thf(idempotence_k3_xboole_0, axiom,
% 5.49/5.67    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 5.49/5.67  thf('8', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 5.49/5.67      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 5.49/5.67  thf(t16_xboole_1, axiom,
% 5.49/5.67    (![A:$i,B:$i,C:$i]:
% 5.49/5.67     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 5.49/5.67       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 5.49/5.67  thf('9', plain,
% 5.49/5.67      (![X7 : $i, X8 : $i, X9 : $i]:
% 5.49/5.67         ((k3_xboole_0 @ (k3_xboole_0 @ X7 @ X8) @ X9)
% 5.49/5.67           = (k3_xboole_0 @ X7 @ (k3_xboole_0 @ X8 @ X9)))),
% 5.49/5.67      inference('cnf', [status(esa)], [t16_xboole_1])).
% 5.49/5.67  thf('10', plain,
% 5.49/5.67      (![X0 : $i, X1 : $i]:
% 5.49/5.67         ((k3_xboole_0 @ X0 @ X1)
% 5.49/5.67           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 5.49/5.67      inference('sup+', [status(thm)], ['8', '9'])).
% 5.49/5.67  thf(t100_xboole_1, axiom,
% 5.49/5.67    (![A:$i,B:$i]:
% 5.49/5.67     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 5.49/5.67  thf('11', plain,
% 5.49/5.67      (![X5 : $i, X6 : $i]:
% 5.49/5.67         ((k4_xboole_0 @ X5 @ X6)
% 5.49/5.67           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 5.49/5.67      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.49/5.67  thf('12', plain,
% 5.49/5.67      (![X0 : $i, X1 : $i]:
% 5.49/5.67         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 5.49/5.67           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 5.49/5.67      inference('sup+', [status(thm)], ['10', '11'])).
% 5.49/5.67  thf('13', plain,
% 5.49/5.67      (![X5 : $i, X6 : $i]:
% 5.49/5.67         ((k4_xboole_0 @ X5 @ X6)
% 5.49/5.67           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 5.49/5.67      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.49/5.67  thf('14', plain,
% 5.49/5.67      (![X0 : $i, X1 : $i]:
% 5.49/5.67         ((k4_xboole_0 @ X1 @ X0)
% 5.49/5.67           = (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 5.49/5.67      inference('sup+', [status(thm)], ['12', '13'])).
% 5.49/5.67  thf('15', plain,
% 5.49/5.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.49/5.67         ((k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)
% 5.49/5.67           = (k3_xboole_0 @ X2 @ 
% 5.49/5.67              (k4_xboole_0 @ X1 @ (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))))),
% 5.49/5.67      inference('sup+', [status(thm)], ['7', '14'])).
% 5.49/5.67  thf('16', plain,
% 5.49/5.67      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.49/5.67      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.49/5.67  thf('17', plain,
% 5.49/5.67      (![X10 : $i, X11 : $i, X12 : $i]:
% 5.49/5.67         ((k3_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X12))
% 5.49/5.67           = (k4_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12))),
% 5.49/5.67      inference('cnf', [status(esa)], [t49_xboole_1])).
% 5.49/5.67  thf('18', plain,
% 5.49/5.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.49/5.67         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 5.49/5.67           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 5.49/5.67      inference('sup+', [status(thm)], ['16', '17'])).
% 5.49/5.67  thf('19', plain,
% 5.49/5.67      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.49/5.67      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.49/5.67  thf('20', plain,
% 5.49/5.67      (![X7 : $i, X8 : $i, X9 : $i]:
% 5.49/5.67         ((k3_xboole_0 @ (k3_xboole_0 @ X7 @ X8) @ X9)
% 5.49/5.67           = (k3_xboole_0 @ X7 @ (k3_xboole_0 @ X8 @ X9)))),
% 5.49/5.67      inference('cnf', [status(esa)], [t16_xboole_1])).
% 5.49/5.67  thf('21', plain,
% 5.49/5.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.49/5.67         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 5.49/5.67           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 5.49/5.67      inference('sup+', [status(thm)], ['19', '20'])).
% 5.49/5.67  thf('22', plain,
% 5.49/5.67      (![X0 : $i, X1 : $i]:
% 5.49/5.67         ((k4_xboole_0 @ X1 @ X0)
% 5.49/5.67           = (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 5.49/5.67      inference('sup+', [status(thm)], ['12', '13'])).
% 5.49/5.67  thf('23', plain,
% 5.49/5.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.49/5.67         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X0))
% 5.49/5.67           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ X0))))),
% 5.49/5.67      inference('demod', [status(thm)], ['15', '18', '21', '22'])).
% 5.49/5.67  thf('24', plain,
% 5.49/5.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.49/5.67         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 5.49/5.67           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 5.49/5.67      inference('sup+', [status(thm)], ['16', '17'])).
% 5.49/5.67  thf('25', plain,
% 5.49/5.67      (![X10 : $i, X11 : $i, X12 : $i]:
% 5.49/5.67         ((k3_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X12))
% 5.49/5.67           = (k4_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12))),
% 5.49/5.67      inference('cnf', [status(esa)], [t49_xboole_1])).
% 5.49/5.67  thf('26', plain,
% 5.49/5.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.49/5.67         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X0))
% 5.49/5.67           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 5.49/5.67      inference('sup+', [status(thm)], ['24', '25'])).
% 5.49/5.67  thf('27', plain,
% 5.49/5.67      (((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))
% 5.49/5.67         != (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 5.49/5.67      inference('demod', [status(thm)], ['6', '23', '26'])).
% 5.49/5.67  thf('28', plain, ($false), inference('simplify', [status(thm)], ['27'])).
% 5.49/5.67  
% 5.49/5.67  % SZS output end Refutation
% 5.49/5.67  
% 5.49/5.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

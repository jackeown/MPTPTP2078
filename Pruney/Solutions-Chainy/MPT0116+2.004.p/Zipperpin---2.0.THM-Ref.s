%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LNyUB457Z0

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:46 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :   49 (  55 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :  287 ( 332 expanded)
%              Number of equality atoms :   26 (  29 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t109_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t109_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('2',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('6',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('14',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('15',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('18',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','21'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('23',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X6 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['1','26'])).

thf('28',plain,(
    $false ),
    inference(demod,[status(thm)],['0','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LNyUB457Z0
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:34:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.58/0.79  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.79  % Solved by: fo/fo7.sh
% 0.58/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.79  % done 556 iterations in 0.324s
% 0.58/0.79  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.79  % SZS output start Refutation
% 0.58/0.79  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.58/0.79  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.79  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.79  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.58/0.79  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.58/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.79  thf(sk_C_type, type, sk_C: $i).
% 0.58/0.79  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.58/0.79  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.79  thf(t109_xboole_1, conjecture,
% 0.58/0.79    (![A:$i,B:$i,C:$i]:
% 0.58/0.79     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 0.58/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.79    (~( ![A:$i,B:$i,C:$i]:
% 0.58/0.79        ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )),
% 0.58/0.79    inference('cnf.neg', [status(esa)], [t109_xboole_1])).
% 0.58/0.79  thf('0', plain, (~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf(t36_xboole_1, axiom,
% 0.58/0.79    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.58/0.79  thf('1', plain,
% 0.58/0.79      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 0.58/0.79      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.58/0.79  thf('2', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf(t28_xboole_1, axiom,
% 0.58/0.79    (![A:$i,B:$i]:
% 0.58/0.79     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.58/0.79  thf('3', plain,
% 0.58/0.79      (![X9 : $i, X10 : $i]:
% 0.58/0.79         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.58/0.79      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.58/0.79  thf('4', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.58/0.79      inference('sup-', [status(thm)], ['2', '3'])).
% 0.58/0.79  thf(commutativity_k3_xboole_0, axiom,
% 0.58/0.79    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.58/0.79  thf('5', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.58/0.79      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.58/0.79  thf('6', plain,
% 0.58/0.79      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 0.58/0.79      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.58/0.79  thf('7', plain,
% 0.58/0.79      (![X9 : $i, X10 : $i]:
% 0.58/0.79         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.58/0.79      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.58/0.79  thf('8', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]:
% 0.58/0.79         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.58/0.79           = (k4_xboole_0 @ X0 @ X1))),
% 0.58/0.79      inference('sup-', [status(thm)], ['6', '7'])).
% 0.58/0.79  thf('9', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.58/0.79      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.58/0.79  thf('10', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]:
% 0.58/0.79         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.58/0.79           = (k4_xboole_0 @ X0 @ X1))),
% 0.58/0.79      inference('demod', [status(thm)], ['8', '9'])).
% 0.58/0.79  thf(t100_xboole_1, axiom,
% 0.58/0.79    (![A:$i,B:$i]:
% 0.58/0.79     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.58/0.79  thf('11', plain,
% 0.58/0.79      (![X4 : $i, X5 : $i]:
% 0.58/0.79         ((k4_xboole_0 @ X4 @ X5)
% 0.58/0.79           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.58/0.79      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.58/0.79  thf('12', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]:
% 0.58/0.79         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.58/0.79           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.58/0.79      inference('sup+', [status(thm)], ['10', '11'])).
% 0.58/0.79  thf('13', plain,
% 0.58/0.79      (![X4 : $i, X5 : $i]:
% 0.58/0.79         ((k4_xboole_0 @ X4 @ X5)
% 0.58/0.79           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.58/0.79      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.58/0.79  thf(t92_xboole_1, axiom,
% 0.58/0.79    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.58/0.79  thf('14', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ X17) = (k1_xboole_0))),
% 0.58/0.79      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.58/0.79  thf(t91_xboole_1, axiom,
% 0.58/0.79    (![A:$i,B:$i,C:$i]:
% 0.58/0.79     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.58/0.79       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.58/0.79  thf('15', plain,
% 0.58/0.79      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.58/0.79         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 0.58/0.79           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 0.58/0.79      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.58/0.79  thf('16', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]:
% 0.58/0.79         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.58/0.79           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.58/0.79      inference('sup+', [status(thm)], ['14', '15'])).
% 0.58/0.79  thf(commutativity_k5_xboole_0, axiom,
% 0.58/0.79    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.58/0.79  thf('17', plain,
% 0.58/0.79      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.58/0.79      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.58/0.79  thf(t5_boole, axiom,
% 0.58/0.79    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.58/0.79  thf('18', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.58/0.79      inference('cnf', [status(esa)], [t5_boole])).
% 0.58/0.79  thf('19', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.58/0.79      inference('sup+', [status(thm)], ['17', '18'])).
% 0.58/0.79  thf('20', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]:
% 0.58/0.79         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.58/0.79      inference('demod', [status(thm)], ['16', '19'])).
% 0.58/0.79  thf('21', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]:
% 0.58/0.79         ((k3_xboole_0 @ X1 @ X0)
% 0.58/0.79           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.58/0.79      inference('sup+', [status(thm)], ['13', '20'])).
% 0.58/0.79  thf('22', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]:
% 0.58/0.79         ((k3_xboole_0 @ X1 @ X0)
% 0.58/0.79           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.58/0.79      inference('sup+', [status(thm)], ['12', '21'])).
% 0.58/0.79  thf(t106_xboole_1, axiom,
% 0.58/0.79    (![A:$i,B:$i,C:$i]:
% 0.58/0.79     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.58/0.79       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.58/0.79  thf('23', plain,
% 0.58/0.79      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.58/0.79         ((r1_tarski @ X6 @ X7) | ~ (r1_tarski @ X6 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.58/0.79      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.58/0.79  thf('24', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.79         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X1))),
% 0.58/0.79      inference('sup-', [status(thm)], ['22', '23'])).
% 0.58/0.79  thf('25', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.79         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X0))),
% 0.58/0.79      inference('sup-', [status(thm)], ['5', '24'])).
% 0.58/0.79  thf('26', plain,
% 0.58/0.79      (![X0 : $i]: (~ (r1_tarski @ X0 @ sk_A) | (r1_tarski @ X0 @ sk_B))),
% 0.58/0.79      inference('sup-', [status(thm)], ['4', '25'])).
% 0.58/0.79  thf('27', plain,
% 0.58/0.79      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_A @ X0) @ sk_B)),
% 0.58/0.79      inference('sup-', [status(thm)], ['1', '26'])).
% 0.58/0.79  thf('28', plain, ($false), inference('demod', [status(thm)], ['0', '27'])).
% 0.58/0.79  
% 0.58/0.79  % SZS output end Refutation
% 0.58/0.79  
% 0.58/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AhZZQXpIml

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:30 EST 2020

% Result     : Theorem 1.21s
% Output     : Refutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :   43 (  48 expanded)
%              Number of leaves         :   16 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :  255 ( 299 expanded)
%              Number of equality atoms :   25 (  30 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t79_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) ),
    inference('cnf.neg',[status(esa)],[t79_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('1',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','10'])).

thf('12',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('15',plain,(
    ! [X13: $i] :
      ( r1_xboole_0 @ X13 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','20'])).

thf('22',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    $false ),
    inference(demod,[status(thm)],['0','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AhZZQXpIml
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:16:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.21/1.40  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.21/1.40  % Solved by: fo/fo7.sh
% 1.21/1.40  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.21/1.40  % done 1745 iterations in 0.951s
% 1.21/1.40  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.21/1.40  % SZS output start Refutation
% 1.21/1.40  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.21/1.40  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.21/1.40  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.21/1.40  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.21/1.40  thf(sk_A_type, type, sk_A: $i).
% 1.21/1.40  thf(sk_B_type, type, sk_B: $i).
% 1.21/1.40  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.21/1.40  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.21/1.40  thf(t79_xboole_1, conjecture,
% 1.21/1.40    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 1.21/1.40  thf(zf_stmt_0, negated_conjecture,
% 1.21/1.40    (~( ![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )),
% 1.21/1.40    inference('cnf.neg', [status(esa)], [t79_xboole_1])).
% 1.21/1.40  thf('0', plain, (~ (r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_B)),
% 1.21/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.40  thf(t3_boole, axiom,
% 1.21/1.40    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.21/1.40  thf('1', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 1.21/1.40      inference('cnf', [status(esa)], [t3_boole])).
% 1.21/1.40  thf(t36_xboole_1, axiom,
% 1.21/1.40    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.21/1.40  thf('2', plain,
% 1.21/1.40      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 1.21/1.40      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.21/1.40  thf('3', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.21/1.40      inference('sup+', [status(thm)], ['1', '2'])).
% 1.21/1.40  thf(t12_xboole_1, axiom,
% 1.21/1.40    (![A:$i,B:$i]:
% 1.21/1.40     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.21/1.40  thf('4', plain,
% 1.21/1.40      (![X3 : $i, X4 : $i]:
% 1.21/1.40         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 1.21/1.40      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.21/1.40  thf('5', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 1.21/1.40      inference('sup-', [status(thm)], ['3', '4'])).
% 1.21/1.40  thf(t41_xboole_1, axiom,
% 1.21/1.40    (![A:$i,B:$i,C:$i]:
% 1.21/1.40     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 1.21/1.40       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.21/1.40  thf('6', plain,
% 1.21/1.40      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.21/1.40         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 1.21/1.40           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 1.21/1.40      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.21/1.40  thf(t48_xboole_1, axiom,
% 1.21/1.40    (![A:$i,B:$i]:
% 1.21/1.40     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.21/1.40  thf('7', plain,
% 1.21/1.40      (![X11 : $i, X12 : $i]:
% 1.21/1.40         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 1.21/1.40           = (k3_xboole_0 @ X11 @ X12))),
% 1.21/1.40      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.21/1.40  thf('8', plain,
% 1.21/1.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.21/1.40         ((k4_xboole_0 @ X2 @ 
% 1.21/1.40           (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))
% 1.21/1.40           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 1.21/1.40      inference('sup+', [status(thm)], ['6', '7'])).
% 1.21/1.40  thf('9', plain,
% 1.21/1.40      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.21/1.40         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 1.21/1.40           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 1.21/1.40      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.21/1.40  thf('10', plain,
% 1.21/1.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.21/1.40         ((k4_xboole_0 @ X2 @ 
% 1.21/1.40           (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))
% 1.21/1.40           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 1.21/1.40      inference('demod', [status(thm)], ['8', '9'])).
% 1.21/1.40  thf('11', plain,
% 1.21/1.40      (![X0 : $i, X1 : $i]:
% 1.21/1.40         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 1.21/1.40           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 1.21/1.40      inference('sup+', [status(thm)], ['5', '10'])).
% 1.21/1.40  thf('12', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 1.21/1.40      inference('cnf', [status(esa)], [t3_boole])).
% 1.21/1.40  thf('13', plain,
% 1.21/1.40      (![X11 : $i, X12 : $i]:
% 1.21/1.40         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 1.21/1.40           = (k3_xboole_0 @ X11 @ X12))),
% 1.21/1.40      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.21/1.40  thf('14', plain,
% 1.21/1.40      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.21/1.40      inference('sup+', [status(thm)], ['12', '13'])).
% 1.21/1.40  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 1.21/1.40  thf('15', plain, (![X13 : $i]: (r1_xboole_0 @ X13 @ k1_xboole_0)),
% 1.21/1.40      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.21/1.40  thf(d7_xboole_0, axiom,
% 1.21/1.40    (![A:$i,B:$i]:
% 1.21/1.40     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.21/1.40       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.21/1.40  thf('16', plain,
% 1.21/1.40      (![X0 : $i, X1 : $i]:
% 1.21/1.40         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.21/1.40      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.21/1.40  thf('17', plain,
% 1.21/1.40      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.21/1.40      inference('sup-', [status(thm)], ['15', '16'])).
% 1.21/1.40  thf('18', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.21/1.40      inference('demod', [status(thm)], ['14', '17'])).
% 1.21/1.40  thf('19', plain,
% 1.21/1.40      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.21/1.40         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 1.21/1.40           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 1.21/1.40      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.21/1.40  thf('20', plain,
% 1.21/1.40      (![X0 : $i, X1 : $i]:
% 1.21/1.40         ((k1_xboole_0)
% 1.21/1.40           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.21/1.40      inference('sup+', [status(thm)], ['18', '19'])).
% 1.21/1.40  thf('21', plain,
% 1.21/1.40      (![X0 : $i, X1 : $i]:
% 1.21/1.40         ((k1_xboole_0) = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 1.21/1.40      inference('sup+', [status(thm)], ['11', '20'])).
% 1.21/1.40  thf('22', plain,
% 1.21/1.40      (![X0 : $i, X2 : $i]:
% 1.21/1.40         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 1.21/1.40      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.21/1.40  thf('23', plain,
% 1.21/1.40      (![X0 : $i, X1 : $i]:
% 1.21/1.40         (((k1_xboole_0) != (k1_xboole_0))
% 1.21/1.40          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 1.21/1.40      inference('sup-', [status(thm)], ['21', '22'])).
% 1.21/1.40  thf('24', plain,
% 1.21/1.40      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 1.21/1.40      inference('simplify', [status(thm)], ['23'])).
% 1.21/1.40  thf('25', plain, ($false), inference('demod', [status(thm)], ['0', '24'])).
% 1.21/1.40  
% 1.21/1.40  % SZS output end Refutation
% 1.21/1.40  
% 1.21/1.41  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

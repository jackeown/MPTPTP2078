%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hn6iwKunPL

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:26 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   34 (  37 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :    9
%              Number of atoms          :  206 ( 239 expanded)
%              Number of equality atoms :   24 (  27 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t78_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_xboole_0 @ A @ B )
       => ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          = ( k3_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t78_xboole_1])).

thf('0',plain,(
    ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
 != ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ ( k4_xboole_0 @ X13 @ X14 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('5',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_A ),
    inference('sup+',[status(thm)],['3','4'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('7',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ( k3_xboole_0 @ sk_A @ sk_C )
 != ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['0','15'])).

thf('17',plain,(
    $false ),
    inference(simplify,[status(thm)],['16'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hn6iwKunPL
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:49:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.37/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.53  % Solved by: fo/fo7.sh
% 0.37/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.53  % done 164 iterations in 0.072s
% 0.37/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.53  % SZS output start Refutation
% 0.37/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.53  thf(t78_xboole_1, conjecture,
% 0.37/0.53    (![A:$i,B:$i,C:$i]:
% 0.37/0.53     ( ( r1_xboole_0 @ A @ B ) =>
% 0.37/0.53       ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.37/0.53         ( k3_xboole_0 @ A @ C ) ) ))).
% 0.37/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.53        ( ( r1_xboole_0 @ A @ B ) =>
% 0.37/0.53          ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.37/0.53            ( k3_xboole_0 @ A @ C ) ) ) )),
% 0.37/0.53    inference('cnf.neg', [status(esa)], [t78_xboole_1])).
% 0.37/0.53  thf('0', plain,
% 0.37/0.53      (((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.37/0.53         != (k3_xboole_0 @ sk_A @ sk_C))),
% 0.37/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.53  thf('1', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.37/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.53  thf(d7_xboole_0, axiom,
% 0.37/0.53    (![A:$i,B:$i]:
% 0.37/0.53     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.37/0.53       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.37/0.53  thf('2', plain,
% 0.37/0.53      (![X2 : $i, X3 : $i]:
% 0.37/0.53         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.37/0.53      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.37/0.53  thf('3', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.37/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.53  thf(t51_xboole_1, axiom,
% 0.37/0.53    (![A:$i,B:$i]:
% 0.37/0.53     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.37/0.53       ( A ) ))).
% 0.37/0.53  thf('4', plain,
% 0.37/0.53      (![X13 : $i, X14 : $i]:
% 0.37/0.53         ((k2_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ (k4_xboole_0 @ X13 @ X14))
% 0.37/0.53           = (X13))),
% 0.37/0.54      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.37/0.54  thf('5', plain,
% 0.37/0.54      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_A))),
% 0.37/0.54      inference('sup+', [status(thm)], ['3', '4'])).
% 0.37/0.54  thf(commutativity_k2_xboole_0, axiom,
% 0.37/0.54    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.37/0.54  thf('6', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.54      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.37/0.54  thf(t1_boole, axiom,
% 0.37/0.54    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.37/0.54  thf('7', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.37/0.54      inference('cnf', [status(esa)], [t1_boole])).
% 0.37/0.54  thf('8', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.37/0.54      inference('sup+', [status(thm)], ['6', '7'])).
% 0.37/0.54  thf('9', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.37/0.54      inference('demod', [status(thm)], ['5', '8'])).
% 0.37/0.54  thf(t41_xboole_1, axiom,
% 0.37/0.54    (![A:$i,B:$i,C:$i]:
% 0.37/0.54     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.37/0.54       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.37/0.54  thf('10', plain,
% 0.37/0.54      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.37/0.54         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 0.37/0.54           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 0.37/0.54      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.37/0.54  thf(t48_xboole_1, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.37/0.54  thf('11', plain,
% 0.37/0.54      (![X11 : $i, X12 : $i]:
% 0.37/0.54         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.37/0.54           = (k3_xboole_0 @ X11 @ X12))),
% 0.37/0.54      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.54  thf('12', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.54         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 0.37/0.54           = (k3_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.37/0.54      inference('sup+', [status(thm)], ['10', '11'])).
% 0.37/0.54  thf('13', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ X0))
% 0.37/0.54           = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.37/0.54      inference('sup+', [status(thm)], ['9', '12'])).
% 0.37/0.54  thf('14', plain,
% 0.37/0.54      (![X11 : $i, X12 : $i]:
% 0.37/0.54         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.37/0.54           = (k3_xboole_0 @ X11 @ X12))),
% 0.37/0.54      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.54  thf('15', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         ((k3_xboole_0 @ sk_A @ X0)
% 0.37/0.54           = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.37/0.54      inference('demod', [status(thm)], ['13', '14'])).
% 0.37/0.54  thf('16', plain,
% 0.37/0.54      (((k3_xboole_0 @ sk_A @ sk_C) != (k3_xboole_0 @ sk_A @ sk_C))),
% 0.37/0.54      inference('demod', [status(thm)], ['0', '15'])).
% 0.37/0.54  thf('17', plain, ($false), inference('simplify', [status(thm)], ['16'])).
% 0.37/0.54  
% 0.37/0.54  % SZS output end Refutation
% 0.37/0.54  
% 0.37/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

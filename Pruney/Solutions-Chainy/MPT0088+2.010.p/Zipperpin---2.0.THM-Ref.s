%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.J9F9v8KpOE

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   41 (  54 expanded)
%              Number of leaves         :   12 (  22 expanded)
%              Depth                    :   12
%              Number of atoms          :  272 ( 414 expanded)
%              Number of equality atoms :    7 (  10 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t81_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
       => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t81_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('3',plain,(
    r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) )
      | ~ ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ ( k2_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('9',plain,(
    r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ ( k2_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('12',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ( r1_xboole_0 @ X6 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('17',plain,(
    r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('19',plain,(
    r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('22',plain,(
    r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('24',plain,(
    r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('26',plain,(
    r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['0','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.J9F9v8KpOE
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:36:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 79 iterations in 0.052s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.53  thf(t81_xboole_1, conjecture,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.21/0.53       ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.53        ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.21/0.53          ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t81_xboole_1])).
% 0.21/0.53  thf('0', plain, (~ (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('1', plain, ((r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(symmetry_r1_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X2 : $i, X3 : $i]:
% 0.21/0.53         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.21/0.53      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.21/0.53  thf('3', plain, ((r1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.21/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.53  thf(t79_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (![X10 : $i, X11 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X11)),
% 0.21/0.53      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.21/0.53  thf(t70_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.21/0.53            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.21/0.53       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.21/0.53            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.53         ((r1_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8))
% 0.21/0.53          | ~ (r1_xboole_0 @ X6 @ X7)
% 0.21/0.53          | ~ (r1_xboole_0 @ X6 @ X8))),
% 0.21/0.53      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.21/0.53          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      ((r1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ (k2_xboole_0 @ sk_C @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['3', '6'])).
% 0.21/0.53  thf(commutativity_k2_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      ((r1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ (k2_xboole_0 @ sk_A @ sk_C))),
% 0.21/0.53      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.53  thf(t39_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      (![X4 : $i, X5 : $i]:
% 0.21/0.53         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 0.21/0.53           = (k2_xboole_0 @ X4 @ X5))),
% 0.21/0.53      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (![X6 : $i, X7 : $i, X9 : $i]:
% 0.21/0.53         ((r1_xboole_0 @ X6 @ X9)
% 0.21/0.53          | ~ (r1_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X9)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (r1_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.21/0.53          | (r1_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (r1_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.21/0.53          | (r1_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['10', '13'])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      ((r1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ (k4_xboole_0 @ sk_A @ sk_C))),
% 0.21/0.53      inference('sup-', [status(thm)], ['9', '14'])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (![X2 : $i, X3 : $i]:
% 0.21/0.53         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.21/0.53      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      ((r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C) @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.21/0.53          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      ((r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C) @ 
% 0.21/0.53        (k2_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (![X4 : $i, X5 : $i]:
% 0.21/0.53         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 0.21/0.53           = (k2_xboole_0 @ X4 @ X5))),
% 0.21/0.53      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      ((r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C) @ (k2_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.53      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      (![X6 : $i, X7 : $i, X9 : $i]:
% 0.21/0.53         ((r1_xboole_0 @ X6 @ X7)
% 0.21/0.53          | ~ (r1_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X9)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.21/0.53  thf('24', plain, ((r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 0.21/0.53      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      (![X2 : $i, X3 : $i]:
% 0.21/0.53         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.21/0.53      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.21/0.53  thf('26', plain, ((r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 0.21/0.53      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.53  thf('27', plain, ($false), inference('demod', [status(thm)], ['0', '26'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

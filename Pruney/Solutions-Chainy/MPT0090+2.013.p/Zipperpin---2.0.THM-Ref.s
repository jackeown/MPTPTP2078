%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5MlitfVfsz

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   45 (  75 expanded)
%              Number of leaves         :   16 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :  262 ( 496 expanded)
%              Number of equality atoms :   31 (  59 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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

thf(t83_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_xboole_0 @ A @ B )
      <=> ( ( k4_xboole_0 @ A @ B )
          = A ) ) ),
    inference('cnf.neg',[status(esa)],[t83_xboole_1])).

thf('0',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('3',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('8',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_B )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('10',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['5','10','11'])).

thf('13',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['3','12'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('17',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ k1_xboole_0 )
    = sk_A ),
    inference('sup+',[status(thm)],['13','20'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('22',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('23',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('25',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['5','10'])).

thf('26',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['24','25'])).

thf('27',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['23','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5MlitfVfsz
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:58:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 106 iterations in 0.035s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.46  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.46  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.46  thf(t83_xboole_1, conjecture,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i,B:$i]:
% 0.20/0.46        ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t83_xboole_1])).
% 0.20/0.46  thf('0', plain,
% 0.20/0.46      ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)) | (r1_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      (((r1_xboole_0 @ sk_A @ sk_B)) <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.46      inference('split', [status(esa)], ['0'])).
% 0.20/0.46  thf(d7_xboole_0, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.20/0.46       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.20/0.46      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      ((((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.20/0.46         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      ((((k4_xboole_0 @ sk_A @ sk_B) != (sk_A)) | ~ (r1_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (~ (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))) | 
% 0.20/0.46       ~ ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.46      inference('split', [status(esa)], ['4'])).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))
% 0.20/0.46         <= ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))))),
% 0.20/0.46      inference('split', [status(esa)], ['0'])).
% 0.20/0.46  thf(t79_xboole_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      (![X12 : $i, X13 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X13)),
% 0.20/0.46      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      (((r1_xboole_0 @ sk_A @ sk_B))
% 0.20/0.46         <= ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))))),
% 0.20/0.46      inference('sup+', [status(thm)], ['6', '7'])).
% 0.20/0.46  thf('9', plain,
% 0.20/0.46      ((~ (r1_xboole_0 @ sk_A @ sk_B)) <= (~ ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.46      inference('split', [status(esa)], ['4'])).
% 0.20/0.46  thf('10', plain,
% 0.20/0.46      (((r1_xboole_0 @ sk_A @ sk_B)) | 
% 0.20/0.46       ~ (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      (((r1_xboole_0 @ sk_A @ sk_B)) | (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 0.20/0.46      inference('split', [status(esa)], ['0'])).
% 0.20/0.46  thf('12', plain, (((r1_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.46      inference('sat_resolution*', [status(thm)], ['5', '10', '11'])).
% 0.20/0.46  thf('13', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.46      inference('simpl_trail', [status(thm)], ['3', '12'])).
% 0.20/0.46  thf(t48_xboole_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.46  thf('14', plain,
% 0.20/0.46      (![X10 : $i, X11 : $i]:
% 0.20/0.46         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.20/0.46           = (k3_xboole_0 @ X10 @ X11))),
% 0.20/0.46      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.46  thf(t39_xboole_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.46  thf('15', plain,
% 0.20/0.46      (![X8 : $i, X9 : $i]:
% 0.20/0.46         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 0.20/0.46           = (k2_xboole_0 @ X8 @ X9))),
% 0.20/0.46      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.20/0.46  thf('16', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.20/0.46           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.20/0.46      inference('sup+', [status(thm)], ['14', '15'])).
% 0.20/0.46  thf(t36_xboole_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.46  thf('17', plain,
% 0.20/0.46      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 0.20/0.46      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.20/0.46  thf(t12_xboole_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.20/0.46  thf('18', plain,
% 0.20/0.46      (![X3 : $i, X4 : $i]:
% 0.20/0.46         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.20/0.46      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.20/0.46  thf('19', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.46  thf('20', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.20/0.46           = (X1))),
% 0.20/0.46      inference('demod', [status(thm)], ['16', '19'])).
% 0.20/0.46  thf('21', plain,
% 0.20/0.46      (((k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ k1_xboole_0) = (sk_A))),
% 0.20/0.46      inference('sup+', [status(thm)], ['13', '20'])).
% 0.20/0.46  thf(t1_boole, axiom,
% 0.20/0.46    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.46  thf('22', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.20/0.46      inference('cnf', [status(esa)], [t1_boole])).
% 0.20/0.46  thf('23', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.20/0.46      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.46  thf('24', plain,
% 0.20/0.46      ((((k4_xboole_0 @ sk_A @ sk_B) != (sk_A)))
% 0.20/0.46         <= (~ (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))))),
% 0.20/0.46      inference('split', [status(esa)], ['4'])).
% 0.20/0.46  thf('25', plain, (~ (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 0.20/0.46      inference('sat_resolution*', [status(thm)], ['5', '10'])).
% 0.20/0.46  thf('26', plain, (((k4_xboole_0 @ sk_A @ sk_B) != (sk_A))),
% 0.20/0.46      inference('simpl_trail', [status(thm)], ['24', '25'])).
% 0.20/0.46  thf('27', plain, ($false),
% 0.20/0.46      inference('simplify_reflect-', [status(thm)], ['23', '26'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

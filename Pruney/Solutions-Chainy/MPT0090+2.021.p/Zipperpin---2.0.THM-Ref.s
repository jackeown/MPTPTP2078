%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6tj53Of0Wv

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   42 (  74 expanded)
%              Number of leaves         :   13 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :  229 ( 480 expanded)
%              Number of equality atoms :   29 (  59 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X9: $i,X10: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X10 ) ),
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

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('14',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X6 @ X7 ) @ ( k4_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('15',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_A ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('16',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X6 @ X7 ) @ ( k4_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('21',plain,(
    ! [X3: $i] :
      ( ( k4_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['15','22'])).

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
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6tj53Of0Wv
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:21:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 40 iterations in 0.017s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(t83_xboole_1, conjecture,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i]:
% 0.21/0.47        ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t83_xboole_1])).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)) | (r1_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (((r1_xboole_0 @ sk_A @ sk_B)) <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf(d7_xboole_0, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.21/0.47       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.47      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      ((((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.21/0.47         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      ((((k4_xboole_0 @ sk_A @ sk_B) != (sk_A)) | ~ (r1_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (~ (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))) | 
% 0.21/0.47       ~ ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.47      inference('split', [status(esa)], ['4'])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))
% 0.21/0.47         <= ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf(t79_xboole_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X9 : $i, X10 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X10)),
% 0.21/0.47      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (((r1_xboole_0 @ sk_A @ sk_B))
% 0.21/0.47         <= ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))))),
% 0.21/0.47      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      ((~ (r1_xboole_0 @ sk_A @ sk_B)) <= (~ ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.47      inference('split', [status(esa)], ['4'])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (((r1_xboole_0 @ sk_A @ sk_B)) | 
% 0.21/0.47       ~ (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (((r1_xboole_0 @ sk_A @ sk_B)) | (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('12', plain, (((r1_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.47      inference('sat_resolution*', [status(thm)], ['5', '10', '11'])).
% 0.21/0.47  thf('13', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.21/0.47      inference('simpl_trail', [status(thm)], ['3', '12'])).
% 0.21/0.47  thf(t51_xboole_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.21/0.47       ( A ) ))).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (![X6 : $i, X7 : $i]:
% 0.21/0.47         ((k2_xboole_0 @ (k3_xboole_0 @ X6 @ X7) @ (k4_xboole_0 @ X6 @ X7))
% 0.21/0.47           = (X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_A))),
% 0.21/0.47      inference('sup+', [status(thm)], ['13', '14'])).
% 0.21/0.47  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.21/0.47  thf('16', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 0.21/0.47      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.47      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (![X6 : $i, X7 : $i]:
% 0.21/0.47         ((k2_xboole_0 @ (k3_xboole_0 @ X6 @ X7) @ (k4_xboole_0 @ X6 @ X7))
% 0.21/0.47           = (X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 0.21/0.47      inference('sup+', [status(thm)], ['18', '19'])).
% 0.21/0.47  thf(t3_boole, axiom,
% 0.21/0.47    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.47  thf('21', plain, (![X3 : $i]: ((k4_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.21/0.47      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.47  thf('22', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.21/0.47      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.47  thf('23', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['15', '22'])).
% 0.21/0.47  thf('24', plain,
% 0.21/0.47      ((((k4_xboole_0 @ sk_A @ sk_B) != (sk_A)))
% 0.21/0.47         <= (~ (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))))),
% 0.21/0.47      inference('split', [status(esa)], ['4'])).
% 0.21/0.47  thf('25', plain, (~ (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 0.21/0.47      inference('sat_resolution*', [status(thm)], ['5', '10'])).
% 0.21/0.47  thf('26', plain, (((k4_xboole_0 @ sk_A @ sk_B) != (sk_A))),
% 0.21/0.47      inference('simpl_trail', [status(thm)], ['24', '25'])).
% 0.21/0.47  thf('27', plain, ($false),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['23', '26'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2T7zk0pvhm

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:41 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   42 (  59 expanded)
%              Number of leaves         :   12 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :  281 ( 415 expanded)
%              Number of equality atoms :   39 (  56 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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
     != sk_A )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('5',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) )
      = ( k4_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('7',plain,
    ( ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
      = ( k4_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('9',plain,
    ( ( sk_A
      = ( k4_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('11',plain,
    ( ( sk_A != sk_A )
   <= ( ( ( k4_xboole_0 @ sk_A @ sk_B )
       != sk_A )
      & ( r1_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('14',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_A )
      = ( k3_xboole_0 @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('18',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('20',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference(demod,[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('24',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_B )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','12','13','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.14/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2T7zk0pvhm
% 0.15/0.37  % Computer   : n020.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 16:39:52 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.23/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.51  % Solved by: fo/fo7.sh
% 0.23/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.51  % done 38 iterations in 0.021s
% 0.23/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.51  % SZS output start Refutation
% 0.23/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.23/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.23/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.23/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.51  thf(t83_xboole_1, conjecture,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.23/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.51    (~( ![A:$i,B:$i]:
% 0.23/0.51        ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ) )),
% 0.23/0.51    inference('cnf.neg', [status(esa)], [t83_xboole_1])).
% 0.23/0.51  thf('0', plain,
% 0.23/0.51      ((((k4_xboole_0 @ sk_A @ sk_B) != (sk_A)) | ~ (r1_xboole_0 @ sk_A @ sk_B))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('1', plain,
% 0.23/0.51      (~ (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))) | 
% 0.23/0.51       ~ ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.23/0.51      inference('split', [status(esa)], ['0'])).
% 0.23/0.51  thf('2', plain,
% 0.23/0.51      ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)) | (r1_xboole_0 @ sk_A @ sk_B))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('3', plain,
% 0.23/0.51      (((r1_xboole_0 @ sk_A @ sk_B)) <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.23/0.51      inference('split', [status(esa)], ['2'])).
% 0.23/0.51  thf(d7_xboole_0, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.23/0.51       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.23/0.51  thf('4', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]:
% 0.23/0.51         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.23/0.51      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.23/0.51  thf('5', plain,
% 0.23/0.51      ((((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.23/0.51         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.23/0.51  thf(t47_xboole_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.23/0.51  thf('6', plain,
% 0.23/0.51      (![X5 : $i, X6 : $i]:
% 0.23/0.51         ((k4_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6))
% 0.23/0.51           = (k4_xboole_0 @ X5 @ X6))),
% 0.23/0.51      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.23/0.51  thf('7', plain,
% 0.23/0.51      ((((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B)))
% 0.23/0.51         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.23/0.51      inference('sup+', [status(thm)], ['5', '6'])).
% 0.23/0.51  thf(t3_boole, axiom,
% 0.23/0.51    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.23/0.51  thf('8', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.23/0.51      inference('cnf', [status(esa)], [t3_boole])).
% 0.23/0.51  thf('9', plain,
% 0.23/0.51      ((((sk_A) = (k4_xboole_0 @ sk_A @ sk_B)))
% 0.23/0.51         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.23/0.51      inference('demod', [status(thm)], ['7', '8'])).
% 0.23/0.51  thf('10', plain,
% 0.23/0.51      ((((k4_xboole_0 @ sk_A @ sk_B) != (sk_A)))
% 0.23/0.51         <= (~ (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))))),
% 0.23/0.51      inference('split', [status(esa)], ['0'])).
% 0.23/0.51  thf('11', plain,
% 0.23/0.51      ((((sk_A) != (sk_A)))
% 0.23/0.51         <= (~ (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))) & 
% 0.23/0.51             ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.23/0.51  thf('12', plain,
% 0.23/0.51      ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))) | 
% 0.23/0.51       ~ ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.23/0.51      inference('simplify', [status(thm)], ['11'])).
% 0.23/0.51  thf('13', plain,
% 0.23/0.51      ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))) | ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.23/0.51      inference('split', [status(esa)], ['2'])).
% 0.23/0.51  thf('14', plain,
% 0.23/0.51      ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))
% 0.23/0.51         <= ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))))),
% 0.23/0.51      inference('split', [status(esa)], ['2'])).
% 0.23/0.51  thf(t48_xboole_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.23/0.51  thf('15', plain,
% 0.23/0.51      (![X7 : $i, X8 : $i]:
% 0.23/0.51         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.23/0.51           = (k3_xboole_0 @ X7 @ X8))),
% 0.23/0.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.23/0.51  thf('16', plain,
% 0.23/0.51      ((((k4_xboole_0 @ sk_A @ sk_A) = (k3_xboole_0 @ sk_A @ sk_B)))
% 0.23/0.51         <= ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))))),
% 0.23/0.51      inference('sup+', [status(thm)], ['14', '15'])).
% 0.23/0.51  thf('17', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.23/0.51      inference('cnf', [status(esa)], [t3_boole])).
% 0.23/0.51  thf('18', plain,
% 0.23/0.51      (![X7 : $i, X8 : $i]:
% 0.23/0.51         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.23/0.51           = (k3_xboole_0 @ X7 @ X8))),
% 0.23/0.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.23/0.51  thf('19', plain,
% 0.23/0.51      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.23/0.51      inference('sup+', [status(thm)], ['17', '18'])).
% 0.23/0.51  thf(t2_boole, axiom,
% 0.23/0.51    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.23/0.51  thf('20', plain,
% 0.23/0.51      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.23/0.51      inference('cnf', [status(esa)], [t2_boole])).
% 0.23/0.51  thf('21', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.23/0.51      inference('demod', [status(thm)], ['19', '20'])).
% 0.23/0.51  thf('22', plain,
% 0.23/0.51      ((((k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_B)))
% 0.23/0.51         <= ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))))),
% 0.23/0.51      inference('demod', [status(thm)], ['16', '21'])).
% 0.23/0.51  thf('23', plain,
% 0.23/0.51      (![X0 : $i, X2 : $i]:
% 0.23/0.51         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.23/0.51      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.23/0.51  thf('24', plain,
% 0.23/0.51      (((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_B)))
% 0.23/0.51         <= ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))))),
% 0.23/0.51      inference('sup-', [status(thm)], ['22', '23'])).
% 0.23/0.51  thf('25', plain,
% 0.23/0.51      (((r1_xboole_0 @ sk_A @ sk_B))
% 0.23/0.51         <= ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))))),
% 0.23/0.51      inference('simplify', [status(thm)], ['24'])).
% 0.23/0.51  thf('26', plain,
% 0.23/0.51      ((~ (r1_xboole_0 @ sk_A @ sk_B)) <= (~ ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.23/0.51      inference('split', [status(esa)], ['0'])).
% 0.23/0.51  thf('27', plain,
% 0.23/0.51      (~ (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))) | 
% 0.23/0.51       ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.23/0.51      inference('sup-', [status(thm)], ['25', '26'])).
% 0.23/0.51  thf('28', plain, ($false),
% 0.23/0.51      inference('sat_resolution*', [status(thm)], ['1', '12', '13', '27'])).
% 0.23/0.51  
% 0.23/0.51  % SZS output end Refutation
% 0.23/0.51  
% 0.23/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

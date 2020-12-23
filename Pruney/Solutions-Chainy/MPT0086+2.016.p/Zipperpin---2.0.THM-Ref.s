%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IwbYgVAH1t

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:30 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :   35 (  38 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :    8
%              Number of atoms          :  217 ( 248 expanded)
%              Number of equality atoms :   23 (  26 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('1',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('9',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('10',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('12',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','14'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['0','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IwbYgVAH1t
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:30:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.58/0.82  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.58/0.82  % Solved by: fo/fo7.sh
% 0.58/0.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.82  % done 545 iterations in 0.371s
% 0.58/0.82  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.58/0.82  % SZS output start Refutation
% 0.58/0.82  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.82  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.82  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.82  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.58/0.82  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.58/0.82  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.58/0.82  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.58/0.82  thf(t79_xboole_1, conjecture,
% 0.58/0.82    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.58/0.82  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.82    (~( ![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )),
% 0.58/0.82    inference('cnf.neg', [status(esa)], [t79_xboole_1])).
% 0.58/0.82  thf('0', plain, (~ (r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_B)),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf(idempotence_k2_xboole_0, axiom,
% 0.58/0.82    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.58/0.82  thf('1', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ X3) = (X3))),
% 0.58/0.82      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.58/0.82  thf(t48_xboole_1, axiom,
% 0.58/0.82    (![A:$i,B:$i]:
% 0.58/0.82     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.58/0.82  thf('2', plain,
% 0.58/0.82      (![X9 : $i, X10 : $i]:
% 0.58/0.82         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.58/0.82           = (k3_xboole_0 @ X9 @ X10))),
% 0.58/0.82      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.58/0.82  thf(t41_xboole_1, axiom,
% 0.58/0.82    (![A:$i,B:$i,C:$i]:
% 0.58/0.82     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.58/0.82       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.58/0.82  thf('3', plain,
% 0.58/0.82      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.58/0.82         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 0.58/0.82           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 0.58/0.82      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.58/0.82  thf('4', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.82         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.58/0.82           = (k4_xboole_0 @ X2 @ 
% 0.58/0.82              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))))),
% 0.58/0.82      inference('sup+', [status(thm)], ['2', '3'])).
% 0.58/0.82  thf('5', plain,
% 0.58/0.82      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.58/0.82         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 0.58/0.82           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 0.58/0.82      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.58/0.82  thf('6', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.82         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.58/0.82           = (k4_xboole_0 @ X2 @ 
% 0.58/0.82              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 0.58/0.82      inference('demod', [status(thm)], ['4', '5'])).
% 0.58/0.82  thf('7', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.58/0.82           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.58/0.82      inference('sup+', [status(thm)], ['1', '6'])).
% 0.58/0.82  thf('8', plain,
% 0.58/0.82      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.58/0.82         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 0.58/0.82           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 0.58/0.82      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.58/0.82  thf(t3_boole, axiom,
% 0.58/0.82    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.58/0.82  thf('9', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.58/0.82      inference('cnf', [status(esa)], [t3_boole])).
% 0.58/0.82  thf('10', plain,
% 0.58/0.82      (![X9 : $i, X10 : $i]:
% 0.58/0.82         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.58/0.82           = (k3_xboole_0 @ X9 @ X10))),
% 0.58/0.82      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.58/0.82  thf('11', plain,
% 0.58/0.82      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.58/0.82      inference('sup+', [status(thm)], ['9', '10'])).
% 0.58/0.82  thf(t2_boole, axiom,
% 0.58/0.82    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.58/0.82  thf('12', plain,
% 0.58/0.82      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.82      inference('cnf', [status(esa)], [t2_boole])).
% 0.58/0.82  thf('13', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.58/0.82      inference('demod', [status(thm)], ['11', '12'])).
% 0.58/0.82  thf('14', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 0.58/0.82           = (k1_xboole_0))),
% 0.58/0.82      inference('sup+', [status(thm)], ['8', '13'])).
% 0.58/0.82  thf('15', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.58/0.82      inference('sup+', [status(thm)], ['7', '14'])).
% 0.58/0.82  thf(d7_xboole_0, axiom,
% 0.58/0.82    (![A:$i,B:$i]:
% 0.58/0.82     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.58/0.82       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.58/0.82  thf('16', plain,
% 0.58/0.82      (![X0 : $i, X2 : $i]:
% 0.58/0.82         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.58/0.82      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.58/0.82  thf('17', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         (((k1_xboole_0) != (k1_xboole_0))
% 0.58/0.82          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.58/0.82      inference('sup-', [status(thm)], ['15', '16'])).
% 0.58/0.82  thf('18', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.58/0.82      inference('simplify', [status(thm)], ['17'])).
% 0.58/0.82  thf('19', plain, ($false), inference('demod', [status(thm)], ['0', '18'])).
% 0.58/0.82  
% 0.58/0.82  % SZS output end Refutation
% 0.58/0.82  
% 0.58/0.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rWEoIteyHa

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:17 EST 2020

% Result     : Theorem 0.33s
% Output     : Refutation 0.33s
% Verified   : 
% Statistics : Number of formulae       :   35 (  36 expanded)
%              Number of leaves         :   16 (  17 expanded)
%              Depth                    :   10
%              Number of atoms          :  219 ( 228 expanded)
%              Number of equality atoms :   24 (  25 expanded)
%              Maximal formula depth    :    8 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t100_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k4_xboole_0 @ A @ B )
        = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t100_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(l98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k5_xboole_0 @ X3 @ X4 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X3 @ X4 ) @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','15'])).

thf('17',plain,(
    $false ),
    inference(simplify,[status(thm)],['16'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rWEoIteyHa
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:36:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.33/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.33/0.53  % Solved by: fo/fo7.sh
% 0.33/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.33/0.53  % done 181 iterations in 0.063s
% 0.33/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.33/0.53  % SZS output start Refutation
% 0.33/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.33/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.33/0.53  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.33/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.33/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.33/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.33/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.33/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.33/0.53  thf(t100_xboole_1, conjecture,
% 0.33/0.53    (![A:$i,B:$i]:
% 0.33/0.53     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.33/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.33/0.53    (~( ![A:$i,B:$i]:
% 0.33/0.53        ( ( k4_xboole_0 @ A @ B ) =
% 0.33/0.53          ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.33/0.53    inference('cnf.neg', [status(esa)], [t100_xboole_1])).
% 0.33/0.53  thf('0', plain,
% 0.33/0.53      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.33/0.53         != (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf(t48_xboole_1, axiom,
% 0.33/0.53    (![A:$i,B:$i]:
% 0.33/0.53     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.33/0.53  thf('1', plain,
% 0.33/0.53      (![X9 : $i, X10 : $i]:
% 0.33/0.53         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.33/0.53           = (k3_xboole_0 @ X9 @ X10))),
% 0.33/0.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.33/0.53  thf(t36_xboole_1, axiom,
% 0.33/0.53    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.33/0.53  thf('2', plain,
% 0.33/0.53      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 0.33/0.53      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.33/0.53  thf(l32_xboole_1, axiom,
% 0.33/0.53    (![A:$i,B:$i]:
% 0.33/0.53     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.33/0.53  thf('3', plain,
% 0.33/0.53      (![X0 : $i, X2 : $i]:
% 0.33/0.53         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.33/0.53      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.33/0.53  thf('4', plain,
% 0.33/0.53      (![X0 : $i, X1 : $i]:
% 0.33/0.53         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.33/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.33/0.53  thf('5', plain,
% 0.33/0.53      (![X0 : $i, X1 : $i]:
% 0.33/0.53         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 0.33/0.53      inference('sup+', [status(thm)], ['1', '4'])).
% 0.33/0.53  thf(t98_xboole_1, axiom,
% 0.33/0.53    (![A:$i,B:$i]:
% 0.33/0.53     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.33/0.53  thf('6', plain,
% 0.33/0.53      (![X12 : $i, X13 : $i]:
% 0.33/0.53         ((k2_xboole_0 @ X12 @ X13)
% 0.33/0.53           = (k5_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12)))),
% 0.33/0.53      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.33/0.53  thf('7', plain,
% 0.33/0.53      (![X0 : $i, X1 : $i]:
% 0.33/0.53         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.33/0.53           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.33/0.53      inference('sup+', [status(thm)], ['5', '6'])).
% 0.33/0.53  thf(t5_boole, axiom,
% 0.33/0.53    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.33/0.53  thf('8', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.33/0.53      inference('cnf', [status(esa)], [t5_boole])).
% 0.33/0.53  thf('9', plain,
% 0.33/0.53      (![X0 : $i, X1 : $i]:
% 0.33/0.53         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) = (X0))),
% 0.33/0.53      inference('demod', [status(thm)], ['7', '8'])).
% 0.33/0.53  thf(l98_xboole_1, axiom,
% 0.33/0.53    (![A:$i,B:$i]:
% 0.33/0.53     ( ( k5_xboole_0 @ A @ B ) =
% 0.33/0.53       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.33/0.53  thf('10', plain,
% 0.33/0.53      (![X3 : $i, X4 : $i]:
% 0.33/0.53         ((k5_xboole_0 @ X3 @ X4)
% 0.33/0.53           = (k4_xboole_0 @ (k2_xboole_0 @ X3 @ X4) @ (k3_xboole_0 @ X3 @ X4)))),
% 0.33/0.53      inference('cnf', [status(esa)], [l98_xboole_1])).
% 0.33/0.53  thf('11', plain,
% 0.33/0.53      (![X0 : $i, X1 : $i]:
% 0.33/0.53         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.33/0.53           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))))),
% 0.33/0.53      inference('sup+', [status(thm)], ['9', '10'])).
% 0.33/0.53  thf(t47_xboole_1, axiom,
% 0.33/0.53    (![A:$i,B:$i]:
% 0.33/0.53     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.33/0.53  thf('12', plain,
% 0.33/0.53      (![X7 : $i, X8 : $i]:
% 0.33/0.53         ((k4_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8))
% 0.33/0.53           = (k4_xboole_0 @ X7 @ X8))),
% 0.33/0.53      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.33/0.53  thf('13', plain,
% 0.33/0.53      (![X0 : $i, X1 : $i]:
% 0.33/0.53         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.33/0.53           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.33/0.53      inference('demod', [status(thm)], ['11', '12'])).
% 0.33/0.53  thf('14', plain,
% 0.33/0.53      (![X7 : $i, X8 : $i]:
% 0.33/0.53         ((k4_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8))
% 0.33/0.53           = (k4_xboole_0 @ X7 @ X8))),
% 0.33/0.53      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.33/0.53  thf('15', plain,
% 0.33/0.53      (![X0 : $i, X1 : $i]:
% 0.33/0.53         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.33/0.53           = (k4_xboole_0 @ X1 @ X0))),
% 0.33/0.53      inference('sup+', [status(thm)], ['13', '14'])).
% 0.33/0.53  thf('16', plain,
% 0.33/0.53      (((k4_xboole_0 @ sk_A @ sk_B) != (k4_xboole_0 @ sk_A @ sk_B))),
% 0.33/0.53      inference('demod', [status(thm)], ['0', '15'])).
% 0.33/0.53  thf('17', plain, ($false), inference('simplify', [status(thm)], ['16'])).
% 0.33/0.53  
% 0.33/0.53  % SZS output end Refutation
% 0.33/0.53  
% 0.33/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

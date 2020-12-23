%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cRBk0sw2Kl

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   41 (  65 expanded)
%              Number of leaves         :   16 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :  331 ( 618 expanded)
%              Number of equality atoms :   30 (  54 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t108_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ B @ A @ C @ D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k2_enumset1 @ A @ B @ C @ D )
        = ( k2_enumset1 @ B @ A @ C @ D ) ) ),
    inference('cnf.neg',[status(esa)],[t108_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_enumset1 @ X34 @ X34 @ X35 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_tarski @ X5 @ X4 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('4',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k3_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42 )
      = ( k2_enumset1 @ X39 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('5',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k2_enumset1 @ X36 @ X36 @ X37 @ X38 )
      = ( k1_enumset1 @ X36 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k2_enumset1 @ X36 @ X36 @ X37 @ X38 )
      = ( k1_enumset1 @ X36 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t50_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k3_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) @ ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['3','10'])).

thf('12',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_enumset1 @ X34 @ X34 @ X35 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X2 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('17',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k3_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42 )
      = ( k2_enumset1 @ X39 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) )
      = ( k2_enumset1 @ X1 @ X2 @ X0 @ X3 ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X2 @ X3 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','21'])).

thf('23',plain,(
    $false ),
    inference(simplify,[status(thm)],['22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cRBk0sw2Kl
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:09:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 146 iterations in 0.070s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.21/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.53  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.53  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(t108_enumset1, conjecture,
% 0.21/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.53     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ A @ C @ D ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.53        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ A @ C @ D ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t108_enumset1])).
% 0.21/0.53  thf('0', plain,
% 0.21/0.53      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.21/0.53         != (k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_D))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t70_enumset1, axiom,
% 0.21/0.53    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (![X34 : $i, X35 : $i]:
% 0.21/0.53         ((k1_enumset1 @ X34 @ X34 @ X35) = (k2_tarski @ X34 @ X35))),
% 0.21/0.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.53  thf(commutativity_k2_tarski, axiom,
% 0.21/0.53    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X4 : $i, X5 : $i]: ((k2_tarski @ X5 @ X4) = (k2_tarski @ X4 @ X5))),
% 0.21/0.53      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((k2_tarski @ X0 @ X1) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['1', '2'])).
% 0.21/0.53  thf(t72_enumset1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.53     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.21/0.53         ((k3_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42)
% 0.21/0.53           = (k2_enumset1 @ X39 @ X40 @ X41 @ X42))),
% 0.21/0.53      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.21/0.53  thf(t71_enumset1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.21/0.53         ((k2_enumset1 @ X36 @ X36 @ X37 @ X38)
% 0.21/0.53           = (k1_enumset1 @ X36 @ X37 @ X38))),
% 0.21/0.53      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['4', '5'])).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.21/0.53         ((k2_enumset1 @ X36 @ X36 @ X37 @ X38)
% 0.21/0.53           = (k1_enumset1 @ X36 @ X37 @ X38))),
% 0.21/0.53      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.21/0.53  thf(t50_enumset1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.53     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.21/0.53       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ))).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.53         ((k3_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10)
% 0.21/0.53           = (k2_xboole_0 @ (k2_enumset1 @ X6 @ X7 @ X8 @ X9) @ 
% 0.21/0.53              (k1_tarski @ X10)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t50_enumset1])).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.53         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3)
% 0.21/0.53           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['7', '8'])).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         ((k1_enumset1 @ X2 @ X1 @ X0)
% 0.21/0.53           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X2 @ X1) @ (k1_tarski @ X0)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['6', '9'])).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         ((k1_enumset1 @ X0 @ X1 @ X2)
% 0.21/0.53           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['3', '10'])).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (![X34 : $i, X35 : $i]:
% 0.21/0.53         ((k1_enumset1 @ X34 @ X34 @ X35) = (k2_tarski @ X34 @ X35))),
% 0.21/0.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         ((k1_enumset1 @ X2 @ X1 @ X0)
% 0.21/0.53           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X2 @ X1) @ (k1_tarski @ X0)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['6', '9'])).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         ((k1_enumset1 @ X1 @ X0 @ X2)
% 0.21/0.53           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         ((k1_enumset1 @ X1 @ X2 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['11', '14'])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.53         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3)
% 0.21/0.53           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['7', '8'])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.21/0.53         ((k3_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42)
% 0.21/0.53           = (k2_enumset1 @ X39 @ X40 @ X41 @ X42))),
% 0.21/0.53      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.53         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 0.21/0.53           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['16', '17'])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.53         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3))
% 0.21/0.53           = (k2_enumset1 @ X1 @ X2 @ X0 @ X3))),
% 0.21/0.53      inference('sup+', [status(thm)], ['15', '18'])).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.53         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 0.21/0.53           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['16', '17'])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.53         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X2 @ X3 @ X1 @ X0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['19', '20'])).
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.21/0.53         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.53      inference('demod', [status(thm)], ['0', '21'])).
% 0.21/0.53  thf('23', plain, ($false), inference('simplify', [status(thm)], ['22'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

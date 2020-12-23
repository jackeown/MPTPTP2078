%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kFIcAsjaLx

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:41 EST 2020

% Result     : Theorem 15.91s
% Output     : Refutation 15.91s
% Verified   : 
% Statistics : Number of formulae       :   37 (  47 expanded)
%              Number of leaves         :   15 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :  282 ( 377 expanded)
%              Number of equality atoms :   28 (  38 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t78_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_enumset1 @ A @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k3_enumset1 @ A @ A @ A @ B @ C )
        = ( k1_enumset1 @ A @ B @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t78_enumset1])).

thf('0',plain,(
    ( k3_enumset1 @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ( k1_enumset1 @ X56 @ X57 @ X58 )
      = ( k2_xboole_0 @ ( k1_tarski @ X56 ) @ ( k2_tarski @ X57 @ X58 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t43_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ) )).

thf('4',plain,(
    ! [X59: $i,X60: $i,X61: $i] :
      ( ( k1_enumset1 @ X59 @ X60 @ X61 )
      = ( k2_xboole_0 @ ( k2_tarski @ X59 @ X60 ) @ ( k1_tarski @ X61 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('7',plain,(
    ( k3_enumset1 @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['0','5','6'])).

thf(t76_enumset1,axiom,(
    ! [A: $i] :
      ( ( k1_enumset1 @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('8',plain,(
    ! [X69: $i] :
      ( ( k1_enumset1 @ X69 @ X69 @ X69 )
      = ( k1_tarski @ X69 ) ) ),
    inference(cnf,[status(esa)],[t76_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X67: $i,X68: $i] :
      ( ( k1_enumset1 @ X67 @ X67 @ X68 )
      = ( k2_tarski @ X67 @ X68 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('10',plain,(
    ! [X69: $i] :
      ( ( k2_tarski @ X69 @ X69 )
      = ( k1_tarski @ X69 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X67: $i,X68: $i] :
      ( ( k1_enumset1 @ X67 @ X67 @ X68 )
      = ( k2_tarski @ X67 @ X68 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t49_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) )).

thf('12',plain,(
    ! [X62: $i,X63: $i,X64: $i,X65: $i,X66: $i] :
      ( ( k3_enumset1 @ X62 @ X63 @ X64 @ X65 @ X66 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X62 @ X63 @ X64 ) @ ( k2_tarski @ X65 @ X66 ) ) ) ),
    inference(cnf,[status(esa)],[t49_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X59: $i,X60: $i,X61: $i] :
      ( ( k1_enumset1 @ X59 @ X60 @ X61 )
      = ( k2_xboole_0 @ ( k2_tarski @ X59 @ X60 ) @ ( k1_tarski @ X61 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X0 @ X2 @ X1 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,(
    ( k1_enumset1 @ sk_B @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['7','18'])).

thf('20',plain,(
    $false ),
    inference(simplify,[status(thm)],['19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kFIcAsjaLx
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:59:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 15.91/16.10  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 15.91/16.10  % Solved by: fo/fo7.sh
% 15.91/16.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 15.91/16.10  % done 10881 iterations in 15.645s
% 15.91/16.10  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 15.91/16.10  % SZS output start Refutation
% 15.91/16.10  thf(sk_B_type, type, sk_B: $i).
% 15.91/16.10  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 15.91/16.10  thf(sk_C_type, type, sk_C: $i).
% 15.91/16.10  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 15.91/16.10  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 15.91/16.10  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 15.91/16.10  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 15.91/16.10  thf(sk_A_type, type, sk_A: $i).
% 15.91/16.10  thf(t78_enumset1, conjecture,
% 15.91/16.10    (![A:$i,B:$i,C:$i]:
% 15.91/16.10     ( ( k3_enumset1 @ A @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 15.91/16.10  thf(zf_stmt_0, negated_conjecture,
% 15.91/16.10    (~( ![A:$i,B:$i,C:$i]:
% 15.91/16.10        ( ( k3_enumset1 @ A @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ) )),
% 15.91/16.10    inference('cnf.neg', [status(esa)], [t78_enumset1])).
% 15.91/16.10  thf('0', plain,
% 15.91/16.10      (((k3_enumset1 @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 15.91/16.10         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 15.91/16.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.91/16.10  thf(t42_enumset1, axiom,
% 15.91/16.10    (![A:$i,B:$i,C:$i]:
% 15.91/16.10     ( ( k1_enumset1 @ A @ B @ C ) =
% 15.91/16.10       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 15.91/16.10  thf('1', plain,
% 15.91/16.10      (![X56 : $i, X57 : $i, X58 : $i]:
% 15.91/16.10         ((k1_enumset1 @ X56 @ X57 @ X58)
% 15.91/16.10           = (k2_xboole_0 @ (k1_tarski @ X56) @ (k2_tarski @ X57 @ X58)))),
% 15.91/16.10      inference('cnf', [status(esa)], [t42_enumset1])).
% 15.91/16.10  thf(commutativity_k2_xboole_0, axiom,
% 15.91/16.10    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 15.91/16.10  thf('2', plain,
% 15.91/16.10      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 15.91/16.10      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 15.91/16.10  thf('3', plain,
% 15.91/16.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.91/16.10         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2))
% 15.91/16.10           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 15.91/16.10      inference('sup+', [status(thm)], ['1', '2'])).
% 15.91/16.10  thf(t43_enumset1, axiom,
% 15.91/16.10    (![A:$i,B:$i,C:$i]:
% 15.91/16.10     ( ( k1_enumset1 @ A @ B @ C ) =
% 15.91/16.10       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ))).
% 15.91/16.10  thf('4', plain,
% 15.91/16.10      (![X59 : $i, X60 : $i, X61 : $i]:
% 15.91/16.10         ((k1_enumset1 @ X59 @ X60 @ X61)
% 15.91/16.10           = (k2_xboole_0 @ (k2_tarski @ X59 @ X60) @ (k1_tarski @ X61)))),
% 15.91/16.10      inference('cnf', [status(esa)], [t43_enumset1])).
% 15.91/16.10  thf('5', plain,
% 15.91/16.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.91/16.10         ((k1_enumset1 @ X1 @ X0 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 15.91/16.10      inference('sup+', [status(thm)], ['3', '4'])).
% 15.91/16.10  thf('6', plain,
% 15.91/16.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.91/16.10         ((k1_enumset1 @ X1 @ X0 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 15.91/16.10      inference('sup+', [status(thm)], ['3', '4'])).
% 15.91/16.10  thf('7', plain,
% 15.91/16.10      (((k3_enumset1 @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 15.91/16.10         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 15.91/16.10      inference('demod', [status(thm)], ['0', '5', '6'])).
% 15.91/16.10  thf(t76_enumset1, axiom,
% 15.91/16.10    (![A:$i]: ( ( k1_enumset1 @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 15.91/16.10  thf('8', plain,
% 15.91/16.10      (![X69 : $i]: ((k1_enumset1 @ X69 @ X69 @ X69) = (k1_tarski @ X69))),
% 15.91/16.10      inference('cnf', [status(esa)], [t76_enumset1])).
% 15.91/16.10  thf(t70_enumset1, axiom,
% 15.91/16.10    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 15.91/16.10  thf('9', plain,
% 15.91/16.10      (![X67 : $i, X68 : $i]:
% 15.91/16.10         ((k1_enumset1 @ X67 @ X67 @ X68) = (k2_tarski @ X67 @ X68))),
% 15.91/16.10      inference('cnf', [status(esa)], [t70_enumset1])).
% 15.91/16.10  thf('10', plain,
% 15.91/16.10      (![X69 : $i]: ((k2_tarski @ X69 @ X69) = (k1_tarski @ X69))),
% 15.91/16.10      inference('demod', [status(thm)], ['8', '9'])).
% 15.91/16.10  thf('11', plain,
% 15.91/16.10      (![X67 : $i, X68 : $i]:
% 15.91/16.10         ((k1_enumset1 @ X67 @ X67 @ X68) = (k2_tarski @ X67 @ X68))),
% 15.91/16.10      inference('cnf', [status(esa)], [t70_enumset1])).
% 15.91/16.10  thf(t49_enumset1, axiom,
% 15.91/16.10    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 15.91/16.10     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 15.91/16.10       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ))).
% 15.91/16.10  thf('12', plain,
% 15.91/16.10      (![X62 : $i, X63 : $i, X64 : $i, X65 : $i, X66 : $i]:
% 15.91/16.10         ((k3_enumset1 @ X62 @ X63 @ X64 @ X65 @ X66)
% 15.91/16.10           = (k2_xboole_0 @ (k1_enumset1 @ X62 @ X63 @ X64) @ 
% 15.91/16.10              (k2_tarski @ X65 @ X66)))),
% 15.91/16.10      inference('cnf', [status(esa)], [t49_enumset1])).
% 15.91/16.10  thf('13', plain,
% 15.91/16.10      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 15.91/16.10         ((k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2)
% 15.91/16.10           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 15.91/16.10      inference('sup+', [status(thm)], ['11', '12'])).
% 15.91/16.10  thf('14', plain,
% 15.91/16.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.91/16.10         ((k3_enumset1 @ X0 @ X0 @ X0 @ X2 @ X1)
% 15.91/16.10           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 15.91/16.10      inference('sup+', [status(thm)], ['10', '13'])).
% 15.91/16.10  thf('15', plain,
% 15.91/16.10      (![X59 : $i, X60 : $i, X61 : $i]:
% 15.91/16.10         ((k1_enumset1 @ X59 @ X60 @ X61)
% 15.91/16.10           = (k2_xboole_0 @ (k2_tarski @ X59 @ X60) @ (k1_tarski @ X61)))),
% 15.91/16.10      inference('cnf', [status(esa)], [t43_enumset1])).
% 15.91/16.10  thf('16', plain,
% 15.91/16.10      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 15.91/16.10      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 15.91/16.10  thf('17', plain,
% 15.91/16.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.91/16.10         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1))
% 15.91/16.10           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 15.91/16.10      inference('sup+', [status(thm)], ['15', '16'])).
% 15.91/16.10  thf('18', plain,
% 15.91/16.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.91/16.10         ((k3_enumset1 @ X0 @ X0 @ X0 @ X2 @ X1) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 15.91/16.10      inference('demod', [status(thm)], ['14', '17'])).
% 15.91/16.10  thf('19', plain,
% 15.91/16.10      (((k1_enumset1 @ sk_B @ sk_C @ sk_A)
% 15.91/16.10         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 15.91/16.10      inference('demod', [status(thm)], ['7', '18'])).
% 15.91/16.10  thf('20', plain, ($false), inference('simplify', [status(thm)], ['19'])).
% 15.91/16.10  
% 15.91/16.10  % SZS output end Refutation
% 15.91/16.10  
% 15.91/16.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

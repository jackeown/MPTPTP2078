%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.48yyM8r8W2

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:37 EST 2020

% Result     : Theorem 0.84s
% Output     : Refutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :   43 (  47 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :  349 ( 386 expanded)
%              Number of equality atoms :   33 (  37 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t137_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) )
        = ( k1_enumset1 @ A @ B @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t137_enumset1])).

thf('0',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k2_tarski @ sk_C @ sk_A ) )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t100_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ B @ C @ A ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k1_enumset1 @ X13 @ X11 @ X12 )
      = ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('2',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k1_enumset1 @ X13 @ X11 @ X12 )
      = ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('3',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k2_tarski @ sk_C @ sk_A ) )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X3 ) @ ( k2_tarski @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('5',plain,(
    ( k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k1_enumset1 @ X13 @ X11 @ X12 )
      = ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_enumset1 @ X27 @ X27 @ X28 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('9',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t48_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ) )).

thf('10',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( k3_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 )
      = ( k2_xboole_0 @ ( k2_tarski @ X21 @ X22 ) @ ( k1_enumset1 @ X23 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t48_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_enumset1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('12',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k3_enumset1 @ X32 @ X32 @ X33 @ X34 @ X35 )
      = ( k2_enumset1 @ X32 @ X33 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_enumset1 @ X3 @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('16',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X3 ) @ ( k2_tarski @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('18',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k2_enumset1 @ X29 @ X29 @ X30 @ X31 )
      = ( k1_enumset1 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X1 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','19'])).

thf(t98_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ A @ C @ B ) ) )).

thf('21',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k1_enumset1 @ X36 @ X38 @ X37 )
      = ( k1_enumset1 @ X36 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf('22',plain,(
    ( k1_enumset1 @ sk_B @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['5','20','21'])).

thf('23',plain,(
    $false ),
    inference(simplify,[status(thm)],['22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.48yyM8r8W2
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:42:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.84/1.03  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.84/1.03  % Solved by: fo/fo7.sh
% 0.84/1.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.84/1.03  % done 1062 iterations in 0.573s
% 0.84/1.03  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.84/1.03  % SZS output start Refutation
% 0.84/1.03  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.84/1.03  thf(sk_A_type, type, sk_A: $i).
% 0.84/1.03  thf(sk_B_type, type, sk_B: $i).
% 0.84/1.03  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.84/1.03  thf(sk_C_type, type, sk_C: $i).
% 0.84/1.03  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.84/1.03  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.84/1.03  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.84/1.03  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.84/1.03  thf(t137_enumset1, conjecture,
% 0.84/1.03    (![A:$i,B:$i,C:$i]:
% 0.84/1.03     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 0.84/1.03       ( k1_enumset1 @ A @ B @ C ) ))).
% 0.84/1.03  thf(zf_stmt_0, negated_conjecture,
% 0.84/1.03    (~( ![A:$i,B:$i,C:$i]:
% 0.84/1.03        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 0.84/1.03          ( k1_enumset1 @ A @ B @ C ) ) )),
% 0.84/1.03    inference('cnf.neg', [status(esa)], [t137_enumset1])).
% 0.84/1.03  thf('0', plain,
% 0.84/1.03      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 0.84/1.03         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.84/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.03  thf(t100_enumset1, axiom,
% 0.84/1.03    (![A:$i,B:$i,C:$i]:
% 0.84/1.03     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ B @ C @ A ) ))).
% 0.84/1.03  thf('1', plain,
% 0.84/1.03      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.84/1.03         ((k1_enumset1 @ X13 @ X11 @ X12) = (k1_enumset1 @ X11 @ X12 @ X13))),
% 0.84/1.03      inference('cnf', [status(esa)], [t100_enumset1])).
% 0.84/1.03  thf('2', plain,
% 0.84/1.03      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.84/1.03         ((k1_enumset1 @ X13 @ X11 @ X12) = (k1_enumset1 @ X11 @ X12 @ X13))),
% 0.84/1.03      inference('cnf', [status(esa)], [t100_enumset1])).
% 0.84/1.03  thf('3', plain,
% 0.84/1.03      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 0.84/1.03         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 0.84/1.03      inference('demod', [status(thm)], ['0', '1', '2'])).
% 0.84/1.03  thf(l53_enumset1, axiom,
% 0.84/1.03    (![A:$i,B:$i,C:$i,D:$i]:
% 0.84/1.03     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.84/1.03       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.84/1.03  thf('4', plain,
% 0.84/1.03      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.84/1.03         ((k2_enumset1 @ X2 @ X3 @ X4 @ X5)
% 0.84/1.03           = (k2_xboole_0 @ (k2_tarski @ X2 @ X3) @ (k2_tarski @ X4 @ X5)))),
% 0.84/1.03      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.84/1.03  thf('5', plain,
% 0.84/1.03      (((k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A)
% 0.84/1.03         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 0.84/1.03      inference('demod', [status(thm)], ['3', '4'])).
% 0.84/1.03  thf('6', plain,
% 0.84/1.03      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.84/1.03         ((k1_enumset1 @ X13 @ X11 @ X12) = (k1_enumset1 @ X11 @ X12 @ X13))),
% 0.84/1.03      inference('cnf', [status(esa)], [t100_enumset1])).
% 0.84/1.03  thf(t70_enumset1, axiom,
% 0.84/1.03    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.84/1.03  thf('7', plain,
% 0.84/1.03      (![X27 : $i, X28 : $i]:
% 0.84/1.03         ((k1_enumset1 @ X27 @ X27 @ X28) = (k2_tarski @ X27 @ X28))),
% 0.84/1.03      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.84/1.03  thf('8', plain,
% 0.84/1.03      (![X0 : $i, X1 : $i]:
% 0.84/1.03         ((k1_enumset1 @ X0 @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.84/1.03      inference('sup+', [status(thm)], ['6', '7'])).
% 0.84/1.03  thf(t69_enumset1, axiom,
% 0.84/1.03    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.84/1.03  thf('9', plain, (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 0.84/1.03      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.84/1.03  thf(t48_enumset1, axiom,
% 0.84/1.03    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.84/1.03     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.84/1.03       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ))).
% 0.84/1.03  thf('10', plain,
% 0.84/1.03      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.84/1.03         ((k3_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25)
% 0.84/1.03           = (k2_xboole_0 @ (k2_tarski @ X21 @ X22) @ 
% 0.84/1.03              (k1_enumset1 @ X23 @ X24 @ X25)))),
% 0.84/1.03      inference('cnf', [status(esa)], [t48_enumset1])).
% 0.84/1.03  thf('11', plain,
% 0.84/1.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.84/1.03         ((k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1)
% 0.84/1.03           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_enumset1 @ X3 @ X2 @ X1)))),
% 0.84/1.03      inference('sup+', [status(thm)], ['9', '10'])).
% 0.84/1.03  thf(t72_enumset1, axiom,
% 0.84/1.03    (![A:$i,B:$i,C:$i,D:$i]:
% 0.84/1.03     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.84/1.03  thf('12', plain,
% 0.84/1.03      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.84/1.03         ((k3_enumset1 @ X32 @ X32 @ X33 @ X34 @ X35)
% 0.84/1.03           = (k2_enumset1 @ X32 @ X33 @ X34 @ X35))),
% 0.84/1.03      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.84/1.03  thf('13', plain,
% 0.84/1.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.84/1.03         ((k2_enumset1 @ X0 @ X3 @ X2 @ X1)
% 0.84/1.03           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_enumset1 @ X3 @ X2 @ X1)))),
% 0.84/1.03      inference('demod', [status(thm)], ['11', '12'])).
% 0.84/1.03  thf('14', plain,
% 0.84/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.03         ((k2_enumset1 @ X2 @ X1 @ X0 @ X1)
% 0.84/1.03           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.84/1.03      inference('sup+', [status(thm)], ['8', '13'])).
% 0.84/1.03  thf('15', plain,
% 0.84/1.03      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 0.84/1.03      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.84/1.03  thf('16', plain,
% 0.84/1.03      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.84/1.03         ((k2_enumset1 @ X2 @ X3 @ X4 @ X5)
% 0.84/1.03           = (k2_xboole_0 @ (k2_tarski @ X2 @ X3) @ (k2_tarski @ X4 @ X5)))),
% 0.84/1.03      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.84/1.03  thf('17', plain,
% 0.84/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.03         ((k2_enumset1 @ X0 @ X0 @ X2 @ X1)
% 0.84/1.03           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 0.84/1.03      inference('sup+', [status(thm)], ['15', '16'])).
% 0.84/1.03  thf(t71_enumset1, axiom,
% 0.84/1.03    (![A:$i,B:$i,C:$i]:
% 0.84/1.03     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.84/1.03  thf('18', plain,
% 0.84/1.03      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.84/1.03         ((k2_enumset1 @ X29 @ X29 @ X30 @ X31)
% 0.84/1.03           = (k1_enumset1 @ X29 @ X30 @ X31))),
% 0.84/1.03      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.84/1.03  thf('19', plain,
% 0.84/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.03         ((k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0))
% 0.84/1.03           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.84/1.03      inference('sup+', [status(thm)], ['17', '18'])).
% 0.84/1.03  thf('20', plain,
% 0.84/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.03         ((k2_enumset1 @ X2 @ X1 @ X0 @ X1) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.84/1.03      inference('demod', [status(thm)], ['14', '19'])).
% 0.84/1.03  thf(t98_enumset1, axiom,
% 0.84/1.03    (![A:$i,B:$i,C:$i]:
% 0.84/1.03     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ A @ C @ B ) ))).
% 0.84/1.03  thf('21', plain,
% 0.84/1.03      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.84/1.03         ((k1_enumset1 @ X36 @ X38 @ X37) = (k1_enumset1 @ X36 @ X37 @ X38))),
% 0.84/1.03      inference('cnf', [status(esa)], [t98_enumset1])).
% 0.84/1.03  thf('22', plain,
% 0.84/1.03      (((k1_enumset1 @ sk_B @ sk_C @ sk_A)
% 0.84/1.03         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 0.84/1.03      inference('demod', [status(thm)], ['5', '20', '21'])).
% 0.84/1.03  thf('23', plain, ($false), inference('simplify', [status(thm)], ['22'])).
% 0.84/1.03  
% 0.84/1.03  % SZS output end Refutation
% 0.84/1.03  
% 0.84/1.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

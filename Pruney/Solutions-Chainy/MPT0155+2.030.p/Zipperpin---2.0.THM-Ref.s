%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eF2f26BtuG

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:30 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   36 (  45 expanded)
%              Number of leaves         :   16 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :  297 ( 399 expanded)
%              Number of equality atoms :   26 (  35 expanded)
%              Maximal formula depth    :   12 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t71_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_enumset1 @ A @ A @ B @ C )
        = ( k1_enumset1 @ A @ B @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t71_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_enumset1 @ X26 @ X26 @ X27 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k2_enumset1 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k1_enumset1 @ X6 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k1_enumset1 @ X2 @ X3 @ X4 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k2_enumset1 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k1_enumset1 @ X6 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t47_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k3_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X9 ) @ ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('10',plain,(
    ! [X25: $i] :
      ( ( k2_tarski @ X25 @ X25 )
      = ( k1_tarski @ X25 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t48_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ) )).

thf('11',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k2_tarski @ X14 @ X15 ) @ ( k1_enumset1 @ X16 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t48_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_enumset1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k2_enumset1 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k1_enumset1 @ X6 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_enumset1 @ X0 @ X3 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('17',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','15','16'])).

thf('18',plain,(
    $false ),
    inference(simplify,[status(thm)],['17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eF2f26BtuG
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:25:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.44  % Solved by: fo/fo7.sh
% 0.20/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.44  % done 31 iterations in 0.022s
% 0.20/0.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.44  % SZS output start Refutation
% 0.20/0.44  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.20/0.44  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.44  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.44  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.44  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.44  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.20/0.44  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.44  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.44  thf(t71_enumset1, conjecture,
% 0.20/0.44    (![A:$i,B:$i,C:$i]:
% 0.20/0.44     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.20/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.44    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.44        ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ) )),
% 0.20/0.44    inference('cnf.neg', [status(esa)], [t71_enumset1])).
% 0.20/0.44  thf('0', plain,
% 0.20/0.44      (((k2_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.20/0.44         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf(t70_enumset1, axiom,
% 0.20/0.44    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.44  thf('1', plain,
% 0.20/0.44      (![X26 : $i, X27 : $i]:
% 0.20/0.44         ((k1_enumset1 @ X26 @ X26 @ X27) = (k2_tarski @ X26 @ X27))),
% 0.20/0.44      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.44  thf(t44_enumset1, axiom,
% 0.20/0.44    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.44     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.20/0.44       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 0.20/0.44  thf('2', plain,
% 0.20/0.44      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.44         ((k2_enumset1 @ X5 @ X6 @ X7 @ X8)
% 0.20/0.44           = (k2_xboole_0 @ (k1_tarski @ X5) @ (k1_enumset1 @ X6 @ X7 @ X8)))),
% 0.20/0.44      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.20/0.44  thf('3', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.44         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0)
% 0.20/0.44           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.20/0.44      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.44  thf(t42_enumset1, axiom,
% 0.20/0.44    (![A:$i,B:$i,C:$i]:
% 0.20/0.44     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.20/0.44       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.20/0.44  thf('4', plain,
% 0.20/0.44      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.44         ((k1_enumset1 @ X2 @ X3 @ X4)
% 0.20/0.44           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X3 @ X4)))),
% 0.20/0.44      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.20/0.44  thf('5', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.44         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.20/0.44      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.44  thf('6', plain,
% 0.20/0.44      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.44         ((k2_enumset1 @ X5 @ X6 @ X7 @ X8)
% 0.20/0.44           = (k2_xboole_0 @ (k1_tarski @ X5) @ (k1_enumset1 @ X6 @ X7 @ X8)))),
% 0.20/0.44      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.20/0.44  thf('7', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.44         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.44           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 0.20/0.44              (k2_enumset1 @ X2 @ X1 @ X1 @ X0)))),
% 0.20/0.44      inference('sup+', [status(thm)], ['5', '6'])).
% 0.20/0.44  thf(t47_enumset1, axiom,
% 0.20/0.44    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.44     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.20/0.44       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ))).
% 0.20/0.44  thf('8', plain,
% 0.20/0.44      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.44         ((k3_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13)
% 0.20/0.44           = (k2_xboole_0 @ (k1_tarski @ X9) @ 
% 0.20/0.44              (k2_enumset1 @ X10 @ X11 @ X12 @ X13)))),
% 0.20/0.44      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.20/0.44  thf('9', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.44         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.44           = (k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0))),
% 0.20/0.44      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.44  thf(t69_enumset1, axiom,
% 0.20/0.44    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.44  thf('10', plain,
% 0.20/0.44      (![X25 : $i]: ((k2_tarski @ X25 @ X25) = (k1_tarski @ X25))),
% 0.20/0.44      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.44  thf(t48_enumset1, axiom,
% 0.20/0.44    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.44     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.20/0.44       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ))).
% 0.20/0.44  thf('11', plain,
% 0.20/0.44      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.44         ((k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18)
% 0.20/0.44           = (k2_xboole_0 @ (k2_tarski @ X14 @ X15) @ 
% 0.20/0.44              (k1_enumset1 @ X16 @ X17 @ X18)))),
% 0.20/0.44      inference('cnf', [status(esa)], [t48_enumset1])).
% 0.20/0.44  thf('12', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.44         ((k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1)
% 0.20/0.44           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_enumset1 @ X3 @ X2 @ X1)))),
% 0.20/0.44      inference('sup+', [status(thm)], ['10', '11'])).
% 0.20/0.44  thf('13', plain,
% 0.20/0.44      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.44         ((k2_enumset1 @ X5 @ X6 @ X7 @ X8)
% 0.20/0.44           = (k2_xboole_0 @ (k1_tarski @ X5) @ (k1_enumset1 @ X6 @ X7 @ X8)))),
% 0.20/0.44      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.20/0.44  thf('14', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.44         ((k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1)
% 0.20/0.44           = (k2_enumset1 @ X0 @ X3 @ X2 @ X1))),
% 0.20/0.44      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.44  thf('15', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.44         ((k2_enumset1 @ X2 @ X2 @ X1 @ X0) = (k2_enumset1 @ X2 @ X1 @ X1 @ X0))),
% 0.20/0.44      inference('sup+', [status(thm)], ['9', '14'])).
% 0.20/0.44  thf('16', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.44         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.20/0.44      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.44  thf('17', plain,
% 0.20/0.44      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.20/0.44         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.44      inference('demod', [status(thm)], ['0', '15', '16'])).
% 0.20/0.44  thf('18', plain, ($false), inference('simplify', [status(thm)], ['17'])).
% 0.20/0.44  
% 0.20/0.44  % SZS output end Refutation
% 0.20/0.44  
% 0.20/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

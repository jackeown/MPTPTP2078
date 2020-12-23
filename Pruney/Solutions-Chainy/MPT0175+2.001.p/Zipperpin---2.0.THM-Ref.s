%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hwRqDoZZwc

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:49 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   38 (  44 expanded)
%              Number of leaves         :   17 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :  301 ( 358 expanded)
%              Number of equality atoms :   28 (  34 expanded)
%              Maximal formula depth    :   16 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t91_enumset1,conjecture,(
    ! [A: $i] :
      ( ( k4_enumset1 @ A @ A @ A @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k4_enumset1 @ A @ A @ A @ A @ A @ A )
        = ( k1_tarski @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t91_enumset1])).

thf('0',plain,(
    ( k4_enumset1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t79_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_enumset1 @ A @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k4_enumset1 @ X17 @ X17 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_enumset1 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t79_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k2_enumset1 @ X12 @ X12 @ X13 @ X14 )
      = ( k1_enumset1 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t77_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_enumset1 @ A @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_enumset1 @ X15 @ X15 @ X15 @ X16 )
      = ( k2_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t77_enumset1])).

thf('4',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k2_enumset1 @ X12 @ X12 @ X13 @ X14 )
      = ( k1_enumset1 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('5',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_enumset1 @ X15 @ X15 @ X16 )
      = ( k2_tarski @ X15 @ X16 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ( k2_tarski @ sk_A @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['0','1','2','5'])).

thf(t87_enumset1,axiom,(
    ! [A: $i] :
      ( ( k3_enumset1 @ A @ A @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('7',plain,(
    ! [X32: $i] :
      ( ( k3_enumset1 @ X32 @ X32 @ X32 @ X32 @ X32 )
      = ( k1_tarski @ X32 ) ) ),
    inference(cnf,[status(esa)],[t87_enumset1])).

thf(t80_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k5_enumset1 @ A @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('8',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( k5_enumset1 @ X21 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25 )
      = ( k3_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t80_enumset1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k5_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X32: $i] :
      ( ( k3_enumset1 @ X32 @ X32 @ X32 @ X32 @ X32 )
      = ( k1_tarski @ X32 ) ) ),
    inference(cnf,[status(esa)],[t87_enumset1])).

thf(t57_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k3_enumset1 @ C @ D @ E @ F @ G ) ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k5_enumset1 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 )
      = ( k2_xboole_0 @ ( k2_tarski @ X5 @ X6 ) @ ( k3_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t57_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_enumset1 @ X2 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t43_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ) )).

thf('13',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k1_enumset1 @ X2 @ X3 @ X4 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X3 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_enumset1 @ X2 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_enumset1 @ X15 @ X15 @ X16 )
      = ( k2_tarski @ X15 @ X16 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
      = ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['6','17'])).

thf('19',plain,(
    $false ),
    inference(simplify,[status(thm)],['18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hwRqDoZZwc
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:31:45 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.44  % Solved by: fo/fo7.sh
% 0.19/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.44  % done 17 iterations in 0.015s
% 0.19/0.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.44  % SZS output start Refutation
% 0.19/0.44  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.19/0.44  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.19/0.44  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.19/0.44  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.19/0.44  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.44  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.44  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.19/0.44  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.44  thf(t91_enumset1, conjecture,
% 0.19/0.44    (![A:$i]: ( ( k4_enumset1 @ A @ A @ A @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.19/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.44    (~( ![A:$i]:
% 0.19/0.44        ( ( k4_enumset1 @ A @ A @ A @ A @ A @ A ) = ( k1_tarski @ A ) ) )),
% 0.19/0.44    inference('cnf.neg', [status(esa)], [t91_enumset1])).
% 0.19/0.44  thf('0', plain,
% 0.19/0.44      (((k4_enumset1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.19/0.44         != (k1_tarski @ sk_A))),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf(t79_enumset1, axiom,
% 0.19/0.44    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.44     ( ( k4_enumset1 @ A @ A @ A @ B @ C @ D ) =
% 0.19/0.44       ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.19/0.44  thf('1', plain,
% 0.19/0.44      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.19/0.44         ((k4_enumset1 @ X17 @ X17 @ X17 @ X18 @ X19 @ X20)
% 0.19/0.44           = (k2_enumset1 @ X17 @ X18 @ X19 @ X20))),
% 0.19/0.44      inference('cnf', [status(esa)], [t79_enumset1])).
% 0.19/0.44  thf(t71_enumset1, axiom,
% 0.19/0.44    (![A:$i,B:$i,C:$i]:
% 0.19/0.44     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.19/0.44  thf('2', plain,
% 0.19/0.44      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.44         ((k2_enumset1 @ X12 @ X12 @ X13 @ X14)
% 0.19/0.44           = (k1_enumset1 @ X12 @ X13 @ X14))),
% 0.19/0.44      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.19/0.44  thf(t77_enumset1, axiom,
% 0.19/0.44    (![A:$i,B:$i]: ( ( k2_enumset1 @ A @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.19/0.44  thf('3', plain,
% 0.19/0.44      (![X15 : $i, X16 : $i]:
% 0.19/0.44         ((k2_enumset1 @ X15 @ X15 @ X15 @ X16) = (k2_tarski @ X15 @ X16))),
% 0.19/0.44      inference('cnf', [status(esa)], [t77_enumset1])).
% 0.19/0.44  thf('4', plain,
% 0.19/0.44      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.44         ((k2_enumset1 @ X12 @ X12 @ X13 @ X14)
% 0.19/0.44           = (k1_enumset1 @ X12 @ X13 @ X14))),
% 0.19/0.44      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.19/0.44  thf('5', plain,
% 0.19/0.44      (![X15 : $i, X16 : $i]:
% 0.19/0.44         ((k1_enumset1 @ X15 @ X15 @ X16) = (k2_tarski @ X15 @ X16))),
% 0.19/0.44      inference('demod', [status(thm)], ['3', '4'])).
% 0.19/0.44  thf('6', plain, (((k2_tarski @ sk_A @ sk_A) != (k1_tarski @ sk_A))),
% 0.19/0.44      inference('demod', [status(thm)], ['0', '1', '2', '5'])).
% 0.19/0.44  thf(t87_enumset1, axiom,
% 0.19/0.44    (![A:$i]: ( ( k3_enumset1 @ A @ A @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.19/0.44  thf('7', plain,
% 0.19/0.44      (![X32 : $i]:
% 0.19/0.44         ((k3_enumset1 @ X32 @ X32 @ X32 @ X32 @ X32) = (k1_tarski @ X32))),
% 0.19/0.44      inference('cnf', [status(esa)], [t87_enumset1])).
% 0.19/0.44  thf(t80_enumset1, axiom,
% 0.19/0.44    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.19/0.44     ( ( k5_enumset1 @ A @ A @ A @ B @ C @ D @ E ) =
% 0.19/0.44       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.19/0.44  thf('8', plain,
% 0.19/0.44      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.19/0.44         ((k5_enumset1 @ X21 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25)
% 0.19/0.44           = (k3_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25))),
% 0.19/0.44      inference('cnf', [status(esa)], [t80_enumset1])).
% 0.19/0.44  thf('9', plain,
% 0.19/0.44      (![X0 : $i]:
% 0.19/0.44         ((k5_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.19/0.44      inference('sup+', [status(thm)], ['7', '8'])).
% 0.19/0.44  thf('10', plain,
% 0.19/0.44      (![X32 : $i]:
% 0.19/0.44         ((k3_enumset1 @ X32 @ X32 @ X32 @ X32 @ X32) = (k1_tarski @ X32))),
% 0.19/0.44      inference('cnf', [status(esa)], [t87_enumset1])).
% 0.19/0.44  thf(t57_enumset1, axiom,
% 0.19/0.44    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.19/0.44     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.19/0.44       ( k2_xboole_0 @
% 0.19/0.44         ( k2_tarski @ A @ B ) @ ( k3_enumset1 @ C @ D @ E @ F @ G ) ) ))).
% 0.19/0.44  thf('11', plain,
% 0.19/0.44      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.19/0.44         ((k5_enumset1 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11)
% 0.19/0.44           = (k2_xboole_0 @ (k2_tarski @ X5 @ X6) @ 
% 0.19/0.44              (k3_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11)))),
% 0.19/0.44      inference('cnf', [status(esa)], [t57_enumset1])).
% 0.19/0.44  thf('12', plain,
% 0.19/0.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.44         ((k5_enumset1 @ X2 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0)
% 0.19/0.44           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)))),
% 0.19/0.44      inference('sup+', [status(thm)], ['10', '11'])).
% 0.19/0.44  thf(t43_enumset1, axiom,
% 0.19/0.44    (![A:$i,B:$i,C:$i]:
% 0.19/0.44     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.19/0.44       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ))).
% 0.19/0.44  thf('13', plain,
% 0.19/0.44      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.44         ((k1_enumset1 @ X2 @ X3 @ X4)
% 0.19/0.44           = (k2_xboole_0 @ (k2_tarski @ X2 @ X3) @ (k1_tarski @ X4)))),
% 0.19/0.44      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.19/0.44  thf('14', plain,
% 0.19/0.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.44         ((k5_enumset1 @ X2 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0)
% 0.19/0.44           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.19/0.44      inference('demod', [status(thm)], ['12', '13'])).
% 0.19/0.44  thf('15', plain,
% 0.19/0.44      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.19/0.44      inference('demod', [status(thm)], ['9', '14'])).
% 0.19/0.44  thf('16', plain,
% 0.19/0.44      (![X15 : $i, X16 : $i]:
% 0.19/0.44         ((k1_enumset1 @ X15 @ X15 @ X16) = (k2_tarski @ X15 @ X16))),
% 0.19/0.44      inference('demod', [status(thm)], ['3', '4'])).
% 0.19/0.44  thf('17', plain, (![X0 : $i]: ((k1_tarski @ X0) = (k2_tarski @ X0 @ X0))),
% 0.19/0.44      inference('sup+', [status(thm)], ['15', '16'])).
% 0.19/0.44  thf('18', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 0.19/0.44      inference('demod', [status(thm)], ['6', '17'])).
% 0.19/0.44  thf('19', plain, ($false), inference('simplify', [status(thm)], ['18'])).
% 0.19/0.44  
% 0.19/0.44  % SZS output end Refutation
% 0.19/0.44  
% 0.19/0.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

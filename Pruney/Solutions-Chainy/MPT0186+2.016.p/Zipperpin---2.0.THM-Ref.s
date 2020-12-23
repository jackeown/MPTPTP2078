%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7TSZlqrbGE

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:05 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   26 (  28 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    7
%              Number of atoms          :  195 ( 222 expanded)
%              Number of equality atoms :   16 (  18 expanded)
%              Maximal formula depth    :   12 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(t104_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ C @ B @ D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k2_enumset1 @ A @ B @ C @ D )
        = ( k2_enumset1 @ A @ C @ B @ D ) ) ),
    inference('cnf.neg',[status(esa)],[t104_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_C @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t99_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ B @ A @ C ) ) )).

thf('1',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( k1_enumset1 @ X33 @ X32 @ X34 )
      = ( k1_enumset1 @ X32 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t99_enumset1])).

thf(t48_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 )
      = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k1_enumset1 @ X2 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t48_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X1 @ X2 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 )
      = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k1_enumset1 @ X2 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t48_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X1 @ X2 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k3_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k3_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','9'])).

thf('11',plain,(
    $false ),
    inference(simplify,[status(thm)],['10'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7TSZlqrbGE
% 0.14/0.32  % Computer   : n001.cluster.edu
% 0.14/0.32  % Model      : x86_64 x86_64
% 0.14/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.32  % Memory     : 8042.1875MB
% 0.14/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.32  % CPULimit   : 60
% 0.14/0.32  % DateTime   : Tue Dec  1 13:42:15 EST 2020
% 0.14/0.32  % CPUTime    : 
% 0.14/0.32  % Running portfolio for 600 s
% 0.14/0.32  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.33  % Number of cores: 8
% 0.14/0.33  % Python version: Python 3.6.8
% 0.14/0.33  % Running in FO mode
% 0.19/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.51  % Solved by: fo/fo7.sh
% 0.19/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.51  % done 195 iterations in 0.071s
% 0.19/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.51  % SZS output start Refutation
% 0.19/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.51  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.19/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.51  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.19/0.51  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.19/0.51  thf(t104_enumset1, conjecture,
% 0.19/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.51     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ B @ D ) ))).
% 0.19/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.51    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.51        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ B @ D ) ) )),
% 0.19/0.51    inference('cnf.neg', [status(esa)], [t104_enumset1])).
% 0.19/0.51  thf('0', plain,
% 0.19/0.51      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.19/0.51         != (k2_enumset1 @ sk_A @ sk_C @ sk_B @ sk_D))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(t99_enumset1, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i]:
% 0.19/0.51     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ B @ A @ C ) ))).
% 0.19/0.51  thf('1', plain,
% 0.19/0.51      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.19/0.51         ((k1_enumset1 @ X33 @ X32 @ X34) = (k1_enumset1 @ X32 @ X33 @ X34))),
% 0.19/0.51      inference('cnf', [status(esa)], [t99_enumset1])).
% 0.19/0.51  thf(t48_enumset1, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.19/0.51     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.19/0.51       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ))).
% 0.19/0.51  thf('2', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.51         ((k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4)
% 0.19/0.51           = (k2_xboole_0 @ (k2_tarski @ X0 @ X1) @ 
% 0.19/0.51              (k1_enumset1 @ X2 @ X3 @ X4)))),
% 0.19/0.51      inference('cnf', [status(esa)], [t48_enumset1])).
% 0.19/0.51  thf('3', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.51         ((k3_enumset1 @ X4 @ X3 @ X1 @ X2 @ X0)
% 0.19/0.51           = (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ 
% 0.19/0.51              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.19/0.51      inference('sup+', [status(thm)], ['1', '2'])).
% 0.19/0.51  thf('4', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.51         ((k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4)
% 0.19/0.51           = (k2_xboole_0 @ (k2_tarski @ X0 @ X1) @ 
% 0.19/0.51              (k1_enumset1 @ X2 @ X3 @ X4)))),
% 0.19/0.51      inference('cnf', [status(esa)], [t48_enumset1])).
% 0.19/0.51  thf('5', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.51         ((k3_enumset1 @ X4 @ X3 @ X1 @ X2 @ X0)
% 0.19/0.51           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.19/0.51      inference('sup+', [status(thm)], ['3', '4'])).
% 0.19/0.51  thf(t72_enumset1, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.51     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.19/0.51  thf('6', plain,
% 0.19/0.51      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.51         ((k3_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13)
% 0.19/0.51           = (k2_enumset1 @ X10 @ X11 @ X12 @ X13))),
% 0.19/0.51      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.19/0.51  thf('7', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.51         ((k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0)
% 0.19/0.51           = (k2_enumset1 @ X3 @ X1 @ X2 @ X0))),
% 0.19/0.51      inference('sup+', [status(thm)], ['5', '6'])).
% 0.19/0.51  thf('8', plain,
% 0.19/0.51      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.51         ((k3_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13)
% 0.19/0.51           = (k2_enumset1 @ X10 @ X11 @ X12 @ X13))),
% 0.19/0.51      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.19/0.51  thf('9', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.51         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X3 @ X1 @ X2 @ X0))),
% 0.19/0.51      inference('sup+', [status(thm)], ['7', '8'])).
% 0.19/0.51  thf('10', plain,
% 0.19/0.51      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.19/0.51         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.19/0.51      inference('demod', [status(thm)], ['0', '9'])).
% 0.19/0.51  thf('11', plain, ($false), inference('simplify', [status(thm)], ['10'])).
% 0.19/0.51  
% 0.19/0.51  % SZS output end Refutation
% 0.19/0.51  
% 0.19/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

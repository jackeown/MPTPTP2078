%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mqcJriyILs

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:36 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   29 (  32 expanded)
%              Number of leaves         :   12 (  15 expanded)
%              Depth                    :    6
%              Number of atoms          :  225 ( 256 expanded)
%              Number of equality atoms :   21 (  24 expanded)
%              Maximal formula depth    :   10 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k2_enumset1 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k2_tarski @ X11 @ X12 ) @ ( k2_tarski @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('2',plain,(
    ( k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t113_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ B @ D @ C @ A ) ) )).

thf('3',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( k2_enumset1 @ X22 @ X19 @ X21 @ X20 )
      = ( k2_enumset1 @ X19 @ X20 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t113_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('4',plain,(
    ! [X59: $i,X60: $i,X61: $i] :
      ( ( k2_enumset1 @ X59 @ X59 @ X60 @ X61 )
      = ( k1_enumset1 @ X59 @ X60 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ( k1_enumset1 @ sk_A @ sk_C @ sk_B )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['2','5'])).

thf(t119_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ C @ D @ B @ A ) ) )).

thf('7',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k2_enumset1 @ X26 @ X25 @ X23 @ X24 )
      = ( k2_enumset1 @ X23 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t119_enumset1])).

thf('8',plain,(
    ! [X59: $i,X60: $i,X61: $i] :
      ( ( k2_enumset1 @ X59 @ X59 @ X60 @ X61 )
      = ( k1_enumset1 @ X59 @ X60 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k2_enumset1 @ X26 @ X25 @ X23 @ X24 )
      = ( k2_enumset1 @ X23 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t119_enumset1])).

thf('11',plain,(
    ! [X59: $i,X60: $i,X61: $i] :
      ( ( k2_enumset1 @ X59 @ X59 @ X60 @ X61 )
      = ( k1_enumset1 @ X59 @ X60 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['6','13'])).

thf('15',plain,(
    $false ),
    inference(simplify,[status(thm)],['14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mqcJriyILs
% 0.16/0.37  % Computer   : n015.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 20:45:38 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.43/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.61  % Solved by: fo/fo7.sh
% 0.43/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.61  % done 76 iterations in 0.125s
% 0.43/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.61  % SZS output start Refutation
% 0.43/0.61  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.43/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.43/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.43/0.61  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.43/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.43/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.43/0.61  thf(t137_enumset1, conjecture,
% 0.43/0.61    (![A:$i,B:$i,C:$i]:
% 0.43/0.61     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 0.43/0.61       ( k1_enumset1 @ A @ B @ C ) ))).
% 0.43/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.43/0.61        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 0.43/0.61          ( k1_enumset1 @ A @ B @ C ) ) )),
% 0.43/0.61    inference('cnf.neg', [status(esa)], [t137_enumset1])).
% 0.43/0.61  thf('0', plain,
% 0.43/0.61      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 0.43/0.61         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(l53_enumset1, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.61     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.43/0.61       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.43/0.61  thf('1', plain,
% 0.43/0.61      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.43/0.61         ((k2_enumset1 @ X11 @ X12 @ X13 @ X14)
% 0.43/0.61           = (k2_xboole_0 @ (k2_tarski @ X11 @ X12) @ (k2_tarski @ X13 @ X14)))),
% 0.43/0.61      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.43/0.61  thf('2', plain,
% 0.43/0.61      (((k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A)
% 0.43/0.61         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.43/0.61      inference('demod', [status(thm)], ['0', '1'])).
% 0.43/0.61  thf(t113_enumset1, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.61     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ D @ C @ A ) ))).
% 0.43/0.61  thf('3', plain,
% 0.43/0.61      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.43/0.61         ((k2_enumset1 @ X22 @ X19 @ X21 @ X20)
% 0.43/0.61           = (k2_enumset1 @ X19 @ X20 @ X21 @ X22))),
% 0.43/0.61      inference('cnf', [status(esa)], [t113_enumset1])).
% 0.43/0.61  thf(t71_enumset1, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i]:
% 0.43/0.61     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.43/0.61  thf('4', plain,
% 0.43/0.61      (![X59 : $i, X60 : $i, X61 : $i]:
% 0.43/0.61         ((k2_enumset1 @ X59 @ X59 @ X60 @ X61)
% 0.43/0.61           = (k1_enumset1 @ X59 @ X60 @ X61))),
% 0.43/0.61      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.43/0.61  thf('5', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.61         ((k2_enumset1 @ X2 @ X0 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.43/0.61      inference('sup+', [status(thm)], ['3', '4'])).
% 0.43/0.61  thf('6', plain,
% 0.43/0.61      (((k1_enumset1 @ sk_A @ sk_C @ sk_B)
% 0.43/0.61         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.43/0.61      inference('demod', [status(thm)], ['2', '5'])).
% 0.43/0.61  thf(t119_enumset1, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.61     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ C @ D @ B @ A ) ))).
% 0.43/0.61  thf('7', plain,
% 0.43/0.61      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.43/0.61         ((k2_enumset1 @ X26 @ X25 @ X23 @ X24)
% 0.43/0.61           = (k2_enumset1 @ X23 @ X24 @ X25 @ X26))),
% 0.43/0.61      inference('cnf', [status(esa)], [t119_enumset1])).
% 0.43/0.61  thf('8', plain,
% 0.43/0.61      (![X59 : $i, X60 : $i, X61 : $i]:
% 0.43/0.61         ((k2_enumset1 @ X59 @ X59 @ X60 @ X61)
% 0.43/0.61           = (k1_enumset1 @ X59 @ X60 @ X61))),
% 0.43/0.61      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.43/0.61  thf('9', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.61         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X2 @ X1))),
% 0.43/0.61      inference('sup+', [status(thm)], ['7', '8'])).
% 0.43/0.61  thf('10', plain,
% 0.43/0.61      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.43/0.61         ((k2_enumset1 @ X26 @ X25 @ X23 @ X24)
% 0.43/0.61           = (k2_enumset1 @ X23 @ X24 @ X25 @ X26))),
% 0.43/0.61      inference('cnf', [status(esa)], [t119_enumset1])).
% 0.43/0.61  thf('11', plain,
% 0.43/0.61      (![X59 : $i, X60 : $i, X61 : $i]:
% 0.43/0.61         ((k2_enumset1 @ X59 @ X59 @ X60 @ X61)
% 0.43/0.61           = (k1_enumset1 @ X59 @ X60 @ X61))),
% 0.43/0.61      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.43/0.61  thf('12', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.61         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.43/0.61      inference('sup+', [status(thm)], ['10', '11'])).
% 0.43/0.61  thf('13', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.61         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 0.43/0.61      inference('sup+', [status(thm)], ['9', '12'])).
% 0.43/0.61  thf('14', plain,
% 0.43/0.61      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.43/0.61         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.43/0.61      inference('demod', [status(thm)], ['6', '13'])).
% 0.43/0.61  thf('15', plain, ($false), inference('simplify', [status(thm)], ['14'])).
% 0.43/0.61  
% 0.43/0.61  % SZS output end Refutation
% 0.43/0.61  
% 0.43/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

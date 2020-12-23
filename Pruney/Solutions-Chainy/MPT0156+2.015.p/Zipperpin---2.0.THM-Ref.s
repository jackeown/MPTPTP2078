%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6Dz2Vgiijh

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:33 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   32 (  34 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :  287 ( 313 expanded)
%              Number of equality atoms :   22 (  24 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(t72_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k3_enumset1 @ A @ A @ B @ C @ D )
        = ( k2_enumset1 @ A @ B @ C @ D ) ) ),
    inference('cnf.neg',[status(esa)],[t72_enumset1])).

thf('0',plain,(
    ( k3_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k2_enumset1 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k1_enumset1 @ X6 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf(t6_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ X3 @ ( k2_xboole_0 @ X3 @ X4 ) )
      = ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k2_enumset1 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k1_enumset1 @ X6 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k2_enumset1 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X9 @ X10 @ X11 ) @ ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('7',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k2_enumset1 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k1_enumset1 @ X6 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf(t50_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k3_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 ) @ ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','12'])).

thf('14',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','13'])).

thf('15',plain,(
    $false ),
    inference(simplify,[status(thm)],['14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6Dz2Vgiijh
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:09:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 20 iterations in 0.021s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.48  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.20/0.48  thf(t72_enumset1, conjecture,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48        ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t72_enumset1])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      (((k3_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.48         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t44_enumset1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.20/0.48       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.48         ((k2_enumset1 @ X5 @ X6 @ X7 @ X8)
% 0.20/0.48           = (k2_xboole_0 @ (k1_tarski @ X5) @ (k1_enumset1 @ X6 @ X7 @ X8)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.20/0.48  thf(t6_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i]:
% 0.20/0.48         ((k2_xboole_0 @ X3 @ (k2_xboole_0 @ X3 @ X4))
% 0.20/0.48           = (k2_xboole_0 @ X3 @ X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [t6_xboole_1])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         ((k2_xboole_0 @ (k1_tarski @ X3) @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.48           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.48         ((k2_enumset1 @ X5 @ X6 @ X7 @ X8)
% 0.20/0.48           = (k2_xboole_0 @ (k1_tarski @ X5) @ (k1_enumset1 @ X6 @ X7 @ X8)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         ((k2_xboole_0 @ (k1_tarski @ X3) @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.48           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.48  thf(t46_enumset1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.20/0.48       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.48         ((k2_enumset1 @ X9 @ X10 @ X11 @ X12)
% 0.20/0.48           = (k2_xboole_0 @ (k1_enumset1 @ X9 @ X10 @ X11) @ (k1_tarski @ X12)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.48         ((k2_enumset1 @ X5 @ X6 @ X7 @ X8)
% 0.20/0.48           = (k2_xboole_0 @ (k1_tarski @ X5) @ (k1_enumset1 @ X6 @ X7 @ X8)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.20/0.48  thf(t4_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.48       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.20/0.48           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.48         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4)
% 0.20/0.48           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 0.20/0.48              (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X4)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['7', '8'])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.48         ((k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 0.20/0.48           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 0.20/0.48              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['6', '9'])).
% 0.20/0.48  thf(t50_enumset1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.48     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.20/0.48       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ))).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.48         ((k3_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17)
% 0.20/0.48           = (k2_xboole_0 @ (k2_enumset1 @ X13 @ X14 @ X15 @ X16) @ 
% 0.20/0.48              (k1_tarski @ X17)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t50_enumset1])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.48         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.48           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 0.20/0.48              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 0.20/0.48      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         ((k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.48           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['5', '12'])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.48         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.48      inference('demod', [status(thm)], ['0', '13'])).
% 0.20/0.48  thf('15', plain, ($false), inference('simplify', [status(thm)], ['14'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

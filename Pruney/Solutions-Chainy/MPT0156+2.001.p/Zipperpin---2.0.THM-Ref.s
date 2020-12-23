%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JIPyzc6jl8

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:31 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   41 (  42 expanded)
%              Number of leaves         :   20 (  21 expanded)
%              Depth                    :   11
%              Number of atoms          :  291 ( 304 expanded)
%              Number of equality atoms :   19 (  20 expanded)
%              Maximal formula depth    :   14 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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

thf(t45_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k2_tarski @ X13 @ X14 ) @ ( k2_tarski @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t45_enumset1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k1_enumset1 @ X23 @ X23 @ X24 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('4',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k2_enumset1 @ X25 @ X25 @ X26 @ X27 )
      = ( k1_enumset1 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k2_tarski @ X13 @ X14 ) @ ( k2_tarski @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t45_enumset1])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 )
      | ( r1_tarski @ ( k2_tarski @ X3 @ X2 ) @ X4 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      | ( r1_tarski @ ( k2_tarski @ X2 @ X2 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('9',plain,(
    ! [X22: $i] :
      ( ( k2_tarski @ X22 @ X22 )
      = ( k1_tarski @ X22 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      | ( r1_tarski @ ( k1_tarski @ X2 ) @ X3 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ ( k1_tarski @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k1_tarski @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_tarski @ ( k1_tarski @ X3 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','12'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('14',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t47_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ) )).

thf('16',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k3_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k1_tarski @ X17 ) @ ( k2_enumset1 @ X18 @ X19 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','17'])).

thf('19',plain,(
    $false ),
    inference(simplify,[status(thm)],['18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.08  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JIPyzc6jl8
% 0.08/0.28  % Computer   : n011.cluster.edu
% 0.08/0.28  % Model      : x86_64 x86_64
% 0.08/0.28  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.28  % Memory     : 8042.1875MB
% 0.08/0.28  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.28  % CPULimit   : 60
% 0.08/0.28  % DateTime   : Tue Dec  1 09:25:12 EST 2020
% 0.08/0.28  % CPUTime    : 
% 0.08/0.28  % Running portfolio for 600 s
% 0.08/0.28  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.08/0.29  % Number of cores: 8
% 0.08/0.29  % Python version: Python 3.6.8
% 0.08/0.29  % Running in FO mode
% 0.37/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.54  % Solved by: fo/fo7.sh
% 0.37/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.54  % done 463 iterations in 0.165s
% 0.37/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.54  % SZS output start Refutation
% 0.37/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.37/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.54  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.37/0.54  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.37/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.54  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.37/0.54  thf(t72_enumset1, conjecture,
% 0.37/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.54     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.37/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.54    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.54        ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ) )),
% 0.37/0.54    inference('cnf.neg', [status(esa)], [t72_enumset1])).
% 0.37/0.54  thf('0', plain,
% 0.37/0.54      (((k3_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.37/0.54         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf(t45_enumset1, axiom,
% 0.37/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.54     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.37/0.54       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.37/0.54  thf('1', plain,
% 0.37/0.54      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.37/0.54         ((k2_enumset1 @ X13 @ X14 @ X15 @ X16)
% 0.37/0.54           = (k2_xboole_0 @ (k2_tarski @ X13 @ X14) @ (k2_tarski @ X15 @ X16)))),
% 0.37/0.54      inference('cnf', [status(esa)], [t45_enumset1])).
% 0.37/0.54  thf(t7_xboole_1, axiom,
% 0.37/0.54    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.37/0.54  thf('2', plain,
% 0.37/0.54      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 0.37/0.54      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.37/0.54  thf(t70_enumset1, axiom,
% 0.37/0.54    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.37/0.54  thf('3', plain,
% 0.37/0.54      (![X23 : $i, X24 : $i]:
% 0.37/0.54         ((k1_enumset1 @ X23 @ X23 @ X24) = (k2_tarski @ X23 @ X24))),
% 0.37/0.54      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.37/0.54  thf(t71_enumset1, axiom,
% 0.37/0.54    (![A:$i,B:$i,C:$i]:
% 0.37/0.54     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.37/0.54  thf('4', plain,
% 0.37/0.54      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.37/0.54         ((k2_enumset1 @ X25 @ X25 @ X26 @ X27)
% 0.37/0.54           = (k1_enumset1 @ X25 @ X26 @ X27))),
% 0.37/0.54      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.37/0.54  thf('5', plain,
% 0.37/0.54      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.37/0.54         ((k2_enumset1 @ X13 @ X14 @ X15 @ X16)
% 0.37/0.54           = (k2_xboole_0 @ (k2_tarski @ X13 @ X14) @ (k2_tarski @ X15 @ X16)))),
% 0.37/0.54      inference('cnf', [status(esa)], [t45_enumset1])).
% 0.37/0.54  thf(t11_xboole_1, axiom,
% 0.37/0.54    (![A:$i,B:$i,C:$i]:
% 0.37/0.54     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.37/0.54  thf('6', plain,
% 0.37/0.54      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.37/0.54         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 0.37/0.54      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.37/0.54  thf('7', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.37/0.54         (~ (r1_tarski @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4)
% 0.37/0.54          | (r1_tarski @ (k2_tarski @ X3 @ X2) @ X4))),
% 0.37/0.54      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.54  thf('8', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.54         (~ (r1_tarski @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.37/0.54          | (r1_tarski @ (k2_tarski @ X2 @ X2) @ X3))),
% 0.37/0.54      inference('sup-', [status(thm)], ['4', '7'])).
% 0.37/0.54  thf(t69_enumset1, axiom,
% 0.37/0.54    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.37/0.54  thf('9', plain, (![X22 : $i]: ((k2_tarski @ X22 @ X22) = (k1_tarski @ X22))),
% 0.37/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.54  thf('10', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.54         (~ (r1_tarski @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.37/0.54          | (r1_tarski @ (k1_tarski @ X2) @ X3))),
% 0.37/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.37/0.54  thf('11', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.54         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ X2)
% 0.37/0.54          | (r1_tarski @ (k1_tarski @ X1) @ X2))),
% 0.37/0.54      inference('sup-', [status(thm)], ['3', '10'])).
% 0.37/0.54  thf('12', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.54         (r1_tarski @ (k1_tarski @ X2) @ 
% 0.37/0.54          (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['2', '11'])).
% 0.37/0.54  thf('13', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.54         (r1_tarski @ (k1_tarski @ X3) @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.37/0.54      inference('sup+', [status(thm)], ['1', '12'])).
% 0.37/0.54  thf(t12_xboole_1, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.37/0.54  thf('14', plain,
% 0.37/0.54      (![X6 : $i, X7 : $i]:
% 0.37/0.54         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.37/0.54      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.37/0.54  thf('15', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.54         ((k2_xboole_0 @ (k1_tarski @ X3) @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.37/0.54           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.37/0.54  thf(t47_enumset1, axiom,
% 0.37/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.37/0.54     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.37/0.54       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ))).
% 0.37/0.54  thf('16', plain,
% 0.37/0.54      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.37/0.54         ((k3_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21)
% 0.37/0.54           = (k2_xboole_0 @ (k1_tarski @ X17) @ 
% 0.37/0.54              (k2_enumset1 @ X18 @ X19 @ X20 @ X21)))),
% 0.37/0.54      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.37/0.54  thf('17', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.54         ((k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0)
% 0.37/0.54           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.37/0.54      inference('demod', [status(thm)], ['15', '16'])).
% 0.37/0.54  thf('18', plain,
% 0.37/0.54      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.37/0.54         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.37/0.54      inference('demod', [status(thm)], ['0', '17'])).
% 0.37/0.54  thf('19', plain, ($false), inference('simplify', [status(thm)], ['18'])).
% 0.37/0.54  
% 0.37/0.54  % SZS output end Refutation
% 0.37/0.54  
% 0.38/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

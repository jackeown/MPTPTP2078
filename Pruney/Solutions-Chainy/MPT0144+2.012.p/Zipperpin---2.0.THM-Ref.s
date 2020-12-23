%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.s4Y5573hxv

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   48 (  57 expanded)
%              Number of leaves         :   21 (  28 expanded)
%              Depth                    :   12
%              Number of atoms          :  470 ( 563 expanded)
%              Number of equality atoms :   33 (  42 expanded)
%              Maximal formula depth    :   17 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t60_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
        ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
        = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ) ),
    inference('cnf.neg',[status(esa)],[t60_enumset1])).

thf('0',plain,(
    ( k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G )
 != ( k2_xboole_0 @ ( k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k2_tarski @ sk_F @ sk_G ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k1_tarski @ X16 ) @ ( k2_tarski @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_tarski @ X14 @ X15 )
      = ( k2_xboole_0 @ ( k1_tarski @ X14 ) @ ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('3',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_tarski @ X14 @ X15 )
      = ( k2_xboole_0 @ ( k1_tarski @ X14 ) @ ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k1_tarski @ X16 ) @ ( k2_tarski @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k1_tarski @ X16 ) @ ( k2_tarski @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('12',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( k2_enumset1 @ X19 @ X20 @ X21 @ X22 )
      = ( k2_xboole_0 @ ( k1_tarski @ X19 ) @ ( k1_enumset1 @ X20 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','15'])).

thf(t48_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ) )).

thf('17',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k3_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 )
      = ( k2_xboole_0 @ ( k2_tarski @ X23 @ X24 ) @ ( k1_enumset1 @ X25 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t48_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X5 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X6 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','20'])).

thf(l68_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_enumset1 @ E @ F @ G ) ) ) )).

thf('22',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k5_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X7 @ X8 @ X9 @ X10 ) @ ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l68_enumset1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ( k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G )
 != ( k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G ) ),
    inference(demod,[status(thm)],['0','23'])).

thf('25',plain,(
    $false ),
    inference(simplify,[status(thm)],['24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.s4Y5573hxv
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:29:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 51 iterations in 0.065s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.52  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.52  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.21/0.52  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.52  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.21/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.52  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(sk_G_type, type, sk_G: $i).
% 0.21/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.52  thf(t60_enumset1, conjecture,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.21/0.52     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.21/0.52       ( k2_xboole_0 @
% 0.21/0.52         ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.21/0.52        ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.21/0.52          ( k2_xboole_0 @
% 0.21/0.52            ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t60_enumset1])).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      (((k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G)
% 0.21/0.52         != (k2_xboole_0 @ (k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.21/0.52             (k2_tarski @ sk_F @ sk_G)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t42_enumset1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.21/0.52       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.52         ((k1_enumset1 @ X16 @ X17 @ X18)
% 0.21/0.52           = (k2_xboole_0 @ (k1_tarski @ X16) @ (k2_tarski @ X17 @ X18)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.21/0.52  thf(t41_enumset1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( k2_tarski @ A @ B ) =
% 0.21/0.52       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (![X14 : $i, X15 : $i]:
% 0.21/0.52         ((k2_tarski @ X14 @ X15)
% 0.21/0.52           = (k2_xboole_0 @ (k1_tarski @ X14) @ (k1_tarski @ X15)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X14 : $i, X15 : $i]:
% 0.21/0.52         ((k2_tarski @ X14 @ X15)
% 0.21/0.52           = (k2_xboole_0 @ (k1_tarski @ X14) @ (k1_tarski @ X15)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.21/0.52  thf(t4_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.21/0.52       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.52         ((k2_xboole_0 @ (k2_xboole_0 @ X2 @ X3) @ X4)
% 0.21/0.52           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ X4)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.21/0.52           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.21/0.52              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['3', '4'])).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.21/0.52           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['2', '5'])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.52         ((k1_enumset1 @ X16 @ X17 @ X18)
% 0.21/0.52           = (k2_xboole_0 @ (k1_tarski @ X16) @ (k2_tarski @ X17 @ X18)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.21/0.52           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.21/0.52      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.52         ((k1_enumset1 @ X16 @ X17 @ X18)
% 0.21/0.52           = (k2_xboole_0 @ (k1_tarski @ X16) @ (k2_tarski @ X17 @ X18)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.21/0.52           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.21/0.52              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['3', '4'])).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.52         ((k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0))
% 0.21/0.52           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.52  thf(t44_enumset1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.52     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.21/0.52       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.52         ((k2_enumset1 @ X19 @ X20 @ X21 @ X22)
% 0.21/0.52           = (k2_xboole_0 @ (k1_tarski @ X19) @ (k1_enumset1 @ X20 @ X21 @ X22)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.52         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 0.21/0.52           = (k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['11', '12'])).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.52         ((k2_xboole_0 @ (k2_xboole_0 @ X2 @ X3) @ X4)
% 0.21/0.52           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ X4)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.52         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4)
% 0.21/0.52           = (k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ 
% 0.21/0.52              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X4)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['13', '14'])).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.52         ((k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 0.21/0.52           = (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ 
% 0.21/0.52              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['8', '15'])).
% 0.21/0.52  thf(t48_enumset1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.52     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.21/0.52       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ))).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.52         ((k3_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27)
% 0.21/0.52           = (k2_xboole_0 @ (k2_tarski @ X23 @ X24) @ 
% 0.21/0.52              (k1_enumset1 @ X25 @ X26 @ X27)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t48_enumset1])).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.52         ((k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 0.21/0.52           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.52      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.52         ((k2_xboole_0 @ (k2_xboole_0 @ X2 @ X3) @ X4)
% 0.21/0.52           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ X4)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.52         ((k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ X5)
% 0.21/0.52           = (k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ 
% 0.21/0.52              (k2_xboole_0 @ (k1_tarski @ X0) @ X5)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['18', '19'])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.52         ((k2_xboole_0 @ (k3_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2) @ 
% 0.21/0.52           (k2_tarski @ X1 @ X0))
% 0.21/0.52           = (k2_xboole_0 @ (k2_enumset1 @ X6 @ X5 @ X4 @ X3) @ 
% 0.21/0.52              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['1', '20'])).
% 0.21/0.52  thf(l68_enumset1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.21/0.52     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.21/0.52       ( k2_xboole_0 @
% 0.21/0.52         ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_enumset1 @ E @ F @ G ) ) ))).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.52         ((k5_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13)
% 0.21/0.52           = (k2_xboole_0 @ (k2_enumset1 @ X7 @ X8 @ X9 @ X10) @ 
% 0.21/0.52              (k1_enumset1 @ X11 @ X12 @ X13)))),
% 0.21/0.52      inference('cnf', [status(esa)], [l68_enumset1])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.52         ((k2_xboole_0 @ (k3_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2) @ 
% 0.21/0.52           (k2_tarski @ X1 @ X0))
% 0.21/0.52           = (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.52      inference('demod', [status(thm)], ['21', '22'])).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      (((k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G)
% 0.21/0.52         != (k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G))),
% 0.21/0.52      inference('demod', [status(thm)], ['0', '23'])).
% 0.21/0.52  thf('25', plain, ($false), inference('simplify', [status(thm)], ['24'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

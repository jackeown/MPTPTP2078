%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HqD0f8hZRi

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:27 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   47 (  53 expanded)
%              Number of leaves         :   18 (  24 expanded)
%              Depth                    :   11
%              Number of atoms          :  417 ( 478 expanded)
%              Number of equality atoms :   36 (  42 expanded)
%              Maximal formula depth    :   14 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X70: $i,X71: $i] :
      ( ( k1_enumset1 @ X70 @ X70 @ X71 )
      = ( k2_tarski @ X70 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k2_enumset1 @ X18 @ X19 @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k1_tarski @ X18 ) @ ( k1_enumset1 @ X19 @ X20 @ X21 ) ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k1_enumset1 @ X15 @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k1_tarski @ X15 ) @ ( k2_tarski @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X70: $i,X71: $i] :
      ( ( k1_enumset1 @ X70 @ X70 @ X71 )
      = ( k2_tarski @ X70 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('8',plain,(
    ! [X69: $i] :
      ( ( k2_tarski @ X69 @ X69 )
      = ( k1_tarski @ X69 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t54_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_tarski @ E @ F ) ) ) )).

thf('10',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k4_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X27 @ X28 @ X29 @ X30 ) @ ( k2_tarski @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t54_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_enumset1 @ X0 @ X0 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k1_enumset1 @ X15 @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k1_tarski @ X15 ) @ ( k2_tarski @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_enumset1 @ X0 @ X0 @ X0 @ X0 @ X2 @ X1 )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X70: $i,X71: $i] :
      ( ( k1_enumset1 @ X70 @ X70 @ X71 )
      = ( k2_tarski @ X70 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(l62_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ) )).

thf('15',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k4_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X9 @ X10 @ X11 ) @ ( k1_enumset1 @ X12 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l62_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X1 @ X1 @ X0 @ X4 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_enumset1 @ X4 @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t48_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ) )).

thf('17',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k3_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 )
      = ( k2_xboole_0 @ ( k2_tarski @ X22 @ X23 ) @ ( k1_enumset1 @ X24 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t48_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X1 @ X1 @ X0 @ X4 @ X3 @ X2 )
      = ( k3_enumset1 @ X1 @ X0 @ X4 @ X3 @ X2 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X69: $i] :
      ( ( k2_tarski @ X69 @ X69 )
      = ( k1_tarski @ X69 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('21',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k3_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 )
      = ( k2_xboole_0 @ ( k2_tarski @ X22 @ X23 ) @ ( k1_enumset1 @ X24 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t48_enumset1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_enumset1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k2_enumset1 @ X18 @ X19 @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k1_tarski @ X18 ) @ ( k1_enumset1 @ X19 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_enumset1 @ X0 @ X3 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','24'])).

thf('26',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','25'])).

thf('27',plain,(
    $false ),
    inference(simplify,[status(thm)],['26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HqD0f8hZRi
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:36:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 113 iterations in 0.064s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.20/0.52  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.52  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.20/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(t71_enumset1, conjecture,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.52        ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t71_enumset1])).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      (((k2_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.20/0.52         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t70_enumset1, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (![X70 : $i, X71 : $i]:
% 0.20/0.52         ((k1_enumset1 @ X70 @ X70 @ X71) = (k2_tarski @ X70 @ X71))),
% 0.20/0.52      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.52  thf(t44_enumset1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.52     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.20/0.52       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.52         ((k2_enumset1 @ X18 @ X19 @ X20 @ X21)
% 0.20/0.52           = (k2_xboole_0 @ (k1_tarski @ X18) @ (k1_enumset1 @ X19 @ X20 @ X21)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0)
% 0.20/0.52           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.52  thf(t42_enumset1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.20/0.52       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.52         ((k1_enumset1 @ X15 @ X16 @ X17)
% 0.20/0.52           = (k2_xboole_0 @ (k1_tarski @ X15) @ (k2_tarski @ X16 @ X17)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (![X70 : $i, X71 : $i]:
% 0.20/0.52         ((k1_enumset1 @ X70 @ X70 @ X71) = (k2_tarski @ X70 @ X71))),
% 0.20/0.52      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['5', '6'])).
% 0.20/0.52  thf(t69_enumset1, axiom,
% 0.20/0.52    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.52  thf('8', plain, (![X69 : $i]: ((k2_tarski @ X69 @ X69) = (k1_tarski @ X69))),
% 0.20/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['7', '8'])).
% 0.20/0.52  thf(t54_enumset1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.52     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.20/0.52       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_tarski @ E @ F ) ) ))).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.20/0.52         ((k4_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32)
% 0.20/0.52           = (k2_xboole_0 @ (k2_enumset1 @ X27 @ X28 @ X29 @ X30) @ 
% 0.20/0.52              (k2_tarski @ X31 @ X32)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t54_enumset1])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         ((k4_enumset1 @ X0 @ X0 @ X0 @ X0 @ X2 @ X1)
% 0.20/0.52           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['9', '10'])).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.52         ((k1_enumset1 @ X15 @ X16 @ X17)
% 0.20/0.52           = (k2_xboole_0 @ (k1_tarski @ X15) @ (k2_tarski @ X16 @ X17)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         ((k4_enumset1 @ X0 @ X0 @ X0 @ X0 @ X2 @ X1)
% 0.20/0.52           = (k1_enumset1 @ X0 @ X2 @ X1))),
% 0.20/0.52      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (![X70 : $i, X71 : $i]:
% 0.20/0.52         ((k1_enumset1 @ X70 @ X70 @ X71) = (k2_tarski @ X70 @ X71))),
% 0.20/0.52      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.52  thf(l62_enumset1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.52     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.20/0.52       ( k2_xboole_0 @
% 0.20/0.52         ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ))).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.52         ((k4_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14)
% 0.20/0.52           = (k2_xboole_0 @ (k1_enumset1 @ X9 @ X10 @ X11) @ 
% 0.20/0.52              (k1_enumset1 @ X12 @ X13 @ X14)))),
% 0.20/0.52      inference('cnf', [status(esa)], [l62_enumset1])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.52         ((k4_enumset1 @ X1 @ X1 @ X0 @ X4 @ X3 @ X2)
% 0.20/0.52           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 0.20/0.52              (k1_enumset1 @ X4 @ X3 @ X2)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['14', '15'])).
% 0.20/0.52  thf(t48_enumset1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.52     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.20/0.52       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ))).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.52         ((k3_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26)
% 0.20/0.52           = (k2_xboole_0 @ (k2_tarski @ X22 @ X23) @ 
% 0.20/0.52              (k1_enumset1 @ X24 @ X25 @ X26)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t48_enumset1])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.52         ((k4_enumset1 @ X1 @ X1 @ X0 @ X4 @ X3 @ X2)
% 0.20/0.52           = (k3_enumset1 @ X1 @ X0 @ X4 @ X3 @ X2))),
% 0.20/0.52      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         ((k1_enumset1 @ X2 @ X1 @ X0) = (k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['13', '18'])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (![X69 : $i]: ((k2_tarski @ X69 @ X69) = (k1_tarski @ X69))),
% 0.20/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.52         ((k3_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26)
% 0.20/0.52           = (k2_xboole_0 @ (k2_tarski @ X22 @ X23) @ 
% 0.20/0.52              (k1_enumset1 @ X24 @ X25 @ X26)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t48_enumset1])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.52         ((k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1)
% 0.20/0.52           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_enumset1 @ X3 @ X2 @ X1)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['20', '21'])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.52         ((k2_enumset1 @ X18 @ X19 @ X20 @ X21)
% 0.20/0.52           = (k2_xboole_0 @ (k1_tarski @ X18) @ (k1_enumset1 @ X19 @ X20 @ X21)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.52         ((k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1)
% 0.20/0.52           = (k2_enumset1 @ X0 @ X3 @ X2 @ X1))),
% 0.20/0.52      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         ((k1_enumset1 @ X2 @ X1 @ X0) = (k2_enumset1 @ X2 @ X2 @ X1 @ X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['19', '24'])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.20/0.52         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.52      inference('demod', [status(thm)], ['0', '25'])).
% 0.20/0.52  thf('27', plain, ($false), inference('simplify', [status(thm)], ['26'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

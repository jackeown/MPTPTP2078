%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zeEWLPaEM7

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   39 (  42 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :  333 ( 363 expanded)
%              Number of equality atoms :   28 (  31 expanded)
%              Maximal formula depth    :   16 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(t14_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t14_zfmisc_1])).

thf('0',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('1',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k5_enumset1 @ X26 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 )
      = ( k4_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k1_enumset1 @ X12 @ X12 @ X13 )
      = ( k2_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('3',plain,(
    ! [X11: $i] :
      ( ( k2_tarski @ X11 @ X11 )
      = ( k1_tarski @ X11 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k2_enumset1 @ X14 @ X14 @ X15 @ X16 )
      = ( k1_enumset1 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k3_enumset1 @ X17 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_enumset1 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t60_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k5_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 ) @ ( k2_tarski @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t60_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X5 @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_enumset1 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('12',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( k4_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25 )
      = ( k3_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('13',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k3_enumset1 @ X17 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_enumset1 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k2_enumset1 @ X14 @ X14 @ X15 @ X16 )
      = ( k1_enumset1 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','14','15'])).

thf('17',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k1_enumset1 @ X12 @ X12 @ X13 )
      = ( k2_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('18',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','16','17'])).

thf('19',plain,(
    $false ),
    inference(simplify,[status(thm)],['18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zeEWLPaEM7
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:39:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 21 iterations in 0.022s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.21/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.47  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.47  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.21/0.47  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.21/0.47  thf(t14_zfmisc_1, conjecture,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.21/0.47       ( k2_tarski @ A @ B ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i]:
% 0.21/0.47        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.21/0.47          ( k2_tarski @ A @ B ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t14_zfmisc_1])).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_A @ sk_B))
% 0.21/0.47         != (k2_tarski @ sk_A @ sk_B))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t74_enumset1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.21/0.47     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.21/0.47       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.21/0.47         ((k5_enumset1 @ X26 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31)
% 0.21/0.47           = (k4_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31))),
% 0.21/0.47      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.21/0.47  thf(t70_enumset1, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X12 : $i, X13 : $i]:
% 0.21/0.47         ((k1_enumset1 @ X12 @ X12 @ X13) = (k2_tarski @ X12 @ X13))),
% 0.21/0.47      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.47  thf(t69_enumset1, axiom,
% 0.21/0.47    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.47  thf('3', plain, (![X11 : $i]: ((k2_tarski @ X11 @ X11) = (k1_tarski @ X11))),
% 0.21/0.47      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.47      inference('sup+', [status(thm)], ['2', '3'])).
% 0.21/0.47  thf(t71_enumset1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.47         ((k2_enumset1 @ X14 @ X14 @ X15 @ X16)
% 0.21/0.47           = (k1_enumset1 @ X14 @ X15 @ X16))),
% 0.21/0.47      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.21/0.47  thf(t72_enumset1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.47     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.47         ((k3_enumset1 @ X17 @ X17 @ X18 @ X19 @ X20)
% 0.21/0.47           = (k2_enumset1 @ X17 @ X18 @ X19 @ X20))),
% 0.21/0.47      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.21/0.47  thf(t60_enumset1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.21/0.47     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.21/0.47       ( k2_xboole_0 @
% 0.21/0.47         ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ))).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.47         ((k5_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10)
% 0.21/0.47           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8) @ 
% 0.21/0.47              (k2_tarski @ X9 @ X10)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t60_enumset1])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.47         ((k5_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4)
% 0.21/0.47           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.21/0.47              (k2_tarski @ X5 @ X4)))),
% 0.21/0.47      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.47         ((k5_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 @ X4 @ X3)
% 0.21/0.47           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 0.21/0.47              (k2_tarski @ X4 @ X3)))),
% 0.21/0.47      inference('sup+', [status(thm)], ['5', '8'])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         ((k5_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X2 @ X1)
% 0.21/0.47           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 0.21/0.47      inference('sup+', [status(thm)], ['4', '9'])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         ((k4_enumset1 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0)
% 0.21/0.47           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.21/0.47      inference('sup+', [status(thm)], ['1', '10'])).
% 0.21/0.47  thf(t73_enumset1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.47     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.21/0.47       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.47         ((k4_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 @ X25)
% 0.21/0.47           = (k3_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25))),
% 0.21/0.47      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.47         ((k3_enumset1 @ X17 @ X17 @ X18 @ X19 @ X20)
% 0.21/0.47           = (k2_enumset1 @ X17 @ X18 @ X19 @ X20))),
% 0.21/0.47      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.47         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 0.21/0.47           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.47      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.47         ((k2_enumset1 @ X14 @ X14 @ X15 @ X16)
% 0.21/0.47           = (k1_enumset1 @ X14 @ X15 @ X16))),
% 0.21/0.47      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         ((k1_enumset1 @ X2 @ X1 @ X0)
% 0.21/0.47           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.21/0.47      inference('demod', [status(thm)], ['11', '14', '15'])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      (![X12 : $i, X13 : $i]:
% 0.21/0.47         ((k1_enumset1 @ X12 @ X12 @ X13) = (k2_tarski @ X12 @ X13))),
% 0.21/0.47      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.47  thf('18', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.21/0.47      inference('demod', [status(thm)], ['0', '16', '17'])).
% 0.21/0.47  thf('19', plain, ($false), inference('simplify', [status(thm)], ['18'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

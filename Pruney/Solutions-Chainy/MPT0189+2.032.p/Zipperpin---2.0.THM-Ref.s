%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.w5WGBamjLP

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:10 EST 2020

% Result     : Theorem 0.98s
% Output     : Refutation 0.98s
% Verified   : 
% Statistics : Number of formulae       :   40 (  58 expanded)
%              Number of leaves         :   18 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :  350 ( 578 expanded)
%              Number of equality atoms :   29 (  47 expanded)
%              Maximal formula depth    :   15 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t108_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ B @ A @ C @ D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k2_enumset1 @ A @ B @ C @ D )
        = ( k2_enumset1 @ B @ A @ C @ D ) ) ),
    inference('cnf.neg',[status(esa)],[t108_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t100_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ B @ C @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X0 @ X1 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('2',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k3_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42 )
      = ( k2_enumset1 @ X39 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t55_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k4_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15 ) @ ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t55_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('5',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( k4_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47 )
      = ( k3_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('6',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k3_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42 )
      = ( k2_enumset1 @ X39 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(t103_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ D @ C ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_enumset1 @ X3 @ X4 @ X6 @ X5 )
      = ( k2_enumset1 @ X3 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t103_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('10',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k2_enumset1 @ X36 @ X36 @ X37 @ X38 )
      = ( k1_enumset1 @ X36 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X1 @ X2 ) @ ( k1_tarski @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) )
      = ( k2_enumset1 @ X1 @ X2 @ X0 @ X3 ) ) ),
    inference('sup+',[status(thm)],['1','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X1 @ X2 ) @ ( k1_tarski @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X2 @ X1 @ X3 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t105_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ C @ D @ B ) ) )).

thf('16',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k2_enumset1 @ X7 @ X10 @ X8 @ X9 )
      = ( k2_enumset1 @ X7 @ X8 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('17',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_enumset1 @ X3 @ X4 @ X6 @ X5 )
      = ( k2_enumset1 @ X3 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t103_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X1 @ X2 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','15','18'])).

thf('20',plain,(
    $false ),
    inference(simplify,[status(thm)],['19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.w5WGBamjLP
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:39:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.98/1.16  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.98/1.16  % Solved by: fo/fo7.sh
% 0.98/1.16  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.98/1.16  % done 659 iterations in 0.672s
% 0.98/1.16  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.98/1.16  % SZS output start Refutation
% 0.98/1.16  thf(sk_A_type, type, sk_A: $i).
% 0.98/1.16  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.98/1.16  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.98/1.16  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.98/1.16  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.98/1.16  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.98/1.16  thf(sk_C_type, type, sk_C: $i).
% 0.98/1.16  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.98/1.16  thf(sk_D_type, type, sk_D: $i).
% 0.98/1.16  thf(sk_B_type, type, sk_B: $i).
% 0.98/1.16  thf(t108_enumset1, conjecture,
% 0.98/1.16    (![A:$i,B:$i,C:$i,D:$i]:
% 0.98/1.16     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ A @ C @ D ) ))).
% 0.98/1.16  thf(zf_stmt_0, negated_conjecture,
% 0.98/1.16    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.98/1.16        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ A @ C @ D ) ) )),
% 0.98/1.16    inference('cnf.neg', [status(esa)], [t108_enumset1])).
% 0.98/1.16  thf('0', plain,
% 0.98/1.16      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.98/1.16         != (k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_D))),
% 0.98/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.98/1.16  thf(t100_enumset1, axiom,
% 0.98/1.16    (![A:$i,B:$i,C:$i]:
% 0.98/1.16     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ B @ C @ A ) ))).
% 0.98/1.16  thf('1', plain,
% 0.98/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.98/1.16         ((k1_enumset1 @ X2 @ X0 @ X1) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.98/1.16      inference('cnf', [status(esa)], [t100_enumset1])).
% 0.98/1.16  thf(t72_enumset1, axiom,
% 0.98/1.16    (![A:$i,B:$i,C:$i,D:$i]:
% 0.98/1.16     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.98/1.16  thf('2', plain,
% 0.98/1.16      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.98/1.16         ((k3_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42)
% 0.98/1.16           = (k2_enumset1 @ X39 @ X40 @ X41 @ X42))),
% 0.98/1.16      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.98/1.16  thf(t55_enumset1, axiom,
% 0.98/1.16    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.98/1.16     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.98/1.16       ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ))).
% 0.98/1.16  thf('3', plain,
% 0.98/1.16      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.98/1.16         ((k4_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16)
% 0.98/1.16           = (k2_xboole_0 @ (k3_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15) @ 
% 0.98/1.16              (k1_tarski @ X16)))),
% 0.98/1.16      inference('cnf', [status(esa)], [t55_enumset1])).
% 0.98/1.16  thf('4', plain,
% 0.98/1.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.98/1.16         ((k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4)
% 0.98/1.16           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.98/1.16              (k1_tarski @ X4)))),
% 0.98/1.16      inference('sup+', [status(thm)], ['2', '3'])).
% 0.98/1.16  thf(t73_enumset1, axiom,
% 0.98/1.16    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.98/1.16     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.98/1.16       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.98/1.16  thf('5', plain,
% 0.98/1.16      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.98/1.16         ((k4_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47)
% 0.98/1.16           = (k3_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47))),
% 0.98/1.16      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.98/1.16  thf('6', plain,
% 0.98/1.16      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.98/1.16         ((k3_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42)
% 0.98/1.16           = (k2_enumset1 @ X39 @ X40 @ X41 @ X42))),
% 0.98/1.16      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.98/1.16  thf('7', plain,
% 0.98/1.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.98/1.16         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 0.98/1.16           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.98/1.16      inference('sup+', [status(thm)], ['5', '6'])).
% 0.98/1.16  thf('8', plain,
% 0.98/1.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.98/1.16         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 0.98/1.16           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.98/1.16      inference('sup+', [status(thm)], ['4', '7'])).
% 0.98/1.16  thf(t103_enumset1, axiom,
% 0.98/1.16    (![A:$i,B:$i,C:$i,D:$i]:
% 0.98/1.16     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ D @ C ) ))).
% 0.98/1.16  thf('9', plain,
% 0.98/1.16      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.98/1.16         ((k2_enumset1 @ X3 @ X4 @ X6 @ X5) = (k2_enumset1 @ X3 @ X4 @ X5 @ X6))),
% 0.98/1.16      inference('cnf', [status(esa)], [t103_enumset1])).
% 0.98/1.16  thf(t71_enumset1, axiom,
% 0.98/1.16    (![A:$i,B:$i,C:$i]:
% 0.98/1.16     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.98/1.16  thf('10', plain,
% 0.98/1.16      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.98/1.16         ((k2_enumset1 @ X36 @ X36 @ X37 @ X38)
% 0.98/1.16           = (k1_enumset1 @ X36 @ X37 @ X38))),
% 0.98/1.16      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.98/1.16  thf('11', plain,
% 0.98/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.98/1.16         ((k2_enumset1 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 0.98/1.16      inference('sup+', [status(thm)], ['9', '10'])).
% 0.98/1.16  thf('12', plain,
% 0.98/1.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.98/1.16         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X1 @ X2) @ (k1_tarski @ X0))
% 0.98/1.16           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.98/1.16      inference('demod', [status(thm)], ['8', '11'])).
% 0.98/1.16  thf('13', plain,
% 0.98/1.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.98/1.16         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3))
% 0.98/1.16           = (k2_enumset1 @ X1 @ X2 @ X0 @ X3))),
% 0.98/1.16      inference('sup+', [status(thm)], ['1', '12'])).
% 0.98/1.16  thf('14', plain,
% 0.98/1.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.98/1.16         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X1 @ X2) @ (k1_tarski @ X0))
% 0.98/1.16           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.98/1.16      inference('demod', [status(thm)], ['8', '11'])).
% 0.98/1.16  thf('15', plain,
% 0.98/1.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.98/1.16         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X2 @ X1 @ X3 @ X0))),
% 0.98/1.16      inference('sup+', [status(thm)], ['13', '14'])).
% 0.98/1.16  thf(t105_enumset1, axiom,
% 0.98/1.16    (![A:$i,B:$i,C:$i,D:$i]:
% 0.98/1.16     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ D @ B ) ))).
% 0.98/1.16  thf('16', plain,
% 0.98/1.16      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.98/1.16         ((k2_enumset1 @ X7 @ X10 @ X8 @ X9)
% 0.98/1.16           = (k2_enumset1 @ X7 @ X8 @ X9 @ X10))),
% 0.98/1.16      inference('cnf', [status(esa)], [t105_enumset1])).
% 0.98/1.16  thf('17', plain,
% 0.98/1.16      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.98/1.16         ((k2_enumset1 @ X3 @ X4 @ X6 @ X5) = (k2_enumset1 @ X3 @ X4 @ X5 @ X6))),
% 0.98/1.16      inference('cnf', [status(esa)], [t103_enumset1])).
% 0.98/1.16  thf('18', plain,
% 0.98/1.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.98/1.16         ((k2_enumset1 @ X3 @ X1 @ X2 @ X0) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.98/1.16      inference('sup+', [status(thm)], ['16', '17'])).
% 0.98/1.16  thf('19', plain,
% 0.98/1.16      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.98/1.16         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.98/1.16      inference('demod', [status(thm)], ['0', '15', '18'])).
% 0.98/1.16  thf('20', plain, ($false), inference('simplify', [status(thm)], ['19'])).
% 0.98/1.16  
% 0.98/1.16  % SZS output end Refutation
% 0.98/1.16  
% 0.98/1.17  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

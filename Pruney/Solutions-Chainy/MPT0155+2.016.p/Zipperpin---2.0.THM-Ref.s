%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.q4qSSSzV4n

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:28 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :   47 (  84 expanded)
%              Number of leaves         :   17 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :  394 ( 762 expanded)
%              Number of equality atoms :   37 (  74 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

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

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X40: $i] :
      ( ( k2_tarski @ X40 @ X40 )
      = ( k1_tarski @ X40 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X41 @ X41 @ X42 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t48_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ) )).

thf('3',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k3_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_xboole_0 @ ( k2_tarski @ X27 @ X28 ) @ ( k1_enumset1 @ X29 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t48_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X1 @ X0 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t43_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k1_enumset1 @ X15 @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k2_tarski @ X15 @ X16 ) @ ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X1 @ X0 @ X0 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X40: $i] :
      ( ( k2_tarski @ X40 @ X40 )
      = ( k1_tarski @ X40 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('9',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X41 @ X41 @ X42 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('10',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k2_enumset1 @ X18 @ X19 @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k1_tarski @ X18 ) @ ( k1_enumset1 @ X19 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X40: $i] :
      ( ( k2_tarski @ X40 @ X40 )
      = ( k1_tarski @ X40 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('14',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k1_enumset1 @ X15 @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k2_tarski @ X15 @ X16 ) @ ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X41 @ X41 @ X42 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','17'])).

thf(t47_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ) )).

thf('19',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k3_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 )
      = ( k2_xboole_0 @ ( k1_tarski @ X22 ) @ ( k2_enumset1 @ X23 @ X24 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X1 @ X0 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','20'])).

thf(t6_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k2_enumset1 @ X18 @ X19 @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k1_tarski @ X18 ) @ ( k1_enumset1 @ X19 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','20'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','26'])).

thf('28',plain,(
    $false ),
    inference(simplify,[status(thm)],['27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.q4qSSSzV4n
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:50:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.50/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.50/0.71  % Solved by: fo/fo7.sh
% 0.50/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.71  % done 459 iterations in 0.253s
% 0.50/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.50/0.71  % SZS output start Refutation
% 0.50/0.71  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.50/0.71  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.50/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.50/0.71  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.50/0.71  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.50/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.50/0.71  thf(sk_C_type, type, sk_C: $i).
% 0.50/0.71  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.50/0.71  thf(t71_enumset1, conjecture,
% 0.50/0.71    (![A:$i,B:$i,C:$i]:
% 0.50/0.71     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.50/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.71    (~( ![A:$i,B:$i,C:$i]:
% 0.50/0.71        ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ) )),
% 0.50/0.71    inference('cnf.neg', [status(esa)], [t71_enumset1])).
% 0.50/0.71  thf('0', plain,
% 0.50/0.71      (((k2_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.50/0.71         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf(t69_enumset1, axiom,
% 0.50/0.71    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.50/0.71  thf('1', plain, (![X40 : $i]: ((k2_tarski @ X40 @ X40) = (k1_tarski @ X40))),
% 0.50/0.71      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.50/0.71  thf(t70_enumset1, axiom,
% 0.50/0.71    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.50/0.71  thf('2', plain,
% 0.50/0.71      (![X41 : $i, X42 : $i]:
% 0.50/0.71         ((k1_enumset1 @ X41 @ X41 @ X42) = (k2_tarski @ X41 @ X42))),
% 0.50/0.71      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.50/0.71  thf(t48_enumset1, axiom,
% 0.50/0.71    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.50/0.71     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.50/0.71       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ))).
% 0.50/0.71  thf('3', plain,
% 0.50/0.71      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.50/0.71         ((k3_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31)
% 0.50/0.71           = (k2_xboole_0 @ (k2_tarski @ X27 @ X28) @ 
% 0.50/0.71              (k1_enumset1 @ X29 @ X30 @ X31)))),
% 0.50/0.71      inference('cnf', [status(esa)], [t48_enumset1])).
% 0.50/0.71  thf('4', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.50/0.71         ((k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0)
% 0.50/0.71           = (k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.50/0.71      inference('sup+', [status(thm)], ['2', '3'])).
% 0.50/0.71  thf('5', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.71         ((k3_enumset1 @ X2 @ X1 @ X0 @ X0 @ X0)
% 0.50/0.71           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)))),
% 0.50/0.71      inference('sup+', [status(thm)], ['1', '4'])).
% 0.50/0.71  thf(t43_enumset1, axiom,
% 0.50/0.71    (![A:$i,B:$i,C:$i]:
% 0.50/0.71     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.50/0.71       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ))).
% 0.50/0.71  thf('6', plain,
% 0.50/0.71      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.50/0.71         ((k1_enumset1 @ X15 @ X16 @ X17)
% 0.50/0.71           = (k2_xboole_0 @ (k2_tarski @ X15 @ X16) @ (k1_tarski @ X17)))),
% 0.50/0.71      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.50/0.71  thf('7', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.71         ((k3_enumset1 @ X2 @ X1 @ X0 @ X0 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.50/0.71      inference('demod', [status(thm)], ['5', '6'])).
% 0.50/0.71  thf('8', plain, (![X40 : $i]: ((k2_tarski @ X40 @ X40) = (k1_tarski @ X40))),
% 0.50/0.71      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.50/0.71  thf('9', plain,
% 0.50/0.71      (![X41 : $i, X42 : $i]:
% 0.50/0.71         ((k1_enumset1 @ X41 @ X41 @ X42) = (k2_tarski @ X41 @ X42))),
% 0.50/0.71      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.50/0.71  thf(t44_enumset1, axiom,
% 0.50/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.71     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.50/0.71       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 0.50/0.71  thf('10', plain,
% 0.50/0.71      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.50/0.71         ((k2_enumset1 @ X18 @ X19 @ X20 @ X21)
% 0.50/0.71           = (k2_xboole_0 @ (k1_tarski @ X18) @ (k1_enumset1 @ X19 @ X20 @ X21)))),
% 0.50/0.71      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.50/0.71  thf('11', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.71         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0)
% 0.50/0.71           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.50/0.71      inference('sup+', [status(thm)], ['9', '10'])).
% 0.50/0.71  thf('12', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((k2_enumset1 @ X1 @ X0 @ X0 @ X0)
% 0.50/0.71           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.50/0.71      inference('sup+', [status(thm)], ['8', '11'])).
% 0.50/0.71  thf('13', plain,
% 0.50/0.71      (![X40 : $i]: ((k2_tarski @ X40 @ X40) = (k1_tarski @ X40))),
% 0.50/0.71      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.50/0.71  thf('14', plain,
% 0.50/0.71      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.50/0.71         ((k1_enumset1 @ X15 @ X16 @ X17)
% 0.50/0.71           = (k2_xboole_0 @ (k2_tarski @ X15 @ X16) @ (k1_tarski @ X17)))),
% 0.50/0.71      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.50/0.71  thf('15', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((k1_enumset1 @ X0 @ X0 @ X1)
% 0.50/0.71           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.50/0.71      inference('sup+', [status(thm)], ['13', '14'])).
% 0.50/0.71  thf('16', plain,
% 0.50/0.71      (![X41 : $i, X42 : $i]:
% 0.50/0.71         ((k1_enumset1 @ X41 @ X41 @ X42) = (k2_tarski @ X41 @ X42))),
% 0.50/0.71      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.50/0.71  thf('17', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((k2_tarski @ X0 @ X1)
% 0.50/0.71           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.50/0.71      inference('demod', [status(thm)], ['15', '16'])).
% 0.50/0.71  thf('18', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((k2_enumset1 @ X1 @ X0 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.50/0.71      inference('demod', [status(thm)], ['12', '17'])).
% 0.50/0.71  thf(t47_enumset1, axiom,
% 0.50/0.71    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.50/0.71     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.50/0.71       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ))).
% 0.50/0.71  thf('19', plain,
% 0.50/0.71      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.50/0.71         ((k3_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26)
% 0.50/0.71           = (k2_xboole_0 @ (k1_tarski @ X22) @ 
% 0.50/0.71              (k2_enumset1 @ X23 @ X24 @ X25 @ X26)))),
% 0.50/0.71      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.50/0.71  thf('20', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.71         ((k3_enumset1 @ X2 @ X1 @ X0 @ X0 @ X0)
% 0.50/0.71           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.50/0.71      inference('sup+', [status(thm)], ['18', '19'])).
% 0.50/0.71  thf('21', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.71         ((k1_enumset1 @ X2 @ X1 @ X0)
% 0.50/0.71           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.50/0.71      inference('sup+', [status(thm)], ['7', '20'])).
% 0.50/0.71  thf(t6_xboole_1, axiom,
% 0.50/0.71    (![A:$i,B:$i]:
% 0.50/0.71     ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.50/0.71  thf('22', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.50/0.71           = (k2_xboole_0 @ X0 @ X1))),
% 0.50/0.71      inference('cnf', [status(esa)], [t6_xboole_1])).
% 0.50/0.71  thf('23', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.71         ((k2_xboole_0 @ (k1_tarski @ X2) @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.50/0.71           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.50/0.71      inference('sup+', [status(thm)], ['21', '22'])).
% 0.50/0.71  thf('24', plain,
% 0.50/0.71      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.50/0.71         ((k2_enumset1 @ X18 @ X19 @ X20 @ X21)
% 0.50/0.71           = (k2_xboole_0 @ (k1_tarski @ X18) @ (k1_enumset1 @ X19 @ X20 @ X21)))),
% 0.50/0.71      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.50/0.71  thf('25', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.71         ((k1_enumset1 @ X2 @ X1 @ X0)
% 0.50/0.71           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.50/0.71      inference('sup+', [status(thm)], ['7', '20'])).
% 0.50/0.71  thf('26', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.71         ((k2_enumset1 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.50/0.71      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.50/0.71  thf('27', plain,
% 0.50/0.71      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.50/0.71         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.50/0.71      inference('demod', [status(thm)], ['0', '26'])).
% 0.50/0.71  thf('28', plain, ($false), inference('simplify', [status(thm)], ['27'])).
% 0.50/0.71  
% 0.50/0.71  % SZS output end Refutation
% 0.50/0.71  
% 0.50/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

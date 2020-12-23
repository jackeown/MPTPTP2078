%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BH84bJ2L4Q

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:32 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   32 (  35 expanded)
%              Number of leaves         :   13 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :  257 ( 288 expanded)
%              Number of equality atoms :   24 (  27 expanded)
%              Maximal formula depth    :   10 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

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
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k2_tarski @ X6 @ X7 ) @ ( k2_tarski @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('2',plain,(
    ( k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t105_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ C @ D @ B ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k2_enumset1 @ X15 @ X18 @ X16 @ X17 )
      = ( k2_enumset1 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('4',plain,(
    ( k2_enumset1 @ sk_B @ sk_C @ sk_A @ sk_A )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t125_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ D @ C @ B @ A ) ) )).

thf('5',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( k2_enumset1 @ X30 @ X29 @ X28 @ X27 )
      = ( k2_enumset1 @ X27 @ X28 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t125_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('6',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ( k2_enumset1 @ X58 @ X58 @ X59 @ X60 )
      = ( k1_enumset1 @ X58 @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ( k1_enumset1 @ sk_A @ sk_C @ sk_B )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['4','7'])).

thf(t107_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ D @ C @ B ) ) )).

thf('9',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( k2_enumset1 @ X19 @ X22 @ X21 @ X20 )
      = ( k2_enumset1 @ X19 @ X20 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf('10',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ( k2_enumset1 @ X58 @ X58 @ X59 @ X60 )
      = ( k1_enumset1 @ X58 @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k2_enumset1 @ X15 @ X18 @ X16 @ X17 )
      = ( k2_enumset1 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('13',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ( k2_enumset1 @ X58 @ X58 @ X59 @ X60 )
      = ( k1_enumset1 @ X58 @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['8','15'])).

thf('17',plain,(
    $false ),
    inference(simplify,[status(thm)],['16'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BH84bJ2L4Q
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:46:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.47/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.70  % Solved by: fo/fo7.sh
% 0.47/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.70  % done 240 iterations in 0.229s
% 0.47/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.70  % SZS output start Refutation
% 0.47/0.70  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.70  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.47/0.70  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.47/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.70  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.47/0.70  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.47/0.70  thf(t137_enumset1, conjecture,
% 0.47/0.70    (![A:$i,B:$i,C:$i]:
% 0.47/0.70     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 0.47/0.70       ( k1_enumset1 @ A @ B @ C ) ))).
% 0.47/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.70    (~( ![A:$i,B:$i,C:$i]:
% 0.47/0.70        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 0.47/0.70          ( k1_enumset1 @ A @ B @ C ) ) )),
% 0.47/0.70    inference('cnf.neg', [status(esa)], [t137_enumset1])).
% 0.47/0.70  thf('0', plain,
% 0.47/0.70      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 0.47/0.70         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf(l53_enumset1, axiom,
% 0.47/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.70     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.47/0.70       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.47/0.70  thf('1', plain,
% 0.47/0.70      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.47/0.70         ((k2_enumset1 @ X6 @ X7 @ X8 @ X9)
% 0.47/0.70           = (k2_xboole_0 @ (k2_tarski @ X6 @ X7) @ (k2_tarski @ X8 @ X9)))),
% 0.47/0.70      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.47/0.70  thf('2', plain,
% 0.47/0.70      (((k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A)
% 0.47/0.70         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.47/0.70      inference('demod', [status(thm)], ['0', '1'])).
% 0.47/0.70  thf(t105_enumset1, axiom,
% 0.47/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.70     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ D @ B ) ))).
% 0.47/0.70  thf('3', plain,
% 0.47/0.70      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.47/0.70         ((k2_enumset1 @ X15 @ X18 @ X16 @ X17)
% 0.47/0.70           = (k2_enumset1 @ X15 @ X16 @ X17 @ X18))),
% 0.47/0.70      inference('cnf', [status(esa)], [t105_enumset1])).
% 0.47/0.70  thf('4', plain,
% 0.47/0.70      (((k2_enumset1 @ sk_B @ sk_C @ sk_A @ sk_A)
% 0.47/0.70         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.47/0.70      inference('demod', [status(thm)], ['2', '3'])).
% 0.47/0.70  thf(t125_enumset1, axiom,
% 0.47/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.70     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ D @ C @ B @ A ) ))).
% 0.47/0.70  thf('5', plain,
% 0.47/0.70      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.47/0.70         ((k2_enumset1 @ X30 @ X29 @ X28 @ X27)
% 0.47/0.70           = (k2_enumset1 @ X27 @ X28 @ X29 @ X30))),
% 0.47/0.70      inference('cnf', [status(esa)], [t125_enumset1])).
% 0.47/0.70  thf(t71_enumset1, axiom,
% 0.47/0.70    (![A:$i,B:$i,C:$i]:
% 0.47/0.70     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.47/0.70  thf('6', plain,
% 0.47/0.70      (![X58 : $i, X59 : $i, X60 : $i]:
% 0.47/0.70         ((k2_enumset1 @ X58 @ X58 @ X59 @ X60)
% 0.47/0.70           = (k1_enumset1 @ X58 @ X59 @ X60))),
% 0.47/0.70      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.47/0.70  thf('7', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.70         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.47/0.70      inference('sup+', [status(thm)], ['5', '6'])).
% 0.47/0.70  thf('8', plain,
% 0.47/0.70      (((k1_enumset1 @ sk_A @ sk_C @ sk_B)
% 0.47/0.70         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.47/0.70      inference('demod', [status(thm)], ['4', '7'])).
% 0.47/0.70  thf(t107_enumset1, axiom,
% 0.47/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.70     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ D @ C @ B ) ))).
% 0.47/0.70  thf('9', plain,
% 0.47/0.70      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.47/0.70         ((k2_enumset1 @ X19 @ X22 @ X21 @ X20)
% 0.47/0.70           = (k2_enumset1 @ X19 @ X20 @ X21 @ X22))),
% 0.47/0.70      inference('cnf', [status(esa)], [t107_enumset1])).
% 0.47/0.70  thf('10', plain,
% 0.47/0.70      (![X58 : $i, X59 : $i, X60 : $i]:
% 0.47/0.70         ((k2_enumset1 @ X58 @ X58 @ X59 @ X60)
% 0.47/0.70           = (k1_enumset1 @ X58 @ X59 @ X60))),
% 0.47/0.70      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.47/0.70  thf('11', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.70         ((k2_enumset1 @ X0 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 0.47/0.70      inference('sup+', [status(thm)], ['9', '10'])).
% 0.47/0.70  thf('12', plain,
% 0.47/0.70      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.47/0.70         ((k2_enumset1 @ X15 @ X18 @ X16 @ X17)
% 0.47/0.70           = (k2_enumset1 @ X15 @ X16 @ X17 @ X18))),
% 0.47/0.70      inference('cnf', [status(esa)], [t105_enumset1])).
% 0.47/0.70  thf('13', plain,
% 0.47/0.70      (![X58 : $i, X59 : $i, X60 : $i]:
% 0.47/0.70         ((k2_enumset1 @ X58 @ X58 @ X59 @ X60)
% 0.47/0.70           = (k1_enumset1 @ X58 @ X59 @ X60))),
% 0.47/0.70      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.47/0.70  thf('14', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.70         ((k2_enumset1 @ X0 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X2 @ X1))),
% 0.47/0.70      inference('sup+', [status(thm)], ['12', '13'])).
% 0.47/0.70  thf('15', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.70         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 0.47/0.70      inference('sup+', [status(thm)], ['11', '14'])).
% 0.47/0.70  thf('16', plain,
% 0.47/0.70      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.47/0.70         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.47/0.70      inference('demod', [status(thm)], ['8', '15'])).
% 0.47/0.70  thf('17', plain, ($false), inference('simplify', [status(thm)], ['16'])).
% 0.47/0.70  
% 0.47/0.70  % SZS output end Refutation
% 0.47/0.70  
% 0.47/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

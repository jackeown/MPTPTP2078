%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZP2dheJuBA

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:22 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   44 (  62 expanded)
%              Number of leaves         :   21 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :  332 ( 499 expanded)
%              Number of equality atoms :   32 (  52 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t39_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) )
      = ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k3_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) )
        = ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t39_mcart_1])).

thf('0',plain,(
    ( k3_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_C ) )
 != ( k1_tarski @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t76_enumset1,axiom,(
    ! [A: $i] :
      ( ( k1_enumset1 @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X18: $i] :
      ( ( k1_enumset1 @ X18 @ X18 @ X18 )
      = ( k1_tarski @ X18 ) ) ),
    inference(cnf,[status(esa)],[t76_enumset1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('4',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X25 ) @ ( k2_tarski @ X26 @ X27 ) )
      = ( k2_tarski @ ( k4_tarski @ X25 @ X26 ) @ ( k4_tarski @ X25 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('8',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k3_zfmisc_1 @ X29 @ X30 @ X31 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) @ X2 )
      = ( k2_zfmisc_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ ( k1_tarski @ X2 ) @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ ( k4_tarski @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ( k1_tarski @ ( k4_tarski @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C ) )
 != ( k1_tarski @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','11'])).

thf(t31_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) @ D ) ) )).

thf('13',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( k4_mcart_1 @ X36 @ X37 @ X38 @ X39 )
      = ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ X36 @ X37 ) @ X38 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[t31_mcart_1])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('14',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X40 @ X41 ) )
      = X40 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ ( k4_tarski @ X3 @ X2 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(d4_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ) )).

thf('16',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k4_mcart_1 @ X32 @ X33 @ X34 @ X35 )
      = ( k4_tarski @ ( k3_mcart_1 @ X32 @ X33 @ X34 ) @ X35 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

thf('17',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X40 @ X41 ) )
      = X40 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( k3_mcart_1 @ X3 @ X2 @ X1 )
      = ( k4_tarski @ ( k4_tarski @ X3 @ X2 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,(
    ( k1_tarski @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) )
 != ( k1_tarski @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['12','19'])).

thf('21',plain,(
    $false ),
    inference(simplify,[status(thm)],['20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZP2dheJuBA
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:39:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 144 iterations in 0.088s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.20/0.54  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.54  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.20/0.54  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.54  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.54  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.54  thf(t39_mcart_1, conjecture,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( k3_zfmisc_1 @
% 0.20/0.54         ( k1_tarski @ A ) @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) ) =
% 0.20/0.54       ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.54        ( ( k3_zfmisc_1 @
% 0.20/0.54            ( k1_tarski @ A ) @ ( k1_tarski @ B ) @ ( k1_tarski @ C ) ) =
% 0.20/0.54          ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t39_mcart_1])).
% 0.20/0.54  thf('0', plain,
% 0.20/0.54      (((k3_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B) @ 
% 0.20/0.54         (k1_tarski @ sk_C)) != (k1_tarski @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(t70_enumset1, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.54  thf('1', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((k1_enumset1 @ X0 @ X0 @ X1) = (k2_tarski @ X0 @ X1))),
% 0.20/0.54      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.54  thf(t76_enumset1, axiom,
% 0.20/0.54    (![A:$i]: ( ( k1_enumset1 @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.54  thf('2', plain,
% 0.20/0.54      (![X18 : $i]: ((k1_enumset1 @ X18 @ X18 @ X18) = (k1_tarski @ X18))),
% 0.20/0.54      inference('cnf', [status(esa)], [t76_enumset1])).
% 0.20/0.54  thf('3', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.54  thf(t36_zfmisc_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 0.20/0.54         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 0.20/0.54       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 0.20/0.54         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 0.20/0.54  thf('4', plain,
% 0.20/0.54      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.54         ((k2_zfmisc_1 @ (k1_tarski @ X25) @ (k2_tarski @ X26 @ X27))
% 0.20/0.54           = (k2_tarski @ (k4_tarski @ X25 @ X26) @ (k4_tarski @ X25 @ X27)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 0.20/0.54  thf('5', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.54  thf('6', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0))
% 0.20/0.54           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['4', '5'])).
% 0.20/0.54  thf('7', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.20/0.54           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['3', '6'])).
% 0.20/0.54  thf(d3_zfmisc_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.20/0.54       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.20/0.54  thf('8', plain,
% 0.20/0.54      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.20/0.54         ((k3_zfmisc_1 @ X29 @ X30 @ X31)
% 0.20/0.54           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30) @ X31))),
% 0.20/0.54      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.54  thf('9', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         ((k3_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0) @ X2)
% 0.20/0.54           = (k2_zfmisc_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)) @ X2))),
% 0.20/0.54      inference('sup+', [status(thm)], ['7', '8'])).
% 0.20/0.54  thf('10', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.20/0.54           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['3', '6'])).
% 0.20/0.54  thf('11', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         ((k3_zfmisc_1 @ (k1_tarski @ X2) @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.20/0.54           = (k1_tarski @ (k4_tarski @ (k4_tarski @ X2 @ X1) @ X0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['9', '10'])).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      (((k1_tarski @ (k4_tarski @ (k4_tarski @ sk_A @ sk_B) @ sk_C))
% 0.20/0.54         != (k1_tarski @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.54      inference('demod', [status(thm)], ['0', '11'])).
% 0.20/0.54  thf(t31_mcart_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.54     ( ( k4_mcart_1 @ A @ B @ C @ D ) =
% 0.20/0.54       ( k4_tarski @ ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) @ D ) ))).
% 0.20/0.54  thf('13', plain,
% 0.20/0.54      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.20/0.54         ((k4_mcart_1 @ X36 @ X37 @ X38 @ X39)
% 0.20/0.54           = (k4_tarski @ (k4_tarski @ (k4_tarski @ X36 @ X37) @ X38) @ X39))),
% 0.20/0.54      inference('cnf', [status(esa)], [t31_mcart_1])).
% 0.20/0.54  thf(t7_mcart_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.20/0.54       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.20/0.54  thf('14', plain,
% 0.20/0.54      (![X40 : $i, X41 : $i]: ((k1_mcart_1 @ (k4_tarski @ X40 @ X41)) = (X40))),
% 0.20/0.54      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.54  thf('15', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.54         ((k1_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.54           = (k4_tarski @ (k4_tarski @ X3 @ X2) @ X1))),
% 0.20/0.54      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.54  thf(d4_mcart_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.54     ( ( k4_mcart_1 @ A @ B @ C @ D ) =
% 0.20/0.54       ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ))).
% 0.20/0.54  thf('16', plain,
% 0.20/0.54      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.20/0.54         ((k4_mcart_1 @ X32 @ X33 @ X34 @ X35)
% 0.20/0.54           = (k4_tarski @ (k3_mcart_1 @ X32 @ X33 @ X34) @ X35))),
% 0.20/0.54      inference('cnf', [status(esa)], [d4_mcart_1])).
% 0.20/0.54  thf('17', plain,
% 0.20/0.54      (![X40 : $i, X41 : $i]: ((k1_mcart_1 @ (k4_tarski @ X40 @ X41)) = (X40))),
% 0.20/0.54      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.54  thf('18', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.54         ((k1_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.54           = (k3_mcart_1 @ X3 @ X2 @ X1))),
% 0.20/0.54      inference('sup+', [status(thm)], ['16', '17'])).
% 0.20/0.54  thf('19', plain,
% 0.20/0.54      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.54         ((k3_mcart_1 @ X3 @ X2 @ X1)
% 0.20/0.54           = (k4_tarski @ (k4_tarski @ X3 @ X2) @ X1))),
% 0.20/0.54      inference('demod', [status(thm)], ['15', '18'])).
% 0.20/0.54  thf('20', plain,
% 0.20/0.54      (((k1_tarski @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C))
% 0.20/0.54         != (k1_tarski @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.54      inference('demod', [status(thm)], ['12', '19'])).
% 0.20/0.54  thf('21', plain, ($false), inference('simplify', [status(thm)], ['20'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

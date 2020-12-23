%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MaiTFG0BBF

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:29 EST 2020

% Result     : Theorem 1.72s
% Output     : Refutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   30 (  30 expanded)
%              Number of leaves         :   19 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :  316 ( 316 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :   22 (  11 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_enumset1_type,type,(
    k7_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_I_type,type,(
    sk_I: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(t134_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I )
      = ( k2_xboole_0 @ ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) @ ( k1_tarski @ I ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
        ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I )
        = ( k2_xboole_0 @ ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) @ ( k1_tarski @ I ) ) ) ),
    inference('cnf.neg',[status(esa)],[t134_enumset1])).

thf('0',plain,(
    ( k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I )
 != ( k2_xboole_0 @ ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H ) @ ( k1_tarski @ sk_I ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t68_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ) )).

thf('1',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( k6_enumset1 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 )
      = ( k2_xboole_0 @ ( k5_enumset1 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 ) @ ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t68_enumset1])).

thf(t62_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k5_enumset1 @ B @ C @ D @ E @ F @ G @ H ) ) ) )).

thf('2',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( k6_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 )
      = ( k2_xboole_0 @ ( k1_tarski @ X29 ) @ ( k5_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t62_enumset1])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X8 )
      = ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ ( k2_xboole_0 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X8 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ ( k6_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X8 ) @ ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t127_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k6_enumset1 @ B @ C @ D @ E @ F @ G @ H @ I ) ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k7_enumset1 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k6_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t127_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ ( k6_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k7_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ( k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I )
 != ( k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('9',plain,(
    $false ),
    inference(simplify,[status(thm)],['8'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MaiTFG0BBF
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:20:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.72/1.98  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.72/1.98  % Solved by: fo/fo7.sh
% 1.72/1.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.72/1.98  % done 2576 iterations in 1.509s
% 1.72/1.98  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.72/1.98  % SZS output start Refutation
% 1.72/1.98  thf(k7_enumset1_type, type, k7_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 1.72/1.98                                           $i > $i > $i).
% 1.72/1.98  thf(sk_A_type, type, sk_A: $i).
% 1.72/1.98  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 1.72/1.98                                           $i > $i).
% 1.72/1.98  thf(sk_B_type, type, sk_B: $i).
% 1.72/1.98  thf(sk_H_type, type, sk_H: $i).
% 1.72/1.98  thf(sk_I_type, type, sk_I: $i).
% 1.72/1.98  thf(sk_E_type, type, sk_E: $i).
% 1.72/1.98  thf(sk_C_type, type, sk_C: $i).
% 1.72/1.98  thf(sk_F_type, type, sk_F: $i).
% 1.72/1.98  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.72/1.98  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.72/1.98  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 1.72/1.98  thf(sk_D_type, type, sk_D: $i).
% 1.72/1.98  thf(sk_G_type, type, sk_G: $i).
% 1.72/1.98  thf(t134_enumset1, conjecture,
% 1.72/1.98    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 1.72/1.98     ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) =
% 1.72/1.98       ( k2_xboole_0 @
% 1.72/1.98         ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) @ ( k1_tarski @ I ) ) ))).
% 1.72/1.98  thf(zf_stmt_0, negated_conjecture,
% 1.72/1.98    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 1.72/1.98        ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) =
% 1.72/1.98          ( k2_xboole_0 @
% 1.72/1.98            ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) @ ( k1_tarski @ I ) ) ) )),
% 1.72/1.98    inference('cnf.neg', [status(esa)], [t134_enumset1])).
% 1.72/1.98  thf('0', plain,
% 1.72/1.98      (((k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ 
% 1.72/1.98         sk_I)
% 1.72/1.98         != (k2_xboole_0 @ 
% 1.72/1.98             (k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ 
% 1.72/1.98              sk_H) @ 
% 1.72/1.98             (k1_tarski @ sk_I)))),
% 1.72/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.98  thf(t68_enumset1, axiom,
% 1.72/1.98    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 1.72/1.98     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 1.72/1.98       ( k2_xboole_0 @
% 1.72/1.98         ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ))).
% 1.72/1.98  thf('1', plain,
% 1.72/1.98      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, 
% 1.72/1.98         X44 : $i]:
% 1.72/1.98         ((k6_enumset1 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44)
% 1.72/1.98           = (k2_xboole_0 @ 
% 1.72/1.98              (k5_enumset1 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43) @ 
% 1.72/1.98              (k1_tarski @ X44)))),
% 1.72/1.98      inference('cnf', [status(esa)], [t68_enumset1])).
% 1.72/1.98  thf(t62_enumset1, axiom,
% 1.72/1.98    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 1.72/1.98     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 1.72/1.98       ( k2_xboole_0 @
% 1.72/1.98         ( k1_tarski @ A ) @ ( k5_enumset1 @ B @ C @ D @ E @ F @ G @ H ) ) ))).
% 1.72/1.98  thf('2', plain,
% 1.72/1.98      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, 
% 1.72/1.98         X36 : $i]:
% 1.72/1.98         ((k6_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36)
% 1.72/1.98           = (k2_xboole_0 @ (k1_tarski @ X29) @ 
% 1.72/1.98              (k5_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36)))),
% 1.72/1.98      inference('cnf', [status(esa)], [t62_enumset1])).
% 1.72/1.98  thf(t4_xboole_1, axiom,
% 1.72/1.98    (![A:$i,B:$i,C:$i]:
% 1.72/1.98     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 1.72/1.98       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.72/1.98  thf('3', plain,
% 1.72/1.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.72/1.98         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 1.72/1.98           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 1.72/1.98      inference('cnf', [status(esa)], [t4_xboole_1])).
% 1.72/1.98  thf('4', plain,
% 1.72/1.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 1.72/1.98         X7 : $i, X8 : $i]:
% 1.72/1.98         ((k2_xboole_0 @ 
% 1.72/1.98           (k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ X8)
% 1.72/1.98           = (k2_xboole_0 @ (k1_tarski @ X7) @ 
% 1.72/1.98              (k2_xboole_0 @ 
% 1.72/1.98               (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ X8)))),
% 1.72/1.98      inference('sup+', [status(thm)], ['2', '3'])).
% 1.72/1.98  thf('5', plain,
% 1.72/1.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 1.72/1.98         X7 : $i, X8 : $i]:
% 1.72/1.98         ((k2_xboole_0 @ 
% 1.72/1.98           (k6_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 1.72/1.98           (k1_tarski @ X0))
% 1.72/1.98           = (k2_xboole_0 @ (k1_tarski @ X8) @ 
% 1.72/1.98              (k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 1.72/1.98      inference('sup+', [status(thm)], ['1', '4'])).
% 1.72/1.98  thf(t127_enumset1, axiom,
% 1.72/1.98    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 1.72/1.98     ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) =
% 1.72/1.98       ( k2_xboole_0 @
% 1.72/1.98         ( k1_tarski @ A ) @ ( k6_enumset1 @ B @ C @ D @ E @ F @ G @ H @ I ) ) ))).
% 1.72/1.98  thf('6', plain,
% 1.72/1.98      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, 
% 1.72/1.98         X12 : $i, X13 : $i]:
% 1.72/1.98         ((k7_enumset1 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13)
% 1.72/1.98           = (k2_xboole_0 @ (k1_tarski @ X5) @ 
% 1.72/1.98              (k6_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13)))),
% 1.72/1.98      inference('cnf', [status(esa)], [t127_enumset1])).
% 1.72/1.98  thf('7', plain,
% 1.72/1.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 1.72/1.98         X7 : $i, X8 : $i]:
% 1.72/1.98         ((k2_xboole_0 @ 
% 1.72/1.98           (k6_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 1.72/1.98           (k1_tarski @ X0))
% 1.72/1.98           = (k7_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 1.72/1.98      inference('demod', [status(thm)], ['5', '6'])).
% 1.72/1.98  thf('8', plain,
% 1.72/1.98      (((k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ 
% 1.72/1.98         sk_I)
% 1.72/1.98         != (k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ 
% 1.72/1.98             sk_H @ sk_I))),
% 1.72/1.98      inference('demod', [status(thm)], ['0', '7'])).
% 1.72/1.98  thf('9', plain, ($false), inference('simplify', [status(thm)], ['8'])).
% 1.72/1.98  
% 1.72/1.98  % SZS output end Refutation
% 1.72/1.98  
% 1.82/1.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

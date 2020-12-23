%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LtazbdeVfd

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:27 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   47 (  53 expanded)
%              Number of leaves         :   24 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :  489 ( 570 expanded)
%              Number of equality atoms :   30 (  36 expanded)
%              Maximal formula depth    :   21 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k7_enumset1_type,type,(
    k7_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_I_type,type,(
    sk_I: $i )).

thf(t129_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k4_enumset1 @ D @ E @ F @ G @ H @ I ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
        ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I )
        = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k4_enumset1 @ D @ E @ F @ G @ H @ I ) ) ) ),
    inference('cnf.neg',[status(esa)],[t129_enumset1])).

thf('0',plain,(
    ( k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I )
 != ( k2_xboole_0 @ ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) @ ( k4_enumset1 @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t51_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k4_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k1_tarski @ X12 ) @ ( k3_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t51_enumset1])).

thf(t84_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_enumset1 @ A @ A @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('2',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( k4_enumset1 @ X33 @ X33 @ X33 @ X33 @ X34 @ X35 )
      = ( k1_enumset1 @ X33 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t84_enumset1])).

thf(t79_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_enumset1 @ A @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('3',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k4_enumset1 @ X29 @ X29 @ X29 @ X30 @ X31 @ X32 )
      = ( k2_enumset1 @ X29 @ X30 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t79_enumset1])).

thf('4',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( k2_enumset1 @ X33 @ X33 @ X34 @ X35 )
      = ( k1_enumset1 @ X33 @ X34 @ X35 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k4_enumset1 @ X29 @ X29 @ X29 @ X30 @ X31 @ X32 )
      = ( k2_enumset1 @ X29 @ X30 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t79_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('6',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k4_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27 @ X28 )
      = ( k3_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('7',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k3_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 )
      = ( k2_enumset1 @ X29 @ X30 @ X31 @ X32 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t55_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ) )).

thf('8',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k4_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 ) @ ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t55_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k4_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27 @ X28 )
      = ( k3_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['4','11'])).

thf('13',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k3_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 )
      = ( k2_enumset1 @ X29 @ X30 @ X31 @ X32 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X8 @ X7 @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X8 @ X7 @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','16'])).

thf(l142_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k3_enumset1 @ E @ F @ G @ H @ I ) ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k7_enumset1 @ X3 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X4 @ X5 @ X6 ) @ ( k3_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l142_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k7_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X8 @ X7 @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ( k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I )
 != ( k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) ),
    inference(demod,[status(thm)],['0','19'])).

thf('21',plain,(
    $false ),
    inference(simplify,[status(thm)],['20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LtazbdeVfd
% 0.13/0.36  % Computer   : n001.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 12:15:30 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.44/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.62  % Solved by: fo/fo7.sh
% 0.44/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.62  % done 121 iterations in 0.143s
% 0.44/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.62  % SZS output start Refutation
% 0.44/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.44/0.62  thf(sk_F_type, type, sk_F: $i).
% 0.44/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.44/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.44/0.62  thf(k7_enumset1_type, type, k7_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.44/0.62                                           $i > $i > $i).
% 0.44/0.62  thf(sk_H_type, type, sk_H: $i).
% 0.44/0.62  thf(sk_G_type, type, sk_G: $i).
% 0.44/0.62  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.44/0.62  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.44/0.62  thf(sk_D_type, type, sk_D: $i).
% 0.44/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.62  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.44/0.62  thf(sk_E_type, type, sk_E: $i).
% 0.44/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.62  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.44/0.62  thf(sk_I_type, type, sk_I: $i).
% 0.44/0.62  thf(t129_enumset1, conjecture,
% 0.44/0.62    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.44/0.62     ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) =
% 0.44/0.62       ( k2_xboole_0 @
% 0.44/0.62         ( k1_enumset1 @ A @ B @ C ) @ ( k4_enumset1 @ D @ E @ F @ G @ H @ I ) ) ))).
% 0.44/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.62    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.44/0.62        ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) =
% 0.44/0.62          ( k2_xboole_0 @
% 0.44/0.62            ( k1_enumset1 @ A @ B @ C ) @ 
% 0.44/0.62            ( k4_enumset1 @ D @ E @ F @ G @ H @ I ) ) ) )),
% 0.44/0.62    inference('cnf.neg', [status(esa)], [t129_enumset1])).
% 0.44/0.62  thf('0', plain,
% 0.44/0.62      (((k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ 
% 0.44/0.62         sk_I)
% 0.44/0.62         != (k2_xboole_0 @ (k1_enumset1 @ sk_A @ sk_B @ sk_C) @ 
% 0.44/0.62             (k4_enumset1 @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(t51_enumset1, axiom,
% 0.44/0.62    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.44/0.62     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.44/0.62       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ))).
% 0.44/0.62  thf('1', plain,
% 0.44/0.62      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.44/0.62         ((k4_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17)
% 0.44/0.62           = (k2_xboole_0 @ (k1_tarski @ X12) @ 
% 0.44/0.62              (k3_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17)))),
% 0.44/0.62      inference('cnf', [status(esa)], [t51_enumset1])).
% 0.44/0.62  thf(t84_enumset1, axiom,
% 0.44/0.62    (![A:$i,B:$i,C:$i]:
% 0.44/0.62     ( ( k4_enumset1 @ A @ A @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.44/0.62  thf('2', plain,
% 0.44/0.62      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.44/0.62         ((k4_enumset1 @ X33 @ X33 @ X33 @ X33 @ X34 @ X35)
% 0.44/0.62           = (k1_enumset1 @ X33 @ X34 @ X35))),
% 0.44/0.62      inference('cnf', [status(esa)], [t84_enumset1])).
% 0.44/0.62  thf(t79_enumset1, axiom,
% 0.44/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.62     ( ( k4_enumset1 @ A @ A @ A @ B @ C @ D ) =
% 0.44/0.62       ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.44/0.62  thf('3', plain,
% 0.44/0.62      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.44/0.62         ((k4_enumset1 @ X29 @ X29 @ X29 @ X30 @ X31 @ X32)
% 0.44/0.62           = (k2_enumset1 @ X29 @ X30 @ X31 @ X32))),
% 0.44/0.62      inference('cnf', [status(esa)], [t79_enumset1])).
% 0.44/0.62  thf('4', plain,
% 0.44/0.62      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.44/0.62         ((k2_enumset1 @ X33 @ X33 @ X34 @ X35)
% 0.44/0.62           = (k1_enumset1 @ X33 @ X34 @ X35))),
% 0.44/0.62      inference('demod', [status(thm)], ['2', '3'])).
% 0.44/0.62  thf('5', plain,
% 0.44/0.62      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.44/0.62         ((k4_enumset1 @ X29 @ X29 @ X29 @ X30 @ X31 @ X32)
% 0.44/0.62           = (k2_enumset1 @ X29 @ X30 @ X31 @ X32))),
% 0.44/0.62      inference('cnf', [status(esa)], [t79_enumset1])).
% 0.44/0.62  thf(t73_enumset1, axiom,
% 0.44/0.62    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.44/0.62     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.44/0.62       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.44/0.62  thf('6', plain,
% 0.44/0.62      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.44/0.62         ((k4_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27 @ X28)
% 0.44/0.62           = (k3_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28))),
% 0.44/0.62      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.44/0.62  thf('7', plain,
% 0.44/0.62      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.44/0.62         ((k3_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32)
% 0.44/0.62           = (k2_enumset1 @ X29 @ X30 @ X31 @ X32))),
% 0.44/0.62      inference('demod', [status(thm)], ['5', '6'])).
% 0.44/0.62  thf(t55_enumset1, axiom,
% 0.44/0.62    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.44/0.62     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.44/0.62       ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ))).
% 0.44/0.62  thf('8', plain,
% 0.44/0.62      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.44/0.62         ((k4_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23)
% 0.44/0.62           = (k2_xboole_0 @ (k3_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22) @ 
% 0.44/0.62              (k1_tarski @ X23)))),
% 0.44/0.62      inference('cnf', [status(esa)], [t55_enumset1])).
% 0.44/0.62  thf('9', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.44/0.62         ((k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4)
% 0.44/0.62           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.44/0.62              (k1_tarski @ X4)))),
% 0.44/0.62      inference('sup+', [status(thm)], ['7', '8'])).
% 0.44/0.62  thf('10', plain,
% 0.44/0.62      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.44/0.62         ((k4_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27 @ X28)
% 0.44/0.62           = (k3_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28))),
% 0.44/0.62      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.44/0.62  thf('11', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.44/0.62         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 0.44/0.62           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.44/0.62              (k1_tarski @ X4)))),
% 0.44/0.62      inference('demod', [status(thm)], ['9', '10'])).
% 0.44/0.62  thf('12', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.44/0.62         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3)
% 0.44/0.62           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 0.44/0.62      inference('sup+', [status(thm)], ['4', '11'])).
% 0.44/0.62  thf('13', plain,
% 0.44/0.62      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.44/0.62         ((k3_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32)
% 0.44/0.62           = (k2_enumset1 @ X29 @ X30 @ X31 @ X32))),
% 0.44/0.62      inference('demod', [status(thm)], ['5', '6'])).
% 0.44/0.62  thf('14', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.44/0.62         ((k2_enumset1 @ X2 @ X1 @ X0 @ X3)
% 0.44/0.62           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 0.44/0.62      inference('demod', [status(thm)], ['12', '13'])).
% 0.44/0.62  thf(t4_xboole_1, axiom,
% 0.44/0.62    (![A:$i,B:$i,C:$i]:
% 0.44/0.62     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.44/0.62       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.44/0.62  thf('15', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.62         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.44/0.62           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.44/0.62      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.44/0.62  thf('16', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.44/0.62         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4)
% 0.44/0.62           = (k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ 
% 0.44/0.62              (k2_xboole_0 @ (k1_tarski @ X0) @ X4)))),
% 0.44/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.44/0.62  thf('17', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 0.44/0.62         X7 : $i, X8 : $i]:
% 0.44/0.62         ((k2_xboole_0 @ (k2_enumset1 @ X8 @ X7 @ X6 @ X5) @ 
% 0.44/0.62           (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.44/0.62           = (k2_xboole_0 @ (k1_enumset1 @ X8 @ X7 @ X6) @ 
% 0.44/0.62              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.44/0.62      inference('sup+', [status(thm)], ['1', '16'])).
% 0.44/0.62  thf(l142_enumset1, axiom,
% 0.44/0.62    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.44/0.62     ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) =
% 0.44/0.62       ( k2_xboole_0 @
% 0.44/0.62         ( k2_enumset1 @ A @ B @ C @ D ) @ ( k3_enumset1 @ E @ F @ G @ H @ I ) ) ))).
% 0.44/0.62  thf('18', plain,
% 0.44/0.62      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, 
% 0.44/0.62         X10 : $i, X11 : $i]:
% 0.44/0.62         ((k7_enumset1 @ X3 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11)
% 0.44/0.62           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X4 @ X5 @ X6) @ 
% 0.44/0.62              (k3_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11)))),
% 0.44/0.62      inference('cnf', [status(esa)], [l142_enumset1])).
% 0.44/0.62  thf('19', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 0.44/0.62         X7 : $i, X8 : $i]:
% 0.44/0.62         ((k7_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.44/0.62           = (k2_xboole_0 @ (k1_enumset1 @ X8 @ X7 @ X6) @ 
% 0.44/0.62              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.44/0.62      inference('demod', [status(thm)], ['17', '18'])).
% 0.44/0.62  thf('20', plain,
% 0.44/0.62      (((k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ 
% 0.44/0.62         sk_I)
% 0.44/0.62         != (k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ 
% 0.44/0.62             sk_H @ sk_I))),
% 0.44/0.62      inference('demod', [status(thm)], ['0', '19'])).
% 0.44/0.62  thf('21', plain, ($false), inference('simplify', [status(thm)], ['20'])).
% 0.44/0.62  
% 0.44/0.62  % SZS output end Refutation
% 0.44/0.62  
% 0.44/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

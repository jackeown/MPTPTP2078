%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pZ9htSPX2l

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:03 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   44 (  63 expanded)
%              Number of leaves         :   19 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :  454 ( 736 expanded)
%              Number of equality atoms :   32 (  51 expanded)
%              Maximal formula depth    :   18 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(t103_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ D @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k2_enumset1 @ A @ B @ C @ D )
        = ( k2_enumset1 @ A @ B @ D @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t103_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_D @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t98_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ A @ C @ B ) ) )).

thf('1',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( k1_enumset1 @ X33 @ X35 @ X34 )
      = ( k1_enumset1 @ X33 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('2',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k6_enumset1 @ X26 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 )
      = ( k5_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('3',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( k5_enumset1 @ X20 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 )
      = ( k4_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k3_enumset1 @ X11 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_enumset1 @ X11 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t66_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_enumset1 @ F @ G @ H ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k6_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 ) @ ( k1_enumset1 @ X5 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t66_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_enumset1 @ X6 @ X5 @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X5 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k2_enumset1 @ X8 @ X8 @ X9 @ X10 )
      = ( k1_enumset1 @ X8 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf('12',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( k1_enumset1 @ X33 @ X35 @ X34 )
      = ( k1_enumset1 @ X33 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X2 @ X0 @ X1 @ X5 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_enumset1 @ X5 @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X3 @ X4 @ X2 @ X0 @ X1 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('16',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k4_enumset1 @ X15 @ X15 @ X16 @ X17 @ X18 @ X19 )
      = ( k3_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('17',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k3_enumset1 @ X11 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_enumset1 @ X11 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','21'])).

thf('23',plain,(
    $false ),
    inference(simplify,[status(thm)],['22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pZ9htSPX2l
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:20:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 0.37/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.56  % Solved by: fo/fo7.sh
% 0.37/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.56  % done 112 iterations in 0.075s
% 0.37/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.56  % SZS output start Refutation
% 0.37/0.56  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.37/0.56                                           $i > $i).
% 0.37/0.56  thf(sk_D_type, type, sk_D: $i).
% 0.37/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.56  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.37/0.56  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.37/0.56  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.37/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.56  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.37/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.56  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.37/0.56  thf(t103_enumset1, conjecture,
% 0.37/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.56     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ D @ C ) ))).
% 0.37/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.56    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.56        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ D @ C ) ) )),
% 0.37/0.56    inference('cnf.neg', [status(esa)], [t103_enumset1])).
% 0.37/0.56  thf('0', plain,
% 0.37/0.56      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.37/0.56         != (k2_enumset1 @ sk_A @ sk_B @ sk_D @ sk_C))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(t98_enumset1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ A @ C @ B ) ))).
% 0.37/0.56  thf('1', plain,
% 0.37/0.56      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.37/0.56         ((k1_enumset1 @ X33 @ X35 @ X34) = (k1_enumset1 @ X33 @ X34 @ X35))),
% 0.37/0.56      inference('cnf', [status(esa)], [t98_enumset1])).
% 0.37/0.56  thf(t75_enumset1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.37/0.56     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.37/0.56       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.37/0.56  thf('2', plain,
% 0.37/0.56      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.37/0.56         ((k6_enumset1 @ X26 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32)
% 0.37/0.56           = (k5_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32))),
% 0.37/0.56      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.37/0.56  thf(t74_enumset1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.37/0.56     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.37/0.56       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.37/0.56  thf('3', plain,
% 0.37/0.56      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.37/0.56         ((k5_enumset1 @ X20 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25)
% 0.37/0.56           = (k4_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25))),
% 0.37/0.56      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.37/0.56  thf('4', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.37/0.56         ((k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.37/0.56           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['2', '3'])).
% 0.37/0.56  thf(t72_enumset1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.56     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.37/0.56  thf('5', plain,
% 0.37/0.56      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.37/0.56         ((k3_enumset1 @ X11 @ X11 @ X12 @ X13 @ X14)
% 0.37/0.56           = (k2_enumset1 @ X11 @ X12 @ X13 @ X14))),
% 0.37/0.56      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.37/0.56  thf(t66_enumset1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.37/0.56     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.37/0.56       ( k2_xboole_0 @
% 0.37/0.56         ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_enumset1 @ F @ G @ H ) ) ))).
% 0.37/0.56  thf('6', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.37/0.56         ((k6_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7)
% 0.37/0.56           = (k2_xboole_0 @ (k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4) @ 
% 0.37/0.56              (k1_enumset1 @ X5 @ X6 @ X7)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t66_enumset1])).
% 0.37/0.56  thf('7', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.37/0.56         ((k6_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4)
% 0.37/0.56           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.37/0.56              (k1_enumset1 @ X6 @ X5 @ X4)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['5', '6'])).
% 0.37/0.56  thf('8', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.37/0.56         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.37/0.56           = (k2_xboole_0 @ (k2_enumset1 @ X5 @ X5 @ X4 @ X3) @ 
% 0.37/0.56              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['4', '7'])).
% 0.37/0.56  thf(t71_enumset1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.37/0.56  thf('9', plain,
% 0.37/0.56      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.37/0.56         ((k2_enumset1 @ X8 @ X8 @ X9 @ X10) = (k1_enumset1 @ X8 @ X9 @ X10))),
% 0.37/0.56      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.37/0.56  thf('10', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.37/0.56         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.37/0.56           = (k2_xboole_0 @ (k1_enumset1 @ X5 @ X4 @ X3) @ 
% 0.37/0.56              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.37/0.56      inference('demod', [status(thm)], ['8', '9'])).
% 0.37/0.56  thf('11', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.37/0.56         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X0 @ X1)
% 0.37/0.56           = (k2_xboole_0 @ (k1_enumset1 @ X5 @ X4 @ X3) @ 
% 0.37/0.56              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['1', '10'])).
% 0.37/0.56  thf('12', plain,
% 0.37/0.56      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.37/0.56         ((k1_enumset1 @ X33 @ X35 @ X34) = (k1_enumset1 @ X33 @ X34 @ X35))),
% 0.37/0.56      inference('cnf', [status(esa)], [t98_enumset1])).
% 0.37/0.56  thf('13', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.37/0.56         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.37/0.56           = (k2_xboole_0 @ (k1_enumset1 @ X5 @ X4 @ X3) @ 
% 0.37/0.56              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.37/0.56      inference('demod', [status(thm)], ['8', '9'])).
% 0.37/0.56  thf('14', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.37/0.56         ((k4_enumset1 @ X2 @ X0 @ X1 @ X5 @ X4 @ X3)
% 0.37/0.56           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 0.37/0.56              (k1_enumset1 @ X5 @ X4 @ X3)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['12', '13'])).
% 0.37/0.56  thf('15', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.37/0.56         ((k4_enumset1 @ X5 @ X3 @ X4 @ X2 @ X0 @ X1)
% 0.37/0.56           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['11', '14'])).
% 0.37/0.56  thf(t73_enumset1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.37/0.56     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.37/0.56       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.37/0.56  thf('16', plain,
% 0.37/0.56      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.56         ((k4_enumset1 @ X15 @ X15 @ X16 @ X17 @ X18 @ X19)
% 0.37/0.56           = (k3_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19))),
% 0.37/0.56      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.37/0.56  thf('17', plain,
% 0.37/0.56      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.37/0.56         ((k3_enumset1 @ X11 @ X11 @ X12 @ X13 @ X14)
% 0.37/0.56           = (k2_enumset1 @ X11 @ X12 @ X13 @ X14))),
% 0.37/0.56      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.37/0.56  thf('18', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.56         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 0.37/0.56           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['16', '17'])).
% 0.37/0.56  thf('19', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.56         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 0.37/0.56           = (k2_enumset1 @ X3 @ X2 @ X0 @ X1))),
% 0.37/0.56      inference('sup+', [status(thm)], ['15', '18'])).
% 0.37/0.56  thf('20', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.56         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 0.37/0.56           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['16', '17'])).
% 0.37/0.56  thf('21', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.56         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X3 @ X2 @ X0 @ X1))),
% 0.37/0.56      inference('sup+', [status(thm)], ['19', '20'])).
% 0.37/0.56  thf('22', plain,
% 0.37/0.56      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.37/0.56         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.37/0.56      inference('demod', [status(thm)], ['0', '21'])).
% 0.37/0.56  thf('23', plain, ($false), inference('simplify', [status(thm)], ['22'])).
% 0.37/0.56  
% 0.37/0.56  % SZS output end Refutation
% 0.37/0.56  
% 0.37/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

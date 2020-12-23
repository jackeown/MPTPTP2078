%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oN14LJnc9Q

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:09 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   53 (  60 expanded)
%              Number of leaves         :   22 (  29 expanded)
%              Depth                    :   12
%              Number of atoms          :  561 ( 640 expanded)
%              Number of equality atoms :   38 (  45 expanded)
%              Maximal formula depth    :   17 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

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

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k2_tarski @ X10 @ X11 ) @ ( k2_tarski @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k2_tarski @ X10 @ X11 ) @ ( k2_tarski @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('6',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( k2_enumset1 @ X26 @ X27 @ X28 @ X29 )
      = ( k2_xboole_0 @ ( k1_tarski @ X26 ) @ ( k1_enumset1 @ X27 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('7',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_tarski @ X21 @ X22 )
      = ( k2_xboole_0 @ ( k1_tarski @ X21 ) @ ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('8',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_tarski @ X21 @ X22 )
      = ( k2_xboole_0 @ ( k1_tarski @ X21 ) @ ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('9',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k1_enumset1 @ X23 @ X24 @ X25 )
      = ( k2_xboole_0 @ ( k1_tarski @ X23 ) @ ( k2_tarski @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','16'])).

thf(t47_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ) )).

thf('18',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( k3_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34 )
      = ( k2_xboole_0 @ ( k1_tarski @ X30 ) @ ( k2_enumset1 @ X31 @ X32 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('19',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X5 )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ ( k2_xboole_0 @ ( k1_enumset1 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( k2_enumset1 @ X26 @ X27 @ X28 @ X29 )
      = ( k2_xboole_0 @ ( k1_tarski @ X26 ) @ ( k1_enumset1 @ X27 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('23',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X6 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf(l68_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_enumset1 @ E @ F @ G ) ) ) )).

thf('26',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k5_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X14 @ X15 @ X16 @ X17 ) @ ( k1_enumset1 @ X18 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[l68_enumset1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ( k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G )
 != ( k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G ) ),
    inference(demod,[status(thm)],['0','27'])).

thf('29',plain,(
    $false ),
    inference(simplify,[status(thm)],['28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oN14LJnc9Q
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:35:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.58  % Solved by: fo/fo7.sh
% 0.20/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.58  % done 54 iterations in 0.095s
% 0.20/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.58  % SZS output start Refutation
% 0.20/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.58  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.20/0.58  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.58  thf(sk_G_type, type, sk_G: $i).
% 0.20/0.58  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.58  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.20/0.58  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.58  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.58  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.20/0.58  thf(t60_enumset1, conjecture,
% 0.20/0.58    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.20/0.58     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.20/0.58       ( k2_xboole_0 @
% 0.20/0.58         ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ))).
% 0.20/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.58    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.20/0.58        ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.20/0.58          ( k2_xboole_0 @
% 0.20/0.58            ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ) )),
% 0.20/0.58    inference('cnf.neg', [status(esa)], [t60_enumset1])).
% 0.20/0.58  thf('0', plain,
% 0.20/0.58      (((k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G)
% 0.20/0.58         != (k2_xboole_0 @ (k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.20/0.58             (k2_tarski @ sk_F @ sk_G)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf(l53_enumset1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.58     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.20/0.58       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.20/0.58  thf('1', plain,
% 0.20/0.58      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.58         ((k2_enumset1 @ X10 @ X11 @ X12 @ X13)
% 0.20/0.58           = (k2_xboole_0 @ (k2_tarski @ X10 @ X11) @ (k2_tarski @ X12 @ X13)))),
% 0.20/0.58      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.20/0.58  thf('2', plain,
% 0.20/0.58      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.58         ((k2_enumset1 @ X10 @ X11 @ X12 @ X13)
% 0.20/0.58           = (k2_xboole_0 @ (k2_tarski @ X10 @ X11) @ (k2_tarski @ X12 @ X13)))),
% 0.20/0.58      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.20/0.58  thf(t4_xboole_1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.58       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.20/0.58  thf('3', plain,
% 0.20/0.58      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.58         ((k2_xboole_0 @ (k2_xboole_0 @ X2 @ X3) @ X4)
% 0.20/0.58           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ X4)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.20/0.58  thf('4', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.58         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4)
% 0.20/0.58           = (k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ 
% 0.20/0.58              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X4)))),
% 0.20/0.58      inference('sup+', [status(thm)], ['2', '3'])).
% 0.20/0.58  thf('5', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.58         ((k2_xboole_0 @ (k2_enumset1 @ X5 @ X4 @ X3 @ X2) @ 
% 0.20/0.58           (k2_tarski @ X1 @ X0))
% 0.20/0.58           = (k2_xboole_0 @ (k2_tarski @ X5 @ X4) @ 
% 0.20/0.58              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 0.20/0.58      inference('sup+', [status(thm)], ['1', '4'])).
% 0.20/0.58  thf(t44_enumset1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.58     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.20/0.58       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 0.20/0.58  thf('6', plain,
% 0.20/0.58      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.58         ((k2_enumset1 @ X26 @ X27 @ X28 @ X29)
% 0.20/0.58           = (k2_xboole_0 @ (k1_tarski @ X26) @ (k1_enumset1 @ X27 @ X28 @ X29)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.20/0.58  thf(t41_enumset1, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( k2_tarski @ A @ B ) =
% 0.20/0.58       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.20/0.58  thf('7', plain,
% 0.20/0.58      (![X21 : $i, X22 : $i]:
% 0.20/0.58         ((k2_tarski @ X21 @ X22)
% 0.20/0.58           = (k2_xboole_0 @ (k1_tarski @ X21) @ (k1_tarski @ X22)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.20/0.58  thf('8', plain,
% 0.20/0.58      (![X21 : $i, X22 : $i]:
% 0.20/0.58         ((k2_tarski @ X21 @ X22)
% 0.20/0.58           = (k2_xboole_0 @ (k1_tarski @ X21) @ (k1_tarski @ X22)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.20/0.58  thf('9', plain,
% 0.20/0.58      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.58         ((k2_xboole_0 @ (k2_xboole_0 @ X2 @ X3) @ X4)
% 0.20/0.58           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ X4)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.20/0.58  thf('10', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.58         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.20/0.58           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.20/0.58              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.20/0.58      inference('sup+', [status(thm)], ['8', '9'])).
% 0.20/0.58  thf('11', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.58         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.20/0.58           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.20/0.58      inference('sup+', [status(thm)], ['7', '10'])).
% 0.20/0.58  thf(t42_enumset1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.20/0.58       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.20/0.58  thf('12', plain,
% 0.20/0.58      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.58         ((k1_enumset1 @ X23 @ X24 @ X25)
% 0.20/0.58           = (k2_xboole_0 @ (k1_tarski @ X23) @ (k2_tarski @ X24 @ X25)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.20/0.58  thf('13', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.58         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.20/0.58           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.20/0.58      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.58  thf('14', plain,
% 0.20/0.58      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.58         ((k2_xboole_0 @ (k2_xboole_0 @ X2 @ X3) @ X4)
% 0.20/0.58           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ X4)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.20/0.58  thf('15', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.58         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.20/0.58           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ 
% 0.20/0.58              (k2_xboole_0 @ (k1_tarski @ X0) @ X3)))),
% 0.20/0.58      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.58  thf('16', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.58         ((k2_xboole_0 @ (k1_enumset1 @ X5 @ X4 @ X3) @ 
% 0.20/0.58           (k1_enumset1 @ X2 @ X1 @ X0))
% 0.20/0.58           = (k2_xboole_0 @ (k2_tarski @ X5 @ X4) @ 
% 0.20/0.58              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 0.20/0.58      inference('sup+', [status(thm)], ['6', '15'])).
% 0.20/0.58  thf('17', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.58         ((k2_xboole_0 @ (k2_enumset1 @ X5 @ X4 @ X3 @ X2) @ 
% 0.20/0.58           (k2_tarski @ X1 @ X0))
% 0.20/0.58           = (k2_xboole_0 @ (k1_enumset1 @ X5 @ X4 @ X3) @ 
% 0.20/0.58              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.20/0.58      inference('demod', [status(thm)], ['5', '16'])).
% 0.20/0.58  thf(t47_enumset1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.58     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.20/0.58       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ))).
% 0.20/0.58  thf('18', plain,
% 0.20/0.58      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.20/0.58         ((k3_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34)
% 0.20/0.58           = (k2_xboole_0 @ (k1_tarski @ X30) @ 
% 0.20/0.58              (k2_enumset1 @ X31 @ X32 @ X33 @ X34)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.20/0.58  thf('19', plain,
% 0.20/0.58      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.58         ((k2_xboole_0 @ (k2_xboole_0 @ X2 @ X3) @ X4)
% 0.20/0.58           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ X4)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.20/0.58  thf('20', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.58         ((k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ X5)
% 0.20/0.58           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 0.20/0.58              (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X5)))),
% 0.20/0.58      inference('sup+', [status(thm)], ['18', '19'])).
% 0.20/0.58  thf('21', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.58         ((k2_xboole_0 @ (k3_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2) @ 
% 0.20/0.58           (k2_tarski @ X1 @ X0))
% 0.20/0.58           = (k2_xboole_0 @ (k1_tarski @ X6) @ 
% 0.20/0.58              (k2_xboole_0 @ (k1_enumset1 @ X5 @ X4 @ X3) @ 
% 0.20/0.58               (k1_enumset1 @ X2 @ X1 @ X0))))),
% 0.20/0.58      inference('sup+', [status(thm)], ['17', '20'])).
% 0.20/0.58  thf('22', plain,
% 0.20/0.58      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.58         ((k2_enumset1 @ X26 @ X27 @ X28 @ X29)
% 0.20/0.58           = (k2_xboole_0 @ (k1_tarski @ X26) @ (k1_enumset1 @ X27 @ X28 @ X29)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.20/0.58  thf('23', plain,
% 0.20/0.58      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.58         ((k2_xboole_0 @ (k2_xboole_0 @ X2 @ X3) @ X4)
% 0.20/0.58           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ X4)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.20/0.58  thf('24', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.58         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4)
% 0.20/0.58           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 0.20/0.58              (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X4)))),
% 0.20/0.58      inference('sup+', [status(thm)], ['22', '23'])).
% 0.20/0.58  thf('25', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.58         ((k2_xboole_0 @ (k3_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2) @ 
% 0.20/0.58           (k2_tarski @ X1 @ X0))
% 0.20/0.58           = (k2_xboole_0 @ (k2_enumset1 @ X6 @ X5 @ X4 @ X3) @ 
% 0.20/0.58              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.20/0.58      inference('demod', [status(thm)], ['21', '24'])).
% 0.20/0.58  thf(l68_enumset1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.20/0.58     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.20/0.58       ( k2_xboole_0 @
% 0.20/0.58         ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_enumset1 @ E @ F @ G ) ) ))).
% 0.20/0.58  thf('26', plain,
% 0.20/0.58      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.58         ((k5_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20)
% 0.20/0.58           = (k2_xboole_0 @ (k2_enumset1 @ X14 @ X15 @ X16 @ X17) @ 
% 0.20/0.58              (k1_enumset1 @ X18 @ X19 @ X20)))),
% 0.20/0.58      inference('cnf', [status(esa)], [l68_enumset1])).
% 0.20/0.58  thf('27', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.58         ((k2_xboole_0 @ (k3_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2) @ 
% 0.20/0.58           (k2_tarski @ X1 @ X0))
% 0.20/0.58           = (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.20/0.58      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.58  thf('28', plain,
% 0.20/0.58      (((k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G)
% 0.20/0.58         != (k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G))),
% 0.20/0.58      inference('demod', [status(thm)], ['0', '27'])).
% 0.20/0.58  thf('29', plain, ($false), inference('simplify', [status(thm)], ['28'])).
% 0.20/0.58  
% 0.20/0.58  % SZS output end Refutation
% 0.20/0.58  
% 0.43/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

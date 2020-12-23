%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pZbcbjtgdU

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:12 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   53 (  60 expanded)
%              Number of leaves         :   26 (  31 expanded)
%              Depth                    :   11
%              Number of atoms          :  552 ( 623 expanded)
%              Number of equality atoms :   35 (  42 expanded)
%              Maximal formula depth    :   19 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t62_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k5_enumset1 @ B @ C @ D @ E @ F @ G @ H ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
        ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
        = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k5_enumset1 @ B @ C @ D @ E @ F @ G @ H ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_enumset1])).

thf('0',plain,(
    ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H )
 != ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_enumset1 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t47_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ) )).

thf('1',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k3_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 )
      = ( k2_xboole_0 @ ( k1_tarski @ X22 ) @ ( k2_enumset1 @ X23 @ X24 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_tarski @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k1_tarski @ X13 ) @ ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_tarski @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k1_tarski @ X13 ) @ ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k1_enumset1 @ X15 @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k1_tarski @ X15 ) @ ( k2_tarski @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X6 @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf(t51_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ) )).

thf('12',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k4_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 )
      = ( k2_xboole_0 @ ( k1_tarski @ X27 ) @ ( k3_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t51_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t56_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k4_enumset1 @ B @ C @ D @ E @ F @ G ) ) ) )).

thf('15',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( k5_enumset1 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 )
      = ( k2_xboole_0 @ ( k1_tarski @ X33 ) @ ( k4_enumset1 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t56_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X6 @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('18',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k2_enumset1 @ X18 @ X19 @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k1_tarski @ X18 ) @ ( k1_enumset1 @ X19 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X7 @ X6 @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf(l75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ) )).

thf('22',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k6_enumset1 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X5 @ X6 @ X7 @ X8 ) @ ( k2_enumset1 @ X9 @ X10 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[l75_enumset1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H )
 != ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['0','23'])).

thf('25',plain,(
    $false ),
    inference(simplify,[status(thm)],['24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pZbcbjtgdU
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:30:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 77 iterations in 0.071s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.52  thf(sk_G_type, type, sk_G: $i).
% 0.20/0.52  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.20/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.20/0.52  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.52  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.52  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.20/0.52                                           $i > $i).
% 0.20/0.52  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.20/0.52  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.52  thf(sk_H_type, type, sk_H: $i).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.52  thf(t62_enumset1, conjecture,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.20/0.52     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.20/0.52       ( k2_xboole_0 @
% 0.20/0.52         ( k1_tarski @ A ) @ ( k5_enumset1 @ B @ C @ D @ E @ F @ G @ H ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.20/0.52        ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.20/0.52          ( k2_xboole_0 @
% 0.20/0.52            ( k1_tarski @ A ) @ ( k5_enumset1 @ B @ C @ D @ E @ F @ G @ H ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t62_enumset1])).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      (((k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.20/0.52         != (k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.20/0.52             (k5_enumset1 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t47_enumset1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.52     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.20/0.52       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ))).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.52         ((k3_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26)
% 0.20/0.52           = (k2_xboole_0 @ (k1_tarski @ X22) @ 
% 0.20/0.52              (k2_enumset1 @ X23 @ X24 @ X25 @ X26)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.20/0.52  thf(t41_enumset1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( k2_tarski @ A @ B ) =
% 0.20/0.52       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (![X13 : $i, X14 : $i]:
% 0.20/0.52         ((k2_tarski @ X13 @ X14)
% 0.20/0.52           = (k2_xboole_0 @ (k1_tarski @ X13) @ (k1_tarski @ X14)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (![X13 : $i, X14 : $i]:
% 0.20/0.52         ((k2_tarski @ X13 @ X14)
% 0.20/0.52           = (k2_xboole_0 @ (k1_tarski @ X13) @ (k1_tarski @ X14)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.20/0.52  thf(t4_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.52       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.20/0.52           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.20/0.52           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.20/0.52              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['3', '4'])).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.20/0.52           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['2', '5'])).
% 0.20/0.52  thf(t42_enumset1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.20/0.52       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.52         ((k1_enumset1 @ X15 @ X16 @ X17)
% 0.20/0.52           = (k2_xboole_0 @ (k1_tarski @ X15) @ (k2_tarski @ X16 @ X17)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.20/0.52           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.20/0.52           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.52         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.20/0.52           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ 
% 0.20/0.52              (k2_xboole_0 @ (k1_tarski @ X0) @ X3)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['8', '9'])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.52         ((k2_xboole_0 @ (k1_enumset1 @ X6 @ X5 @ X4) @ 
% 0.20/0.52           (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.52           = (k2_xboole_0 @ (k2_tarski @ X6 @ X5) @ 
% 0.20/0.52              (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['1', '10'])).
% 0.20/0.52  thf(t51_enumset1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.52     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.20/0.52       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ))).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.20/0.52         ((k4_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32)
% 0.20/0.52           = (k2_xboole_0 @ (k1_tarski @ X27) @ 
% 0.20/0.52              (k3_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t51_enumset1])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.20/0.52           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.20/0.52              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['3', '4'])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.52         ((k2_xboole_0 @ (k2_tarski @ X6 @ X5) @ 
% 0.20/0.52           (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.52           = (k2_xboole_0 @ (k1_tarski @ X6) @ 
% 0.20/0.52              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['12', '13'])).
% 0.20/0.52  thf(t56_enumset1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.20/0.52     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.20/0.52       ( k2_xboole_0 @
% 0.20/0.52         ( k1_tarski @ A ) @ ( k4_enumset1 @ B @ C @ D @ E @ F @ G ) ) ))).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.20/0.52         ((k5_enumset1 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39)
% 0.20/0.52           = (k2_xboole_0 @ (k1_tarski @ X33) @ 
% 0.20/0.52              (k4_enumset1 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t56_enumset1])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.52         ((k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.52           = (k2_xboole_0 @ (k2_tarski @ X6 @ X5) @ 
% 0.20/0.52              (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['14', '15'])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.52         ((k2_xboole_0 @ (k1_enumset1 @ X6 @ X5 @ X4) @ 
% 0.20/0.52           (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.52           = (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['11', '16'])).
% 0.20/0.52  thf(t44_enumset1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.52     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.20/0.52       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.52         ((k2_enumset1 @ X18 @ X19 @ X20 @ X21)
% 0.20/0.52           = (k2_xboole_0 @ (k1_tarski @ X18) @ (k1_enumset1 @ X19 @ X20 @ X21)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.20/0.52           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.52         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4)
% 0.20/0.52           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 0.20/0.52              (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X4)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['18', '19'])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.52         ((k2_xboole_0 @ (k2_enumset1 @ X7 @ X6 @ X5 @ X4) @ 
% 0.20/0.52           (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.52           = (k2_xboole_0 @ (k1_tarski @ X7) @ 
% 0.20/0.52              (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.20/0.52      inference('sup+', [status(thm)], ['17', '20'])).
% 0.20/0.52  thf(l75_enumset1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.20/0.52     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.20/0.52       ( k2_xboole_0 @
% 0.20/0.52         ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ))).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, 
% 0.20/0.52         X12 : $i]:
% 0.20/0.52         ((k6_enumset1 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12)
% 0.20/0.52           = (k2_xboole_0 @ (k2_enumset1 @ X5 @ X6 @ X7 @ X8) @ 
% 0.20/0.52              (k2_enumset1 @ X9 @ X10 @ X11 @ X12)))),
% 0.20/0.52      inference('cnf', [status(esa)], [l75_enumset1])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.52         ((k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.52           = (k2_xboole_0 @ (k1_tarski @ X7) @ 
% 0.20/0.52              (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.20/0.52      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (((k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.20/0.52         != (k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ 
% 0.20/0.52             sk_H))),
% 0.20/0.52      inference('demod', [status(thm)], ['0', '23'])).
% 0.20/0.52  thf('25', plain, ($false), inference('simplify', [status(thm)], ['24'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

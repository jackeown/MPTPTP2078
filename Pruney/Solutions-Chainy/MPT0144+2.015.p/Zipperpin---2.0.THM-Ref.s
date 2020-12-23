%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Psms384GtX

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   54 (  75 expanded)
%              Number of leaves         :   21 (  34 expanded)
%              Depth                    :   13
%              Number of atoms          :  548 ( 779 expanded)
%              Number of equality atoms :   39 (  60 expanded)
%              Maximal formula depth    :   17 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

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

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k1_enumset1 @ X5 @ X6 @ X7 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k2_tarski @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_tarski @ X3 @ X4 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_tarski @ X3 @ X4 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_tarski @ X4 ) ) ) ),
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

thf('7',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k1_enumset1 @ X5 @ X6 @ X7 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k2_tarski @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k1_enumset1 @ X5 @ X6 @ X7 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k2_tarski @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k1_enumset1 @ X5 @ X6 @ X7 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k2_tarski @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t45_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('16',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k2_enumset1 @ X8 @ X9 @ X10 @ X11 )
      = ( k2_xboole_0 @ ( k2_tarski @ X8 @ X9 ) @ ( k2_tarski @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t45_enumset1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf(t47_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ) )).

thf('23',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k3_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k1_tarski @ X12 ) @ ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X5 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X6 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','26'])).

thf(t59_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_enumset1 @ E @ F @ G ) ) ) )).

thf('28',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k5_enumset1 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X36 @ X37 @ X38 @ X39 ) @ ( k1_enumset1 @ X40 @ X41 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t59_enumset1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ( k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G )
 != ( k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G ) ),
    inference(demod,[status(thm)],['0','29'])).

thf('31',plain,(
    $false ),
    inference(simplify,[status(thm)],['30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Psms384GtX
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:39:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 51 iterations in 0.051s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.51  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.51  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.21/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.21/0.51  thf(sk_G_type, type, sk_G: $i).
% 0.21/0.51  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.51  thf(t60_enumset1, conjecture,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.21/0.51     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.21/0.51       ( k2_xboole_0 @
% 0.21/0.51         ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.21/0.51        ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.21/0.51          ( k2_xboole_0 @
% 0.21/0.51            ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t60_enumset1])).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      (((k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G)
% 0.21/0.51         != (k2_xboole_0 @ (k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.21/0.51             (k2_tarski @ sk_F @ sk_G)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t42_enumset1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.21/0.51       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.51         ((k1_enumset1 @ X5 @ X6 @ X7)
% 0.21/0.51           = (k2_xboole_0 @ (k1_tarski @ X5) @ (k2_tarski @ X6 @ X7)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.21/0.51  thf(t41_enumset1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( k2_tarski @ A @ B ) =
% 0.21/0.51       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X3 : $i, X4 : $i]:
% 0.21/0.51         ((k2_tarski @ X3 @ X4)
% 0.21/0.51           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_tarski @ X4)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X3 : $i, X4 : $i]:
% 0.21/0.51         ((k2_tarski @ X3 @ X4)
% 0.21/0.51           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_tarski @ X4)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.21/0.51  thf(t4_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.21/0.51       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.21/0.51           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.21/0.51           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.21/0.51              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['3', '4'])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.21/0.51           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['2', '5'])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.51         ((k1_enumset1 @ X5 @ X6 @ X7)
% 0.21/0.51           = (k2_xboole_0 @ (k1_tarski @ X5) @ (k2_tarski @ X6 @ X7)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.21/0.51           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.51         ((k1_enumset1 @ X5 @ X6 @ X7)
% 0.21/0.51           = (k2_xboole_0 @ (k1_tarski @ X5) @ (k2_tarski @ X6 @ X7)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.21/0.51           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.21/0.51           = (k2_xboole_0 @ (k1_tarski @ X2) @ 
% 0.21/0.51              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X3)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 0.21/0.51           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['8', '11'])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.51         ((k1_enumset1 @ X5 @ X6 @ X7)
% 0.21/0.51           = (k2_xboole_0 @ (k1_tarski @ X5) @ (k2_tarski @ X6 @ X7)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.21/0.51           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.21/0.51              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['3', '4'])).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         ((k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0))
% 0.21/0.51           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['13', '14'])).
% 0.21/0.51  thf(t45_enumset1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.21/0.51       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.51         ((k2_enumset1 @ X8 @ X9 @ X10 @ X11)
% 0.21/0.51           = (k2_xboole_0 @ (k2_tarski @ X8 @ X9) @ (k2_tarski @ X10 @ X11)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t45_enumset1])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 0.21/0.51           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.21/0.51      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 0.21/0.51           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['12', '17'])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 0.21/0.51           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.21/0.51      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.21/0.51           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.51         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4)
% 0.21/0.51           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 0.21/0.51              (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X4)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['19', '20'])).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.51         ((k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 0.21/0.51           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 0.21/0.51              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['18', '21'])).
% 0.21/0.51  thf(t47_enumset1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.51     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.21/0.51       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ))).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.51         ((k3_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16)
% 0.21/0.51           = (k2_xboole_0 @ (k1_tarski @ X12) @ 
% 0.21/0.51              (k2_enumset1 @ X13 @ X14 @ X15 @ X16)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.51         ((k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 0.21/0.51           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.21/0.51           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.51         ((k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ X5)
% 0.21/0.51           = (k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ 
% 0.21/0.51              (k2_xboole_0 @ (k1_tarski @ X0) @ X5)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['24', '25'])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.51         ((k2_xboole_0 @ (k3_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2) @ 
% 0.21/0.51           (k2_tarski @ X1 @ X0))
% 0.21/0.51           = (k2_xboole_0 @ (k2_enumset1 @ X6 @ X5 @ X4 @ X3) @ 
% 0.21/0.51              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['1', '26'])).
% 0.21/0.51  thf(t59_enumset1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.21/0.51     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.21/0.51       ( k2_xboole_0 @
% 0.21/0.51         ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_enumset1 @ E @ F @ G ) ) ))).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.21/0.51         ((k5_enumset1 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42)
% 0.21/0.51           = (k2_xboole_0 @ (k2_enumset1 @ X36 @ X37 @ X38 @ X39) @ 
% 0.21/0.51              (k1_enumset1 @ X40 @ X41 @ X42)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t59_enumset1])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.51         ((k2_xboole_0 @ (k3_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2) @ 
% 0.21/0.51           (k2_tarski @ X1 @ X0))
% 0.21/0.51           = (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      (((k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G)
% 0.21/0.51         != (k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G))),
% 0.21/0.51      inference('demod', [status(thm)], ['0', '29'])).
% 0.21/0.51  thf('31', plain, ($false), inference('simplify', [status(thm)], ['30'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KDWJaErM9N

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   54 (  84 expanded)
%              Number of leaves         :   22 (  38 expanded)
%              Depth                    :   13
%              Number of atoms          :  581 ( 925 expanded)
%              Number of equality atoms :   38 (  68 expanded)
%              Maximal formula depth    :   19 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_H_type,type,(
    sk_H: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(t65_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
        ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
        = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_enumset1])).

thf('0',plain,(
    ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H )
 != ( k2_xboole_0 @ ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k2_enumset1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k2_enumset1 @ X8 @ X9 @ X10 @ X11 )
      = ( k2_xboole_0 @ ( k1_tarski @ X8 ) @ ( k1_enumset1 @ X9 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

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

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

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
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k2_enumset1 @ X8 @ X9 @ X10 @ X11 )
      = ( k2_xboole_0 @ ( k1_tarski @ X8 ) @ ( k1_enumset1 @ X9 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

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
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X6 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X6 @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','16'])).

thf(t58_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_enumset1 @ D @ E @ F @ G ) ) ) )).

thf('18',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k5_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X12 @ X13 @ X14 ) @ ( k2_enumset1 @ X15 @ X16 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t58_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X6 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('21',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k2_enumset1 @ X8 @ X9 @ X10 @ X11 )
      = ( k2_xboole_0 @ ( k1_tarski @ X8 ) @ ( k1_enumset1 @ X9 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X7 @ X6 @ X5 @ X4 ) @ ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k2_enumset1 @ X8 @ X9 @ X10 @ X11 )
      = ( k2_xboole_0 @ ( k1_tarski @ X8 ) @ ( k1_enumset1 @ X9 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf(t62_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k5_enumset1 @ B @ C @ D @ E @ F @ G @ H ) ) ) )).

thf('27',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k6_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 )
      = ( k2_xboole_0 @ ( k1_tarski @ X19 ) @ ( k5_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t62_enumset1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X7 @ X6 @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H )
 != ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['0','28'])).

thf('30',plain,(
    $false ),
    inference(simplify,[status(thm)],['29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KDWJaErM9N
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:32:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 70 iterations in 0.073s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(sk_H_type, type, sk_H: $i).
% 0.20/0.53  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.53  thf(sk_G_type, type, sk_G: $i).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.53  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.53  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.20/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.53  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.20/0.53  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.20/0.53                                           $i > $i).
% 0.20/0.53  thf(t65_enumset1, conjecture,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.20/0.53     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.20/0.53       ( k2_xboole_0 @
% 0.20/0.53         ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.20/0.53        ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.20/0.53          ( k2_xboole_0 @
% 0.20/0.53            ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t65_enumset1])).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      (((k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.20/0.53         != (k2_xboole_0 @ (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.20/0.53             (k2_enumset1 @ sk_E @ sk_F @ sk_G @ sk_H)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t44_enumset1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.53     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.20/0.53       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.53         ((k2_enumset1 @ X8 @ X9 @ X10 @ X11)
% 0.20/0.53           = (k2_xboole_0 @ (k1_tarski @ X8) @ (k1_enumset1 @ X9 @ X10 @ X11)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.20/0.53  thf(t41_enumset1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( k2_tarski @ A @ B ) =
% 0.20/0.53       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (![X3 : $i, X4 : $i]:
% 0.20/0.53         ((k2_tarski @ X3 @ X4)
% 0.20/0.53           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_tarski @ X4)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X3 : $i, X4 : $i]:
% 0.20/0.53         ((k2_tarski @ X3 @ X4)
% 0.20/0.53           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_tarski @ X4)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.20/0.53  thf(t4_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.53       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.20/0.53           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.20/0.53           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.20/0.53              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['3', '4'])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.20/0.53           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['2', '5'])).
% 0.20/0.53  thf(t42_enumset1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.20/0.53       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.53         ((k1_enumset1 @ X5 @ X6 @ X7)
% 0.20/0.53           = (k2_xboole_0 @ (k1_tarski @ X5) @ (k2_tarski @ X6 @ X7)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.20/0.53           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.20/0.53      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.53         ((k1_enumset1 @ X5 @ X6 @ X7)
% 0.20/0.53           = (k2_xboole_0 @ (k1_tarski @ X5) @ (k2_tarski @ X6 @ X7)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.20/0.53           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.20/0.53           = (k2_xboole_0 @ (k1_tarski @ X2) @ 
% 0.20/0.53              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X3)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['9', '10'])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 0.20/0.53           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['8', '11'])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.53         ((k2_enumset1 @ X8 @ X9 @ X10 @ X11)
% 0.20/0.53           = (k2_xboole_0 @ (k1_tarski @ X8) @ (k1_enumset1 @ X9 @ X10 @ X11)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 0.20/0.53           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.20/0.53      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.20/0.53           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4)
% 0.20/0.53           = (k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ 
% 0.20/0.53              (k2_xboole_0 @ (k1_tarski @ X0) @ X4)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['14', '15'])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ (k2_enumset1 @ X6 @ X5 @ X4 @ X3) @ 
% 0.20/0.53           (k1_enumset1 @ X2 @ X1 @ X0))
% 0.20/0.53           = (k2_xboole_0 @ (k1_enumset1 @ X6 @ X5 @ X4) @ 
% 0.20/0.53              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['1', '16'])).
% 0.20/0.53  thf(t58_enumset1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.20/0.53     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.20/0.53       ( k2_xboole_0 @
% 0.20/0.53         ( k1_enumset1 @ A @ B @ C ) @ ( k2_enumset1 @ D @ E @ F @ G ) ) ))).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.53         ((k5_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18)
% 0.20/0.53           = (k2_xboole_0 @ (k1_enumset1 @ X12 @ X13 @ X14) @ 
% 0.20/0.53              (k2_enumset1 @ X15 @ X16 @ X17 @ X18)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t58_enumset1])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ (k2_enumset1 @ X6 @ X5 @ X4 @ X3) @ 
% 0.20/0.53           (k1_enumset1 @ X2 @ X1 @ X0))
% 0.20/0.53           = (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.20/0.53      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4)
% 0.20/0.53           = (k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ 
% 0.20/0.53              (k2_xboole_0 @ (k1_tarski @ X0) @ X4)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['14', '15'])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.53         ((k2_enumset1 @ X8 @ X9 @ X10 @ X11)
% 0.20/0.53           = (k2_xboole_0 @ (k1_tarski @ X8) @ (k1_enumset1 @ X9 @ X10 @ X11)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.20/0.53           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4)
% 0.20/0.53           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 0.20/0.53              (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X4)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['21', '22'])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ (k2_enumset1 @ X5 @ X4 @ X3 @ X2) @ 
% 0.20/0.53           (k2_xboole_0 @ (k1_tarski @ X1) @ X0))
% 0.20/0.53           = (k2_xboole_0 @ (k1_tarski @ X5) @ 
% 0.20/0.53              (k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ X0)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['20', '23'])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ (k2_enumset1 @ X7 @ X6 @ X5 @ X4) @ 
% 0.20/0.53           (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))
% 0.20/0.53           = (k2_xboole_0 @ (k1_tarski @ X7) @ 
% 0.20/0.53              (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['19', '24'])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.53         ((k2_enumset1 @ X8 @ X9 @ X10 @ X11)
% 0.20/0.53           = (k2_xboole_0 @ (k1_tarski @ X8) @ (k1_enumset1 @ X9 @ X10 @ X11)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.20/0.53  thf(t62_enumset1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.20/0.53     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.20/0.53       ( k2_xboole_0 @
% 0.20/0.53         ( k1_tarski @ A ) @ ( k5_enumset1 @ B @ C @ D @ E @ F @ G @ H ) ) ))).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, 
% 0.20/0.53         X26 : $i]:
% 0.20/0.53         ((k6_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26)
% 0.20/0.53           = (k2_xboole_0 @ (k1_tarski @ X19) @ 
% 0.20/0.53              (k5_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t62_enumset1])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ (k2_enumset1 @ X7 @ X6 @ X5 @ X4) @ 
% 0.20/0.53           (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.53           = (k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.20/0.53      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      (((k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.20/0.53         != (k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ 
% 0.20/0.53             sk_H))),
% 0.20/0.53      inference('demod', [status(thm)], ['0', '28'])).
% 0.20/0.53  thf('30', plain, ($false), inference('simplify', [status(thm)], ['29'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

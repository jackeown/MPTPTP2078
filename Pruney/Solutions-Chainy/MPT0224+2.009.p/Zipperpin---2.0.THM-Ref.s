%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Xe1KtPegBQ

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:44 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   61 (  64 expanded)
%              Number of leaves         :   28 (  31 expanded)
%              Depth                    :   13
%              Number of atoms          :  465 ( 486 expanded)
%              Number of equality atoms :   45 (  48 expanded)
%              Maximal formula depth    :   19 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t19_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k1_tarski @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
        = ( k1_tarski @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t19_zfmisc_1])).

thf('0',plain,(
    ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k1_enumset1 @ X23 @ X23 @ X24 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('2',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k3_enumset1 @ X28 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_enumset1 @ X28 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('3',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k2_enumset1 @ X25 @ X25 @ X26 @ X27 )
      = ( k1_enumset1 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k1_enumset1 @ X23 @ X23 @ X24 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('6',plain,(
    ! [X22: $i] :
      ( ( k2_tarski @ X22 @ X22 )
      = ( k1_tarski @ X22 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('8',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( k6_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 )
      = ( k5_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('9',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k5_enumset1 @ X37 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 )
      = ( k4_enumset1 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(l75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ) )).

thf('11',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k6_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X14 @ X15 @ X16 @ X17 ) @ ( k2_enumset1 @ X18 @ X19 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[l75_enumset1])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ ( k2_xboole_0 @ X3 @ X4 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('13',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('14',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ ( k2_xboole_0 @ X3 @ X4 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k2_enumset1 @ X7 @ X6 @ X5 @ X4 ) @ ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ ( k2_enumset1 @ X5 @ X5 @ X5 @ X4 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k2_enumset1 @ X25 @ X25 @ X26 @ X27 )
      = ( k1_enumset1 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ ( k1_enumset1 @ X5 @ X5 @ X4 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k4_enumset1 @ X0 @ X0 @ X4 @ X3 @ X2 @ X1 ) )
      = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','18'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('20',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( k4_enumset1 @ X32 @ X32 @ X33 @ X34 @ X35 @ X36 )
      = ( k3_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k3_enumset1 @ X0 @ X4 @ X3 @ X2 @ X1 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X2 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['4','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','22'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ o_0_0_xboole_0 )
      = ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('27',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ o_0_0_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_tarski @ X1 )
      = ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['0','29'])).

thf('31',plain,(
    $false ),
    inference(simplify,[status(thm)],['30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Xe1KtPegBQ
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:13:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.59/0.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.77  % Solved by: fo/fo7.sh
% 0.59/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.77  % done 453 iterations in 0.328s
% 0.59/0.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.77  % SZS output start Refutation
% 0.59/0.77  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.59/0.77  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.59/0.77  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.59/0.77  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.59/0.77  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.59/0.77  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.59/0.77  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.59/0.77  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.59/0.77  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.59/0.77  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.59/0.77                                           $i > $i).
% 0.59/0.77  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.59/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.77  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.77  thf(t19_zfmisc_1, conjecture,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.59/0.77       ( k1_tarski @ A ) ))).
% 0.59/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.77    (~( ![A:$i,B:$i]:
% 0.59/0.77        ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.59/0.77          ( k1_tarski @ A ) ) )),
% 0.59/0.77    inference('cnf.neg', [status(esa)], [t19_zfmisc_1])).
% 0.59/0.77  thf('0', plain,
% 0.59/0.77      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_A @ sk_B))
% 0.59/0.77         != (k1_tarski @ sk_A))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf(t70_enumset1, axiom,
% 0.59/0.77    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.59/0.77  thf('1', plain,
% 0.59/0.77      (![X23 : $i, X24 : $i]:
% 0.59/0.77         ((k1_enumset1 @ X23 @ X23 @ X24) = (k2_tarski @ X23 @ X24))),
% 0.59/0.77      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.59/0.77  thf(t72_enumset1, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.77     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.59/0.77  thf('2', plain,
% 0.59/0.77      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.59/0.77         ((k3_enumset1 @ X28 @ X28 @ X29 @ X30 @ X31)
% 0.59/0.77           = (k2_enumset1 @ X28 @ X29 @ X30 @ X31))),
% 0.59/0.77      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.59/0.77  thf(t71_enumset1, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.59/0.77  thf('3', plain,
% 0.59/0.77      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.59/0.77         ((k2_enumset1 @ X25 @ X25 @ X26 @ X27)
% 0.59/0.77           = (k1_enumset1 @ X25 @ X26 @ X27))),
% 0.59/0.77      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.59/0.77  thf('4', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['2', '3'])).
% 0.59/0.77  thf('5', plain,
% 0.59/0.77      (![X23 : $i, X24 : $i]:
% 0.59/0.77         ((k1_enumset1 @ X23 @ X23 @ X24) = (k2_tarski @ X23 @ X24))),
% 0.59/0.77      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.59/0.77  thf(t69_enumset1, axiom,
% 0.59/0.77    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.59/0.77  thf('6', plain, (![X22 : $i]: ((k2_tarski @ X22 @ X22) = (k1_tarski @ X22))),
% 0.59/0.77      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.59/0.77  thf('7', plain,
% 0.59/0.77      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['5', '6'])).
% 0.59/0.77  thf(t75_enumset1, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.59/0.77     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.59/0.77       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.59/0.77  thf('8', plain,
% 0.59/0.77      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.59/0.77         ((k6_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49)
% 0.59/0.77           = (k5_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 @ X49))),
% 0.59/0.77      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.59/0.77  thf(t74_enumset1, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.59/0.77     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.59/0.77       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.59/0.77  thf('9', plain,
% 0.59/0.77      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.59/0.77         ((k5_enumset1 @ X37 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42)
% 0.59/0.77           = (k4_enumset1 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42))),
% 0.59/0.77      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.59/0.77  thf('10', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.59/0.77         ((k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.59/0.77           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['8', '9'])).
% 0.59/0.77  thf(l75_enumset1, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.59/0.77     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.59/0.77       ( k2_xboole_0 @
% 0.59/0.77         ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ))).
% 0.59/0.77  thf('11', plain,
% 0.59/0.77      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, 
% 0.59/0.77         X21 : $i]:
% 0.59/0.77         ((k6_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21)
% 0.59/0.77           = (k2_xboole_0 @ (k2_enumset1 @ X14 @ X15 @ X16 @ X17) @ 
% 0.59/0.77              (k2_enumset1 @ X18 @ X19 @ X20 @ X21)))),
% 0.59/0.77      inference('cnf', [status(esa)], [l75_enumset1])).
% 0.59/0.77  thf(t46_xboole_1, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.59/0.77  thf('12', plain,
% 0.59/0.77      (![X3 : $i, X4 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ X3 @ (k2_xboole_0 @ X3 @ X4)) = (k1_xboole_0))),
% 0.59/0.77      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.59/0.77  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.59/0.77  thf('13', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.59/0.77      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.59/0.77  thf('14', plain,
% 0.59/0.77      (![X3 : $i, X4 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ X3 @ (k2_xboole_0 @ X3 @ X4)) = (o_0_0_xboole_0))),
% 0.59/0.77      inference('demod', [status(thm)], ['12', '13'])).
% 0.59/0.77  thf('15', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ (k2_enumset1 @ X7 @ X6 @ X5 @ X4) @ 
% 0.59/0.77           (k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.59/0.77           = (o_0_0_xboole_0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['11', '14'])).
% 0.59/0.77  thf('16', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ (k2_enumset1 @ X5 @ X5 @ X5 @ X4) @ 
% 0.59/0.77           (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)) = (o_0_0_xboole_0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['10', '15'])).
% 0.59/0.77  thf('17', plain,
% 0.59/0.77      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.59/0.77         ((k2_enumset1 @ X25 @ X25 @ X26 @ X27)
% 0.59/0.77           = (k1_enumset1 @ X25 @ X26 @ X27))),
% 0.59/0.77      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.59/0.77  thf('18', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ (k1_enumset1 @ X5 @ X5 @ X4) @ 
% 0.59/0.77           (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)) = (o_0_0_xboole_0))),
% 0.59/0.77      inference('demod', [status(thm)], ['16', '17'])).
% 0.59/0.77  thf('19', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ (k1_tarski @ X0) @ 
% 0.59/0.77           (k4_enumset1 @ X0 @ X0 @ X4 @ X3 @ X2 @ X1)) = (o_0_0_xboole_0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['7', '18'])).
% 0.59/0.77  thf(t73_enumset1, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.59/0.77     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.59/0.77       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.59/0.77  thf('20', plain,
% 0.59/0.77      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.59/0.77         ((k4_enumset1 @ X32 @ X32 @ X33 @ X34 @ X35 @ X36)
% 0.59/0.77           = (k3_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36))),
% 0.59/0.77      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.59/0.77  thf('21', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ (k1_tarski @ X0) @ 
% 0.59/0.77           (k3_enumset1 @ X0 @ X4 @ X3 @ X2 @ X1)) = (o_0_0_xboole_0))),
% 0.59/0.77      inference('demod', [status(thm)], ['19', '20'])).
% 0.59/0.77  thf('22', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ (k1_tarski @ X2) @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.59/0.77           = (o_0_0_xboole_0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['4', '21'])).
% 0.59/0.77  thf('23', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.59/0.77           = (o_0_0_xboole_0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['1', '22'])).
% 0.59/0.77  thf(t48_xboole_1, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.59/0.77  thf('24', plain,
% 0.59/0.77      (![X5 : $i, X6 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ X5 @ (k4_xboole_0 @ X5 @ X6))
% 0.59/0.77           = (k3_xboole_0 @ X5 @ X6))),
% 0.59/0.77      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.59/0.77  thf('25', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k4_xboole_0 @ (k1_tarski @ X1) @ o_0_0_xboole_0)
% 0.59/0.77           = (k3_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0)))),
% 0.59/0.77      inference('sup+', [status(thm)], ['23', '24'])).
% 0.59/0.77  thf(t3_boole, axiom,
% 0.59/0.77    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.59/0.77  thf('26', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.59/0.77      inference('cnf', [status(esa)], [t3_boole])).
% 0.59/0.77  thf('27', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.59/0.77      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.59/0.77  thf('28', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ o_0_0_xboole_0) = (X0))),
% 0.59/0.77      inference('demod', [status(thm)], ['26', '27'])).
% 0.59/0.77  thf('29', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         ((k1_tarski @ X1)
% 0.59/0.77           = (k3_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0)))),
% 0.59/0.77      inference('demod', [status(thm)], ['25', '28'])).
% 0.59/0.77  thf('30', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 0.59/0.77      inference('demod', [status(thm)], ['0', '29'])).
% 0.59/0.77  thf('31', plain, ($false), inference('simplify', [status(thm)], ['30'])).
% 0.59/0.77  
% 0.59/0.77  % SZS output end Refutation
% 0.59/0.77  
% 0.59/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

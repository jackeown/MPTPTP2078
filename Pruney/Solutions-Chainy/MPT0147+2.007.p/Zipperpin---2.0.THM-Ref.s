%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Bwb998a1fW

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:13 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   52 (  70 expanded)
%              Number of leaves         :   24 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :  540 ( 732 expanded)
%              Number of equality atoms :   35 (  53 expanded)
%              Maximal formula depth    :   19 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t63_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k4_enumset1 @ C @ D @ E @ F @ G @ H ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
        ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
        = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k4_enumset1 @ C @ D @ E @ F @ G @ H ) ) ) ),
    inference('cnf.neg',[status(esa)],[t63_enumset1])).

thf('0',plain,(
    ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H )
 != ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k4_enumset1 @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t51_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ) )).

thf('1',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( k4_enumset1 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 )
      = ( k2_xboole_0 @ ( k1_tarski @ X34 ) @ ( k3_enumset1 @ X35 @ X36 @ X37 @ X38 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t51_enumset1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_tarski @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k1_tarski @ X20 ) @ ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('3',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_tarski @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k1_tarski @ X20 ) @ ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k2_xboole_0 @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k1_enumset1 @ X22 @ X23 @ X24 )
      = ( k2_xboole_0 @ ( k1_tarski @ X22 ) @ ( k2_tarski @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k2_xboole_0 @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X7 @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X7 @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf('12',plain,(
    ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H )
 != ( k2_xboole_0 @ ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) @ ( k3_enumset1 @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(demod,[status(thm)],['0','11'])).

thf(t47_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ) )).

thf('13',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( k3_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 )
      = ( k2_xboole_0 @ ( k1_tarski @ X29 ) @ ( k2_enumset1 @ X30 @ X31 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X6 @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('16',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k2_enumset1 @ X25 @ X26 @ X27 @ X28 )
      = ( k2_xboole_0 @ ( k1_tarski @ X25 ) @ ( k1_enumset1 @ X26 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('17',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k2_xboole_0 @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X7 @ X6 @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ ( k2_xboole_0 @ ( k2_tarski @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf(l75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ) )).

thf('20',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k6_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X12 @ X13 @ X14 @ X15 ) @ ( k2_enumset1 @ X16 @ X17 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[l75_enumset1])).

thf('21',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k1_enumset1 @ X22 @ X23 @ X24 )
      = ( k2_xboole_0 @ ( k1_tarski @ X22 ) @ ( k2_tarski @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('22',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k2_xboole_0 @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X7 @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20','23'])).

thf('25',plain,(
    ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H )
 != ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['12','24'])).

thf('26',plain,(
    $false ),
    inference(simplify,[status(thm)],['25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Bwb998a1fW
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:22:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.45/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.63  % Solved by: fo/fo7.sh
% 0.45/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.63  % done 165 iterations in 0.181s
% 0.45/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.63  % SZS output start Refutation
% 0.45/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.63  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.63  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.45/0.63  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.45/0.63  thf(sk_H_type, type, sk_H: $i).
% 0.45/0.63  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.45/0.63  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.63  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.45/0.63  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.45/0.63                                           $i > $i).
% 0.45/0.63  thf(sk_F_type, type, sk_F: $i).
% 0.45/0.63  thf(sk_G_type, type, sk_G: $i).
% 0.45/0.63  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.63  thf(sk_E_type, type, sk_E: $i).
% 0.45/0.63  thf(sk_D_type, type, sk_D: $i).
% 0.45/0.63  thf(t63_enumset1, conjecture,
% 0.45/0.63    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.45/0.63     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.45/0.63       ( k2_xboole_0 @
% 0.45/0.63         ( k2_tarski @ A @ B ) @ ( k4_enumset1 @ C @ D @ E @ F @ G @ H ) ) ))).
% 0.45/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.63    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.45/0.63        ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.45/0.63          ( k2_xboole_0 @
% 0.45/0.63            ( k2_tarski @ A @ B ) @ ( k4_enumset1 @ C @ D @ E @ F @ G @ H ) ) ) )),
% 0.45/0.63    inference('cnf.neg', [status(esa)], [t63_enumset1])).
% 0.45/0.63  thf('0', plain,
% 0.45/0.63      (((k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.45/0.63         != (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 0.45/0.63             (k4_enumset1 @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(t51_enumset1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.45/0.63     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.45/0.63       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ))).
% 0.45/0.63  thf('1', plain,
% 0.45/0.63      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.45/0.63         ((k4_enumset1 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39)
% 0.45/0.63           = (k2_xboole_0 @ (k1_tarski @ X34) @ 
% 0.45/0.63              (k3_enumset1 @ X35 @ X36 @ X37 @ X38 @ X39)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t51_enumset1])).
% 0.45/0.63  thf(t41_enumset1, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( k2_tarski @ A @ B ) =
% 0.45/0.63       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.45/0.63  thf('2', plain,
% 0.45/0.63      (![X20 : $i, X21 : $i]:
% 0.45/0.63         ((k2_tarski @ X20 @ X21)
% 0.45/0.63           = (k2_xboole_0 @ (k1_tarski @ X20) @ (k1_tarski @ X21)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.45/0.63  thf('3', plain,
% 0.45/0.63      (![X20 : $i, X21 : $i]:
% 0.45/0.63         ((k2_tarski @ X20 @ X21)
% 0.45/0.63           = (k2_xboole_0 @ (k1_tarski @ X20) @ (k1_tarski @ X21)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.45/0.63  thf(t4_xboole_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.45/0.63       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.45/0.63  thf('4', plain,
% 0.45/0.63      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.45/0.63         ((k2_xboole_0 @ (k2_xboole_0 @ X7 @ X8) @ X9)
% 0.45/0.63           = (k2_xboole_0 @ X7 @ (k2_xboole_0 @ X8 @ X9)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.45/0.63  thf('5', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.63         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.45/0.63           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.45/0.63              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.45/0.63      inference('sup+', [status(thm)], ['3', '4'])).
% 0.45/0.63  thf('6', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.63         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.45/0.63           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.45/0.63      inference('sup+', [status(thm)], ['2', '5'])).
% 0.45/0.63  thf(t42_enumset1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.45/0.63       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.45/0.63  thf('7', plain,
% 0.45/0.63      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.45/0.63         ((k1_enumset1 @ X22 @ X23 @ X24)
% 0.45/0.63           = (k2_xboole_0 @ (k1_tarski @ X22) @ (k2_tarski @ X23 @ X24)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.45/0.63  thf('8', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.63         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.45/0.63           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.45/0.63      inference('demod', [status(thm)], ['6', '7'])).
% 0.45/0.63  thf('9', plain,
% 0.45/0.63      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.45/0.63         ((k2_xboole_0 @ (k2_xboole_0 @ X7 @ X8) @ X9)
% 0.45/0.63           = (k2_xboole_0 @ X7 @ (k2_xboole_0 @ X8 @ X9)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.45/0.63  thf('10', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.63         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.45/0.63           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ 
% 0.45/0.63              (k2_xboole_0 @ (k1_tarski @ X0) @ X3)))),
% 0.45/0.63      inference('sup+', [status(thm)], ['8', '9'])).
% 0.45/0.63  thf('11', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.63         ((k2_xboole_0 @ (k1_enumset1 @ X7 @ X6 @ X5) @ 
% 0.45/0.63           (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.45/0.63           = (k2_xboole_0 @ (k2_tarski @ X7 @ X6) @ 
% 0.45/0.63              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.45/0.63      inference('sup+', [status(thm)], ['1', '10'])).
% 0.45/0.63  thf('12', plain,
% 0.45/0.63      (((k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.45/0.63         != (k2_xboole_0 @ (k1_enumset1 @ sk_A @ sk_B @ sk_C) @ 
% 0.45/0.63             (k3_enumset1 @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)))),
% 0.45/0.63      inference('demod', [status(thm)], ['0', '11'])).
% 0.45/0.63  thf(t47_enumset1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.45/0.63     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.45/0.63       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ))).
% 0.45/0.63  thf('13', plain,
% 0.45/0.63      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.45/0.63         ((k3_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33)
% 0.45/0.63           = (k2_xboole_0 @ (k1_tarski @ X29) @ 
% 0.45/0.63              (k2_enumset1 @ X30 @ X31 @ X32 @ X33)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.45/0.63  thf('14', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.63         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.45/0.63           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ 
% 0.45/0.63              (k2_xboole_0 @ (k1_tarski @ X0) @ X3)))),
% 0.45/0.63      inference('sup+', [status(thm)], ['8', '9'])).
% 0.45/0.63  thf('15', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.45/0.63         ((k2_xboole_0 @ (k1_enumset1 @ X6 @ X5 @ X4) @ 
% 0.45/0.63           (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.45/0.63           = (k2_xboole_0 @ (k2_tarski @ X6 @ X5) @ 
% 0.45/0.63              (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.45/0.63      inference('sup+', [status(thm)], ['13', '14'])).
% 0.45/0.63  thf(t44_enumset1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.63     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.45/0.63       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 0.45/0.63  thf('16', plain,
% 0.45/0.63      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.45/0.63         ((k2_enumset1 @ X25 @ X26 @ X27 @ X28)
% 0.45/0.63           = (k2_xboole_0 @ (k1_tarski @ X25) @ (k1_enumset1 @ X26 @ X27 @ X28)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.45/0.63  thf('17', plain,
% 0.45/0.63      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.45/0.63         ((k2_xboole_0 @ (k2_xboole_0 @ X7 @ X8) @ X9)
% 0.45/0.63           = (k2_xboole_0 @ X7 @ (k2_xboole_0 @ X8 @ X9)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.45/0.63  thf('18', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.45/0.63         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4)
% 0.45/0.63           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 0.45/0.63              (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X4)))),
% 0.45/0.63      inference('sup+', [status(thm)], ['16', '17'])).
% 0.45/0.63  thf('19', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.63         ((k2_xboole_0 @ (k2_enumset1 @ X7 @ X6 @ X5 @ X4) @ 
% 0.45/0.63           (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.45/0.63           = (k2_xboole_0 @ (k1_tarski @ X7) @ 
% 0.45/0.63              (k2_xboole_0 @ (k2_tarski @ X6 @ X5) @ 
% 0.45/0.63               (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))))),
% 0.45/0.63      inference('sup+', [status(thm)], ['15', '18'])).
% 0.45/0.63  thf(l75_enumset1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.45/0.63     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.45/0.63       ( k2_xboole_0 @
% 0.45/0.63         ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ))).
% 0.45/0.63  thf('20', plain,
% 0.45/0.63      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, 
% 0.45/0.63         X19 : $i]:
% 0.45/0.63         ((k6_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19)
% 0.45/0.63           = (k2_xboole_0 @ (k2_enumset1 @ X12 @ X13 @ X14 @ X15) @ 
% 0.45/0.63              (k2_enumset1 @ X16 @ X17 @ X18 @ X19)))),
% 0.45/0.63      inference('cnf', [status(esa)], [l75_enumset1])).
% 0.45/0.63  thf('21', plain,
% 0.45/0.63      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.45/0.63         ((k1_enumset1 @ X22 @ X23 @ X24)
% 0.45/0.63           = (k2_xboole_0 @ (k1_tarski @ X22) @ (k2_tarski @ X23 @ X24)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.45/0.63  thf('22', plain,
% 0.45/0.63      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.45/0.63         ((k2_xboole_0 @ (k2_xboole_0 @ X7 @ X8) @ X9)
% 0.45/0.63           = (k2_xboole_0 @ X7 @ (k2_xboole_0 @ X8 @ X9)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.45/0.63  thf('23', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.63         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.45/0.63           = (k2_xboole_0 @ (k1_tarski @ X2) @ 
% 0.45/0.63              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X3)))),
% 0.45/0.63      inference('sup+', [status(thm)], ['21', '22'])).
% 0.45/0.63  thf('24', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.63         ((k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.45/0.63           = (k2_xboole_0 @ (k1_enumset1 @ X7 @ X6 @ X5) @ 
% 0.45/0.63              (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.45/0.63      inference('demod', [status(thm)], ['19', '20', '23'])).
% 0.45/0.63  thf('25', plain,
% 0.45/0.63      (((k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.45/0.63         != (k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ 
% 0.45/0.63             sk_H))),
% 0.45/0.63      inference('demod', [status(thm)], ['12', '24'])).
% 0.45/0.63  thf('26', plain, ($false), inference('simplify', [status(thm)], ['25'])).
% 0.45/0.63  
% 0.45/0.63  % SZS output end Refutation
% 0.45/0.63  
% 0.45/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

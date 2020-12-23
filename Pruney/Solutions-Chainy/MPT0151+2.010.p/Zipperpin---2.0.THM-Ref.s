%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Hw8J5xAWtA

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:18 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   58 (  86 expanded)
%              Number of leaves         :   24 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :  704 (1016 expanded)
%              Number of equality atoms :   41 (  69 expanded)
%              Maximal formula depth    :   19 (  11 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(t67_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
        ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
        = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ) ),
    inference('cnf.neg',[status(esa)],[t67_enumset1])).

thf('0',plain,(
    ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H )
 != ( k2_xboole_0 @ ( k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k2_tarski @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t54_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_tarski @ E @ F ) ) ) )).

thf('1',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( k4_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X28 @ X29 @ X30 @ X31 ) @ ( k2_tarski @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t54_enumset1])).

thf(t47_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k3_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k1_tarski @ X17 ) @ ( k2_enumset1 @ X18 @ X19 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k2_xboole_0 @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X5 )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_tarski @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k1_tarski @ X15 ) @ ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('7',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k2_xboole_0 @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X7 @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ ( k2_xboole_0 @ ( k3_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k3_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k1_tarski @ X17 ) @ ( k2_enumset1 @ X18 @ X19 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t51_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ) )).

thf('13',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k4_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 )
      = ( k2_xboole_0 @ ( k1_tarski @ X22 ) @ ( k3_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t51_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X6 @ X5 ) @ ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k3_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k1_tarski @ X17 ) @ ( k2_enumset1 @ X18 @ X19 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf(t56_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k4_enumset1 @ B @ C @ D @ E @ F @ G ) ) ) )).

thf('20',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( k5_enumset1 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 )
      = ( k2_xboole_0 @ ( k1_tarski @ X34 ) @ ( k4_enumset1 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t56_enumset1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X7 @ X6 ) @ ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k4_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 )
      = ( k2_xboole_0 @ ( k1_tarski @ X22 ) @ ( k3_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t51_enumset1])).

thf(t62_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k5_enumset1 @ B @ C @ D @ E @ F @ G @ H ) ) ) )).

thf('25',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( k6_enumset1 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 )
      = ( k2_xboole_0 @ ( k1_tarski @ X41 ) @ ( k5_enumset1 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t62_enumset1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X7 @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k4_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 )
      = ( k2_xboole_0 @ ( k1_tarski @ X22 ) @ ( k3_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t51_enumset1])).

thf('28',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k2_xboole_0 @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X6 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X6 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','26','29'])).

thf('31',plain,(
    ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H )
 != ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['0','30'])).

thf('32',plain,(
    $false ),
    inference(simplify,[status(thm)],['31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Hw8J5xAWtA
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:26:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.59  % Solved by: fo/fo7.sh
% 0.38/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.59  % done 89 iterations in 0.141s
% 0.38/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.59  % SZS output start Refutation
% 0.38/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.59  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.38/0.59  thf(sk_E_type, type, sk_E: $i).
% 0.38/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.59  thf(sk_D_type, type, sk_D: $i).
% 0.38/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.59  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.38/0.59  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.38/0.59  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.38/0.59  thf(sk_H_type, type, sk_H: $i).
% 0.38/0.59  thf(sk_G_type, type, sk_G: $i).
% 0.38/0.59  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.38/0.59                                           $i > $i).
% 0.38/0.59  thf(sk_F_type, type, sk_F: $i).
% 0.38/0.59  thf(t67_enumset1, conjecture,
% 0.38/0.59    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.38/0.59     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.38/0.59       ( k2_xboole_0 @
% 0.38/0.59         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ))).
% 0.38/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.59    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.38/0.59        ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.38/0.59          ( k2_xboole_0 @
% 0.38/0.59            ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ) )),
% 0.38/0.59    inference('cnf.neg', [status(esa)], [t67_enumset1])).
% 0.38/0.59  thf('0', plain,
% 0.38/0.59      (((k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.38/0.59         != (k2_xboole_0 @ 
% 0.38/0.59             (k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.38/0.59             (k2_tarski @ sk_G @ sk_H)))),
% 0.38/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.59  thf(t54_enumset1, axiom,
% 0.38/0.59    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.38/0.59     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.38/0.60       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_tarski @ E @ F ) ) ))).
% 0.38/0.60  thf('1', plain,
% 0.38/0.60      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.38/0.60         ((k4_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33)
% 0.38/0.60           = (k2_xboole_0 @ (k2_enumset1 @ X28 @ X29 @ X30 @ X31) @ 
% 0.38/0.60              (k2_tarski @ X32 @ X33)))),
% 0.38/0.60      inference('cnf', [status(esa)], [t54_enumset1])).
% 0.38/0.60  thf(t47_enumset1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.38/0.60     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.38/0.60       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ))).
% 0.38/0.60  thf('2', plain,
% 0.38/0.60      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.38/0.60         ((k3_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21)
% 0.38/0.60           = (k2_xboole_0 @ (k1_tarski @ X17) @ 
% 0.38/0.60              (k2_enumset1 @ X18 @ X19 @ X20 @ X21)))),
% 0.38/0.60      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.38/0.60  thf(t4_xboole_1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.38/0.60       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.38/0.60  thf('3', plain,
% 0.38/0.60      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.38/0.60         ((k2_xboole_0 @ (k2_xboole_0 @ X7 @ X8) @ X9)
% 0.38/0.60           = (k2_xboole_0 @ X7 @ (k2_xboole_0 @ X8 @ X9)))),
% 0.38/0.60      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.38/0.60  thf('4', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.38/0.60         ((k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ X5)
% 0.38/0.60           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 0.38/0.60              (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X5)))),
% 0.38/0.60      inference('sup+', [status(thm)], ['2', '3'])).
% 0.38/0.60  thf('5', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.38/0.60         ((k2_xboole_0 @ (k3_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2) @ 
% 0.38/0.60           (k2_tarski @ X1 @ X0))
% 0.38/0.60           = (k2_xboole_0 @ (k1_tarski @ X6) @ 
% 0.38/0.60              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.38/0.60      inference('sup+', [status(thm)], ['1', '4'])).
% 0.38/0.60  thf(t41_enumset1, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( k2_tarski @ A @ B ) =
% 0.38/0.60       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.38/0.60  thf('6', plain,
% 0.38/0.60      (![X15 : $i, X16 : $i]:
% 0.38/0.60         ((k2_tarski @ X15 @ X16)
% 0.38/0.60           = (k2_xboole_0 @ (k1_tarski @ X15) @ (k1_tarski @ X16)))),
% 0.38/0.60      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.38/0.60  thf('7', plain,
% 0.38/0.60      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.38/0.60         ((k2_xboole_0 @ (k2_xboole_0 @ X7 @ X8) @ X9)
% 0.38/0.60           = (k2_xboole_0 @ X7 @ (k2_xboole_0 @ X8 @ X9)))),
% 0.38/0.60      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.38/0.60  thf('8', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.60         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.38/0.60           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.38/0.60              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.38/0.60      inference('sup+', [status(thm)], ['6', '7'])).
% 0.38/0.60  thf('9', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.38/0.60         ((k2_xboole_0 @ (k2_tarski @ X7 @ X6) @ 
% 0.38/0.60           (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.38/0.60           = (k2_xboole_0 @ (k1_tarski @ X7) @ 
% 0.38/0.60              (k2_xboole_0 @ (k3_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2) @ 
% 0.38/0.60               (k2_tarski @ X1 @ X0))))),
% 0.38/0.60      inference('sup+', [status(thm)], ['5', '8'])).
% 0.38/0.60  thf('10', plain,
% 0.38/0.60      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.38/0.60         ((k3_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21)
% 0.38/0.60           = (k2_xboole_0 @ (k1_tarski @ X17) @ 
% 0.38/0.60              (k2_enumset1 @ X18 @ X19 @ X20 @ X21)))),
% 0.38/0.60      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.38/0.60  thf('11', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.60         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.38/0.60           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.38/0.60              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.38/0.60      inference('sup+', [status(thm)], ['6', '7'])).
% 0.38/0.60  thf('12', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.38/0.60         ((k2_xboole_0 @ (k2_tarski @ X5 @ X4) @ 
% 0.38/0.60           (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.38/0.60           = (k2_xboole_0 @ (k1_tarski @ X5) @ 
% 0.38/0.60              (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.38/0.60      inference('sup+', [status(thm)], ['10', '11'])).
% 0.38/0.60  thf(t51_enumset1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.38/0.60     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.38/0.60       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ))).
% 0.38/0.60  thf('13', plain,
% 0.38/0.60      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.38/0.60         ((k4_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27)
% 0.38/0.60           = (k2_xboole_0 @ (k1_tarski @ X22) @ 
% 0.38/0.60              (k3_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27)))),
% 0.38/0.60      inference('cnf', [status(esa)], [t51_enumset1])).
% 0.38/0.60  thf('14', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.38/0.60         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.38/0.60           = (k2_xboole_0 @ (k2_tarski @ X5 @ X4) @ 
% 0.38/0.60              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 0.38/0.60      inference('sup+', [status(thm)], ['12', '13'])).
% 0.38/0.60  thf('15', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.60         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.38/0.60           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.38/0.60              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.38/0.60      inference('sup+', [status(thm)], ['6', '7'])).
% 0.38/0.60  thf('16', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.60         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.38/0.60           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.38/0.60              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.38/0.60      inference('sup+', [status(thm)], ['6', '7'])).
% 0.38/0.60  thf('17', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.60         ((k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ 
% 0.38/0.60           (k2_xboole_0 @ (k1_tarski @ X1) @ X0))
% 0.38/0.60           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 0.38/0.60              (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0)))),
% 0.38/0.60      inference('sup+', [status(thm)], ['15', '16'])).
% 0.38/0.60  thf('18', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.38/0.60         ((k2_xboole_0 @ (k2_tarski @ X6 @ X5) @ 
% 0.38/0.60           (k2_xboole_0 @ (k1_tarski @ X4) @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))
% 0.38/0.60           = (k2_xboole_0 @ (k1_tarski @ X6) @ 
% 0.38/0.60              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.38/0.60      inference('sup+', [status(thm)], ['14', '17'])).
% 0.38/0.60  thf('19', plain,
% 0.38/0.60      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.38/0.60         ((k3_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21)
% 0.38/0.60           = (k2_xboole_0 @ (k1_tarski @ X17) @ 
% 0.38/0.60              (k2_enumset1 @ X18 @ X19 @ X20 @ X21)))),
% 0.38/0.60      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.38/0.60  thf(t56_enumset1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.38/0.60     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.38/0.60       ( k2_xboole_0 @
% 0.38/0.60         ( k1_tarski @ A ) @ ( k4_enumset1 @ B @ C @ D @ E @ F @ G ) ) ))).
% 0.38/0.60  thf('20', plain,
% 0.38/0.60      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.38/0.60         ((k5_enumset1 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40)
% 0.38/0.60           = (k2_xboole_0 @ (k1_tarski @ X34) @ 
% 0.38/0.60              (k4_enumset1 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40)))),
% 0.38/0.60      inference('cnf', [status(esa)], [t56_enumset1])).
% 0.38/0.60  thf('21', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.38/0.60         ((k2_xboole_0 @ (k2_tarski @ X6 @ X5) @ 
% 0.38/0.60           (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.38/0.60           = (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.38/0.60      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.38/0.60  thf('22', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.60         ((k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ 
% 0.38/0.60           (k2_xboole_0 @ (k1_tarski @ X1) @ X0))
% 0.38/0.60           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 0.38/0.60              (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0)))),
% 0.38/0.60      inference('sup+', [status(thm)], ['15', '16'])).
% 0.38/0.60  thf('23', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.38/0.60         ((k2_xboole_0 @ (k2_tarski @ X7 @ X6) @ 
% 0.38/0.60           (k2_xboole_0 @ (k1_tarski @ X5) @ 
% 0.38/0.60            (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)))
% 0.38/0.60           = (k2_xboole_0 @ (k1_tarski @ X7) @ 
% 0.38/0.60              (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.38/0.60      inference('sup+', [status(thm)], ['21', '22'])).
% 0.38/0.60  thf('24', plain,
% 0.38/0.60      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.38/0.60         ((k4_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27)
% 0.38/0.60           = (k2_xboole_0 @ (k1_tarski @ X22) @ 
% 0.38/0.60              (k3_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27)))),
% 0.38/0.60      inference('cnf', [status(esa)], [t51_enumset1])).
% 0.38/0.60  thf(t62_enumset1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.38/0.60     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.38/0.60       ( k2_xboole_0 @
% 0.38/0.60         ( k1_tarski @ A ) @ ( k5_enumset1 @ B @ C @ D @ E @ F @ G @ H ) ) ))).
% 0.38/0.60  thf('25', plain,
% 0.38/0.60      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, 
% 0.38/0.60         X48 : $i]:
% 0.38/0.60         ((k6_enumset1 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48)
% 0.38/0.60           = (k2_xboole_0 @ (k1_tarski @ X41) @ 
% 0.38/0.60              (k5_enumset1 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48)))),
% 0.38/0.60      inference('cnf', [status(esa)], [t62_enumset1])).
% 0.38/0.60  thf('26', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.38/0.60         ((k2_xboole_0 @ (k2_tarski @ X7 @ X6) @ 
% 0.38/0.60           (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.38/0.60           = (k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.38/0.60      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.38/0.60  thf('27', plain,
% 0.38/0.60      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.38/0.60         ((k4_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27)
% 0.38/0.60           = (k2_xboole_0 @ (k1_tarski @ X22) @ 
% 0.38/0.60              (k3_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27)))),
% 0.38/0.60      inference('cnf', [status(esa)], [t51_enumset1])).
% 0.38/0.60  thf('28', plain,
% 0.38/0.60      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.38/0.60         ((k2_xboole_0 @ (k2_xboole_0 @ X7 @ X8) @ X9)
% 0.38/0.60           = (k2_xboole_0 @ X7 @ (k2_xboole_0 @ X8 @ X9)))),
% 0.38/0.60      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.38/0.60  thf('29', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.38/0.60         ((k2_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ X6)
% 0.38/0.60           = (k2_xboole_0 @ (k1_tarski @ X5) @ 
% 0.38/0.60              (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ X6)))),
% 0.38/0.60      inference('sup+', [status(thm)], ['27', '28'])).
% 0.38/0.60  thf('30', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.38/0.60         ((k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.38/0.60           = (k2_xboole_0 @ (k4_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2) @ 
% 0.38/0.60              (k2_tarski @ X1 @ X0)))),
% 0.38/0.60      inference('demod', [status(thm)], ['9', '26', '29'])).
% 0.38/0.60  thf('31', plain,
% 0.38/0.60      (((k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.38/0.60         != (k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ 
% 0.38/0.60             sk_H))),
% 0.38/0.60      inference('demod', [status(thm)], ['0', '30'])).
% 0.38/0.60  thf('32', plain, ($false), inference('simplify', [status(thm)], ['31'])).
% 0.38/0.60  
% 0.38/0.60  % SZS output end Refutation
% 0.38/0.60  
% 0.38/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

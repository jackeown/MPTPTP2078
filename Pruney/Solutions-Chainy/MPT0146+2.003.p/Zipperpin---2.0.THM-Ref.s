%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jP185FHWFb

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:12 EST 2020

% Result     : Theorem 5.28s
% Output     : Refutation 5.28s
% Verified   : 
% Statistics : Number of formulae       :   57 (  92 expanded)
%              Number of leaves         :   22 (  41 expanded)
%              Depth                    :   13
%              Number of atoms          :  662 (1049 expanded)
%              Number of equality atoms :   41 (  76 expanded)
%              Maximal formula depth    :   19 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

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

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('1',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k2_tarski @ X32 @ X33 )
      = ( k2_xboole_0 @ ( k1_tarski @ X32 ) @ ( k1_tarski @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('2',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k2_tarski @ X32 @ X33 )
      = ( k2_xboole_0 @ ( k1_tarski @ X32 ) @ ( k1_tarski @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k2_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('8',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k2_enumset1 @ X20 @ X21 @ X22 @ X23 )
      = ( k2_xboole_0 @ ( k2_tarski @ X20 @ X21 ) @ ( k2_tarski @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('12',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k2_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k2_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X4 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k2_enumset1 @ X20 @ X21 @ X22 @ X23 )
      = ( k2_xboole_0 @ ( k2_tarski @ X20 @ X21 ) @ ( k2_tarski @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('18',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k2_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X7 @ X6 @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ ( k2_xboole_0 @ ( k2_enumset1 @ X6 @ X5 @ X4 @ X3 ) @ ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['9','20'])).

thf(l75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ) )).

thf('22',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k6_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X24 @ X25 @ X26 @ X27 ) @ ( k2_enumset1 @ X28 @ X29 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[l75_enumset1])).

thf('23',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k2_enumset1 @ X20 @ X21 @ X22 @ X23 )
      = ( k2_xboole_0 @ ( k2_tarski @ X20 @ X21 ) @ ( k2_tarski @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t52_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_enumset1 @ C @ D @ E @ F ) ) ) )).

thf('26',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( k4_enumset1 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 )
      = ( k2_xboole_0 @ ( k2_tarski @ X34 @ X35 ) @ ( k2_enumset1 @ X36 @ X37 @ X38 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t52_enumset1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k2_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X6 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X6 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(t61_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ) )).

thf('30',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( k5_enumset1 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 ) @ ( k1_tarski @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[t61_enumset1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22','29','30'])).

thf('32',plain,(
    ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H )
 != ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['0','31'])).

thf('33',plain,(
    $false ),
    inference(simplify,[status(thm)],['32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jP185FHWFb
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:38:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 5.28/5.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.28/5.52  % Solved by: fo/fo7.sh
% 5.28/5.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.28/5.52  % done 979 iterations in 5.044s
% 5.28/5.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.28/5.52  % SZS output start Refutation
% 5.28/5.52  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 5.28/5.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 5.28/5.52  thf(sk_A_type, type, sk_A: $i).
% 5.28/5.52  thf(sk_D_type, type, sk_D: $i).
% 5.28/5.52  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 5.28/5.52  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 5.28/5.52                                           $i > $i).
% 5.28/5.52  thf(sk_C_type, type, sk_C: $i).
% 5.28/5.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 5.28/5.52  thf(sk_E_type, type, sk_E: $i).
% 5.28/5.52  thf(sk_H_type, type, sk_H: $i).
% 5.28/5.52  thf(sk_B_type, type, sk_B: $i).
% 5.28/5.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 5.28/5.52  thf(sk_G_type, type, sk_G: $i).
% 5.28/5.52  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 5.28/5.52  thf(sk_F_type, type, sk_F: $i).
% 5.28/5.52  thf(t62_enumset1, conjecture,
% 5.28/5.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 5.28/5.52     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 5.28/5.52       ( k2_xboole_0 @
% 5.28/5.52         ( k1_tarski @ A ) @ ( k5_enumset1 @ B @ C @ D @ E @ F @ G @ H ) ) ))).
% 5.28/5.52  thf(zf_stmt_0, negated_conjecture,
% 5.28/5.52    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 5.28/5.52        ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 5.28/5.52          ( k2_xboole_0 @
% 5.28/5.52            ( k1_tarski @ A ) @ ( k5_enumset1 @ B @ C @ D @ E @ F @ G @ H ) ) ) )),
% 5.28/5.52    inference('cnf.neg', [status(esa)], [t62_enumset1])).
% 5.28/5.52  thf('0', plain,
% 5.28/5.52      (((k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)
% 5.28/5.52         != (k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 5.28/5.52             (k5_enumset1 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)))),
% 5.28/5.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.28/5.52  thf(t41_enumset1, axiom,
% 5.28/5.52    (![A:$i,B:$i]:
% 5.28/5.52     ( ( k2_tarski @ A @ B ) =
% 5.28/5.52       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 5.28/5.52  thf('1', plain,
% 5.28/5.52      (![X32 : $i, X33 : $i]:
% 5.28/5.52         ((k2_tarski @ X32 @ X33)
% 5.28/5.52           = (k2_xboole_0 @ (k1_tarski @ X32) @ (k1_tarski @ X33)))),
% 5.28/5.52      inference('cnf', [status(esa)], [t41_enumset1])).
% 5.28/5.52  thf('2', plain,
% 5.28/5.52      (![X32 : $i, X33 : $i]:
% 5.28/5.52         ((k2_tarski @ X32 @ X33)
% 5.28/5.52           = (k2_xboole_0 @ (k1_tarski @ X32) @ (k1_tarski @ X33)))),
% 5.28/5.52      inference('cnf', [status(esa)], [t41_enumset1])).
% 5.28/5.52  thf(t4_xboole_1, axiom,
% 5.28/5.52    (![A:$i,B:$i,C:$i]:
% 5.28/5.52     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 5.28/5.52       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 5.28/5.52  thf('3', plain,
% 5.28/5.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 5.28/5.52         ((k2_xboole_0 @ (k2_xboole_0 @ X12 @ X13) @ X14)
% 5.28/5.52           = (k2_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 5.28/5.52      inference('cnf', [status(esa)], [t4_xboole_1])).
% 5.28/5.52  thf('4', plain,
% 5.28/5.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.28/5.52         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 5.28/5.52           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 5.28/5.52              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 5.28/5.52      inference('sup+', [status(thm)], ['2', '3'])).
% 5.28/5.52  thf('5', plain,
% 5.28/5.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.28/5.52         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 5.28/5.52           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 5.28/5.52      inference('sup+', [status(thm)], ['1', '4'])).
% 5.28/5.52  thf('6', plain,
% 5.28/5.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.28/5.52         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 5.28/5.52           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 5.28/5.52              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 5.28/5.52      inference('sup+', [status(thm)], ['2', '3'])).
% 5.28/5.52  thf('7', plain,
% 5.28/5.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.28/5.52         ((k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0))
% 5.28/5.52           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 5.28/5.52              (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))))),
% 5.28/5.52      inference('sup+', [status(thm)], ['5', '6'])).
% 5.28/5.52  thf(l53_enumset1, axiom,
% 5.28/5.52    (![A:$i,B:$i,C:$i,D:$i]:
% 5.28/5.52     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 5.28/5.52       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 5.28/5.52  thf('8', plain,
% 5.28/5.52      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 5.28/5.52         ((k2_enumset1 @ X20 @ X21 @ X22 @ X23)
% 5.28/5.52           = (k2_xboole_0 @ (k2_tarski @ X20 @ X21) @ (k2_tarski @ X22 @ X23)))),
% 5.28/5.52      inference('cnf', [status(esa)], [l53_enumset1])).
% 5.28/5.52  thf('9', plain,
% 5.28/5.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.28/5.52         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 5.28/5.52           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 5.28/5.52              (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))))),
% 5.28/5.52      inference('demod', [status(thm)], ['7', '8'])).
% 5.28/5.52  thf('10', plain,
% 5.28/5.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.28/5.52         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 5.28/5.52           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 5.28/5.52              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 5.28/5.52      inference('sup+', [status(thm)], ['2', '3'])).
% 5.28/5.52  thf('11', plain,
% 5.28/5.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.28/5.52         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 5.28/5.52           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 5.28/5.52              (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))))),
% 5.28/5.52      inference('demod', [status(thm)], ['7', '8'])).
% 5.28/5.52  thf('12', plain,
% 5.28/5.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 5.28/5.52         ((k2_xboole_0 @ (k2_xboole_0 @ X12 @ X13) @ X14)
% 5.28/5.52           = (k2_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 5.28/5.52      inference('cnf', [status(esa)], [t4_xboole_1])).
% 5.28/5.52  thf('13', plain,
% 5.28/5.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 5.28/5.52         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4)
% 5.28/5.52           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 5.28/5.52              (k2_xboole_0 @ 
% 5.28/5.52               (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)) @ X4)))),
% 5.28/5.52      inference('sup+', [status(thm)], ['11', '12'])).
% 5.28/5.52  thf('14', plain,
% 5.28/5.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 5.28/5.52         ((k2_xboole_0 @ (k2_xboole_0 @ X12 @ X13) @ X14)
% 5.28/5.52           = (k2_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 5.28/5.52      inference('cnf', [status(esa)], [t4_xboole_1])).
% 5.28/5.52  thf('15', plain,
% 5.28/5.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 5.28/5.52         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4)
% 5.28/5.52           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 5.28/5.52              (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ 
% 5.28/5.52               (k2_xboole_0 @ (k1_tarski @ X0) @ X4))))),
% 5.28/5.52      inference('demod', [status(thm)], ['13', '14'])).
% 5.28/5.52  thf('16', plain,
% 5.28/5.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 5.28/5.52         ((k2_xboole_0 @ (k2_enumset1 @ X5 @ X4 @ X3 @ X2) @ 
% 5.28/5.52           (k2_xboole_0 @ (k1_tarski @ X1) @ X0))
% 5.28/5.52           = (k2_xboole_0 @ (k1_tarski @ X5) @ 
% 5.28/5.52              (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ 
% 5.28/5.52               (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0))))),
% 5.28/5.52      inference('sup+', [status(thm)], ['10', '15'])).
% 5.28/5.52  thf('17', plain,
% 5.28/5.52      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 5.28/5.52         ((k2_enumset1 @ X20 @ X21 @ X22 @ X23)
% 5.28/5.52           = (k2_xboole_0 @ (k2_tarski @ X20 @ X21) @ (k2_tarski @ X22 @ X23)))),
% 5.28/5.52      inference('cnf', [status(esa)], [l53_enumset1])).
% 5.28/5.52  thf('18', plain,
% 5.28/5.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 5.28/5.52         ((k2_xboole_0 @ (k2_xboole_0 @ X12 @ X13) @ X14)
% 5.28/5.52           = (k2_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 5.28/5.52      inference('cnf', [status(esa)], [t4_xboole_1])).
% 5.28/5.52  thf('19', plain,
% 5.28/5.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 5.28/5.52         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4)
% 5.28/5.52           = (k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ 
% 5.28/5.52              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X4)))),
% 5.28/5.52      inference('sup+', [status(thm)], ['17', '18'])).
% 5.28/5.52  thf('20', plain,
% 5.28/5.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 5.28/5.52         ((k2_xboole_0 @ (k2_enumset1 @ X5 @ X4 @ X3 @ X2) @ 
% 5.28/5.52           (k2_xboole_0 @ (k1_tarski @ X1) @ X0))
% 5.28/5.52           = (k2_xboole_0 @ (k1_tarski @ X5) @ 
% 5.28/5.52              (k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ X0)))),
% 5.28/5.52      inference('demod', [status(thm)], ['16', '19'])).
% 5.28/5.52  thf('21', plain,
% 5.28/5.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 5.28/5.52         ((k2_xboole_0 @ (k2_enumset1 @ X7 @ X6 @ X5 @ X4) @ 
% 5.28/5.52           (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 5.28/5.52           = (k2_xboole_0 @ (k1_tarski @ X7) @ 
% 5.28/5.52              (k2_xboole_0 @ (k2_enumset1 @ X6 @ X5 @ X4 @ X3) @ 
% 5.28/5.52               (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)))))),
% 5.28/5.52      inference('sup+', [status(thm)], ['9', '20'])).
% 5.28/5.52  thf(l75_enumset1, axiom,
% 5.28/5.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 5.28/5.52     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 5.28/5.52       ( k2_xboole_0 @
% 5.28/5.52         ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ))).
% 5.28/5.52  thf('22', plain,
% 5.28/5.52      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, 
% 5.28/5.52         X31 : $i]:
% 5.28/5.52         ((k6_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31)
% 5.28/5.52           = (k2_xboole_0 @ (k2_enumset1 @ X24 @ X25 @ X26 @ X27) @ 
% 5.28/5.52              (k2_enumset1 @ X28 @ X29 @ X30 @ X31)))),
% 5.28/5.52      inference('cnf', [status(esa)], [l75_enumset1])).
% 5.28/5.52  thf('23', plain,
% 5.28/5.52      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 5.28/5.52         ((k2_enumset1 @ X20 @ X21 @ X22 @ X23)
% 5.28/5.52           = (k2_xboole_0 @ (k2_tarski @ X20 @ X21) @ (k2_tarski @ X22 @ X23)))),
% 5.28/5.52      inference('cnf', [status(esa)], [l53_enumset1])).
% 5.28/5.52  thf('24', plain,
% 5.28/5.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 5.28/5.52         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4)
% 5.28/5.52           = (k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ 
% 5.28/5.52              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X4)))),
% 5.28/5.52      inference('sup+', [status(thm)], ['17', '18'])).
% 5.28/5.52  thf('25', plain,
% 5.28/5.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 5.28/5.52         ((k2_xboole_0 @ (k2_enumset1 @ X5 @ X4 @ X3 @ X2) @ 
% 5.28/5.52           (k2_tarski @ X1 @ X0))
% 5.28/5.52           = (k2_xboole_0 @ (k2_tarski @ X5 @ X4) @ 
% 5.28/5.52              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 5.28/5.52      inference('sup+', [status(thm)], ['23', '24'])).
% 5.28/5.52  thf(t52_enumset1, axiom,
% 5.28/5.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 5.28/5.52     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 5.28/5.52       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_enumset1 @ C @ D @ E @ F ) ) ))).
% 5.28/5.52  thf('26', plain,
% 5.28/5.52      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 5.28/5.52         ((k4_enumset1 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39)
% 5.28/5.52           = (k2_xboole_0 @ (k2_tarski @ X34 @ X35) @ 
% 5.28/5.52              (k2_enumset1 @ X36 @ X37 @ X38 @ X39)))),
% 5.28/5.52      inference('cnf', [status(esa)], [t52_enumset1])).
% 5.28/5.52  thf('27', plain,
% 5.28/5.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 5.28/5.52         ((k2_xboole_0 @ (k2_enumset1 @ X5 @ X4 @ X3 @ X2) @ 
% 5.28/5.52           (k2_tarski @ X1 @ X0)) = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 5.28/5.52      inference('demod', [status(thm)], ['25', '26'])).
% 5.28/5.52  thf('28', plain,
% 5.28/5.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 5.28/5.52         ((k2_xboole_0 @ (k2_xboole_0 @ X12 @ X13) @ X14)
% 5.28/5.52           = (k2_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 5.28/5.52      inference('cnf', [status(esa)], [t4_xboole_1])).
% 5.28/5.52  thf('29', plain,
% 5.28/5.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 5.28/5.52         ((k2_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ X6)
% 5.28/5.52           = (k2_xboole_0 @ (k2_enumset1 @ X5 @ X4 @ X3 @ X2) @ 
% 5.28/5.52              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X6)))),
% 5.28/5.52      inference('sup+', [status(thm)], ['27', '28'])).
% 5.28/5.52  thf(t61_enumset1, axiom,
% 5.28/5.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 5.28/5.52     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 5.28/5.52       ( k2_xboole_0 @
% 5.28/5.52         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ))).
% 5.28/5.52  thf('30', plain,
% 5.28/5.52      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 5.28/5.52         ((k5_enumset1 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46)
% 5.28/5.52           = (k2_xboole_0 @ 
% 5.28/5.52              (k4_enumset1 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45) @ 
% 5.28/5.52              (k1_tarski @ X46)))),
% 5.28/5.52      inference('cnf', [status(esa)], [t61_enumset1])).
% 5.28/5.52  thf('31', plain,
% 5.28/5.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 5.28/5.52         ((k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 5.28/5.52           = (k2_xboole_0 @ (k1_tarski @ X7) @ 
% 5.28/5.52              (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 5.28/5.52      inference('demod', [status(thm)], ['21', '22', '29', '30'])).
% 5.28/5.52  thf('32', plain,
% 5.28/5.52      (((k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)
% 5.28/5.52         != (k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ 
% 5.28/5.52             sk_H))),
% 5.28/5.52      inference('demod', [status(thm)], ['0', '31'])).
% 5.28/5.52  thf('33', plain, ($false), inference('simplify', [status(thm)], ['32'])).
% 5.28/5.52  
% 5.28/5.52  % SZS output end Refutation
% 5.28/5.52  
% 5.28/5.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

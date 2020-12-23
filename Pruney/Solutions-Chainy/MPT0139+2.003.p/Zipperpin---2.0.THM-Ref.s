%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aFV7QTC9vO

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:03 EST 2020

% Result     : Theorem 52.04s
% Output     : Refutation 52.04s
% Verified   : 
% Statistics : Number of formulae       :   62 (  70 expanded)
%              Number of leaves         :   24 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :  628 ( 718 expanded)
%              Number of equality atoms :   48 (  56 expanded)
%              Maximal formula depth    :   16 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(t55_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
        ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
        = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ) ),
    inference('cnf.neg',[status(esa)],[t55_enumset1])).

thf('0',plain,(
    ( k4_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E_1 @ sk_F )
 != ( k2_xboole_0 @ ( k3_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E_1 ) @ ( k1_tarski @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('1',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( k2_enumset1 @ X41 @ X42 @ X43 @ X44 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X41 @ X42 @ X43 ) @ ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf(t48_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ) )).

thf('2',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( k3_enumset1 @ X45 @ X46 @ X47 @ X48 @ X49 )
      = ( k2_xboole_0 @ ( k2_tarski @ X45 @ X46 ) @ ( k1_enumset1 @ X47 @ X48 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[t48_enumset1])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X2 ) @ X3 )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X5 )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('6',plain,(
    ( k4_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E_1 @ sk_F )
 != ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_enumset1 @ sk_C_1 @ sk_D @ sk_E_1 @ sk_F ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('7',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k2_tarski @ X32 @ X33 )
      = ( k2_xboole_0 @ ( k1_tarski @ X32 ) @ ( k1_tarski @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('10',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k1_enumset1 @ X34 @ X35 @ X36 )
      = ( k2_xboole_0 @ ( k1_tarski @ X34 ) @ ( k2_tarski @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('12',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k2_enumset1 @ X23 @ X24 @ X25 @ X26 )
      = ( k2_xboole_0 @ ( k2_tarski @ X23 @ X24 ) @ ( k2_tarski @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X2 @ X1 )
      = ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('14',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( k2_enumset1 @ X37 @ X38 @ X39 @ X40 )
      = ( k2_xboole_0 @ ( k1_tarski @ X37 ) @ ( k1_enumset1 @ X38 @ X39 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('15',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( k2_enumset1 @ X41 @ X42 @ X43 @ X44 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X41 @ X42 @ X43 ) @ ( k1_tarski @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('16',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X2 ) @ X3 )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X6 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X6 @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_enumset1 @ X5 @ X4 @ X3 ) )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X2 @ X1 ) @ ( k2_enumset1 @ X0 @ X5 @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( k3_enumset1 @ X45 @ X46 @ X47 @ X48 @ X49 )
      = ( k2_xboole_0 @ ( k2_tarski @ X45 @ X46 ) @ ( k1_enumset1 @ X47 @ X48 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[t48_enumset1])).

thf('21',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k1_enumset1 @ X34 @ X35 @ X36 )
      = ( k2_xboole_0 @ ( k1_tarski @ X34 ) @ ( k2_tarski @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('22',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X2 ) @ X3 )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf(t51_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ) )).

thf('25',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( k4_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 )
      = ( k2_xboole_0 @ ( k1_tarski @ X50 ) @ ( k3_enumset1 @ X51 @ X52 @ X53 @ X54 @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[t51_enumset1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k2_tarski @ X32 @ X33 )
      = ( k2_xboole_0 @ ( k1_tarski @ X32 ) @ ( k1_tarski @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t6_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('28',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k2_tarski @ X32 @ X33 )
      = ( k2_xboole_0 @ ( k1_tarski @ X32 ) @ ( k1_tarski @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k1_enumset1 @ X34 @ X35 @ X36 )
      = ( k2_xboole_0 @ ( k1_tarski @ X34 ) @ ( k2_tarski @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_enumset1 @ X0 @ X5 @ X4 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['19','26','33'])).

thf('35',plain,(
    ( k4_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E_1 @ sk_F )
 != ( k4_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E_1 @ sk_F ) ),
    inference(demod,[status(thm)],['6','34'])).

thf('36',plain,(
    $false ),
    inference(simplify,[status(thm)],['35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aFV7QTC9vO
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:29:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 52.04/52.21  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 52.04/52.21  % Solved by: fo/fo7.sh
% 52.04/52.21  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 52.04/52.21  % done 16024 iterations in 51.751s
% 52.04/52.21  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 52.04/52.21  % SZS output start Refutation
% 52.04/52.21  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 52.04/52.21  thf(sk_A_type, type, sk_A: $i).
% 52.04/52.21  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 52.04/52.21  thf(sk_D_type, type, sk_D: $i).
% 52.04/52.21  thf(sk_C_1_type, type, sk_C_1: $i).
% 52.04/52.21  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 52.04/52.21  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 52.04/52.21  thf(sk_E_1_type, type, sk_E_1: $i).
% 52.04/52.21  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 52.04/52.21  thf(sk_B_type, type, sk_B: $i).
% 52.04/52.21  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 52.04/52.21  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 52.04/52.21  thf(sk_F_type, type, sk_F: $i).
% 52.04/52.21  thf(t55_enumset1, conjecture,
% 52.04/52.21    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 52.04/52.21     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 52.04/52.21       ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ))).
% 52.04/52.21  thf(zf_stmt_0, negated_conjecture,
% 52.04/52.21    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 52.04/52.21        ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 52.04/52.21          ( k2_xboole_0 @
% 52.04/52.21            ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ) )),
% 52.04/52.21    inference('cnf.neg', [status(esa)], [t55_enumset1])).
% 52.04/52.21  thf('0', plain,
% 52.04/52.21      (((k4_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E_1 @ sk_F)
% 52.04/52.21         != (k2_xboole_0 @ 
% 52.04/52.21             (k3_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E_1) @ 
% 52.04/52.21             (k1_tarski @ sk_F)))),
% 52.04/52.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 52.04/52.21  thf(t46_enumset1, axiom,
% 52.04/52.21    (![A:$i,B:$i,C:$i,D:$i]:
% 52.04/52.21     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 52.04/52.21       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 52.04/52.21  thf('1', plain,
% 52.04/52.21      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 52.04/52.21         ((k2_enumset1 @ X41 @ X42 @ X43 @ X44)
% 52.04/52.21           = (k2_xboole_0 @ (k1_enumset1 @ X41 @ X42 @ X43) @ (k1_tarski @ X44)))),
% 52.04/52.21      inference('cnf', [status(esa)], [t46_enumset1])).
% 52.04/52.21  thf(t48_enumset1, axiom,
% 52.04/52.21    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 52.04/52.21     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 52.04/52.21       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ))).
% 52.04/52.21  thf('2', plain,
% 52.04/52.21      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 52.04/52.21         ((k3_enumset1 @ X45 @ X46 @ X47 @ X48 @ X49)
% 52.04/52.21           = (k2_xboole_0 @ (k2_tarski @ X45 @ X46) @ 
% 52.04/52.21              (k1_enumset1 @ X47 @ X48 @ X49)))),
% 52.04/52.21      inference('cnf', [status(esa)], [t48_enumset1])).
% 52.04/52.21  thf(t4_xboole_1, axiom,
% 52.04/52.21    (![A:$i,B:$i,C:$i]:
% 52.04/52.21     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 52.04/52.21       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 52.04/52.21  thf('3', plain,
% 52.04/52.21      (![X1 : $i, X2 : $i, X3 : $i]:
% 52.04/52.21         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ X3)
% 52.04/52.21           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ X3)))),
% 52.04/52.21      inference('cnf', [status(esa)], [t4_xboole_1])).
% 52.04/52.21  thf('4', plain,
% 52.04/52.21      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 52.04/52.21         ((k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ X5)
% 52.04/52.21           = (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ 
% 52.04/52.21              (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X5)))),
% 52.04/52.21      inference('sup+', [status(thm)], ['2', '3'])).
% 52.04/52.21  thf('5', plain,
% 52.04/52.21      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 52.04/52.21         ((k2_xboole_0 @ (k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 52.04/52.21           (k1_tarski @ X0))
% 52.04/52.21           = (k2_xboole_0 @ (k2_tarski @ X5 @ X4) @ 
% 52.04/52.21              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 52.04/52.21      inference('sup+', [status(thm)], ['1', '4'])).
% 52.04/52.21  thf('6', plain,
% 52.04/52.21      (((k4_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E_1 @ sk_F)
% 52.04/52.21         != (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 52.04/52.21             (k2_enumset1 @ sk_C_1 @ sk_D @ sk_E_1 @ sk_F)))),
% 52.04/52.21      inference('demod', [status(thm)], ['0', '5'])).
% 52.04/52.21  thf(t41_enumset1, axiom,
% 52.04/52.21    (![A:$i,B:$i]:
% 52.04/52.21     ( ( k2_tarski @ A @ B ) =
% 52.04/52.21       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 52.04/52.21  thf('7', plain,
% 52.04/52.21      (![X32 : $i, X33 : $i]:
% 52.04/52.21         ((k2_tarski @ X32 @ X33)
% 52.04/52.21           = (k2_xboole_0 @ (k1_tarski @ X32) @ (k1_tarski @ X33)))),
% 52.04/52.21      inference('cnf', [status(esa)], [t41_enumset1])).
% 52.04/52.21  thf(idempotence_k2_xboole_0, axiom,
% 52.04/52.21    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 52.04/52.21  thf('8', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 52.04/52.21      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 52.04/52.21  thf('9', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 52.04/52.21      inference('sup+', [status(thm)], ['7', '8'])).
% 52.04/52.21  thf(t42_enumset1, axiom,
% 52.04/52.21    (![A:$i,B:$i,C:$i]:
% 52.04/52.21     ( ( k1_enumset1 @ A @ B @ C ) =
% 52.04/52.21       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 52.04/52.21  thf('10', plain,
% 52.04/52.21      (![X34 : $i, X35 : $i, X36 : $i]:
% 52.04/52.21         ((k1_enumset1 @ X34 @ X35 @ X36)
% 52.04/52.21           = (k2_xboole_0 @ (k1_tarski @ X34) @ (k2_tarski @ X35 @ X36)))),
% 52.04/52.21      inference('cnf', [status(esa)], [t42_enumset1])).
% 52.04/52.21  thf('11', plain,
% 52.04/52.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.04/52.21         ((k1_enumset1 @ X0 @ X2 @ X1)
% 52.04/52.21           = (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k2_tarski @ X2 @ X1)))),
% 52.04/52.21      inference('sup+', [status(thm)], ['9', '10'])).
% 52.04/52.21  thf(l53_enumset1, axiom,
% 52.04/52.21    (![A:$i,B:$i,C:$i,D:$i]:
% 52.04/52.21     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 52.04/52.21       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 52.04/52.21  thf('12', plain,
% 52.04/52.21      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 52.04/52.21         ((k2_enumset1 @ X23 @ X24 @ X25 @ X26)
% 52.04/52.21           = (k2_xboole_0 @ (k2_tarski @ X23 @ X24) @ (k2_tarski @ X25 @ X26)))),
% 52.04/52.21      inference('cnf', [status(esa)], [l53_enumset1])).
% 52.04/52.21  thf('13', plain,
% 52.04/52.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 52.04/52.21         ((k1_enumset1 @ X0 @ X2 @ X1) = (k2_enumset1 @ X0 @ X0 @ X2 @ X1))),
% 52.04/52.21      inference('demod', [status(thm)], ['11', '12'])).
% 52.04/52.21  thf(t44_enumset1, axiom,
% 52.04/52.21    (![A:$i,B:$i,C:$i,D:$i]:
% 52.04/52.21     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 52.04/52.21       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 52.04/52.21  thf('14', plain,
% 52.04/52.21      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 52.04/52.21         ((k2_enumset1 @ X37 @ X38 @ X39 @ X40)
% 52.04/52.21           = (k2_xboole_0 @ (k1_tarski @ X37) @ (k1_enumset1 @ X38 @ X39 @ X40)))),
% 52.04/52.21      inference('cnf', [status(esa)], [t44_enumset1])).
% 52.04/52.21  thf('15', plain,
% 52.04/52.21      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 52.04/52.21         ((k2_enumset1 @ X41 @ X42 @ X43 @ X44)
% 52.04/52.21           = (k2_xboole_0 @ (k1_enumset1 @ X41 @ X42 @ X43) @ (k1_tarski @ X44)))),
% 52.04/52.21      inference('cnf', [status(esa)], [t46_enumset1])).
% 52.04/52.21  thf('16', plain,
% 52.04/52.21      (![X1 : $i, X2 : $i, X3 : $i]:
% 52.04/52.21         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ X3)
% 52.04/52.21           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ X3)))),
% 52.04/52.21      inference('cnf', [status(esa)], [t4_xboole_1])).
% 52.04/52.21  thf('17', plain,
% 52.04/52.21      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 52.04/52.21         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4)
% 52.04/52.21           = (k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ 
% 52.04/52.21              (k2_xboole_0 @ (k1_tarski @ X0) @ X4)))),
% 52.04/52.21      inference('sup+', [status(thm)], ['15', '16'])).
% 52.04/52.21  thf('18', plain,
% 52.04/52.21      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 52.04/52.21         ((k2_xboole_0 @ (k2_enumset1 @ X6 @ X5 @ X4 @ X3) @ 
% 52.04/52.21           (k1_enumset1 @ X2 @ X1 @ X0))
% 52.04/52.21           = (k2_xboole_0 @ (k1_enumset1 @ X6 @ X5 @ X4) @ 
% 52.04/52.21              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 52.04/52.21      inference('sup+', [status(thm)], ['14', '17'])).
% 52.04/52.21  thf('19', plain,
% 52.04/52.21      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 52.04/52.21         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 52.04/52.21           (k1_enumset1 @ X5 @ X4 @ X3))
% 52.04/52.21           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X2 @ X1) @ 
% 52.04/52.21              (k2_enumset1 @ X0 @ X5 @ X4 @ X3)))),
% 52.04/52.21      inference('sup+', [status(thm)], ['13', '18'])).
% 52.04/52.21  thf('20', plain,
% 52.04/52.21      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 52.04/52.21         ((k3_enumset1 @ X45 @ X46 @ X47 @ X48 @ X49)
% 52.04/52.21           = (k2_xboole_0 @ (k2_tarski @ X45 @ X46) @ 
% 52.04/52.21              (k1_enumset1 @ X47 @ X48 @ X49)))),
% 52.04/52.21      inference('cnf', [status(esa)], [t48_enumset1])).
% 52.04/52.21  thf('21', plain,
% 52.04/52.21      (![X34 : $i, X35 : $i, X36 : $i]:
% 52.04/52.21         ((k1_enumset1 @ X34 @ X35 @ X36)
% 52.04/52.21           = (k2_xboole_0 @ (k1_tarski @ X34) @ (k2_tarski @ X35 @ X36)))),
% 52.04/52.21      inference('cnf', [status(esa)], [t42_enumset1])).
% 52.04/52.21  thf('22', plain,
% 52.04/52.21      (![X1 : $i, X2 : $i, X3 : $i]:
% 52.04/52.21         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ X3)
% 52.04/52.21           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ X3)))),
% 52.04/52.21      inference('cnf', [status(esa)], [t4_xboole_1])).
% 52.04/52.21  thf('23', plain,
% 52.04/52.21      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 52.04/52.21         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 52.04/52.21           = (k2_xboole_0 @ (k1_tarski @ X2) @ 
% 52.04/52.21              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X3)))),
% 52.04/52.21      inference('sup+', [status(thm)], ['21', '22'])).
% 52.04/52.21  thf('24', plain,
% 52.04/52.21      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 52.04/52.21         ((k2_xboole_0 @ (k1_enumset1 @ X5 @ X4 @ X3) @ 
% 52.04/52.21           (k1_enumset1 @ X2 @ X1 @ X0))
% 52.04/52.21           = (k2_xboole_0 @ (k1_tarski @ X5) @ 
% 52.04/52.21              (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 52.04/52.21      inference('sup+', [status(thm)], ['20', '23'])).
% 52.04/52.21  thf(t51_enumset1, axiom,
% 52.04/52.21    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 52.04/52.21     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 52.04/52.21       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ))).
% 52.04/52.21  thf('25', plain,
% 52.04/52.21      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 52.04/52.21         ((k4_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55)
% 52.04/52.21           = (k2_xboole_0 @ (k1_tarski @ X50) @ 
% 52.04/52.21              (k3_enumset1 @ X51 @ X52 @ X53 @ X54 @ X55)))),
% 52.04/52.21      inference('cnf', [status(esa)], [t51_enumset1])).
% 52.04/52.21  thf('26', plain,
% 52.04/52.21      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 52.04/52.21         ((k2_xboole_0 @ (k1_enumset1 @ X5 @ X4 @ X3) @ 
% 52.04/52.21           (k1_enumset1 @ X2 @ X1 @ X0))
% 52.04/52.21           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 52.04/52.21      inference('demod', [status(thm)], ['24', '25'])).
% 52.04/52.21  thf('27', plain,
% 52.04/52.21      (![X32 : $i, X33 : $i]:
% 52.04/52.21         ((k2_tarski @ X32 @ X33)
% 52.04/52.21           = (k2_xboole_0 @ (k1_tarski @ X32) @ (k1_tarski @ X33)))),
% 52.04/52.21      inference('cnf', [status(esa)], [t41_enumset1])).
% 52.04/52.21  thf(t6_xboole_1, axiom,
% 52.04/52.21    (![A:$i,B:$i]:
% 52.04/52.21     ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 52.04/52.21  thf('28', plain,
% 52.04/52.21      (![X4 : $i, X5 : $i]:
% 52.04/52.21         ((k2_xboole_0 @ X4 @ (k2_xboole_0 @ X4 @ X5))
% 52.04/52.21           = (k2_xboole_0 @ X4 @ X5))),
% 52.04/52.21      inference('cnf', [status(esa)], [t6_xboole_1])).
% 52.04/52.21  thf('29', plain,
% 52.04/52.21      (![X0 : $i, X1 : $i]:
% 52.04/52.21         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 52.04/52.21           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 52.04/52.21      inference('sup+', [status(thm)], ['27', '28'])).
% 52.04/52.21  thf('30', plain,
% 52.04/52.21      (![X32 : $i, X33 : $i]:
% 52.04/52.21         ((k2_tarski @ X32 @ X33)
% 52.04/52.21           = (k2_xboole_0 @ (k1_tarski @ X32) @ (k1_tarski @ X33)))),
% 52.04/52.21      inference('cnf', [status(esa)], [t41_enumset1])).
% 52.04/52.21  thf('31', plain,
% 52.04/52.21      (![X0 : $i, X1 : $i]:
% 52.04/52.21         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 52.04/52.21           = (k2_tarski @ X1 @ X0))),
% 52.04/52.21      inference('demod', [status(thm)], ['29', '30'])).
% 52.04/52.21  thf('32', plain,
% 52.04/52.21      (![X34 : $i, X35 : $i, X36 : $i]:
% 52.04/52.21         ((k1_enumset1 @ X34 @ X35 @ X36)
% 52.04/52.21           = (k2_xboole_0 @ (k1_tarski @ X34) @ (k2_tarski @ X35 @ X36)))),
% 52.04/52.21      inference('cnf', [status(esa)], [t42_enumset1])).
% 52.04/52.21  thf('33', plain,
% 52.04/52.21      (![X0 : $i, X1 : $i]:
% 52.04/52.21         ((k1_enumset1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 52.04/52.21      inference('demod', [status(thm)], ['31', '32'])).
% 52.04/52.21  thf('34', plain,
% 52.04/52.21      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 52.04/52.21         ((k4_enumset1 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3)
% 52.04/52.21           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ 
% 52.04/52.21              (k2_enumset1 @ X0 @ X5 @ X4 @ X3)))),
% 52.04/52.21      inference('demod', [status(thm)], ['19', '26', '33'])).
% 52.04/52.21  thf('35', plain,
% 52.04/52.21      (((k4_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E_1 @ sk_F)
% 52.04/52.21         != (k4_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E_1 @ sk_F))),
% 52.04/52.21      inference('demod', [status(thm)], ['6', '34'])).
% 52.04/52.21  thf('36', plain, ($false), inference('simplify', [status(thm)], ['35'])).
% 52.04/52.21  
% 52.04/52.21  % SZS output end Refutation
% 52.04/52.21  
% 52.04/52.22  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

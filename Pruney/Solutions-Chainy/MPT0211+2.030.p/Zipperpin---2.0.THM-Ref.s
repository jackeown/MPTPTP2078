%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lzFbHgc3oj

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:34 EST 2020

% Result     : Theorem 5.95s
% Output     : Refutation 5.95s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 244 expanded)
%              Number of leaves         :   27 (  91 expanded)
%              Depth                    :   13
%              Number of atoms          :  637 (2286 expanded)
%              Number of equality atoms :   63 ( 231 expanded)
%              Maximal formula depth    :   12 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t137_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) )
        = ( k1_enumset1 @ A @ B @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t137_enumset1])).

thf('0',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k2_tarski @ sk_C @ sk_A ) )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X60: $i] :
      ( ( k2_tarski @ X60 @ X60 )
      = ( k1_tarski @ X60 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X61: $i,X62: $i] :
      ( ( k1_enumset1 @ X61 @ X61 @ X62 )
      = ( k2_tarski @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('3',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( k2_enumset1 @ X50 @ X51 @ X52 @ X53 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X50 @ X51 @ X52 ) @ ( k1_tarski @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('5',plain,(
    ! [X63: $i,X64: $i,X65: $i] :
      ( ( k2_enumset1 @ X63 @ X63 @ X64 @ X65 )
      = ( k1_enumset1 @ X63 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X61: $i,X62: $i] :
      ( ( k1_enumset1 @ X61 @ X61 @ X62 )
      = ( k2_tarski @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k5_xboole_0 @ X4 @ ( k5_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X8 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(demod,[status(thm)],['10','13','14'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['9','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X2 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t104_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ C @ B @ D ) ) )).

thf('25',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k2_enumset1 @ X25 @ X27 @ X26 @ X28 )
      = ( k2_enumset1 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t104_enumset1])).

thf('26',plain,(
    ! [X63: $i,X64: $i,X65: $i] :
      ( ( k2_enumset1 @ X63 @ X63 @ X64 @ X65 )
      = ( k1_enumset1 @ X63 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(t107_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ D @ C @ B ) ) )).

thf('28',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k2_enumset1 @ X29 @ X32 @ X31 @ X30 )
      = ( k2_enumset1 @ X29 @ X30 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X2 @ X1 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k2_tarski @ sk_C @ sk_A ) )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['0','24','31'])).

thf('33',plain,(
    ! [X61: $i,X62: $i] :
      ( ( k1_enumset1 @ X61 @ X61 @ X62 )
      = ( k2_tarski @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(l57_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) )).

thf('34',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( k3_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X20 @ X21 @ X22 ) @ ( k2_tarski @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(t113_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ B @ D @ C @ A ) ) )).

thf('36',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( k2_enumset1 @ X36 @ X33 @ X35 @ X34 )
      = ( k2_enumset1 @ X33 @ X34 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t113_enumset1])).

thf('37',plain,(
    ! [X63: $i,X64: $i,X65: $i] :
      ( ( k2_enumset1 @ X63 @ X63 @ X64 @ X65 )
      = ( k1_enumset1 @ X63 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('39',plain,(
    ! [X66: $i,X67: $i,X68: $i,X69: $i] :
      ( ( k3_enumset1 @ X66 @ X66 @ X67 @ X68 @ X69 )
      = ( k2_enumset1 @ X66 @ X67 @ X68 @ X69 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X2 @ X1 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X2 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X2 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ( k1_enumset1 @ sk_B @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['32','35','40','45'])).

thf('47',plain,(
    $false ),
    inference(simplify,[status(thm)],['46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lzFbHgc3oj
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:44:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 5.95/6.13  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.95/6.13  % Solved by: fo/fo7.sh
% 5.95/6.13  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.95/6.13  % done 3412 iterations in 5.666s
% 5.95/6.13  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.95/6.13  % SZS output start Refutation
% 5.95/6.13  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 5.95/6.13  thf(sk_C_type, type, sk_C: $i).
% 5.95/6.13  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 5.95/6.13  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 5.95/6.13  thf(sk_B_type, type, sk_B: $i).
% 5.95/6.13  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 5.95/6.13  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 5.95/6.13  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 5.95/6.13  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 5.95/6.13  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 5.95/6.13  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 5.95/6.13  thf(sk_A_type, type, sk_A: $i).
% 5.95/6.13  thf(t137_enumset1, conjecture,
% 5.95/6.13    (![A:$i,B:$i,C:$i]:
% 5.95/6.13     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 5.95/6.13       ( k1_enumset1 @ A @ B @ C ) ))).
% 5.95/6.13  thf(zf_stmt_0, negated_conjecture,
% 5.95/6.13    (~( ![A:$i,B:$i,C:$i]:
% 5.95/6.13        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 5.95/6.13          ( k1_enumset1 @ A @ B @ C ) ) )),
% 5.95/6.13    inference('cnf.neg', [status(esa)], [t137_enumset1])).
% 5.95/6.13  thf('0', plain,
% 5.95/6.13      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 5.95/6.13         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 5.95/6.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.95/6.13  thf(t69_enumset1, axiom,
% 5.95/6.13    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 5.95/6.13  thf('1', plain, (![X60 : $i]: ((k2_tarski @ X60 @ X60) = (k1_tarski @ X60))),
% 5.95/6.13      inference('cnf', [status(esa)], [t69_enumset1])).
% 5.95/6.13  thf(t70_enumset1, axiom,
% 5.95/6.13    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 5.95/6.13  thf('2', plain,
% 5.95/6.13      (![X61 : $i, X62 : $i]:
% 5.95/6.13         ((k1_enumset1 @ X61 @ X61 @ X62) = (k2_tarski @ X61 @ X62))),
% 5.95/6.13      inference('cnf', [status(esa)], [t70_enumset1])).
% 5.95/6.13  thf(t46_enumset1, axiom,
% 5.95/6.13    (![A:$i,B:$i,C:$i,D:$i]:
% 5.95/6.13     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 5.95/6.13       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 5.95/6.13  thf('3', plain,
% 5.95/6.13      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 5.95/6.13         ((k2_enumset1 @ X50 @ X51 @ X52 @ X53)
% 5.95/6.13           = (k2_xboole_0 @ (k1_enumset1 @ X50 @ X51 @ X52) @ (k1_tarski @ X53)))),
% 5.95/6.13      inference('cnf', [status(esa)], [t46_enumset1])).
% 5.95/6.13  thf('4', plain,
% 5.95/6.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.95/6.13         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 5.95/6.13           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 5.95/6.13      inference('sup+', [status(thm)], ['2', '3'])).
% 5.95/6.13  thf(t71_enumset1, axiom,
% 5.95/6.13    (![A:$i,B:$i,C:$i]:
% 5.95/6.13     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 5.95/6.13  thf('5', plain,
% 5.95/6.13      (![X63 : $i, X64 : $i, X65 : $i]:
% 5.95/6.13         ((k2_enumset1 @ X63 @ X63 @ X64 @ X65)
% 5.95/6.13           = (k1_enumset1 @ X63 @ X64 @ X65))),
% 5.95/6.13      inference('cnf', [status(esa)], [t71_enumset1])).
% 5.95/6.13  thf('6', plain,
% 5.95/6.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.95/6.13         ((k1_enumset1 @ X1 @ X0 @ X2)
% 5.95/6.13           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 5.95/6.13      inference('demod', [status(thm)], ['4', '5'])).
% 5.95/6.13  thf('7', plain,
% 5.95/6.13      (![X0 : $i, X1 : $i]:
% 5.95/6.13         ((k1_enumset1 @ X0 @ X0 @ X1)
% 5.95/6.13           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 5.95/6.13      inference('sup+', [status(thm)], ['1', '6'])).
% 5.95/6.13  thf('8', plain,
% 5.95/6.13      (![X61 : $i, X62 : $i]:
% 5.95/6.13         ((k1_enumset1 @ X61 @ X61 @ X62) = (k2_tarski @ X61 @ X62))),
% 5.95/6.13      inference('cnf', [status(esa)], [t70_enumset1])).
% 5.95/6.13  thf('9', plain,
% 5.95/6.13      (![X0 : $i, X1 : $i]:
% 5.95/6.13         ((k2_tarski @ X0 @ X1)
% 5.95/6.13           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 5.95/6.13      inference('demod', [status(thm)], ['7', '8'])).
% 5.95/6.13  thf(t94_xboole_1, axiom,
% 5.95/6.13    (![A:$i,B:$i]:
% 5.95/6.13     ( ( k2_xboole_0 @ A @ B ) =
% 5.95/6.13       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 5.95/6.13  thf('10', plain,
% 5.95/6.13      (![X7 : $i, X8 : $i]:
% 5.95/6.13         ((k2_xboole_0 @ X7 @ X8)
% 5.95/6.13           = (k5_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ (k3_xboole_0 @ X7 @ X8)))),
% 5.95/6.13      inference('cnf', [status(esa)], [t94_xboole_1])).
% 5.95/6.13  thf(commutativity_k5_xboole_0, axiom,
% 5.95/6.13    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 5.95/6.13  thf('11', plain,
% 5.95/6.13      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 5.95/6.13      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 5.95/6.13  thf(t91_xboole_1, axiom,
% 5.95/6.13    (![A:$i,B:$i,C:$i]:
% 5.95/6.13     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 5.95/6.13       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 5.95/6.13  thf('12', plain,
% 5.95/6.13      (![X4 : $i, X5 : $i, X6 : $i]:
% 5.95/6.13         ((k5_xboole_0 @ (k5_xboole_0 @ X4 @ X5) @ X6)
% 5.95/6.13           = (k5_xboole_0 @ X4 @ (k5_xboole_0 @ X5 @ X6)))),
% 5.95/6.13      inference('cnf', [status(esa)], [t91_xboole_1])).
% 5.95/6.13  thf('13', plain,
% 5.95/6.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.95/6.13         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 5.95/6.13           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 5.95/6.13      inference('sup+', [status(thm)], ['11', '12'])).
% 5.95/6.13  thf(t100_xboole_1, axiom,
% 5.95/6.13    (![A:$i,B:$i]:
% 5.95/6.13     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 5.95/6.13  thf('14', plain,
% 5.95/6.13      (![X2 : $i, X3 : $i]:
% 5.95/6.13         ((k4_xboole_0 @ X2 @ X3)
% 5.95/6.13           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 5.95/6.13      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.95/6.13  thf('15', plain,
% 5.95/6.13      (![X7 : $i, X8 : $i]:
% 5.95/6.13         ((k2_xboole_0 @ X7 @ X8)
% 5.95/6.13           = (k5_xboole_0 @ X8 @ (k4_xboole_0 @ X7 @ X8)))),
% 5.95/6.13      inference('demod', [status(thm)], ['10', '13', '14'])).
% 5.95/6.13  thf(t98_xboole_1, axiom,
% 5.95/6.13    (![A:$i,B:$i]:
% 5.95/6.13     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 5.95/6.13  thf('16', plain,
% 5.95/6.13      (![X9 : $i, X10 : $i]:
% 5.95/6.13         ((k2_xboole_0 @ X9 @ X10)
% 5.95/6.13           = (k5_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9)))),
% 5.95/6.13      inference('cnf', [status(esa)], [t98_xboole_1])).
% 5.95/6.13  thf('17', plain,
% 5.95/6.13      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 5.95/6.13      inference('sup+', [status(thm)], ['15', '16'])).
% 5.95/6.13  thf('18', plain,
% 5.95/6.13      (![X0 : $i, X1 : $i]:
% 5.95/6.13         ((k2_tarski @ X1 @ X0)
% 5.95/6.13           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 5.95/6.13      inference('sup+', [status(thm)], ['9', '17'])).
% 5.95/6.13  thf('19', plain,
% 5.95/6.13      (![X0 : $i, X1 : $i]:
% 5.95/6.13         ((k2_tarski @ X0 @ X1)
% 5.95/6.13           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 5.95/6.13      inference('demod', [status(thm)], ['7', '8'])).
% 5.95/6.13  thf('20', plain,
% 5.95/6.13      (![X0 : $i, X1 : $i]: ((k2_tarski @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 5.95/6.13      inference('sup+', [status(thm)], ['18', '19'])).
% 5.95/6.13  thf('21', plain,
% 5.95/6.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.95/6.13         ((k1_enumset1 @ X1 @ X0 @ X2)
% 5.95/6.13           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 5.95/6.13      inference('demod', [status(thm)], ['4', '5'])).
% 5.95/6.13  thf('22', plain,
% 5.95/6.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.95/6.13         ((k1_enumset1 @ X0 @ X1 @ X2)
% 5.95/6.13           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 5.95/6.13      inference('sup+', [status(thm)], ['20', '21'])).
% 5.95/6.13  thf('23', plain,
% 5.95/6.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.95/6.13         ((k1_enumset1 @ X1 @ X0 @ X2)
% 5.95/6.13           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 5.95/6.13      inference('demod', [status(thm)], ['4', '5'])).
% 5.95/6.13  thf('24', plain,
% 5.95/6.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.95/6.13         ((k1_enumset1 @ X1 @ X2 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 5.95/6.13      inference('sup+', [status(thm)], ['22', '23'])).
% 5.95/6.13  thf(t104_enumset1, axiom,
% 5.95/6.13    (![A:$i,B:$i,C:$i,D:$i]:
% 5.95/6.13     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ B @ D ) ))).
% 5.95/6.13  thf('25', plain,
% 5.95/6.13      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 5.95/6.13         ((k2_enumset1 @ X25 @ X27 @ X26 @ X28)
% 5.95/6.13           = (k2_enumset1 @ X25 @ X26 @ X27 @ X28))),
% 5.95/6.13      inference('cnf', [status(esa)], [t104_enumset1])).
% 5.95/6.13  thf('26', plain,
% 5.95/6.13      (![X63 : $i, X64 : $i, X65 : $i]:
% 5.95/6.13         ((k2_enumset1 @ X63 @ X63 @ X64 @ X65)
% 5.95/6.13           = (k1_enumset1 @ X63 @ X64 @ X65))),
% 5.95/6.13      inference('cnf', [status(esa)], [t71_enumset1])).
% 5.95/6.13  thf('27', plain,
% 5.95/6.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.95/6.13         ((k2_enumset1 @ X1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 5.95/6.13      inference('sup+', [status(thm)], ['25', '26'])).
% 5.95/6.13  thf(t107_enumset1, axiom,
% 5.95/6.13    (![A:$i,B:$i,C:$i,D:$i]:
% 5.95/6.13     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ D @ C @ B ) ))).
% 5.95/6.13  thf('28', plain,
% 5.95/6.13      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 5.95/6.13         ((k2_enumset1 @ X29 @ X32 @ X31 @ X30)
% 5.95/6.13           = (k2_enumset1 @ X29 @ X30 @ X31 @ X32))),
% 5.95/6.13      inference('cnf', [status(esa)], [t107_enumset1])).
% 5.95/6.13  thf('29', plain,
% 5.95/6.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.95/6.13         ((k2_enumset1 @ X2 @ X0 @ X2 @ X1) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 5.95/6.13      inference('sup+', [status(thm)], ['27', '28'])).
% 5.95/6.13  thf('30', plain,
% 5.95/6.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.95/6.13         ((k2_enumset1 @ X1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 5.95/6.13      inference('sup+', [status(thm)], ['25', '26'])).
% 5.95/6.13  thf('31', plain,
% 5.95/6.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.95/6.13         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 5.95/6.13      inference('sup+', [status(thm)], ['29', '30'])).
% 5.95/6.13  thf('32', plain,
% 5.95/6.13      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 5.95/6.13         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 5.95/6.13      inference('demod', [status(thm)], ['0', '24', '31'])).
% 5.95/6.13  thf('33', plain,
% 5.95/6.13      (![X61 : $i, X62 : $i]:
% 5.95/6.13         ((k1_enumset1 @ X61 @ X61 @ X62) = (k2_tarski @ X61 @ X62))),
% 5.95/6.13      inference('cnf', [status(esa)], [t70_enumset1])).
% 5.95/6.13  thf(l57_enumset1, axiom,
% 5.95/6.13    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 5.95/6.13     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 5.95/6.13       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ))).
% 5.95/6.13  thf('34', plain,
% 5.95/6.13      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 5.95/6.13         ((k3_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24)
% 5.95/6.13           = (k2_xboole_0 @ (k1_enumset1 @ X20 @ X21 @ X22) @ 
% 5.95/6.13              (k2_tarski @ X23 @ X24)))),
% 5.95/6.13      inference('cnf', [status(esa)], [l57_enumset1])).
% 5.95/6.13  thf('35', plain,
% 5.95/6.13      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.95/6.13         ((k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2)
% 5.95/6.13           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 5.95/6.13      inference('sup+', [status(thm)], ['33', '34'])).
% 5.95/6.13  thf(t113_enumset1, axiom,
% 5.95/6.13    (![A:$i,B:$i,C:$i,D:$i]:
% 5.95/6.13     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ D @ C @ A ) ))).
% 5.95/6.13  thf('36', plain,
% 5.95/6.13      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 5.95/6.13         ((k2_enumset1 @ X36 @ X33 @ X35 @ X34)
% 5.95/6.13           = (k2_enumset1 @ X33 @ X34 @ X35 @ X36))),
% 5.95/6.13      inference('cnf', [status(esa)], [t113_enumset1])).
% 5.95/6.13  thf('37', plain,
% 5.95/6.13      (![X63 : $i, X64 : $i, X65 : $i]:
% 5.95/6.13         ((k2_enumset1 @ X63 @ X63 @ X64 @ X65)
% 5.95/6.13           = (k1_enumset1 @ X63 @ X64 @ X65))),
% 5.95/6.13      inference('cnf', [status(esa)], [t71_enumset1])).
% 5.95/6.13  thf('38', plain,
% 5.95/6.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.95/6.13         ((k2_enumset1 @ X2 @ X0 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 5.95/6.13      inference('sup+', [status(thm)], ['36', '37'])).
% 5.95/6.13  thf(t72_enumset1, axiom,
% 5.95/6.13    (![A:$i,B:$i,C:$i,D:$i]:
% 5.95/6.13     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 5.95/6.13  thf('39', plain,
% 5.95/6.13      (![X66 : $i, X67 : $i, X68 : $i, X69 : $i]:
% 5.95/6.13         ((k3_enumset1 @ X66 @ X66 @ X67 @ X68 @ X69)
% 5.95/6.13           = (k2_enumset1 @ X66 @ X67 @ X68 @ X69))),
% 5.95/6.13      inference('cnf', [status(esa)], [t72_enumset1])).
% 5.95/6.13  thf('40', plain,
% 5.95/6.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.95/6.13         ((k3_enumset1 @ X0 @ X0 @ X2 @ X1 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 5.95/6.13      inference('sup+', [status(thm)], ['38', '39'])).
% 5.95/6.13  thf('41', plain,
% 5.95/6.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.95/6.13         ((k1_enumset1 @ X1 @ X2 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 5.95/6.13      inference('sup+', [status(thm)], ['22', '23'])).
% 5.95/6.13  thf('42', plain,
% 5.95/6.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.95/6.13         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 5.95/6.13      inference('sup+', [status(thm)], ['29', '30'])).
% 5.95/6.13  thf('43', plain,
% 5.95/6.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.95/6.13         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 5.95/6.13      inference('sup+', [status(thm)], ['41', '42'])).
% 5.95/6.13  thf('44', plain,
% 5.95/6.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.95/6.13         ((k1_enumset1 @ X1 @ X2 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 5.95/6.13      inference('sup+', [status(thm)], ['22', '23'])).
% 5.95/6.13  thf('45', plain,
% 5.95/6.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.95/6.13         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 5.95/6.13      inference('sup+', [status(thm)], ['43', '44'])).
% 5.95/6.13  thf('46', plain,
% 5.95/6.13      (((k1_enumset1 @ sk_B @ sk_C @ sk_A)
% 5.95/6.13         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 5.95/6.13      inference('demod', [status(thm)], ['32', '35', '40', '45'])).
% 5.95/6.13  thf('47', plain, ($false), inference('simplify', [status(thm)], ['46'])).
% 5.95/6.13  
% 5.95/6.13  % SZS output end Refutation
% 5.95/6.13  
% 5.95/6.14  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

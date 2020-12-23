%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.U5zawHurgN

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:38 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 176 expanded)
%              Number of leaves         :   17 (  65 expanded)
%              Depth                    :   13
%              Number of atoms          :  691 (1729 expanded)
%              Number of equality atoms :   67 ( 167 expanded)
%              Maximal formula depth    :   10 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X3 ) @ ( k2_tarski @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf(t105_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ C @ D @ B ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X6 @ X9 @ X7 @ X8 )
      = ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('3',plain,(
    ( k2_enumset1 @ sk_B @ sk_C @ sk_A @ sk_A )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('4',plain,(
    ! [X32: $i] :
      ( ( k2_tarski @ X32 @ X32 )
      = ( k1_tarski @ X32 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('5',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X3 ) @ ( k2_tarski @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['3','6'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_enumset1 @ X33 @ X33 @ X34 )
      = ( k2_tarski @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('9',plain,(
    ! [X32: $i] :
      ( ( k2_tarski @ X32 @ X32 )
      = ( k1_tarski @ X32 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('10',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X3 ) @ ( k2_tarski @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('12',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( k2_enumset1 @ X35 @ X35 @ X36 @ X37 )
      = ( k1_enumset1 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('15',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k2_enumset1 @ X18 @ X19 @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k1_tarski @ X18 ) @ ( k1_enumset1 @ X19 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t108_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ B @ A @ C @ D ) ) )).

thf('17',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k2_enumset1 @ X15 @ X14 @ X16 @ X17 )
      = ( k2_enumset1 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t108_enumset1])).

thf('18',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X6 @ X9 @ X7 @ X8 )
      = ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('19',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( k2_enumset1 @ X35 @ X35 @ X36 @ X37 )
      = ( k1_enumset1 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['16','21'])).

thf('24',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['7','22','23'])).

thf('25',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X6 @ X9 @ X7 @ X8 )
      = ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(t107_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ D @ C @ B ) ) )).

thf('28',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X10 @ X13 @ X12 @ X11 )
      = ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf('29',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( k2_enumset1 @ X35 @ X35 @ X36 @ X37 )
      = ( k1_enumset1 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k2_enumset1 @ X15 @ X14 @ X16 @ X17 )
      = ( k2_enumset1 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t108_enumset1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('35',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X6 @ X9 @ X7 @ X8 )
      = ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('36',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( k2_enumset1 @ X35 @ X35 @ X36 @ X37 )
      = ( k1_enumset1 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('40',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( k2_enumset1 @ X35 @ X35 @ X36 @ X37 )
      = ( k1_enumset1 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_enumset1 @ X33 @ X33 @ X34 )
      = ( k2_tarski @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k2_enumset1 @ X18 @ X19 @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k1_tarski @ X18 ) @ ( k1_enumset1 @ X19 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ( k1_enumset1 @ sk_B @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['24','33','55'])).

thf('57',plain,(
    $false ),
    inference(simplify,[status(thm)],['56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.U5zawHurgN
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:49:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.35/1.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.35/1.58  % Solved by: fo/fo7.sh
% 1.35/1.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.35/1.58  % done 1884 iterations in 1.111s
% 1.35/1.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.35/1.58  % SZS output start Refutation
% 1.35/1.58  thf(sk_A_type, type, sk_A: $i).
% 1.35/1.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.35/1.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.35/1.58  thf(sk_B_type, type, sk_B: $i).
% 1.35/1.58  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.35/1.58  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 1.35/1.58  thf(sk_C_type, type, sk_C: $i).
% 1.35/1.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.35/1.58  thf(t137_enumset1, conjecture,
% 1.35/1.58    (![A:$i,B:$i,C:$i]:
% 1.35/1.58     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 1.35/1.58       ( k1_enumset1 @ A @ B @ C ) ))).
% 1.35/1.58  thf(zf_stmt_0, negated_conjecture,
% 1.35/1.58    (~( ![A:$i,B:$i,C:$i]:
% 1.35/1.58        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 1.35/1.58          ( k1_enumset1 @ A @ B @ C ) ) )),
% 1.35/1.58    inference('cnf.neg', [status(esa)], [t137_enumset1])).
% 1.35/1.58  thf('0', plain,
% 1.35/1.58      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 1.35/1.58         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 1.35/1.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.58  thf(l53_enumset1, axiom,
% 1.35/1.58    (![A:$i,B:$i,C:$i,D:$i]:
% 1.35/1.58     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 1.35/1.58       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 1.35/1.58  thf('1', plain,
% 1.35/1.58      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.35/1.58         ((k2_enumset1 @ X2 @ X3 @ X4 @ X5)
% 1.35/1.58           = (k2_xboole_0 @ (k2_tarski @ X2 @ X3) @ (k2_tarski @ X4 @ X5)))),
% 1.35/1.58      inference('cnf', [status(esa)], [l53_enumset1])).
% 1.35/1.58  thf(t105_enumset1, axiom,
% 1.35/1.58    (![A:$i,B:$i,C:$i,D:$i]:
% 1.35/1.58     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ D @ B ) ))).
% 1.35/1.58  thf('2', plain,
% 1.35/1.58      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 1.35/1.58         ((k2_enumset1 @ X6 @ X9 @ X7 @ X8) = (k2_enumset1 @ X6 @ X7 @ X8 @ X9))),
% 1.35/1.58      inference('cnf', [status(esa)], [t105_enumset1])).
% 1.35/1.58  thf('3', plain,
% 1.35/1.58      (((k2_enumset1 @ sk_B @ sk_C @ sk_A @ sk_A)
% 1.35/1.58         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 1.35/1.58      inference('demod', [status(thm)], ['0', '1', '2'])).
% 1.35/1.58  thf(t69_enumset1, axiom,
% 1.35/1.58    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.35/1.58  thf('4', plain, (![X32 : $i]: ((k2_tarski @ X32 @ X32) = (k1_tarski @ X32))),
% 1.35/1.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.35/1.58  thf('5', plain,
% 1.35/1.58      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.35/1.58         ((k2_enumset1 @ X2 @ X3 @ X4 @ X5)
% 1.35/1.58           = (k2_xboole_0 @ (k2_tarski @ X2 @ X3) @ (k2_tarski @ X4 @ X5)))),
% 1.35/1.58      inference('cnf', [status(esa)], [l53_enumset1])).
% 1.35/1.58  thf('6', plain,
% 1.35/1.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.58         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0)
% 1.35/1.58           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)))),
% 1.35/1.58      inference('sup+', [status(thm)], ['4', '5'])).
% 1.35/1.58  thf('7', plain,
% 1.35/1.58      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_A))
% 1.35/1.58         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 1.35/1.58      inference('demod', [status(thm)], ['3', '6'])).
% 1.35/1.58  thf(t70_enumset1, axiom,
% 1.35/1.58    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.35/1.58  thf('8', plain,
% 1.35/1.58      (![X33 : $i, X34 : $i]:
% 1.35/1.58         ((k1_enumset1 @ X33 @ X33 @ X34) = (k2_tarski @ X33 @ X34))),
% 1.35/1.58      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.35/1.58  thf('9', plain, (![X32 : $i]: ((k2_tarski @ X32 @ X32) = (k1_tarski @ X32))),
% 1.35/1.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.35/1.58  thf('10', plain,
% 1.35/1.58      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.35/1.58         ((k2_enumset1 @ X2 @ X3 @ X4 @ X5)
% 1.35/1.58           = (k2_xboole_0 @ (k2_tarski @ X2 @ X3) @ (k2_tarski @ X4 @ X5)))),
% 1.35/1.58      inference('cnf', [status(esa)], [l53_enumset1])).
% 1.35/1.58  thf('11', plain,
% 1.35/1.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.58         ((k2_enumset1 @ X0 @ X0 @ X2 @ X1)
% 1.35/1.58           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 1.35/1.58      inference('sup+', [status(thm)], ['9', '10'])).
% 1.35/1.58  thf(t71_enumset1, axiom,
% 1.35/1.58    (![A:$i,B:$i,C:$i]:
% 1.35/1.58     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 1.35/1.58  thf('12', plain,
% 1.35/1.58      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.35/1.58         ((k2_enumset1 @ X35 @ X35 @ X36 @ X37)
% 1.35/1.58           = (k1_enumset1 @ X35 @ X36 @ X37))),
% 1.35/1.58      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.35/1.58  thf('13', plain,
% 1.35/1.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.58         ((k1_enumset1 @ X0 @ X2 @ X1)
% 1.35/1.58           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 1.35/1.58      inference('demod', [status(thm)], ['11', '12'])).
% 1.35/1.58  thf('14', plain,
% 1.35/1.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.58         ((k1_enumset1 @ X2 @ X1 @ X0)
% 1.35/1.58           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k1_enumset1 @ X1 @ X1 @ X0)))),
% 1.35/1.58      inference('sup+', [status(thm)], ['8', '13'])).
% 1.35/1.58  thf(t44_enumset1, axiom,
% 1.35/1.58    (![A:$i,B:$i,C:$i,D:$i]:
% 1.35/1.58     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 1.35/1.58       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 1.35/1.58  thf('15', plain,
% 1.35/1.58      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.35/1.58         ((k2_enumset1 @ X18 @ X19 @ X20 @ X21)
% 1.35/1.58           = (k2_xboole_0 @ (k1_tarski @ X18) @ (k1_enumset1 @ X19 @ X20 @ X21)))),
% 1.35/1.58      inference('cnf', [status(esa)], [t44_enumset1])).
% 1.35/1.58  thf('16', plain,
% 1.35/1.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.58         ((k1_enumset1 @ X2 @ X1 @ X0) = (k2_enumset1 @ X2 @ X1 @ X1 @ X0))),
% 1.35/1.58      inference('demod', [status(thm)], ['14', '15'])).
% 1.35/1.58  thf(t108_enumset1, axiom,
% 1.35/1.58    (![A:$i,B:$i,C:$i,D:$i]:
% 1.35/1.58     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ A @ C @ D ) ))).
% 1.35/1.58  thf('17', plain,
% 1.35/1.58      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 1.35/1.58         ((k2_enumset1 @ X15 @ X14 @ X16 @ X17)
% 1.35/1.58           = (k2_enumset1 @ X14 @ X15 @ X16 @ X17))),
% 1.35/1.58      inference('cnf', [status(esa)], [t108_enumset1])).
% 1.35/1.58  thf('18', plain,
% 1.35/1.58      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 1.35/1.58         ((k2_enumset1 @ X6 @ X9 @ X7 @ X8) = (k2_enumset1 @ X6 @ X7 @ X8 @ X9))),
% 1.35/1.58      inference('cnf', [status(esa)], [t105_enumset1])).
% 1.35/1.58  thf('19', plain,
% 1.35/1.58      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.35/1.58         ((k2_enumset1 @ X35 @ X35 @ X36 @ X37)
% 1.35/1.58           = (k1_enumset1 @ X35 @ X36 @ X37))),
% 1.35/1.58      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.35/1.58  thf('20', plain,
% 1.35/1.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.58         ((k2_enumset1 @ X1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 1.35/1.58      inference('sup+', [status(thm)], ['18', '19'])).
% 1.35/1.58  thf('21', plain,
% 1.35/1.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.58         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 1.35/1.58      inference('sup+', [status(thm)], ['17', '20'])).
% 1.35/1.58  thf('22', plain,
% 1.35/1.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.58         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 1.35/1.58      inference('sup+', [status(thm)], ['16', '21'])).
% 1.35/1.58  thf('23', plain,
% 1.35/1.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.58         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 1.35/1.58      inference('sup+', [status(thm)], ['16', '21'])).
% 1.35/1.58  thf('24', plain,
% 1.35/1.58      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_A))
% 1.35/1.58         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 1.35/1.58      inference('demod', [status(thm)], ['7', '22', '23'])).
% 1.35/1.58  thf('25', plain,
% 1.35/1.58      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 1.35/1.58         ((k2_enumset1 @ X6 @ X9 @ X7 @ X8) = (k2_enumset1 @ X6 @ X7 @ X8 @ X9))),
% 1.35/1.58      inference('cnf', [status(esa)], [t105_enumset1])).
% 1.35/1.58  thf('26', plain,
% 1.35/1.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.58         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0)
% 1.35/1.58           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)))),
% 1.35/1.58      inference('sup+', [status(thm)], ['4', '5'])).
% 1.35/1.58  thf('27', plain,
% 1.35/1.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.58         ((k2_enumset1 @ X2 @ X0 @ X1 @ X0)
% 1.35/1.58           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)))),
% 1.35/1.58      inference('sup+', [status(thm)], ['25', '26'])).
% 1.35/1.58  thf(t107_enumset1, axiom,
% 1.35/1.58    (![A:$i,B:$i,C:$i,D:$i]:
% 1.35/1.58     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ D @ C @ B ) ))).
% 1.35/1.58  thf('28', plain,
% 1.35/1.58      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 1.35/1.58         ((k2_enumset1 @ X10 @ X13 @ X12 @ X11)
% 1.35/1.58           = (k2_enumset1 @ X10 @ X11 @ X12 @ X13))),
% 1.35/1.58      inference('cnf', [status(esa)], [t107_enumset1])).
% 1.35/1.58  thf('29', plain,
% 1.35/1.58      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.35/1.58         ((k2_enumset1 @ X35 @ X35 @ X36 @ X37)
% 1.35/1.58           = (k1_enumset1 @ X35 @ X36 @ X37))),
% 1.35/1.58      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.35/1.58  thf('30', plain,
% 1.35/1.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.58         ((k2_enumset1 @ X0 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 1.35/1.58      inference('sup+', [status(thm)], ['28', '29'])).
% 1.35/1.58  thf('31', plain,
% 1.35/1.58      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 1.35/1.58         ((k2_enumset1 @ X15 @ X14 @ X16 @ X17)
% 1.35/1.58           = (k2_enumset1 @ X14 @ X15 @ X16 @ X17))),
% 1.35/1.58      inference('cnf', [status(esa)], [t108_enumset1])).
% 1.35/1.58  thf('32', plain,
% 1.35/1.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.58         ((k2_enumset1 @ X0 @ X2 @ X1 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 1.35/1.58      inference('sup+', [status(thm)], ['30', '31'])).
% 1.35/1.58  thf('33', plain,
% 1.35/1.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.58         ((k1_enumset1 @ X0 @ X1 @ X2)
% 1.35/1.58           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)))),
% 1.35/1.58      inference('demod', [status(thm)], ['27', '32'])).
% 1.35/1.58  thf('34', plain,
% 1.35/1.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.58         ((k1_enumset1 @ X2 @ X1 @ X0) = (k2_enumset1 @ X2 @ X1 @ X1 @ X0))),
% 1.35/1.58      inference('demod', [status(thm)], ['14', '15'])).
% 1.35/1.58  thf('35', plain,
% 1.35/1.58      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 1.35/1.58         ((k2_enumset1 @ X6 @ X9 @ X7 @ X8) = (k2_enumset1 @ X6 @ X7 @ X8 @ X9))),
% 1.35/1.58      inference('cnf', [status(esa)], [t105_enumset1])).
% 1.35/1.58  thf('36', plain,
% 1.35/1.58      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.35/1.58         ((k2_enumset1 @ X35 @ X35 @ X36 @ X37)
% 1.35/1.58           = (k1_enumset1 @ X35 @ X36 @ X37))),
% 1.35/1.58      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.35/1.58  thf('37', plain,
% 1.35/1.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.58         ((k2_enumset1 @ X0 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X2 @ X1))),
% 1.35/1.58      inference('sup+', [status(thm)], ['35', '36'])).
% 1.35/1.58  thf('38', plain,
% 1.35/1.58      (![X0 : $i, X1 : $i]:
% 1.35/1.58         ((k1_enumset1 @ X0 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X1))),
% 1.35/1.58      inference('sup+', [status(thm)], ['34', '37'])).
% 1.35/1.58  thf('39', plain,
% 1.35/1.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.58         ((k2_enumset1 @ X1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 1.35/1.58      inference('sup+', [status(thm)], ['18', '19'])).
% 1.35/1.58  thf('40', plain,
% 1.35/1.58      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.35/1.58         ((k2_enumset1 @ X35 @ X35 @ X36 @ X37)
% 1.35/1.58           = (k1_enumset1 @ X35 @ X36 @ X37))),
% 1.35/1.58      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.35/1.58  thf('41', plain,
% 1.35/1.58      (![X0 : $i, X1 : $i]:
% 1.35/1.58         ((k1_enumset1 @ X0 @ X1 @ X0) = (k1_enumset1 @ X0 @ X0 @ X1))),
% 1.35/1.58      inference('sup+', [status(thm)], ['39', '40'])).
% 1.35/1.58  thf('42', plain,
% 1.35/1.58      (![X33 : $i, X34 : $i]:
% 1.35/1.58         ((k1_enumset1 @ X33 @ X33 @ X34) = (k2_tarski @ X33 @ X34))),
% 1.35/1.58      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.35/1.58  thf('43', plain,
% 1.35/1.58      (![X0 : $i, X1 : $i]:
% 1.35/1.58         ((k1_enumset1 @ X0 @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 1.35/1.58      inference('sup+', [status(thm)], ['41', '42'])).
% 1.35/1.58  thf('44', plain,
% 1.35/1.58      (![X0 : $i, X1 : $i]:
% 1.35/1.58         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 1.35/1.58      inference('sup+', [status(thm)], ['38', '43'])).
% 1.35/1.58  thf('45', plain,
% 1.35/1.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.58         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 1.35/1.58      inference('sup+', [status(thm)], ['17', '20'])).
% 1.35/1.58  thf('46', plain,
% 1.35/1.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.58         ((k2_enumset1 @ X0 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X2 @ X1))),
% 1.35/1.58      inference('sup+', [status(thm)], ['35', '36'])).
% 1.35/1.58  thf('47', plain,
% 1.35/1.58      (![X0 : $i, X1 : $i]:
% 1.35/1.58         ((k1_enumset1 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X1))),
% 1.35/1.58      inference('sup+', [status(thm)], ['45', '46'])).
% 1.35/1.58  thf('48', plain,
% 1.35/1.58      (![X0 : $i, X1 : $i]:
% 1.35/1.58         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X1))),
% 1.35/1.58      inference('sup+', [status(thm)], ['44', '47'])).
% 1.35/1.58  thf('49', plain,
% 1.35/1.58      (![X0 : $i, X1 : $i]:
% 1.35/1.58         ((k1_enumset1 @ X0 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X1))),
% 1.35/1.58      inference('sup+', [status(thm)], ['34', '37'])).
% 1.35/1.58  thf('50', plain,
% 1.35/1.58      (![X0 : $i, X1 : $i]:
% 1.35/1.58         ((k1_enumset1 @ X0 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 1.35/1.58      inference('sup+', [status(thm)], ['48', '49'])).
% 1.35/1.58  thf('51', plain,
% 1.35/1.58      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.35/1.58         ((k2_enumset1 @ X18 @ X19 @ X20 @ X21)
% 1.35/1.58           = (k2_xboole_0 @ (k1_tarski @ X18) @ (k1_enumset1 @ X19 @ X20 @ X21)))),
% 1.35/1.58      inference('cnf', [status(esa)], [t44_enumset1])).
% 1.35/1.58  thf('52', plain,
% 1.35/1.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.58         ((k2_enumset1 @ X2 @ X0 @ X1 @ X0)
% 1.35/1.58           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 1.35/1.58      inference('sup+', [status(thm)], ['50', '51'])).
% 1.35/1.58  thf('53', plain,
% 1.35/1.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.58         ((k2_enumset1 @ X0 @ X2 @ X1 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 1.35/1.58      inference('sup+', [status(thm)], ['30', '31'])).
% 1.35/1.58  thf('54', plain,
% 1.35/1.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.58         ((k1_enumset1 @ X0 @ X2 @ X1)
% 1.35/1.58           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 1.35/1.58      inference('demod', [status(thm)], ['11', '12'])).
% 1.35/1.58  thf('55', plain,
% 1.35/1.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.58         ((k1_enumset1 @ X0 @ X1 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 1.35/1.58      inference('demod', [status(thm)], ['52', '53', '54'])).
% 1.35/1.58  thf('56', plain,
% 1.35/1.58      (((k1_enumset1 @ sk_B @ sk_C @ sk_A)
% 1.35/1.58         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 1.35/1.58      inference('demod', [status(thm)], ['24', '33', '55'])).
% 1.35/1.58  thf('57', plain, ($false), inference('simplify', [status(thm)], ['56'])).
% 1.35/1.58  
% 1.35/1.58  % SZS output end Refutation
% 1.35/1.58  
% 1.35/1.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.N13kj7eplL

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:38 EST 2020

% Result     : Theorem 1.68s
% Output     : Refutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 111 expanded)
%              Number of leaves         :   19 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :  757 (1131 expanded)
%              Number of equality atoms :   68 ( 101 expanded)
%              Maximal formula depth    :   13 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

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

thf(t100_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ B @ C @ A ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X9 @ X7 @ X8 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('2',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X9 @ X7 @ X8 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('3',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k2_tarski @ sk_C @ sk_A ) )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_enumset1 @ X44 @ X44 @ X45 )
      = ( k2_tarski @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(l57_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X3 @ X4 ) @ ( k2_tarski @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('7',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ( k3_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52 )
      = ( k2_enumset1 @ X49 @ X50 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ( k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X9 @ X7 @ X8 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('11',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_enumset1 @ X44 @ X44 @ X45 )
      = ( k2_tarski @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t48_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ) )).

thf('13',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k3_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k2_tarski @ X13 @ X14 ) @ ( k1_enumset1 @ X15 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t48_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X0 @ X1 @ X1 )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('15',plain,(
    ! [X43: $i] :
      ( ( k2_tarski @ X43 @ X43 )
      = ( k1_tarski @ X43 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('16',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X3 @ X4 ) @ ( k2_tarski @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('18',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( k2_enumset1 @ X46 @ X46 @ X47 @ X48 )
      = ( k1_enumset1 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t50_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ) )).

thf('19',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( k3_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X18 @ X19 @ X20 @ X21 ) @ ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ( k3_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52 )
      = ( k2_enumset1 @ X49 @ X50 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X0 @ X1 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','23','24'])).

thf('26',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( k2_enumset1 @ X46 @ X46 @ X47 @ X48 )
      = ( k1_enumset1 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('27',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X9 @ X7 @ X8 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('28',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_enumset1 @ X44 @ X44 @ X45 )
      = ( k2_tarski @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( k2_enumset1 @ X46 @ X46 @ X47 @ X48 )
      = ( k1_enumset1 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('32',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_enumset1 @ X44 @ X44 @ X45 )
      = ( k2_tarski @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( k3_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X18 @ X19 @ X20 @ X21 ) @ ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ( k3_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52 )
      = ( k2_enumset1 @ X49 @ X50 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( k2_enumset1 @ X46 @ X46 @ X47 @ X48 )
      = ( k1_enumset1 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X0 @ X0 @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['30','39'])).

thf('41',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( k3_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X18 @ X19 @ X20 @ X21 ) @ ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

thf(t102_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ C @ B @ A ) ) )).

thf('42',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k1_enumset1 @ X12 @ X11 @ X10 )
      = ( k1_enumset1 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t102_enumset1])).

thf('43',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X9 @ X7 @ X8 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( k2_enumset1 @ X46 @ X46 @ X47 @ X48 )
      = ( k1_enumset1 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X2 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X2 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( k3_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X18 @ X19 @ X20 @ X21 ) @ ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X2 @ X0 @ X3 )
      = ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X0 @ X2 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference(demod,[status(thm)],['40','41','50'])).

thf('52',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X9 @ X7 @ X8 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k2_enumset1 @ X2 @ X0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','53'])).

thf('55',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X9 @ X7 @ X8 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('56',plain,(
    ( k1_enumset1 @ sk_B @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['9','54','55'])).

thf('57',plain,(
    $false ),
    inference(simplify,[status(thm)],['56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.N13kj7eplL
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:47:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.68/1.88  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.68/1.88  % Solved by: fo/fo7.sh
% 1.68/1.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.68/1.88  % done 1783 iterations in 1.403s
% 1.68/1.88  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.68/1.88  % SZS output start Refutation
% 1.68/1.88  thf(sk_B_type, type, sk_B: $i).
% 1.68/1.88  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 1.68/1.88  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 1.68/1.88  thf(sk_C_type, type, sk_C: $i).
% 1.68/1.88  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.68/1.88  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.68/1.88  thf(sk_A_type, type, sk_A: $i).
% 1.68/1.88  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.68/1.88  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.68/1.88  thf(t137_enumset1, conjecture,
% 1.68/1.88    (![A:$i,B:$i,C:$i]:
% 1.68/1.88     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 1.68/1.88       ( k1_enumset1 @ A @ B @ C ) ))).
% 1.68/1.88  thf(zf_stmt_0, negated_conjecture,
% 1.68/1.88    (~( ![A:$i,B:$i,C:$i]:
% 1.68/1.88        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 1.68/1.88          ( k1_enumset1 @ A @ B @ C ) ) )),
% 1.68/1.88    inference('cnf.neg', [status(esa)], [t137_enumset1])).
% 1.68/1.88  thf('0', plain,
% 1.68/1.88      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 1.68/1.88         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 1.68/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.88  thf(t100_enumset1, axiom,
% 1.68/1.88    (![A:$i,B:$i,C:$i]:
% 1.68/1.88     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ B @ C @ A ) ))).
% 1.68/1.88  thf('1', plain,
% 1.68/1.88      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.68/1.88         ((k1_enumset1 @ X9 @ X7 @ X8) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 1.68/1.88      inference('cnf', [status(esa)], [t100_enumset1])).
% 1.68/1.88  thf('2', plain,
% 1.68/1.88      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.68/1.88         ((k1_enumset1 @ X9 @ X7 @ X8) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 1.68/1.88      inference('cnf', [status(esa)], [t100_enumset1])).
% 1.68/1.88  thf('3', plain,
% 1.68/1.88      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 1.68/1.88         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 1.68/1.88      inference('demod', [status(thm)], ['0', '1', '2'])).
% 1.68/1.88  thf(t70_enumset1, axiom,
% 1.68/1.88    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.68/1.88  thf('4', plain,
% 1.68/1.88      (![X44 : $i, X45 : $i]:
% 1.68/1.88         ((k1_enumset1 @ X44 @ X44 @ X45) = (k2_tarski @ X44 @ X45))),
% 1.68/1.88      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.68/1.88  thf(l57_enumset1, axiom,
% 1.68/1.88    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.68/1.88     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 1.68/1.88       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ))).
% 1.68/1.88  thf('5', plain,
% 1.68/1.88      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.68/1.88         ((k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6)
% 1.68/1.88           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X3 @ X4) @ 
% 1.68/1.88              (k2_tarski @ X5 @ X6)))),
% 1.68/1.88      inference('cnf', [status(esa)], [l57_enumset1])).
% 1.68/1.88  thf('6', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.68/1.88         ((k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2)
% 1.68/1.88           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 1.68/1.88      inference('sup+', [status(thm)], ['4', '5'])).
% 1.68/1.88  thf(t72_enumset1, axiom,
% 1.68/1.88    (![A:$i,B:$i,C:$i,D:$i]:
% 1.68/1.88     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 1.68/1.88  thf('7', plain,
% 1.68/1.88      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 1.68/1.88         ((k3_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52)
% 1.68/1.88           = (k2_enumset1 @ X49 @ X50 @ X51 @ X52))),
% 1.68/1.88      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.68/1.88  thf('8', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.68/1.88         ((k2_enumset1 @ X1 @ X0 @ X3 @ X2)
% 1.68/1.88           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 1.68/1.88      inference('demod', [status(thm)], ['6', '7'])).
% 1.68/1.88  thf('9', plain,
% 1.68/1.88      (((k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A)
% 1.68/1.88         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 1.68/1.88      inference('demod', [status(thm)], ['3', '8'])).
% 1.68/1.88  thf('10', plain,
% 1.68/1.88      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.68/1.88         ((k1_enumset1 @ X9 @ X7 @ X8) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 1.68/1.88      inference('cnf', [status(esa)], [t100_enumset1])).
% 1.68/1.88  thf('11', plain,
% 1.68/1.88      (![X44 : $i, X45 : $i]:
% 1.68/1.88         ((k1_enumset1 @ X44 @ X44 @ X45) = (k2_tarski @ X44 @ X45))),
% 1.68/1.88      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.68/1.88  thf('12', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i]:
% 1.68/1.88         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X0 @ X1))),
% 1.68/1.88      inference('sup+', [status(thm)], ['10', '11'])).
% 1.68/1.88  thf(t48_enumset1, axiom,
% 1.68/1.88    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.68/1.88     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 1.68/1.88       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ))).
% 1.68/1.88  thf('13', plain,
% 1.68/1.88      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 1.68/1.88         ((k3_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17)
% 1.68/1.88           = (k2_xboole_0 @ (k2_tarski @ X13 @ X14) @ 
% 1.68/1.88              (k1_enumset1 @ X15 @ X16 @ X17)))),
% 1.68/1.88      inference('cnf', [status(esa)], [t48_enumset1])).
% 1.68/1.88  thf('14', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.68/1.88         ((k3_enumset1 @ X3 @ X2 @ X0 @ X1 @ X1)
% 1.68/1.88           = (k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0)))),
% 1.68/1.88      inference('sup+', [status(thm)], ['12', '13'])).
% 1.68/1.88  thf(t69_enumset1, axiom,
% 1.68/1.88    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.68/1.88  thf('15', plain,
% 1.68/1.88      (![X43 : $i]: ((k2_tarski @ X43 @ X43) = (k1_tarski @ X43))),
% 1.68/1.88      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.68/1.88  thf('16', plain,
% 1.68/1.88      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.68/1.88         ((k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6)
% 1.68/1.88           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X3 @ X4) @ 
% 1.68/1.88              (k2_tarski @ X5 @ X6)))),
% 1.68/1.88      inference('cnf', [status(esa)], [l57_enumset1])).
% 1.68/1.88  thf('17', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.68/1.88         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0)
% 1.68/1.88           = (k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0)))),
% 1.68/1.88      inference('sup+', [status(thm)], ['15', '16'])).
% 1.68/1.88  thf(t71_enumset1, axiom,
% 1.68/1.88    (![A:$i,B:$i,C:$i]:
% 1.68/1.88     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 1.68/1.88  thf('18', plain,
% 1.68/1.88      (![X46 : $i, X47 : $i, X48 : $i]:
% 1.68/1.88         ((k2_enumset1 @ X46 @ X46 @ X47 @ X48)
% 1.68/1.88           = (k1_enumset1 @ X46 @ X47 @ X48))),
% 1.68/1.88      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.68/1.88  thf(t50_enumset1, axiom,
% 1.68/1.88    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.68/1.88     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 1.68/1.88       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ))).
% 1.68/1.88  thf('19', plain,
% 1.68/1.88      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.68/1.88         ((k3_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22)
% 1.68/1.88           = (k2_xboole_0 @ (k2_enumset1 @ X18 @ X19 @ X20 @ X21) @ 
% 1.68/1.88              (k1_tarski @ X22)))),
% 1.68/1.88      inference('cnf', [status(esa)], [t50_enumset1])).
% 1.68/1.88  thf('20', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.68/1.88         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3)
% 1.68/1.88           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 1.68/1.88      inference('sup+', [status(thm)], ['18', '19'])).
% 1.68/1.88  thf('21', plain,
% 1.68/1.88      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 1.68/1.88         ((k3_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52)
% 1.68/1.88           = (k2_enumset1 @ X49 @ X50 @ X51 @ X52))),
% 1.68/1.88      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.68/1.88  thf('22', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.68/1.88         ((k2_enumset1 @ X2 @ X1 @ X0 @ X3)
% 1.68/1.88           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 1.68/1.88      inference('demod', [status(thm)], ['20', '21'])).
% 1.68/1.88  thf('23', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.68/1.88         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0)
% 1.68/1.88           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 1.68/1.88      inference('demod', [status(thm)], ['17', '22'])).
% 1.68/1.88  thf('24', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.68/1.88         ((k2_enumset1 @ X1 @ X0 @ X3 @ X2)
% 1.68/1.88           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 1.68/1.88      inference('demod', [status(thm)], ['6', '7'])).
% 1.68/1.88  thf('25', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.68/1.88         ((k2_enumset1 @ X3 @ X2 @ X0 @ X1) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 1.68/1.88      inference('demod', [status(thm)], ['14', '23', '24'])).
% 1.68/1.88  thf('26', plain,
% 1.68/1.88      (![X46 : $i, X47 : $i, X48 : $i]:
% 1.68/1.88         ((k2_enumset1 @ X46 @ X46 @ X47 @ X48)
% 1.68/1.88           = (k1_enumset1 @ X46 @ X47 @ X48))),
% 1.68/1.88      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.68/1.88  thf('27', plain,
% 1.68/1.88      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.68/1.88         ((k1_enumset1 @ X9 @ X7 @ X8) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 1.68/1.88      inference('cnf', [status(esa)], [t100_enumset1])).
% 1.68/1.88  thf('28', plain,
% 1.68/1.88      (![X44 : $i, X45 : $i]:
% 1.68/1.88         ((k1_enumset1 @ X44 @ X44 @ X45) = (k2_tarski @ X44 @ X45))),
% 1.68/1.88      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.68/1.88  thf('29', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i]:
% 1.68/1.88         ((k1_enumset1 @ X0 @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 1.68/1.88      inference('sup+', [status(thm)], ['27', '28'])).
% 1.68/1.88  thf('30', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i]:
% 1.68/1.88         ((k2_enumset1 @ X0 @ X0 @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 1.68/1.88      inference('sup+', [status(thm)], ['26', '29'])).
% 1.68/1.88  thf('31', plain,
% 1.68/1.88      (![X46 : $i, X47 : $i, X48 : $i]:
% 1.68/1.88         ((k2_enumset1 @ X46 @ X46 @ X47 @ X48)
% 1.68/1.88           = (k1_enumset1 @ X46 @ X47 @ X48))),
% 1.68/1.88      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.68/1.88  thf('32', plain,
% 1.68/1.88      (![X44 : $i, X45 : $i]:
% 1.68/1.88         ((k1_enumset1 @ X44 @ X44 @ X45) = (k2_tarski @ X44 @ X45))),
% 1.68/1.88      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.68/1.88  thf('33', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i]:
% 1.68/1.88         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 1.68/1.88      inference('sup+', [status(thm)], ['31', '32'])).
% 1.68/1.88  thf('34', plain,
% 1.68/1.88      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.68/1.88         ((k3_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22)
% 1.68/1.88           = (k2_xboole_0 @ (k2_enumset1 @ X18 @ X19 @ X20 @ X21) @ 
% 1.68/1.88              (k1_tarski @ X22)))),
% 1.68/1.88      inference('cnf', [status(esa)], [t50_enumset1])).
% 1.68/1.88  thf('35', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.68/1.88         ((k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2)
% 1.68/1.88           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 1.68/1.88      inference('sup+', [status(thm)], ['33', '34'])).
% 1.68/1.88  thf('36', plain,
% 1.68/1.88      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 1.68/1.88         ((k3_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52)
% 1.68/1.88           = (k2_enumset1 @ X49 @ X50 @ X51 @ X52))),
% 1.68/1.88      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.68/1.88  thf('37', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.68/1.88         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 1.68/1.88           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 1.68/1.88      inference('demod', [status(thm)], ['35', '36'])).
% 1.68/1.88  thf('38', plain,
% 1.68/1.88      (![X46 : $i, X47 : $i, X48 : $i]:
% 1.68/1.88         ((k2_enumset1 @ X46 @ X46 @ X47 @ X48)
% 1.68/1.88           = (k1_enumset1 @ X46 @ X47 @ X48))),
% 1.68/1.88      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.68/1.88  thf('39', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.68/1.88         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 1.68/1.88           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 1.68/1.88      inference('sup+', [status(thm)], ['37', '38'])).
% 1.68/1.88  thf('40', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.68/1.88         ((k2_xboole_0 @ (k2_enumset1 @ X0 @ X0 @ X1 @ X0) @ (k1_tarski @ X2))
% 1.68/1.88           = (k1_enumset1 @ X0 @ X1 @ X2))),
% 1.68/1.88      inference('sup+', [status(thm)], ['30', '39'])).
% 1.68/1.88  thf('41', plain,
% 1.68/1.88      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.68/1.88         ((k3_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22)
% 1.68/1.88           = (k2_xboole_0 @ (k2_enumset1 @ X18 @ X19 @ X20 @ X21) @ 
% 1.68/1.88              (k1_tarski @ X22)))),
% 1.68/1.88      inference('cnf', [status(esa)], [t50_enumset1])).
% 1.68/1.88  thf(t102_enumset1, axiom,
% 1.68/1.88    (![A:$i,B:$i,C:$i]:
% 1.68/1.88     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ C @ B @ A ) ))).
% 1.68/1.88  thf('42', plain,
% 1.68/1.88      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.68/1.88         ((k1_enumset1 @ X12 @ X11 @ X10) = (k1_enumset1 @ X10 @ X11 @ X12))),
% 1.68/1.88      inference('cnf', [status(esa)], [t102_enumset1])).
% 1.68/1.88  thf('43', plain,
% 1.68/1.88      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.68/1.88         ((k1_enumset1 @ X9 @ X7 @ X8) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 1.68/1.88      inference('cnf', [status(esa)], [t100_enumset1])).
% 1.68/1.88  thf('44', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.68/1.88         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 1.68/1.88      inference('sup+', [status(thm)], ['42', '43'])).
% 1.68/1.88  thf('45', plain,
% 1.68/1.88      (![X46 : $i, X47 : $i, X48 : $i]:
% 1.68/1.88         ((k2_enumset1 @ X46 @ X46 @ X47 @ X48)
% 1.68/1.88           = (k1_enumset1 @ X46 @ X47 @ X48))),
% 1.68/1.88      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.68/1.88  thf('46', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.68/1.88         ((k2_enumset1 @ X1 @ X1 @ X2 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 1.68/1.88      inference('sup+', [status(thm)], ['44', '45'])).
% 1.68/1.88  thf('47', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.68/1.88         ((k2_enumset1 @ X2 @ X1 @ X0 @ X3)
% 1.68/1.88           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 1.68/1.88      inference('demod', [status(thm)], ['20', '21'])).
% 1.68/1.88  thf('48', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.68/1.88         ((k2_enumset1 @ X1 @ X2 @ X0 @ X3)
% 1.68/1.88           = (k2_xboole_0 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0) @ 
% 1.68/1.88              (k1_tarski @ X3)))),
% 1.68/1.88      inference('sup+', [status(thm)], ['46', '47'])).
% 1.68/1.88  thf('49', plain,
% 1.68/1.88      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.68/1.88         ((k3_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22)
% 1.68/1.88           = (k2_xboole_0 @ (k2_enumset1 @ X18 @ X19 @ X20 @ X21) @ 
% 1.68/1.88              (k1_tarski @ X22)))),
% 1.68/1.88      inference('cnf', [status(esa)], [t50_enumset1])).
% 1.68/1.88  thf('50', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.68/1.88         ((k2_enumset1 @ X1 @ X2 @ X0 @ X3)
% 1.68/1.88           = (k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3))),
% 1.68/1.88      inference('demod', [status(thm)], ['48', '49'])).
% 1.68/1.88  thf('51', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.68/1.88         ((k2_enumset1 @ X1 @ X0 @ X0 @ X2) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 1.68/1.88      inference('demod', [status(thm)], ['40', '41', '50'])).
% 1.68/1.88  thf('52', plain,
% 1.68/1.88      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.68/1.88         ((k1_enumset1 @ X9 @ X7 @ X8) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 1.68/1.88      inference('cnf', [status(esa)], [t100_enumset1])).
% 1.68/1.88  thf('53', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.68/1.88         ((k1_enumset1 @ X0 @ X1 @ X2) = (k2_enumset1 @ X2 @ X1 @ X1 @ X0))),
% 1.68/1.88      inference('sup+', [status(thm)], ['51', '52'])).
% 1.68/1.88  thf('54', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.68/1.88         ((k1_enumset1 @ X1 @ X0 @ X2) = (k2_enumset1 @ X2 @ X0 @ X1 @ X0))),
% 1.68/1.88      inference('sup+', [status(thm)], ['25', '53'])).
% 1.68/1.88  thf('55', plain,
% 1.68/1.88      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.68/1.88         ((k1_enumset1 @ X9 @ X7 @ X8) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 1.68/1.88      inference('cnf', [status(esa)], [t100_enumset1])).
% 1.68/1.88  thf('56', plain,
% 1.68/1.88      (((k1_enumset1 @ sk_B @ sk_C @ sk_A)
% 1.68/1.88         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 1.68/1.88      inference('demod', [status(thm)], ['9', '54', '55'])).
% 1.68/1.88  thf('57', plain, ($false), inference('simplify', [status(thm)], ['56'])).
% 1.68/1.88  
% 1.68/1.88  % SZS output end Refutation
% 1.68/1.88  
% 1.68/1.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

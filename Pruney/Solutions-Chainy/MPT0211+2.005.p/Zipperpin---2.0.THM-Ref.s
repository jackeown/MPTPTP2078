%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7qysUiFpip

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:30 EST 2020

% Result     : Theorem 5.93s
% Output     : Refutation 5.93s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 264 expanded)
%              Number of leaves         :   24 (  96 expanded)
%              Depth                    :   13
%              Number of atoms          : 1200 (2851 expanded)
%              Number of equality atoms :  102 ( 252 expanded)
%              Maximal formula depth    :   16 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_enumset1 @ X40 @ X40 @ X41 )
      = ( k2_tarski @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(l57_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X5 @ X6 ) @ ( k2_tarski @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('4',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( k3_enumset1 @ X45 @ X45 @ X46 @ X47 @ X48 )
      = ( k2_enumset1 @ X45 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ( k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_enumset1 @ X40 @ X40 @ X41 )
      = ( k2_tarski @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_tarski @ X3 @ X2 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('10',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( k2_enumset1 @ X42 @ X42 @ X43 @ X44 )
      = ( k1_enumset1 @ X42 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_enumset1 @ X40 @ X40 @ X41 )
      = ( k2_tarski @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('13',plain,(
    ! [X39: $i] :
      ( ( k2_tarski @ X39 @ X39 )
      = ( k1_tarski @ X39 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X5 @ X6 ) @ ( k2_tarski @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( k3_enumset1 @ X45 @ X45 @ X46 @ X47 @ X48 )
      = ( k2_enumset1 @ X45 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','20'])).

thf(t47_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ) )).

thf('22',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k3_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k1_tarski @ X15 ) @ ( k2_enumset1 @ X16 @ X17 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('23',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( k4_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52 @ X53 )
      = ( k3_enumset1 @ X49 @ X50 @ X51 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('24',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_enumset1 @ X40 @ X40 @ X41 )
      = ( k2_tarski @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('25',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X5 @ X6 ) @ ( k2_tarski @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X3 @ X2 ) @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(l62_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ) )).

thf('27',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k4_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X9 @ X10 @ X11 ) @ ( k1_enumset1 @ X12 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l62_enumset1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','28'])).

thf('30',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( k3_enumset1 @ X45 @ X45 @ X46 @ X47 @ X48 )
      = ( k2_enumset1 @ X45 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('34',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( k2_enumset1 @ X42 @ X42 @ X43 @ X44 )
      = ( k1_enumset1 @ X42 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_enumset1 @ X0 @ X1 @ X1 @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k3_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k1_tarski @ X15 ) @ ( k2_enumset1 @ X16 @ X17 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ( k1_enumset1 @ sk_B @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['6','39'])).

thf('41',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_tarski @ X3 @ X2 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('43',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_enumset1 @ X40 @ X40 @ X41 )
      = ( k2_tarski @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X39: $i] :
      ( ( k2_tarski @ X39 @ X39 )
      = ( k1_tarski @ X39 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('46',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X5 @ X6 ) @ ( k2_tarski @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X1 @ X2 @ X2 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( k3_enumset1 @ X45 @ X45 @ X46 @ X47 @ X48 )
      = ( k2_enumset1 @ X45 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X2 @ X2 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X39: $i] :
      ( ( k2_tarski @ X39 @ X39 )
      = ( k1_tarski @ X39 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('52',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_tarski @ X3 @ X2 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('53',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X5 @ X6 ) @ ( k2_tarski @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','54'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('56',plain,(
    ! [X54: $i,X55: $i,X56: $i,X57: $i,X58: $i,X59: $i] :
      ( ( k5_enumset1 @ X54 @ X54 @ X55 @ X56 @ X57 @ X58 @ X59 )
      = ( k4_enumset1 @ X54 @ X55 @ X56 @ X57 @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('57',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( k4_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52 @ X53 )
      = ( k3_enumset1 @ X49 @ X50 @ X51 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X39: $i] :
      ( ( k2_tarski @ X39 @ X39 )
      = ( k1_tarski @ X39 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t60_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ) )).

thf('60',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( k5_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 ) @ ( k2_tarski @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t60_enumset1])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf(t55_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ) )).

thf('62',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k4_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 ) @ ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t55_enumset1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','63'])).

thf('65',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( k4_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52 @ X53 )
      = ( k3_enumset1 @ X49 @ X50 @ X51 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('66',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( k3_enumset1 @ X45 @ X45 @ X46 @ X47 @ X48 )
      = ( k2_enumset1 @ X45 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['55','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X2 @ X2 )
      = ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['50','69'])).

thf('71',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( k2_enumset1 @ X42 @ X42 @ X43 @ X44 )
      = ( k1_enumset1 @ X42 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_enumset1 @ X40 @ X40 @ X41 )
      = ( k2_tarski @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X0 @ X2 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( k3_enumset1 @ X45 @ X45 @ X46 @ X47 @ X48 )
      = ( k2_enumset1 @ X45 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X2 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X2 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['72','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['41','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X2 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['72','77'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X2 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_tarski @ X3 @ X2 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ( k1_enumset1 @ sk_B @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['40','81','86'])).

thf('88',plain,(
    $false ),
    inference(simplify,[status(thm)],['87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7qysUiFpip
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 21:05:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 5.93/6.18  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.93/6.18  % Solved by: fo/fo7.sh
% 5.93/6.18  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.93/6.18  % done 5615 iterations in 5.736s
% 5.93/6.18  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.93/6.18  % SZS output start Refutation
% 5.93/6.18  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 5.93/6.18  thf(sk_C_type, type, sk_C: $i).
% 5.93/6.18  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 5.93/6.18  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 5.93/6.18  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 5.93/6.18  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 5.93/6.18  thf(sk_A_type, type, sk_A: $i).
% 5.93/6.18  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 5.93/6.18  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 5.93/6.18  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 5.93/6.18  thf(sk_B_type, type, sk_B: $i).
% 5.93/6.18  thf(t137_enumset1, conjecture,
% 5.93/6.18    (![A:$i,B:$i,C:$i]:
% 5.93/6.18     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 5.93/6.18       ( k1_enumset1 @ A @ B @ C ) ))).
% 5.93/6.18  thf(zf_stmt_0, negated_conjecture,
% 5.93/6.18    (~( ![A:$i,B:$i,C:$i]:
% 5.93/6.18        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 5.93/6.18          ( k1_enumset1 @ A @ B @ C ) ) )),
% 5.93/6.18    inference('cnf.neg', [status(esa)], [t137_enumset1])).
% 5.93/6.18  thf('0', plain,
% 5.93/6.18      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 5.93/6.18         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 5.93/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.93/6.18  thf(t70_enumset1, axiom,
% 5.93/6.18    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 5.93/6.18  thf('1', plain,
% 5.93/6.18      (![X40 : $i, X41 : $i]:
% 5.93/6.18         ((k1_enumset1 @ X40 @ X40 @ X41) = (k2_tarski @ X40 @ X41))),
% 5.93/6.18      inference('cnf', [status(esa)], [t70_enumset1])).
% 5.93/6.18  thf(l57_enumset1, axiom,
% 5.93/6.18    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 5.93/6.18     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 5.93/6.18       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ))).
% 5.93/6.18  thf('2', plain,
% 5.93/6.18      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 5.93/6.18         ((k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8)
% 5.93/6.18           = (k2_xboole_0 @ (k1_enumset1 @ X4 @ X5 @ X6) @ 
% 5.93/6.18              (k2_tarski @ X7 @ X8)))),
% 5.93/6.18      inference('cnf', [status(esa)], [l57_enumset1])).
% 5.93/6.18  thf('3', plain,
% 5.93/6.18      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.93/6.18         ((k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2)
% 5.93/6.18           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 5.93/6.18      inference('sup+', [status(thm)], ['1', '2'])).
% 5.93/6.18  thf(t72_enumset1, axiom,
% 5.93/6.18    (![A:$i,B:$i,C:$i,D:$i]:
% 5.93/6.18     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 5.93/6.18  thf('4', plain,
% 5.93/6.18      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 5.93/6.18         ((k3_enumset1 @ X45 @ X45 @ X46 @ X47 @ X48)
% 5.93/6.18           = (k2_enumset1 @ X45 @ X46 @ X47 @ X48))),
% 5.93/6.18      inference('cnf', [status(esa)], [t72_enumset1])).
% 5.93/6.18  thf('5', plain,
% 5.93/6.18      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.93/6.18         ((k2_enumset1 @ X1 @ X0 @ X3 @ X2)
% 5.93/6.18           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 5.93/6.18      inference('demod', [status(thm)], ['3', '4'])).
% 5.93/6.18  thf('6', plain,
% 5.93/6.18      (((k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A)
% 5.93/6.18         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 5.93/6.18      inference('demod', [status(thm)], ['0', '5'])).
% 5.93/6.18  thf('7', plain,
% 5.93/6.18      (![X40 : $i, X41 : $i]:
% 5.93/6.18         ((k1_enumset1 @ X40 @ X40 @ X41) = (k2_tarski @ X40 @ X41))),
% 5.93/6.18      inference('cnf', [status(esa)], [t70_enumset1])).
% 5.93/6.18  thf(commutativity_k2_tarski, axiom,
% 5.93/6.18    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 5.93/6.18  thf('8', plain,
% 5.93/6.18      (![X2 : $i, X3 : $i]: ((k2_tarski @ X3 @ X2) = (k2_tarski @ X2 @ X3))),
% 5.93/6.18      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 5.93/6.18  thf('9', plain,
% 5.93/6.18      (![X0 : $i, X1 : $i]:
% 5.93/6.18         ((k2_tarski @ X0 @ X1) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 5.93/6.18      inference('sup+', [status(thm)], ['7', '8'])).
% 5.93/6.18  thf(t71_enumset1, axiom,
% 5.93/6.18    (![A:$i,B:$i,C:$i]:
% 5.93/6.18     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 5.93/6.18  thf('10', plain,
% 5.93/6.18      (![X42 : $i, X43 : $i, X44 : $i]:
% 5.93/6.18         ((k2_enumset1 @ X42 @ X42 @ X43 @ X44)
% 5.93/6.18           = (k1_enumset1 @ X42 @ X43 @ X44))),
% 5.93/6.18      inference('cnf', [status(esa)], [t71_enumset1])).
% 5.93/6.18  thf('11', plain,
% 5.93/6.18      (![X0 : $i, X1 : $i]:
% 5.93/6.18         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 5.93/6.18      inference('sup+', [status(thm)], ['9', '10'])).
% 5.93/6.18  thf('12', plain,
% 5.93/6.18      (![X40 : $i, X41 : $i]:
% 5.93/6.18         ((k1_enumset1 @ X40 @ X40 @ X41) = (k2_tarski @ X40 @ X41))),
% 5.93/6.18      inference('cnf', [status(esa)], [t70_enumset1])).
% 5.93/6.18  thf(t69_enumset1, axiom,
% 5.93/6.18    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 5.93/6.18  thf('13', plain,
% 5.93/6.18      (![X39 : $i]: ((k2_tarski @ X39 @ X39) = (k1_tarski @ X39))),
% 5.93/6.18      inference('cnf', [status(esa)], [t69_enumset1])).
% 5.93/6.18  thf('14', plain,
% 5.93/6.18      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 5.93/6.18      inference('sup+', [status(thm)], ['12', '13'])).
% 5.93/6.18  thf('15', plain,
% 5.93/6.18      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 5.93/6.18         ((k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8)
% 5.93/6.18           = (k2_xboole_0 @ (k1_enumset1 @ X4 @ X5 @ X6) @ 
% 5.93/6.18              (k2_tarski @ X7 @ X8)))),
% 5.93/6.18      inference('cnf', [status(esa)], [l57_enumset1])).
% 5.93/6.18  thf('16', plain,
% 5.93/6.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.93/6.18         ((k3_enumset1 @ X0 @ X0 @ X0 @ X2 @ X1)
% 5.93/6.18           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 5.93/6.18      inference('sup+', [status(thm)], ['14', '15'])).
% 5.93/6.18  thf('17', plain,
% 5.93/6.18      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 5.93/6.18         ((k3_enumset1 @ X45 @ X45 @ X46 @ X47 @ X48)
% 5.93/6.18           = (k2_enumset1 @ X45 @ X46 @ X47 @ X48))),
% 5.93/6.18      inference('cnf', [status(esa)], [t72_enumset1])).
% 5.93/6.18  thf('18', plain,
% 5.93/6.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.93/6.18         ((k2_enumset1 @ X0 @ X0 @ X2 @ X1)
% 5.93/6.18           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 5.93/6.18      inference('demod', [status(thm)], ['16', '17'])).
% 5.93/6.18  thf('19', plain,
% 5.93/6.18      (![X0 : $i, X1 : $i]:
% 5.93/6.18         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 5.93/6.18      inference('sup+', [status(thm)], ['9', '10'])).
% 5.93/6.18  thf('20', plain,
% 5.93/6.18      (![X0 : $i, X1 : $i]:
% 5.93/6.18         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 5.93/6.18           = (k2_tarski @ X0 @ X1))),
% 5.93/6.18      inference('sup+', [status(thm)], ['18', '19'])).
% 5.93/6.18  thf('21', plain,
% 5.93/6.18      (![X0 : $i, X1 : $i]:
% 5.93/6.18         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k2_enumset1 @ X1 @ X1 @ X1 @ X0))
% 5.93/6.18           = (k2_tarski @ X1 @ X0))),
% 5.93/6.18      inference('sup+', [status(thm)], ['11', '20'])).
% 5.93/6.18  thf(t47_enumset1, axiom,
% 5.93/6.18    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 5.93/6.18     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 5.93/6.18       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ))).
% 5.93/6.18  thf('22', plain,
% 5.93/6.18      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 5.93/6.18         ((k3_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19)
% 5.93/6.18           = (k2_xboole_0 @ (k1_tarski @ X15) @ 
% 5.93/6.18              (k2_enumset1 @ X16 @ X17 @ X18 @ X19)))),
% 5.93/6.18      inference('cnf', [status(esa)], [t47_enumset1])).
% 5.93/6.18  thf(t73_enumset1, axiom,
% 5.93/6.18    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 5.93/6.18     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 5.93/6.18       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 5.93/6.18  thf('23', plain,
% 5.93/6.18      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 5.93/6.18         ((k4_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52 @ X53)
% 5.93/6.18           = (k3_enumset1 @ X49 @ X50 @ X51 @ X52 @ X53))),
% 5.93/6.18      inference('cnf', [status(esa)], [t73_enumset1])).
% 5.93/6.18  thf('24', plain,
% 5.93/6.18      (![X40 : $i, X41 : $i]:
% 5.93/6.18         ((k1_enumset1 @ X40 @ X40 @ X41) = (k2_tarski @ X40 @ X41))),
% 5.93/6.18      inference('cnf', [status(esa)], [t70_enumset1])).
% 5.93/6.18  thf('25', plain,
% 5.93/6.18      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 5.93/6.18         ((k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8)
% 5.93/6.18           = (k2_xboole_0 @ (k1_enumset1 @ X4 @ X5 @ X6) @ 
% 5.93/6.18              (k2_tarski @ X7 @ X8)))),
% 5.93/6.18      inference('cnf', [status(esa)], [l57_enumset1])).
% 5.93/6.18  thf('26', plain,
% 5.93/6.18      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 5.93/6.18         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 5.93/6.18           = (k2_xboole_0 @ (k1_enumset1 @ X4 @ X3 @ X2) @ 
% 5.93/6.18              (k1_enumset1 @ X1 @ X1 @ X0)))),
% 5.93/6.18      inference('sup+', [status(thm)], ['24', '25'])).
% 5.93/6.18  thf(l62_enumset1, axiom,
% 5.93/6.18    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 5.93/6.18     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 5.93/6.18       ( k2_xboole_0 @
% 5.93/6.18         ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ))).
% 5.93/6.18  thf('27', plain,
% 5.93/6.18      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 5.93/6.18         ((k4_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14)
% 5.93/6.18           = (k2_xboole_0 @ (k1_enumset1 @ X9 @ X10 @ X11) @ 
% 5.93/6.18              (k1_enumset1 @ X12 @ X13 @ X14)))),
% 5.93/6.18      inference('cnf', [status(esa)], [l62_enumset1])).
% 5.93/6.18  thf('28', plain,
% 5.93/6.18      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 5.93/6.18         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 5.93/6.18           = (k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X1 @ X0))),
% 5.93/6.18      inference('demod', [status(thm)], ['26', '27'])).
% 5.93/6.18  thf('29', plain,
% 5.93/6.18      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.93/6.18         ((k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0)
% 5.93/6.18           = (k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0))),
% 5.93/6.18      inference('sup+', [status(thm)], ['23', '28'])).
% 5.93/6.18  thf('30', plain,
% 5.93/6.18      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 5.93/6.18         ((k3_enumset1 @ X45 @ X45 @ X46 @ X47 @ X48)
% 5.93/6.18           = (k2_enumset1 @ X45 @ X46 @ X47 @ X48))),
% 5.93/6.18      inference('cnf', [status(esa)], [t72_enumset1])).
% 5.93/6.18  thf('31', plain,
% 5.93/6.18      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.93/6.18         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 5.93/6.18           = (k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0))),
% 5.93/6.18      inference('demod', [status(thm)], ['29', '30'])).
% 5.93/6.18  thf('32', plain,
% 5.93/6.18      (![X0 : $i, X1 : $i]:
% 5.93/6.18         ((k2_enumset1 @ X0 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 5.93/6.18      inference('demod', [status(thm)], ['21', '22', '31'])).
% 5.93/6.18  thf('33', plain,
% 5.93/6.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.93/6.18         ((k2_enumset1 @ X0 @ X0 @ X2 @ X1)
% 5.93/6.18           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 5.93/6.18      inference('demod', [status(thm)], ['16', '17'])).
% 5.93/6.18  thf('34', plain,
% 5.93/6.18      (![X42 : $i, X43 : $i, X44 : $i]:
% 5.93/6.18         ((k2_enumset1 @ X42 @ X42 @ X43 @ X44)
% 5.93/6.18           = (k1_enumset1 @ X42 @ X43 @ X44))),
% 5.93/6.18      inference('cnf', [status(esa)], [t71_enumset1])).
% 5.93/6.18  thf('35', plain,
% 5.93/6.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.93/6.18         ((k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0))
% 5.93/6.18           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 5.93/6.18      inference('sup+', [status(thm)], ['33', '34'])).
% 5.93/6.18  thf('36', plain,
% 5.93/6.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.93/6.18         ((k2_xboole_0 @ (k1_tarski @ X2) @ (k2_enumset1 @ X0 @ X1 @ X1 @ X0))
% 5.93/6.18           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 5.93/6.18      inference('sup+', [status(thm)], ['32', '35'])).
% 5.93/6.18  thf('37', plain,
% 5.93/6.18      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 5.93/6.18         ((k3_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19)
% 5.93/6.18           = (k2_xboole_0 @ (k1_tarski @ X15) @ 
% 5.93/6.18              (k2_enumset1 @ X16 @ X17 @ X18 @ X19)))),
% 5.93/6.18      inference('cnf', [status(esa)], [t47_enumset1])).
% 5.93/6.18  thf('38', plain,
% 5.93/6.18      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.93/6.18         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 5.93/6.18           = (k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0))),
% 5.93/6.18      inference('demod', [status(thm)], ['29', '30'])).
% 5.93/6.18  thf('39', plain,
% 5.93/6.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.93/6.18         ((k2_enumset1 @ X2 @ X0 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 5.93/6.18      inference('demod', [status(thm)], ['36', '37', '38'])).
% 5.93/6.18  thf('40', plain,
% 5.93/6.18      (((k1_enumset1 @ sk_B @ sk_C @ sk_A)
% 5.93/6.18         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 5.93/6.18      inference('demod', [status(thm)], ['6', '39'])).
% 5.93/6.18  thf('41', plain,
% 5.93/6.18      (![X2 : $i, X3 : $i]: ((k2_tarski @ X3 @ X2) = (k2_tarski @ X2 @ X3))),
% 5.93/6.18      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 5.93/6.18  thf('42', plain,
% 5.93/6.18      (![X0 : $i, X1 : $i]:
% 5.93/6.18         ((k2_tarski @ X0 @ X1) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 5.93/6.18      inference('sup+', [status(thm)], ['7', '8'])).
% 5.93/6.18  thf('43', plain,
% 5.93/6.18      (![X40 : $i, X41 : $i]:
% 5.93/6.18         ((k1_enumset1 @ X40 @ X40 @ X41) = (k2_tarski @ X40 @ X41))),
% 5.93/6.18      inference('cnf', [status(esa)], [t70_enumset1])).
% 5.93/6.18  thf('44', plain,
% 5.93/6.18      (![X0 : $i, X1 : $i]:
% 5.93/6.18         ((k1_enumset1 @ X0 @ X0 @ X1) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 5.93/6.18      inference('sup+', [status(thm)], ['42', '43'])).
% 5.93/6.18  thf('45', plain,
% 5.93/6.18      (![X39 : $i]: ((k2_tarski @ X39 @ X39) = (k1_tarski @ X39))),
% 5.93/6.18      inference('cnf', [status(esa)], [t69_enumset1])).
% 5.93/6.18  thf('46', plain,
% 5.93/6.18      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 5.93/6.18         ((k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8)
% 5.93/6.18           = (k2_xboole_0 @ (k1_enumset1 @ X4 @ X5 @ X6) @ 
% 5.93/6.18              (k2_tarski @ X7 @ X8)))),
% 5.93/6.18      inference('cnf', [status(esa)], [l57_enumset1])).
% 5.93/6.18  thf('47', plain,
% 5.93/6.18      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.93/6.18         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0)
% 5.93/6.18           = (k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0)))),
% 5.93/6.18      inference('sup+', [status(thm)], ['45', '46'])).
% 5.93/6.18  thf('48', plain,
% 5.93/6.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.93/6.18         ((k3_enumset1 @ X0 @ X0 @ X1 @ X2 @ X2)
% 5.93/6.18           = (k2_xboole_0 @ (k1_enumset1 @ X1 @ X1 @ X0) @ (k1_tarski @ X2)))),
% 5.93/6.18      inference('sup+', [status(thm)], ['44', '47'])).
% 5.93/6.18  thf('49', plain,
% 5.93/6.18      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 5.93/6.18         ((k3_enumset1 @ X45 @ X45 @ X46 @ X47 @ X48)
% 5.93/6.18           = (k2_enumset1 @ X45 @ X46 @ X47 @ X48))),
% 5.93/6.18      inference('cnf', [status(esa)], [t72_enumset1])).
% 5.93/6.18  thf('50', plain,
% 5.93/6.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.93/6.18         ((k2_enumset1 @ X0 @ X1 @ X2 @ X2)
% 5.93/6.18           = (k2_xboole_0 @ (k1_enumset1 @ X1 @ X1 @ X0) @ (k1_tarski @ X2)))),
% 5.93/6.18      inference('demod', [status(thm)], ['48', '49'])).
% 5.93/6.18  thf('51', plain,
% 5.93/6.18      (![X39 : $i]: ((k2_tarski @ X39 @ X39) = (k1_tarski @ X39))),
% 5.93/6.18      inference('cnf', [status(esa)], [t69_enumset1])).
% 5.93/6.18  thf('52', plain,
% 5.93/6.18      (![X2 : $i, X3 : $i]: ((k2_tarski @ X3 @ X2) = (k2_tarski @ X2 @ X3))),
% 5.93/6.18      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 5.93/6.18  thf('53', plain,
% 5.93/6.18      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 5.93/6.18         ((k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8)
% 5.93/6.18           = (k2_xboole_0 @ (k1_enumset1 @ X4 @ X5 @ X6) @ 
% 5.93/6.18              (k2_tarski @ X7 @ X8)))),
% 5.93/6.18      inference('cnf', [status(esa)], [l57_enumset1])).
% 5.93/6.18  thf('54', plain,
% 5.93/6.18      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 5.93/6.18         ((k3_enumset1 @ X4 @ X3 @ X2 @ X0 @ X1)
% 5.93/6.18           = (k2_xboole_0 @ (k1_enumset1 @ X4 @ X3 @ X2) @ 
% 5.93/6.18              (k2_tarski @ X1 @ X0)))),
% 5.93/6.18      inference('sup+', [status(thm)], ['52', '53'])).
% 5.93/6.18  thf('55', plain,
% 5.93/6.18      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.93/6.18         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0)
% 5.93/6.18           = (k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0)))),
% 5.93/6.18      inference('sup+', [status(thm)], ['51', '54'])).
% 5.93/6.18  thf(t74_enumset1, axiom,
% 5.93/6.18    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 5.93/6.18     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 5.93/6.18       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 5.93/6.18  thf('56', plain,
% 5.93/6.18      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i, X58 : $i, X59 : $i]:
% 5.93/6.18         ((k5_enumset1 @ X54 @ X54 @ X55 @ X56 @ X57 @ X58 @ X59)
% 5.93/6.18           = (k4_enumset1 @ X54 @ X55 @ X56 @ X57 @ X58 @ X59))),
% 5.93/6.18      inference('cnf', [status(esa)], [t74_enumset1])).
% 5.93/6.18  thf('57', plain,
% 5.93/6.18      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 5.93/6.18         ((k4_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52 @ X53)
% 5.93/6.18           = (k3_enumset1 @ X49 @ X50 @ X51 @ X52 @ X53))),
% 5.93/6.18      inference('cnf', [status(esa)], [t73_enumset1])).
% 5.93/6.18  thf('58', plain,
% 5.93/6.18      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 5.93/6.18         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 5.93/6.18           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 5.93/6.18      inference('sup+', [status(thm)], ['56', '57'])).
% 5.93/6.18  thf('59', plain,
% 5.93/6.18      (![X39 : $i]: ((k2_tarski @ X39 @ X39) = (k1_tarski @ X39))),
% 5.93/6.18      inference('cnf', [status(esa)], [t69_enumset1])).
% 5.93/6.18  thf(t60_enumset1, axiom,
% 5.93/6.18    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 5.93/6.18     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 5.93/6.18       ( k2_xboole_0 @
% 5.93/6.18         ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ))).
% 5.93/6.18  thf('60', plain,
% 5.93/6.18      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 5.93/6.18         ((k5_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38)
% 5.93/6.18           = (k2_xboole_0 @ (k3_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36) @ 
% 5.93/6.18              (k2_tarski @ X37 @ X38)))),
% 5.93/6.18      inference('cnf', [status(esa)], [t60_enumset1])).
% 5.93/6.18  thf('61', plain,
% 5.93/6.18      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 5.93/6.18         ((k5_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 5.93/6.18           = (k2_xboole_0 @ (k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 5.93/6.18              (k1_tarski @ X0)))),
% 5.93/6.18      inference('sup+', [status(thm)], ['59', '60'])).
% 5.93/6.18  thf(t55_enumset1, axiom,
% 5.93/6.18    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 5.93/6.18     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 5.93/6.18       ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ))).
% 5.93/6.18  thf('62', plain,
% 5.93/6.18      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 5.93/6.18         ((k4_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31)
% 5.93/6.18           = (k2_xboole_0 @ (k3_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30) @ 
% 5.93/6.18              (k1_tarski @ X31)))),
% 5.93/6.18      inference('cnf', [status(esa)], [t55_enumset1])).
% 5.93/6.18  thf('63', plain,
% 5.93/6.18      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 5.93/6.18         ((k5_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 5.93/6.18           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 5.93/6.18      inference('demod', [status(thm)], ['61', '62'])).
% 5.93/6.18  thf('64', plain,
% 5.93/6.18      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.93/6.18         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0)
% 5.93/6.18           = (k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0))),
% 5.93/6.18      inference('sup+', [status(thm)], ['58', '63'])).
% 5.93/6.18  thf('65', plain,
% 5.93/6.18      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 5.93/6.18         ((k4_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52 @ X53)
% 5.93/6.18           = (k3_enumset1 @ X49 @ X50 @ X51 @ X52 @ X53))),
% 5.93/6.18      inference('cnf', [status(esa)], [t73_enumset1])).
% 5.93/6.18  thf('66', plain,
% 5.93/6.18      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 5.93/6.18         ((k3_enumset1 @ X45 @ X45 @ X46 @ X47 @ X48)
% 5.93/6.18           = (k2_enumset1 @ X45 @ X46 @ X47 @ X48))),
% 5.93/6.18      inference('cnf', [status(esa)], [t72_enumset1])).
% 5.93/6.18  thf('67', plain,
% 5.93/6.18      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.93/6.18         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 5.93/6.18           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 5.93/6.18      inference('sup+', [status(thm)], ['65', '66'])).
% 5.93/6.18  thf('68', plain,
% 5.93/6.18      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.93/6.18         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0)
% 5.93/6.18           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 5.93/6.18      inference('demod', [status(thm)], ['64', '67'])).
% 5.93/6.18  thf('69', plain,
% 5.93/6.18      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.93/6.18         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 5.93/6.18           = (k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0)))),
% 5.93/6.18      inference('demod', [status(thm)], ['55', '68'])).
% 5.93/6.18  thf('70', plain,
% 5.93/6.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.93/6.18         ((k2_enumset1 @ X0 @ X1 @ X2 @ X2) = (k2_enumset1 @ X1 @ X1 @ X0 @ X2))),
% 5.93/6.18      inference('demod', [status(thm)], ['50', '69'])).
% 5.93/6.18  thf('71', plain,
% 5.93/6.18      (![X42 : $i, X43 : $i, X44 : $i]:
% 5.93/6.18         ((k2_enumset1 @ X42 @ X42 @ X43 @ X44)
% 5.93/6.18           = (k1_enumset1 @ X42 @ X43 @ X44))),
% 5.93/6.18      inference('cnf', [status(esa)], [t71_enumset1])).
% 5.93/6.18  thf('72', plain,
% 5.93/6.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.93/6.18         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 5.93/6.18      inference('sup+', [status(thm)], ['70', '71'])).
% 5.93/6.18  thf('73', plain,
% 5.93/6.18      (![X40 : $i, X41 : $i]:
% 5.93/6.18         ((k1_enumset1 @ X40 @ X40 @ X41) = (k2_tarski @ X40 @ X41))),
% 5.93/6.18      inference('cnf', [status(esa)], [t70_enumset1])).
% 5.93/6.18  thf('74', plain,
% 5.93/6.18      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.93/6.18         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0)
% 5.93/6.18           = (k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0)))),
% 5.93/6.18      inference('sup+', [status(thm)], ['45', '46'])).
% 5.93/6.18  thf('75', plain,
% 5.93/6.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.93/6.18         ((k3_enumset1 @ X1 @ X1 @ X0 @ X2 @ X2)
% 5.93/6.18           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 5.93/6.18      inference('sup+', [status(thm)], ['73', '74'])).
% 5.93/6.18  thf('76', plain,
% 5.93/6.18      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 5.93/6.18         ((k3_enumset1 @ X45 @ X45 @ X46 @ X47 @ X48)
% 5.93/6.18           = (k2_enumset1 @ X45 @ X46 @ X47 @ X48))),
% 5.93/6.18      inference('cnf', [status(esa)], [t72_enumset1])).
% 5.93/6.18  thf('77', plain,
% 5.93/6.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.93/6.18         ((k2_enumset1 @ X1 @ X0 @ X2 @ X2)
% 5.93/6.18           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 5.93/6.18      inference('demod', [status(thm)], ['75', '76'])).
% 5.93/6.18  thf('78', plain,
% 5.93/6.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.93/6.18         ((k1_enumset1 @ X2 @ X1 @ X0)
% 5.93/6.18           = (k2_xboole_0 @ (k2_tarski @ X1 @ X2) @ (k1_tarski @ X0)))),
% 5.93/6.18      inference('sup+', [status(thm)], ['72', '77'])).
% 5.93/6.18  thf('79', plain,
% 5.93/6.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.93/6.18         ((k1_enumset1 @ X1 @ X0 @ X2)
% 5.93/6.18           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 5.93/6.18      inference('sup+', [status(thm)], ['41', '78'])).
% 5.93/6.18  thf('80', plain,
% 5.93/6.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.93/6.18         ((k1_enumset1 @ X2 @ X1 @ X0)
% 5.93/6.18           = (k2_xboole_0 @ (k2_tarski @ X1 @ X2) @ (k1_tarski @ X0)))),
% 5.93/6.18      inference('sup+', [status(thm)], ['72', '77'])).
% 5.93/6.18  thf('81', plain,
% 5.93/6.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.93/6.18         ((k1_enumset1 @ X1 @ X2 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 5.93/6.18      inference('sup+', [status(thm)], ['79', '80'])).
% 5.93/6.18  thf('82', plain,
% 5.93/6.18      (![X2 : $i, X3 : $i]: ((k2_tarski @ X3 @ X2) = (k2_tarski @ X2 @ X3))),
% 5.93/6.18      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 5.93/6.18  thf('83', plain,
% 5.93/6.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.93/6.18         ((k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0))
% 5.93/6.18           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 5.93/6.18      inference('sup+', [status(thm)], ['33', '34'])).
% 5.93/6.18  thf('84', plain,
% 5.93/6.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.93/6.18         ((k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0))
% 5.93/6.18           = (k1_enumset1 @ X2 @ X0 @ X1))),
% 5.93/6.18      inference('sup+', [status(thm)], ['82', '83'])).
% 5.93/6.18  thf('85', plain,
% 5.93/6.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.93/6.18         ((k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0))
% 5.93/6.18           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 5.93/6.18      inference('sup+', [status(thm)], ['33', '34'])).
% 5.93/6.18  thf('86', plain,
% 5.93/6.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.93/6.18         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 5.93/6.18      inference('sup+', [status(thm)], ['84', '85'])).
% 5.93/6.18  thf('87', plain,
% 5.93/6.18      (((k1_enumset1 @ sk_B @ sk_C @ sk_A)
% 5.93/6.18         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 5.93/6.18      inference('demod', [status(thm)], ['40', '81', '86'])).
% 5.93/6.18  thf('88', plain, ($false), inference('simplify', [status(thm)], ['87'])).
% 5.93/6.18  
% 5.93/6.18  % SZS output end Refutation
% 5.93/6.18  
% 6.05/6.19  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

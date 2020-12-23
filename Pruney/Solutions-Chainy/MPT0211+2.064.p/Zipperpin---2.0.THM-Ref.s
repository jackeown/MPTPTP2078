%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4bdToGnU3x

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:38 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 140 expanded)
%              Number of leaves         :   21 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :  777 (1370 expanded)
%              Number of equality atoms :   70 ( 129 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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

thf(t99_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ B @ A @ C ) ) )).

thf('1',plain,(
    ! [X65: $i,X66: $i,X67: $i] :
      ( ( k1_enumset1 @ X66 @ X65 @ X67 )
      = ( k1_enumset1 @ X65 @ X66 @ X67 ) ) ),
    inference(cnf,[status(esa)],[t99_enumset1])).

thf(t98_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ A @ C @ B ) ) )).

thf('2',plain,(
    ! [X62: $i,X63: $i,X64: $i] :
      ( ( k1_enumset1 @ X62 @ X64 @ X63 )
      = ( k1_enumset1 @ X62 @ X63 @ X64 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf('3',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k2_tarski @ sk_C @ sk_A ) )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_enumset1 @ X35 @ X35 @ X36 )
      = ( k2_tarski @ X35 @ X36 ) ) ),
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
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( k3_enumset1 @ X40 @ X40 @ X41 @ X42 @ X43 )
      = ( k2_enumset1 @ X40 @ X41 @ X42 @ X43 ) ) ),
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
    ! [X62: $i,X63: $i,X64: $i] :
      ( ( k1_enumset1 @ X62 @ X64 @ X63 )
      = ( k1_enumset1 @ X62 @ X63 @ X64 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf('11',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_enumset1 @ X35 @ X35 @ X36 )
      = ( k2_tarski @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('13',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k2_enumset1 @ X37 @ X37 @ X38 @ X39 )
      = ( k1_enumset1 @ X37 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('14',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_enumset1 @ X35 @ X35 @ X36 )
      = ( k2_tarski @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('16',plain,(
    ! [X34: $i] :
      ( ( k2_tarski @ X34 @ X34 )
      = ( k1_tarski @ X34 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k2_enumset1 @ X37 @ X37 @ X38 @ X39 )
      = ( k1_enumset1 @ X37 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(l62_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ) )).

thf('19',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k4_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X7 @ X8 @ X9 ) @ ( k1_enumset1 @ X10 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[l62_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) @ ( k1_enumset1 @ X5 @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X0 @ X0 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_enumset1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('22',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( k4_enumset1 @ X44 @ X44 @ X45 @ X46 @ X47 @ X48 )
      = ( k3_enumset1 @ X44 @ X45 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('23',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( k3_enumset1 @ X40 @ X40 @ X41 @ X42 @ X43 )
      = ( k2_enumset1 @ X40 @ X41 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_enumset1 @ X3 @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('27',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( k3_enumset1 @ X40 @ X40 @ X41 @ X42 @ X43 )
      = ( k2_enumset1 @ X40 @ X41 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t55_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ) )).

thf('28',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k4_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 ) @ ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t55_enumset1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( k4_enumset1 @ X44 @ X44 @ X45 @ X46 @ X47 @ X48 )
      = ( k3_enumset1 @ X44 @ X45 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['26','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('34',plain,(
    ! [X65: $i,X66: $i,X67: $i] :
      ( ( k1_enumset1 @ X66 @ X65 @ X67 )
      = ( k1_enumset1 @ X65 @ X66 @ X67 ) ) ),
    inference(cnf,[status(esa)],[t99_enumset1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X3 @ X4 ) @ ( k2_tarski @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X0 @ X1 @ X1 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X0 @ X1 @ X1 @ X3 @ X2 )
      = ( k2_enumset1 @ X1 @ X0 @ X3 @ X2 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k2_enumset1 @ X37 @ X37 @ X38 @ X39 )
      = ( k1_enumset1 @ X37 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X34: $i] :
      ( ( k2_tarski @ X34 @ X34 )
      = ( k1_tarski @ X34 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X34: $i] :
      ( ( k2_tarski @ X34 @ X34 )
      = ( k1_tarski @ X34 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','39','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('53',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k2_enumset1 @ X37 @ X37 @ X38 @ X39 )
      = ( k1_enumset1 @ X37 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X1 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['25','55'])).

thf('57',plain,(
    ( k1_enumset1 @ sk_B @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['9','56'])).

thf('58',plain,(
    $false ),
    inference(simplify,[status(thm)],['57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4bdToGnU3x
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:48:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.90/1.14  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.90/1.14  % Solved by: fo/fo7.sh
% 0.90/1.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.14  % done 1287 iterations in 0.681s
% 0.90/1.14  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.90/1.14  % SZS output start Refutation
% 0.90/1.14  thf(sk_C_type, type, sk_C: $i).
% 0.90/1.14  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.90/1.14  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.90/1.14  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.90/1.14  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.90/1.14  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.14  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.90/1.14  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.90/1.14  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.90/1.14  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.14  thf(t137_enumset1, conjecture,
% 0.90/1.14    (![A:$i,B:$i,C:$i]:
% 0.90/1.14     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 0.90/1.14       ( k1_enumset1 @ A @ B @ C ) ))).
% 0.90/1.14  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.14    (~( ![A:$i,B:$i,C:$i]:
% 0.90/1.14        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 0.90/1.14          ( k1_enumset1 @ A @ B @ C ) ) )),
% 0.90/1.14    inference('cnf.neg', [status(esa)], [t137_enumset1])).
% 0.90/1.14  thf('0', plain,
% 0.90/1.14      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 0.90/1.14         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.90/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.14  thf(t99_enumset1, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i]:
% 0.90/1.14     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ B @ A @ C ) ))).
% 0.90/1.14  thf('1', plain,
% 0.90/1.14      (![X65 : $i, X66 : $i, X67 : $i]:
% 0.90/1.14         ((k1_enumset1 @ X66 @ X65 @ X67) = (k1_enumset1 @ X65 @ X66 @ X67))),
% 0.90/1.14      inference('cnf', [status(esa)], [t99_enumset1])).
% 0.90/1.14  thf(t98_enumset1, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i]:
% 0.90/1.14     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ A @ C @ B ) ))).
% 0.90/1.14  thf('2', plain,
% 0.90/1.14      (![X62 : $i, X63 : $i, X64 : $i]:
% 0.90/1.14         ((k1_enumset1 @ X62 @ X64 @ X63) = (k1_enumset1 @ X62 @ X63 @ X64))),
% 0.90/1.14      inference('cnf', [status(esa)], [t98_enumset1])).
% 0.90/1.14  thf('3', plain,
% 0.90/1.14      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 0.90/1.14         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 0.90/1.14      inference('demod', [status(thm)], ['0', '1', '2'])).
% 0.90/1.14  thf(t70_enumset1, axiom,
% 0.90/1.14    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.90/1.14  thf('4', plain,
% 0.90/1.14      (![X35 : $i, X36 : $i]:
% 0.90/1.14         ((k1_enumset1 @ X35 @ X35 @ X36) = (k2_tarski @ X35 @ X36))),
% 0.90/1.14      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.90/1.14  thf(l57_enumset1, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.90/1.14     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.90/1.14       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ))).
% 0.90/1.14  thf('5', plain,
% 0.90/1.14      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.90/1.14         ((k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6)
% 0.90/1.14           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X3 @ X4) @ 
% 0.90/1.14              (k2_tarski @ X5 @ X6)))),
% 0.90/1.14      inference('cnf', [status(esa)], [l57_enumset1])).
% 0.90/1.14  thf('6', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.90/1.14         ((k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2)
% 0.90/1.14           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 0.90/1.14      inference('sup+', [status(thm)], ['4', '5'])).
% 0.90/1.14  thf(t72_enumset1, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.14     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.90/1.14  thf('7', plain,
% 0.90/1.14      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.90/1.14         ((k3_enumset1 @ X40 @ X40 @ X41 @ X42 @ X43)
% 0.90/1.14           = (k2_enumset1 @ X40 @ X41 @ X42 @ X43))),
% 0.90/1.14      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.90/1.14  thf('8', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.90/1.14         ((k2_enumset1 @ X1 @ X0 @ X3 @ X2)
% 0.90/1.14           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 0.90/1.14      inference('demod', [status(thm)], ['6', '7'])).
% 0.90/1.14  thf('9', plain,
% 0.90/1.14      (((k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A)
% 0.90/1.14         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 0.90/1.14      inference('demod', [status(thm)], ['3', '8'])).
% 0.90/1.14  thf('10', plain,
% 0.90/1.14      (![X62 : $i, X63 : $i, X64 : $i]:
% 0.90/1.14         ((k1_enumset1 @ X62 @ X64 @ X63) = (k1_enumset1 @ X62 @ X63 @ X64))),
% 0.90/1.14      inference('cnf', [status(esa)], [t98_enumset1])).
% 0.90/1.14  thf('11', plain,
% 0.90/1.14      (![X35 : $i, X36 : $i]:
% 0.90/1.14         ((k1_enumset1 @ X35 @ X35 @ X36) = (k2_tarski @ X35 @ X36))),
% 0.90/1.14      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.90/1.14  thf('12', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         ((k1_enumset1 @ X0 @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.90/1.14      inference('sup+', [status(thm)], ['10', '11'])).
% 0.90/1.14  thf(t71_enumset1, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i]:
% 0.90/1.14     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.90/1.14  thf('13', plain,
% 0.90/1.14      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.90/1.14         ((k2_enumset1 @ X37 @ X37 @ X38 @ X39)
% 0.90/1.14           = (k1_enumset1 @ X37 @ X38 @ X39))),
% 0.90/1.14      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.90/1.14  thf('14', plain,
% 0.90/1.14      (![X35 : $i, X36 : $i]:
% 0.90/1.14         ((k1_enumset1 @ X35 @ X35 @ X36) = (k2_tarski @ X35 @ X36))),
% 0.90/1.14      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.90/1.14  thf('15', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i]:
% 0.90/1.14         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.90/1.14      inference('sup+', [status(thm)], ['13', '14'])).
% 0.90/1.14  thf(t69_enumset1, axiom,
% 0.90/1.14    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.90/1.14  thf('16', plain,
% 0.90/1.14      (![X34 : $i]: ((k2_tarski @ X34 @ X34) = (k1_tarski @ X34))),
% 0.90/1.14      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.90/1.14  thf('17', plain,
% 0.90/1.14      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.90/1.14      inference('sup+', [status(thm)], ['15', '16'])).
% 0.90/1.14  thf('18', plain,
% 0.90/1.14      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.90/1.14         ((k2_enumset1 @ X37 @ X37 @ X38 @ X39)
% 0.90/1.14           = (k1_enumset1 @ X37 @ X38 @ X39))),
% 0.90/1.14      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.90/1.14  thf(l62_enumset1, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.90/1.14     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.90/1.14       ( k2_xboole_0 @
% 0.90/1.14         ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ))).
% 0.90/1.14  thf('19', plain,
% 0.90/1.14      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.90/1.14         ((k4_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12)
% 0.90/1.14           = (k2_xboole_0 @ (k1_enumset1 @ X7 @ X8 @ X9) @ 
% 0.90/1.14              (k1_enumset1 @ X10 @ X11 @ X12)))),
% 0.90/1.14      inference('cnf', [status(esa)], [l62_enumset1])).
% 0.90/1.14  thf('20', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.90/1.14         ((k4_enumset1 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3)
% 0.90/1.14           = (k2_xboole_0 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0) @ 
% 0.90/1.14              (k1_enumset1 @ X5 @ X4 @ X3)))),
% 0.90/1.14      inference('sup+', [status(thm)], ['18', '19'])).
% 0.90/1.14  thf('21', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.90/1.14         ((k4_enumset1 @ X0 @ X0 @ X0 @ X3 @ X2 @ X1)
% 0.90/1.14           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_enumset1 @ X3 @ X2 @ X1)))),
% 0.90/1.14      inference('sup+', [status(thm)], ['17', '20'])).
% 0.90/1.14  thf(t73_enumset1, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.90/1.14     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.90/1.14       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.90/1.14  thf('22', plain,
% 0.90/1.14      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.90/1.14         ((k4_enumset1 @ X44 @ X44 @ X45 @ X46 @ X47 @ X48)
% 0.90/1.14           = (k3_enumset1 @ X44 @ X45 @ X46 @ X47 @ X48))),
% 0.90/1.14      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.90/1.14  thf('23', plain,
% 0.90/1.14      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.90/1.14         ((k3_enumset1 @ X40 @ X40 @ X41 @ X42 @ X43)
% 0.90/1.14           = (k2_enumset1 @ X40 @ X41 @ X42 @ X43))),
% 0.90/1.14      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.90/1.14  thf('24', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.90/1.14         ((k2_enumset1 @ X0 @ X3 @ X2 @ X1)
% 0.90/1.14           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_enumset1 @ X3 @ X2 @ X1)))),
% 0.90/1.14      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.90/1.14  thf('25', plain,
% 0.90/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.14         ((k2_enumset1 @ X2 @ X1 @ X0 @ X1)
% 0.90/1.14           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.90/1.14      inference('sup+', [status(thm)], ['12', '24'])).
% 0.90/1.14  thf('26', plain,
% 0.90/1.14      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.90/1.14      inference('sup+', [status(thm)], ['15', '16'])).
% 0.90/1.14  thf('27', plain,
% 0.90/1.14      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.90/1.14         ((k3_enumset1 @ X40 @ X40 @ X41 @ X42 @ X43)
% 0.90/1.14           = (k2_enumset1 @ X40 @ X41 @ X42 @ X43))),
% 0.90/1.14      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.90/1.14  thf(t55_enumset1, axiom,
% 0.90/1.14    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.90/1.15     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.90/1.15       ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ))).
% 0.90/1.15  thf('28', plain,
% 0.90/1.15      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.90/1.15         ((k4_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18)
% 0.90/1.15           = (k2_xboole_0 @ (k3_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17) @ 
% 0.90/1.15              (k1_tarski @ X18)))),
% 0.90/1.15      inference('cnf', [status(esa)], [t55_enumset1])).
% 0.90/1.15  thf('29', plain,
% 0.90/1.15      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.90/1.15         ((k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4)
% 0.90/1.15           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.90/1.15              (k1_tarski @ X4)))),
% 0.90/1.15      inference('sup+', [status(thm)], ['27', '28'])).
% 0.90/1.15  thf('30', plain,
% 0.90/1.15      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.90/1.15         ((k4_enumset1 @ X44 @ X44 @ X45 @ X46 @ X47 @ X48)
% 0.90/1.15           = (k3_enumset1 @ X44 @ X45 @ X46 @ X47 @ X48))),
% 0.90/1.15      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.90/1.15  thf('31', plain,
% 0.90/1.15      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.90/1.15         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 0.90/1.15           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.90/1.15              (k1_tarski @ X4)))),
% 0.90/1.15      inference('demod', [status(thm)], ['29', '30'])).
% 0.90/1.15  thf('32', plain,
% 0.90/1.15      (![X0 : $i, X1 : $i]:
% 0.90/1.15         ((k3_enumset1 @ X0 @ X0 @ X0 @ X0 @ X1)
% 0.90/1.15           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.90/1.15      inference('sup+', [status(thm)], ['26', '31'])).
% 0.90/1.15  thf('33', plain,
% 0.90/1.15      (![X0 : $i, X1 : $i]:
% 0.90/1.15         ((k1_enumset1 @ X0 @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.90/1.15      inference('sup+', [status(thm)], ['10', '11'])).
% 0.90/1.15  thf('34', plain,
% 0.90/1.15      (![X65 : $i, X66 : $i, X67 : $i]:
% 0.90/1.15         ((k1_enumset1 @ X66 @ X65 @ X67) = (k1_enumset1 @ X65 @ X66 @ X67))),
% 0.90/1.15      inference('cnf', [status(esa)], [t99_enumset1])).
% 0.90/1.15  thf('35', plain,
% 0.90/1.15      (![X0 : $i, X1 : $i]:
% 0.90/1.15         ((k1_enumset1 @ X0 @ X1 @ X1) = (k2_tarski @ X1 @ X0))),
% 0.90/1.15      inference('sup+', [status(thm)], ['33', '34'])).
% 0.90/1.15  thf('36', plain,
% 0.90/1.15      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.90/1.15         ((k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6)
% 0.90/1.15           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X3 @ X4) @ 
% 0.90/1.15              (k2_tarski @ X5 @ X6)))),
% 0.90/1.15      inference('cnf', [status(esa)], [l57_enumset1])).
% 0.90/1.15  thf('37', plain,
% 0.90/1.15      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.90/1.15         ((k3_enumset1 @ X0 @ X1 @ X1 @ X3 @ X2)
% 0.90/1.15           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 0.90/1.15      inference('sup+', [status(thm)], ['35', '36'])).
% 0.90/1.15  thf('38', plain,
% 0.90/1.15      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.90/1.15         ((k2_enumset1 @ X1 @ X0 @ X3 @ X2)
% 0.90/1.15           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 0.90/1.15      inference('demod', [status(thm)], ['6', '7'])).
% 0.90/1.15  thf('39', plain,
% 0.90/1.15      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.90/1.15         ((k3_enumset1 @ X0 @ X1 @ X1 @ X3 @ X2)
% 0.90/1.15           = (k2_enumset1 @ X1 @ X0 @ X3 @ X2))),
% 0.90/1.15      inference('demod', [status(thm)], ['37', '38'])).
% 0.90/1.15  thf('40', plain,
% 0.90/1.15      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.90/1.15         ((k2_enumset1 @ X37 @ X37 @ X38 @ X39)
% 0.90/1.15           = (k1_enumset1 @ X37 @ X38 @ X39))),
% 0.90/1.15      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.90/1.15  thf('41', plain,
% 0.90/1.15      (![X0 : $i, X1 : $i]:
% 0.90/1.15         ((k1_enumset1 @ X0 @ X1 @ X1) = (k2_tarski @ X1 @ X0))),
% 0.90/1.15      inference('sup+', [status(thm)], ['33', '34'])).
% 0.90/1.15  thf('42', plain,
% 0.90/1.15      (![X0 : $i, X1 : $i]:
% 0.90/1.15         ((k2_enumset1 @ X1 @ X1 @ X0 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.90/1.15      inference('sup+', [status(thm)], ['40', '41'])).
% 0.90/1.15  thf('43', plain,
% 0.90/1.15      (![X34 : $i]: ((k2_tarski @ X34 @ X34) = (k1_tarski @ X34))),
% 0.90/1.15      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.90/1.15  thf('44', plain,
% 0.90/1.15      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.90/1.15         ((k2_enumset1 @ X1 @ X0 @ X3 @ X2)
% 0.90/1.15           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 0.90/1.15      inference('demod', [status(thm)], ['6', '7'])).
% 0.90/1.15  thf('45', plain,
% 0.90/1.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.15         ((k2_enumset1 @ X0 @ X0 @ X2 @ X1)
% 0.90/1.15           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 0.90/1.15      inference('sup+', [status(thm)], ['43', '44'])).
% 0.90/1.15  thf('46', plain,
% 0.90/1.15      (![X0 : $i, X1 : $i]:
% 0.90/1.15         ((k2_tarski @ X1 @ X0)
% 0.90/1.15           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X1)))),
% 0.90/1.15      inference('sup+', [status(thm)], ['42', '45'])).
% 0.90/1.15  thf('47', plain,
% 0.90/1.15      (![X34 : $i]: ((k2_tarski @ X34 @ X34) = (k1_tarski @ X34))),
% 0.90/1.15      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.90/1.15  thf('48', plain,
% 0.90/1.15      (![X0 : $i, X1 : $i]:
% 0.90/1.15         ((k2_tarski @ X1 @ X0)
% 0.90/1.15           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.90/1.15      inference('demod', [status(thm)], ['46', '47'])).
% 0.90/1.15  thf('49', plain,
% 0.90/1.15      (![X0 : $i, X1 : $i]:
% 0.90/1.15         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 0.90/1.15      inference('demod', [status(thm)], ['32', '39', '48'])).
% 0.90/1.15  thf('50', plain,
% 0.90/1.15      (![X0 : $i, X1 : $i]:
% 0.90/1.15         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.90/1.15      inference('sup+', [status(thm)], ['13', '14'])).
% 0.90/1.15  thf('51', plain,
% 0.90/1.15      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.90/1.15      inference('sup+', [status(thm)], ['49', '50'])).
% 0.90/1.15  thf('52', plain,
% 0.90/1.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.15         ((k2_enumset1 @ X0 @ X0 @ X2 @ X1)
% 0.90/1.15           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 0.90/1.15      inference('sup+', [status(thm)], ['43', '44'])).
% 0.90/1.15  thf('53', plain,
% 0.90/1.15      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.90/1.15         ((k2_enumset1 @ X37 @ X37 @ X38 @ X39)
% 0.90/1.15           = (k1_enumset1 @ X37 @ X38 @ X39))),
% 0.90/1.15      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.90/1.15  thf('54', plain,
% 0.90/1.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.15         ((k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0))
% 0.90/1.15           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.90/1.15      inference('sup+', [status(thm)], ['52', '53'])).
% 0.90/1.15  thf('55', plain,
% 0.90/1.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.15         ((k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0))
% 0.90/1.15           = (k1_enumset1 @ X2 @ X0 @ X1))),
% 0.90/1.15      inference('sup+', [status(thm)], ['51', '54'])).
% 0.90/1.15  thf('56', plain,
% 0.90/1.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.15         ((k2_enumset1 @ X2 @ X1 @ X0 @ X1) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 0.90/1.15      inference('demod', [status(thm)], ['25', '55'])).
% 0.90/1.15  thf('57', plain,
% 0.90/1.15      (((k1_enumset1 @ sk_B @ sk_C @ sk_A)
% 0.90/1.15         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 0.90/1.15      inference('demod', [status(thm)], ['9', '56'])).
% 0.90/1.15  thf('58', plain, ($false), inference('simplify', [status(thm)], ['57'])).
% 0.90/1.15  
% 0.90/1.15  % SZS output end Refutation
% 0.90/1.15  
% 0.90/1.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xLE27W8e4f

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:09 EST 2020

% Result     : Theorem 8.93s
% Output     : Refutation 8.93s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 240 expanded)
%              Number of leaves         :   26 (  89 expanded)
%              Depth                    :   19
%              Number of atoms          : 1845 (3010 expanded)
%              Number of equality atoms :  134 ( 227 expanded)
%              Maximal formula depth    :   18 (  11 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t108_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ B @ A @ C @ D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k2_enumset1 @ A @ B @ C @ D )
        = ( k2_enumset1 @ B @ A @ C @ D ) ) ),
    inference('cnf.neg',[status(esa)],[t108_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t105_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ C @ D @ B ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k2_enumset1 @ X20 @ X23 @ X21 @ X22 )
      = ( k2_enumset1 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('2',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( k2_enumset1 @ X49 @ X49 @ X50 @ X51 )
      = ( k1_enumset1 @ X49 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('4',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( k3_enumset1 @ X52 @ X52 @ X53 @ X54 @ X55 )
      = ( k2_enumset1 @ X52 @ X53 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t60_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ) )).

thf('6',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( k5_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 ) @ ( k2_tarski @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t60_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X2 @ X2 @ X1 @ X0 @ X2 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('8',plain,(
    ! [X61: $i,X62: $i,X63: $i,X64: $i,X65: $i,X66: $i] :
      ( ( k5_enumset1 @ X61 @ X61 @ X62 @ X63 @ X64 @ X65 @ X66 )
      = ( k4_enumset1 @ X61 @ X62 @ X63 @ X64 @ X65 @ X66 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(l57_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X5 @ X6 ) @ ( k2_tarski @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X2 @ X1 @ X0 @ X2 @ X4 @ X3 )
      = ( k3_enumset1 @ X2 @ X1 @ X0 @ X4 @ X3 ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k1_enumset1 @ X47 @ X47 @ X48 )
      = ( k2_tarski @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('12',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X5 @ X6 ) @ ( k2_tarski @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k2_enumset1 @ X20 @ X23 @ X21 @ X22 )
      = ( k2_enumset1 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('15',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( k2_enumset1 @ X49 @ X49 @ X50 @ X51 )
      = ( k1_enumset1 @ X49 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( k3_enumset1 @ X52 @ X52 @ X53 @ X54 @ X55 )
      = ( k2_enumset1 @ X52 @ X53 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X0 @ X2 @ X1 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['13','18'])).

thf(t100_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ B @ C @ A ) ) )).

thf('20',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k1_enumset1 @ X19 @ X17 @ X18 )
      = ( k1_enumset1 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('21',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k1_enumset1 @ X47 @ X47 @ X48 )
      = ( k2_tarski @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X5 @ X6 ) @ ( k2_tarski @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X0 @ X1 @ X1 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X0 @ X2 @ X2 @ X2 @ X1 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( k5_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 ) @ ( k2_tarski @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t60_enumset1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X0 @ X2 @ X2 @ X2 @ X1 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k1_enumset1 @ X19 @ X17 @ X18 )
      = ( k1_enumset1 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('29',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X5 @ X6 ) @ ( k2_tarski @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X0 @ X2 @ X1 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X0 @ X2 @ X2 @ X2 @ X1 @ X4 @ X3 )
      = ( k3_enumset1 @ X0 @ X2 @ X1 @ X4 @ X3 ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( k3_enumset1 @ X52 @ X52 @ X53 @ X54 @ X55 )
      = ( k2_enumset1 @ X52 @ X53 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('33',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( k2_enumset1 @ X49 @ X49 @ X50 @ X51 )
      = ( k1_enumset1 @ X49 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('35',plain,(
    ! [X56: $i,X57: $i,X58: $i,X59: $i,X60: $i] :
      ( ( k4_enumset1 @ X56 @ X56 @ X57 @ X58 @ X59 @ X60 )
      = ( k3_enumset1 @ X56 @ X57 @ X58 @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_enumset1 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k1_enumset1 @ X19 @ X17 @ X18 )
      = ( k1_enumset1 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_enumset1 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X56: $i,X57: $i,X58: $i,X59: $i,X60: $i] :
      ( ( k4_enumset1 @ X56 @ X56 @ X57 @ X58 @ X59 @ X60 )
      = ( k3_enumset1 @ X56 @ X57 @ X58 @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('40',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( k3_enumset1 @ X52 @ X52 @ X53 @ X54 @ X55 )
      = ( k2_enumset1 @ X52 @ X53 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( k3_enumset1 @ X52 @ X52 @ X53 @ X54 @ X55 )
      = ( k2_enumset1 @ X52 @ X53 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('44',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k2_enumset1 @ X20 @ X23 @ X21 @ X22 )
      = ( k2_enumset1 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X0 @ X2 @ X1 )
      = ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X0 @ X0 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k1_enumset1 @ X19 @ X17 @ X18 )
      = ( k1_enumset1 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('50',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k1_enumset1 @ X47 @ X47 @ X48 )
      = ( k2_tarski @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X5 @ X6 ) @ ( k2_tarski @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X0 @ X1 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X0 @ X2 @ X0 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_enumset1 @ X0 @ X2 @ X2 @ X2 @ X0 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X0 @ X2 @ X1 )
      = ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf(t64_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k3_enumset1 @ D @ E @ F @ G @ H ) ) ) )).

thf('57',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( k6_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X31 @ X32 @ X33 ) @ ( k3_enumset1 @ X34 @ X35 @ X36 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t64_enumset1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X3 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X6 @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( k3_enumset1 @ X52 @ X52 @ X53 @ X54 @ X55 )
      = ( k2_enumset1 @ X52 @ X53 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('60',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( k6_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X31 @ X32 @ X33 ) @ ( k3_enumset1 @ X34 @ X35 @ X36 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t64_enumset1])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X6 @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( k2_enumset1 @ X49 @ X49 @ X50 @ X51 )
      = ( k1_enumset1 @ X49 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(l75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ) )).

thf('63',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k6_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X9 @ X10 @ X11 @ X12 ) @ ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[l75_enumset1])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X2 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_enumset1 @ X6 @ X5 @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('65',plain,(
    ! [X67: $i,X68: $i,X69: $i,X70: $i,X71: $i,X72: $i,X73: $i] :
      ( ( k6_enumset1 @ X67 @ X67 @ X68 @ X69 @ X70 @ X71 @ X72 @ X73 )
      = ( k5_enumset1 @ X67 @ X68 @ X69 @ X70 @ X71 @ X72 @ X73 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_enumset1 @ X6 @ X5 @ X4 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['61','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_enumset1 @ X6 @ X5 @ X4 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X1 @ X0 @ X2 )
      = ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['58','67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_enumset1 @ X0 @ X2 @ X2 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_enumset1 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('72',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k1_enumset1 @ X19 @ X17 @ X18 )
      = ( k1_enumset1 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X2 @ X1 )
      = ( k4_enumset1 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X56: $i,X57: $i,X58: $i,X59: $i,X60: $i] :
      ( ( k4_enumset1 @ X56 @ X56 @ X57 @ X58 @ X59 @ X60 )
      = ( k3_enumset1 @ X56 @ X57 @ X58 @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( k6_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X31 @ X32 @ X33 ) @ ( k3_enumset1 @ X34 @ X35 @ X36 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t64_enumset1])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X4 @ X3 @ X1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( k2_enumset1 @ X49 @ X49 @ X50 @ X51 )
      = ( k1_enumset1 @ X49 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('79',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k2_enumset1 @ X20 @ X23 @ X21 @ X22 )
      = ( k2_enumset1 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('80',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k6_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X9 @ X10 @ X11 @ X12 ) @ ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[l75_enumset1])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k6_enumset1 @ X3 @ X1 @ X0 @ X2 @ X7 @ X6 @ X5 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_enumset1 @ X7 @ X6 @ X5 @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X6 @ X4 @ X3 @ X5 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X6 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['78','81'])).

thf('83',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( k3_enumset1 @ X52 @ X52 @ X53 @ X54 @ X55 )
      = ( k2_enumset1 @ X52 @ X53 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('84',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k2_enumset1 @ X20 @ X23 @ X21 @ X22 )
      = ( k2_enumset1 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t105_enumset1])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf(t66_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_enumset1 @ F @ G @ H ) ) ) )).

thf('86',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( k6_enumset1 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X39 @ X40 @ X41 @ X42 @ X43 ) @ ( k1_enumset1 @ X44 @ X45 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[t66_enumset1])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X3 @ X3 @ X0 @ X2 @ X1 @ X6 @ X5 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_enumset1 @ X6 @ X5 @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X67: $i,X68: $i,X69: $i,X70: $i,X71: $i,X72: $i,X73: $i] :
      ( ( k6_enumset1 @ X67 @ X67 @ X68 @ X69 @ X70 @ X71 @ X72 @ X73 )
      = ( k5_enumset1 @ X67 @ X68 @ X69 @ X70 @ X71 @ X72 @ X73 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X3 @ X0 @ X2 @ X1 @ X6 @ X5 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_enumset1 @ X6 @ X5 @ X4 ) ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X6 @ X4 @ X3 @ X5 @ X2 @ X2 @ X1 @ X0 )
      = ( k5_enumset1 @ X6 @ X3 @ X5 @ X4 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['82','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('92',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( k6_enumset1 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X39 @ X40 @ X41 @ X42 @ X43 ) @ ( k1_enumset1 @ X44 @ X45 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[t66_enumset1])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_enumset1 @ X5 @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X67: $i,X68: $i,X69: $i,X70: $i,X71: $i,X72: $i,X73: $i] :
      ( ( k6_enumset1 @ X67 @ X67 @ X68 @ X69 @ X70 @ X71 @ X72 @ X73 )
      = ( k5_enumset1 @ X67 @ X68 @ X69 @ X70 @ X71 @ X72 @ X73 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf('95',plain,(
    ! [X61: $i,X62: $i,X63: $i,X64: $i,X65: $i,X66: $i] :
      ( ( k5_enumset1 @ X61 @ X61 @ X62 @ X63 @ X64 @ X65 @ X66 )
      = ( k4_enumset1 @ X61 @ X62 @ X63 @ X64 @ X65 @ X66 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_enumset1 @ X5 @ X4 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X5 @ X3 @ X1 @ X4 @ X1 @ X0 @ X2 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['77','90','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X0 )
      = ( k4_enumset1 @ X0 @ X1 @ X1 @ X0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['70','97'])).

thf('99',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k1_enumset1 @ X47 @ X47 @ X48 )
      = ( k2_tarski @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k4_enumset1 @ X0 @ X1 @ X1 @ X0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k3_enumset1 @ X0 @ X1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X0 @ X2 @ X2 @ X2 @ X1 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','24'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X5 @ X6 ) @ ( k2_tarski @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X0 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('107',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( k3_enumset1 @ X52 @ X52 @ X53 @ X54 @ X55 )
      = ( k2_enumset1 @ X52 @ X53 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X0 @ X0 @ X3 @ X2 )
      = ( k2_enumset1 @ X1 @ X0 @ X3 @ X2 ) ) ),
    inference(demod,[status(thm)],['105','108'])).

thf('110',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k1_enumset1 @ X19 @ X17 @ X18 )
      = ( k1_enumset1 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('111',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X5 @ X6 ) @ ( k2_tarski @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X1 @ X0 @ X2 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X5 @ X6 ) @ ( k2_tarski @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X2 @ X4 @ X3 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( k3_enumset1 @ X52 @ X52 @ X53 @ X54 @ X55 )
      = ( k2_enumset1 @ X52 @ X53 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X2 @ X3 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X2 @ X3 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['109','116'])).

thf('118',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','117'])).

thf('119',plain,(
    $false ),
    inference(simplify,[status(thm)],['118'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xLE27W8e4f
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:39:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 8.93/9.14  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 8.93/9.14  % Solved by: fo/fo7.sh
% 8.93/9.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.93/9.14  % done 6287 iterations in 8.683s
% 8.93/9.14  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 8.93/9.14  % SZS output start Refutation
% 8.93/9.14  thf(sk_D_type, type, sk_D: $i).
% 8.93/9.14  thf(sk_A_type, type, sk_A: $i).
% 8.93/9.14  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 8.93/9.14  thf(sk_B_type, type, sk_B: $i).
% 8.93/9.14  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 8.93/9.14  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 8.93/9.14  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 8.93/9.14  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 8.93/9.14  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 8.93/9.14  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 8.93/9.14                                           $i > $i).
% 8.93/9.14  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 8.93/9.14  thf(sk_C_type, type, sk_C: $i).
% 8.93/9.14  thf(t108_enumset1, conjecture,
% 8.93/9.14    (![A:$i,B:$i,C:$i,D:$i]:
% 8.93/9.14     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ A @ C @ D ) ))).
% 8.93/9.14  thf(zf_stmt_0, negated_conjecture,
% 8.93/9.14    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 8.93/9.14        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ A @ C @ D ) ) )),
% 8.93/9.14    inference('cnf.neg', [status(esa)], [t108_enumset1])).
% 8.93/9.14  thf('0', plain,
% 8.93/9.14      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 8.93/9.14         != (k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_D))),
% 8.93/9.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.93/9.14  thf(t105_enumset1, axiom,
% 8.93/9.14    (![A:$i,B:$i,C:$i,D:$i]:
% 8.93/9.14     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ D @ B ) ))).
% 8.93/9.14  thf('1', plain,
% 8.93/9.14      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 8.93/9.14         ((k2_enumset1 @ X20 @ X23 @ X21 @ X22)
% 8.93/9.14           = (k2_enumset1 @ X20 @ X21 @ X22 @ X23))),
% 8.93/9.14      inference('cnf', [status(esa)], [t105_enumset1])).
% 8.93/9.14  thf(t71_enumset1, axiom,
% 8.93/9.14    (![A:$i,B:$i,C:$i]:
% 8.93/9.14     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 8.93/9.14  thf('2', plain,
% 8.93/9.14      (![X49 : $i, X50 : $i, X51 : $i]:
% 8.93/9.14         ((k2_enumset1 @ X49 @ X49 @ X50 @ X51)
% 8.93/9.14           = (k1_enumset1 @ X49 @ X50 @ X51))),
% 8.93/9.14      inference('cnf', [status(esa)], [t71_enumset1])).
% 8.93/9.14  thf('3', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.93/9.14         ((k2_enumset1 @ X0 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X2 @ X1))),
% 8.93/9.14      inference('sup+', [status(thm)], ['1', '2'])).
% 8.93/9.14  thf(t72_enumset1, axiom,
% 8.93/9.14    (![A:$i,B:$i,C:$i,D:$i]:
% 8.93/9.14     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 8.93/9.14  thf('4', plain,
% 8.93/9.14      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 8.93/9.14         ((k3_enumset1 @ X52 @ X52 @ X53 @ X54 @ X55)
% 8.93/9.14           = (k2_enumset1 @ X52 @ X53 @ X54 @ X55))),
% 8.93/9.14      inference('cnf', [status(esa)], [t72_enumset1])).
% 8.93/9.14  thf('5', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.93/9.14         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 8.93/9.14      inference('sup+', [status(thm)], ['3', '4'])).
% 8.93/9.14  thf(t60_enumset1, axiom,
% 8.93/9.14    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 8.93/9.14     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 8.93/9.14       ( k2_xboole_0 @
% 8.93/9.14         ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ))).
% 8.93/9.14  thf('6', plain,
% 8.93/9.14      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 8.93/9.14         ((k5_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30)
% 8.93/9.14           = (k2_xboole_0 @ (k3_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28) @ 
% 8.93/9.14              (k2_tarski @ X29 @ X30)))),
% 8.93/9.14      inference('cnf', [status(esa)], [t60_enumset1])).
% 8.93/9.14  thf('7', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 8.93/9.14         ((k5_enumset1 @ X2 @ X2 @ X1 @ X0 @ X2 @ X4 @ X3)
% 8.93/9.14           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 8.93/9.14              (k2_tarski @ X4 @ X3)))),
% 8.93/9.14      inference('sup+', [status(thm)], ['5', '6'])).
% 8.93/9.14  thf(t74_enumset1, axiom,
% 8.93/9.14    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 8.93/9.14     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 8.93/9.14       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 8.93/9.14  thf('8', plain,
% 8.93/9.14      (![X61 : $i, X62 : $i, X63 : $i, X64 : $i, X65 : $i, X66 : $i]:
% 8.93/9.14         ((k5_enumset1 @ X61 @ X61 @ X62 @ X63 @ X64 @ X65 @ X66)
% 8.93/9.14           = (k4_enumset1 @ X61 @ X62 @ X63 @ X64 @ X65 @ X66))),
% 8.93/9.14      inference('cnf', [status(esa)], [t74_enumset1])).
% 8.93/9.14  thf(l57_enumset1, axiom,
% 8.93/9.14    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 8.93/9.14     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 8.93/9.14       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ))).
% 8.93/9.14  thf('9', plain,
% 8.93/9.14      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 8.93/9.14         ((k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8)
% 8.93/9.14           = (k2_xboole_0 @ (k1_enumset1 @ X4 @ X5 @ X6) @ 
% 8.93/9.14              (k2_tarski @ X7 @ X8)))),
% 8.93/9.14      inference('cnf', [status(esa)], [l57_enumset1])).
% 8.93/9.14  thf('10', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 8.93/9.14         ((k4_enumset1 @ X2 @ X1 @ X0 @ X2 @ X4 @ X3)
% 8.93/9.14           = (k3_enumset1 @ X2 @ X1 @ X0 @ X4 @ X3))),
% 8.93/9.14      inference('demod', [status(thm)], ['7', '8', '9'])).
% 8.93/9.14  thf(t70_enumset1, axiom,
% 8.93/9.14    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 8.93/9.14  thf('11', plain,
% 8.93/9.14      (![X47 : $i, X48 : $i]:
% 8.93/9.14         ((k1_enumset1 @ X47 @ X47 @ X48) = (k2_tarski @ X47 @ X48))),
% 8.93/9.14      inference('cnf', [status(esa)], [t70_enumset1])).
% 8.93/9.14  thf('12', plain,
% 8.93/9.14      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 8.93/9.14         ((k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8)
% 8.93/9.14           = (k2_xboole_0 @ (k1_enumset1 @ X4 @ X5 @ X6) @ 
% 8.93/9.14              (k2_tarski @ X7 @ X8)))),
% 8.93/9.14      inference('cnf', [status(esa)], [l57_enumset1])).
% 8.93/9.14  thf('13', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.93/9.14         ((k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2)
% 8.93/9.14           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 8.93/9.14      inference('sup+', [status(thm)], ['11', '12'])).
% 8.93/9.14  thf('14', plain,
% 8.93/9.14      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 8.93/9.14         ((k2_enumset1 @ X20 @ X23 @ X21 @ X22)
% 8.93/9.14           = (k2_enumset1 @ X20 @ X21 @ X22 @ X23))),
% 8.93/9.14      inference('cnf', [status(esa)], [t105_enumset1])).
% 8.93/9.14  thf('15', plain,
% 8.93/9.14      (![X49 : $i, X50 : $i, X51 : $i]:
% 8.93/9.14         ((k2_enumset1 @ X49 @ X49 @ X50 @ X51)
% 8.93/9.14           = (k1_enumset1 @ X49 @ X50 @ X51))),
% 8.93/9.14      inference('cnf', [status(esa)], [t71_enumset1])).
% 8.93/9.14  thf('16', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.93/9.14         ((k2_enumset1 @ X1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 8.93/9.14      inference('sup+', [status(thm)], ['14', '15'])).
% 8.93/9.14  thf('17', plain,
% 8.93/9.14      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 8.93/9.14         ((k3_enumset1 @ X52 @ X52 @ X53 @ X54 @ X55)
% 8.93/9.14           = (k2_enumset1 @ X52 @ X53 @ X54 @ X55))),
% 8.93/9.14      inference('cnf', [status(esa)], [t72_enumset1])).
% 8.93/9.14  thf('18', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.93/9.14         ((k3_enumset1 @ X2 @ X2 @ X0 @ X2 @ X1) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 8.93/9.14      inference('sup+', [status(thm)], ['16', '17'])).
% 8.93/9.14  thf('19', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.93/9.14         ((k2_xboole_0 @ (k2_tarski @ X1 @ X2) @ (k2_tarski @ X1 @ X0))
% 8.93/9.14           = (k1_enumset1 @ X1 @ X0 @ X2))),
% 8.93/9.14      inference('sup+', [status(thm)], ['13', '18'])).
% 8.93/9.14  thf(t100_enumset1, axiom,
% 8.93/9.14    (![A:$i,B:$i,C:$i]:
% 8.93/9.14     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ B @ C @ A ) ))).
% 8.93/9.14  thf('20', plain,
% 8.93/9.14      (![X17 : $i, X18 : $i, X19 : $i]:
% 8.93/9.14         ((k1_enumset1 @ X19 @ X17 @ X18) = (k1_enumset1 @ X17 @ X18 @ X19))),
% 8.93/9.14      inference('cnf', [status(esa)], [t100_enumset1])).
% 8.93/9.14  thf('21', plain,
% 8.93/9.14      (![X47 : $i, X48 : $i]:
% 8.93/9.14         ((k1_enumset1 @ X47 @ X47 @ X48) = (k2_tarski @ X47 @ X48))),
% 8.93/9.14      inference('cnf', [status(esa)], [t70_enumset1])).
% 8.93/9.14  thf('22', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i]:
% 8.93/9.14         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X0 @ X1))),
% 8.93/9.14      inference('sup+', [status(thm)], ['20', '21'])).
% 8.93/9.14  thf('23', plain,
% 8.93/9.14      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 8.93/9.14         ((k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8)
% 8.93/9.14           = (k2_xboole_0 @ (k1_enumset1 @ X4 @ X5 @ X6) @ 
% 8.93/9.14              (k2_tarski @ X7 @ X8)))),
% 8.93/9.14      inference('cnf', [status(esa)], [l57_enumset1])).
% 8.93/9.14  thf('24', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.93/9.14         ((k3_enumset1 @ X0 @ X1 @ X1 @ X3 @ X2)
% 8.93/9.14           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 8.93/9.14      inference('sup+', [status(thm)], ['22', '23'])).
% 8.93/9.14  thf('25', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.93/9.14         ((k3_enumset1 @ X0 @ X2 @ X2 @ X2 @ X1) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 8.93/9.14      inference('sup+', [status(thm)], ['19', '24'])).
% 8.93/9.14  thf('26', plain,
% 8.93/9.14      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 8.93/9.14         ((k5_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30)
% 8.93/9.14           = (k2_xboole_0 @ (k3_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28) @ 
% 8.93/9.14              (k2_tarski @ X29 @ X30)))),
% 8.93/9.14      inference('cnf', [status(esa)], [t60_enumset1])).
% 8.93/9.14  thf('27', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 8.93/9.14         ((k5_enumset1 @ X0 @ X2 @ X2 @ X2 @ X1 @ X4 @ X3)
% 8.93/9.14           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 8.93/9.14              (k2_tarski @ X4 @ X3)))),
% 8.93/9.14      inference('sup+', [status(thm)], ['25', '26'])).
% 8.93/9.14  thf('28', plain,
% 8.93/9.14      (![X17 : $i, X18 : $i, X19 : $i]:
% 8.93/9.14         ((k1_enumset1 @ X19 @ X17 @ X18) = (k1_enumset1 @ X17 @ X18 @ X19))),
% 8.93/9.14      inference('cnf', [status(esa)], [t100_enumset1])).
% 8.93/9.14  thf('29', plain,
% 8.93/9.14      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 8.93/9.14         ((k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8)
% 8.93/9.14           = (k2_xboole_0 @ (k1_enumset1 @ X4 @ X5 @ X6) @ 
% 8.93/9.14              (k2_tarski @ X7 @ X8)))),
% 8.93/9.14      inference('cnf', [status(esa)], [l57_enumset1])).
% 8.93/9.14  thf('30', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 8.93/9.14         ((k3_enumset1 @ X0 @ X2 @ X1 @ X4 @ X3)
% 8.93/9.14           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 8.93/9.14              (k2_tarski @ X4 @ X3)))),
% 8.93/9.14      inference('sup+', [status(thm)], ['28', '29'])).
% 8.93/9.14  thf('31', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 8.93/9.14         ((k5_enumset1 @ X0 @ X2 @ X2 @ X2 @ X1 @ X4 @ X3)
% 8.93/9.14           = (k3_enumset1 @ X0 @ X2 @ X1 @ X4 @ X3))),
% 8.93/9.14      inference('demod', [status(thm)], ['27', '30'])).
% 8.93/9.14  thf('32', plain,
% 8.93/9.14      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 8.93/9.14         ((k3_enumset1 @ X52 @ X52 @ X53 @ X54 @ X55)
% 8.93/9.14           = (k2_enumset1 @ X52 @ X53 @ X54 @ X55))),
% 8.93/9.14      inference('cnf', [status(esa)], [t72_enumset1])).
% 8.93/9.14  thf('33', plain,
% 8.93/9.14      (![X49 : $i, X50 : $i, X51 : $i]:
% 8.93/9.14         ((k2_enumset1 @ X49 @ X49 @ X50 @ X51)
% 8.93/9.14           = (k1_enumset1 @ X49 @ X50 @ X51))),
% 8.93/9.14      inference('cnf', [status(esa)], [t71_enumset1])).
% 8.93/9.14  thf('34', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.93/9.14         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 8.93/9.14      inference('sup+', [status(thm)], ['32', '33'])).
% 8.93/9.14  thf(t73_enumset1, axiom,
% 8.93/9.14    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 8.93/9.14     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 8.93/9.14       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 8.93/9.14  thf('35', plain,
% 8.93/9.14      (![X56 : $i, X57 : $i, X58 : $i, X59 : $i, X60 : $i]:
% 8.93/9.14         ((k4_enumset1 @ X56 @ X56 @ X57 @ X58 @ X59 @ X60)
% 8.93/9.14           = (k3_enumset1 @ X56 @ X57 @ X58 @ X59 @ X60))),
% 8.93/9.14      inference('cnf', [status(esa)], [t73_enumset1])).
% 8.93/9.14  thf('36', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.93/9.14         ((k4_enumset1 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0)
% 8.93/9.14           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 8.93/9.14      inference('sup+', [status(thm)], ['34', '35'])).
% 8.93/9.14  thf('37', plain,
% 8.93/9.14      (![X17 : $i, X18 : $i, X19 : $i]:
% 8.93/9.14         ((k1_enumset1 @ X19 @ X17 @ X18) = (k1_enumset1 @ X17 @ X18 @ X19))),
% 8.93/9.14      inference('cnf', [status(esa)], [t100_enumset1])).
% 8.93/9.14  thf('38', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.93/9.14         ((k4_enumset1 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0)
% 8.93/9.14           = (k1_enumset1 @ X1 @ X0 @ X2))),
% 8.93/9.14      inference('sup+', [status(thm)], ['36', '37'])).
% 8.93/9.14  thf('39', plain,
% 8.93/9.14      (![X56 : $i, X57 : $i, X58 : $i, X59 : $i, X60 : $i]:
% 8.93/9.14         ((k4_enumset1 @ X56 @ X56 @ X57 @ X58 @ X59 @ X60)
% 8.93/9.14           = (k3_enumset1 @ X56 @ X57 @ X58 @ X59 @ X60))),
% 8.93/9.14      inference('cnf', [status(esa)], [t73_enumset1])).
% 8.93/9.14  thf('40', plain,
% 8.93/9.14      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 8.93/9.14         ((k3_enumset1 @ X52 @ X52 @ X53 @ X54 @ X55)
% 8.93/9.14           = (k2_enumset1 @ X52 @ X53 @ X54 @ X55))),
% 8.93/9.14      inference('cnf', [status(esa)], [t72_enumset1])).
% 8.93/9.14  thf('41', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.93/9.14         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 8.93/9.14           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 8.93/9.14      inference('sup+', [status(thm)], ['39', '40'])).
% 8.93/9.14  thf('42', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.93/9.14         ((k1_enumset1 @ X2 @ X1 @ X0) = (k2_enumset1 @ X0 @ X0 @ X2 @ X1))),
% 8.93/9.14      inference('sup+', [status(thm)], ['38', '41'])).
% 8.93/9.14  thf('43', plain,
% 8.93/9.14      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 8.93/9.14         ((k3_enumset1 @ X52 @ X52 @ X53 @ X54 @ X55)
% 8.93/9.14           = (k2_enumset1 @ X52 @ X53 @ X54 @ X55))),
% 8.93/9.14      inference('cnf', [status(esa)], [t72_enumset1])).
% 8.93/9.14  thf('44', plain,
% 8.93/9.14      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 8.93/9.14         ((k2_enumset1 @ X20 @ X23 @ X21 @ X22)
% 8.93/9.14           = (k2_enumset1 @ X20 @ X21 @ X22 @ X23))),
% 8.93/9.14      inference('cnf', [status(esa)], [t105_enumset1])).
% 8.93/9.14  thf('45', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.93/9.14         ((k2_enumset1 @ X3 @ X0 @ X2 @ X1)
% 8.93/9.14           = (k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0))),
% 8.93/9.14      inference('sup+', [status(thm)], ['43', '44'])).
% 8.93/9.14  thf('46', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.93/9.14         ((k1_enumset1 @ X2 @ X1 @ X0) = (k3_enumset1 @ X0 @ X0 @ X2 @ X1 @ X0))),
% 8.93/9.14      inference('sup+', [status(thm)], ['42', '45'])).
% 8.93/9.14  thf('47', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.93/9.14         ((k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2)
% 8.93/9.14           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 8.93/9.14      inference('sup+', [status(thm)], ['11', '12'])).
% 8.93/9.14  thf('48', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.93/9.14         ((k1_enumset1 @ X2 @ X1 @ X0)
% 8.93/9.14           = (k2_xboole_0 @ (k2_tarski @ X0 @ X2) @ (k2_tarski @ X1 @ X0)))),
% 8.93/9.14      inference('sup+', [status(thm)], ['46', '47'])).
% 8.93/9.14  thf('49', plain,
% 8.93/9.14      (![X17 : $i, X18 : $i, X19 : $i]:
% 8.93/9.14         ((k1_enumset1 @ X19 @ X17 @ X18) = (k1_enumset1 @ X17 @ X18 @ X19))),
% 8.93/9.14      inference('cnf', [status(esa)], [t100_enumset1])).
% 8.93/9.14  thf('50', plain,
% 8.93/9.14      (![X47 : $i, X48 : $i]:
% 8.93/9.14         ((k1_enumset1 @ X47 @ X47 @ X48) = (k2_tarski @ X47 @ X48))),
% 8.93/9.14      inference('cnf', [status(esa)], [t70_enumset1])).
% 8.93/9.14  thf('51', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i]:
% 8.93/9.14         ((k1_enumset1 @ X0 @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 8.93/9.14      inference('sup+', [status(thm)], ['49', '50'])).
% 8.93/9.14  thf('52', plain,
% 8.93/9.14      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 8.93/9.14         ((k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8)
% 8.93/9.14           = (k2_xboole_0 @ (k1_enumset1 @ X4 @ X5 @ X6) @ 
% 8.93/9.14              (k2_tarski @ X7 @ X8)))),
% 8.93/9.14      inference('cnf', [status(esa)], [l57_enumset1])).
% 8.93/9.14  thf('53', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.93/9.14         ((k3_enumset1 @ X1 @ X0 @ X1 @ X3 @ X2)
% 8.93/9.14           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 8.93/9.14      inference('sup+', [status(thm)], ['51', '52'])).
% 8.93/9.14  thf('54', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.93/9.14         ((k3_enumset1 @ X0 @ X2 @ X0 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 8.93/9.14      inference('sup+', [status(thm)], ['48', '53'])).
% 8.93/9.14  thf('55', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.93/9.14         ((k5_enumset1 @ X0 @ X2 @ X2 @ X2 @ X0 @ X1 @ X0)
% 8.93/9.14           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 8.93/9.14      inference('sup+', [status(thm)], ['31', '54'])).
% 8.93/9.14  thf('56', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.93/9.14         ((k2_enumset1 @ X3 @ X0 @ X2 @ X1)
% 8.93/9.14           = (k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0))),
% 8.93/9.14      inference('sup+', [status(thm)], ['43', '44'])).
% 8.93/9.14  thf(t64_enumset1, axiom,
% 8.93/9.14    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 8.93/9.14     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 8.93/9.14       ( k2_xboole_0 @
% 8.93/9.14         ( k1_enumset1 @ A @ B @ C ) @ ( k3_enumset1 @ D @ E @ F @ G @ H ) ) ))).
% 8.93/9.14  thf('57', plain,
% 8.93/9.14      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, 
% 8.93/9.14         X38 : $i]:
% 8.93/9.14         ((k6_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38)
% 8.93/9.14           = (k2_xboole_0 @ (k1_enumset1 @ X31 @ X32 @ X33) @ 
% 8.93/9.14              (k3_enumset1 @ X34 @ X35 @ X36 @ X37 @ X38)))),
% 8.93/9.14      inference('cnf', [status(esa)], [t64_enumset1])).
% 8.93/9.14  thf('58', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 8.93/9.14         ((k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X3 @ X1 @ X0 @ X2)
% 8.93/9.14           = (k2_xboole_0 @ (k1_enumset1 @ X6 @ X5 @ X4) @ 
% 8.93/9.14              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 8.93/9.14      inference('sup+', [status(thm)], ['56', '57'])).
% 8.93/9.14  thf('59', plain,
% 8.93/9.14      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 8.93/9.14         ((k3_enumset1 @ X52 @ X52 @ X53 @ X54 @ X55)
% 8.93/9.14           = (k2_enumset1 @ X52 @ X53 @ X54 @ X55))),
% 8.93/9.14      inference('cnf', [status(esa)], [t72_enumset1])).
% 8.93/9.14  thf('60', plain,
% 8.93/9.14      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, 
% 8.93/9.14         X38 : $i]:
% 8.93/9.14         ((k6_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38)
% 8.93/9.14           = (k2_xboole_0 @ (k1_enumset1 @ X31 @ X32 @ X33) @ 
% 8.93/9.14              (k3_enumset1 @ X34 @ X35 @ X36 @ X37 @ X38)))),
% 8.93/9.14      inference('cnf', [status(esa)], [t64_enumset1])).
% 8.93/9.14  thf('61', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 8.93/9.14         ((k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X3 @ X2 @ X1 @ X0)
% 8.93/9.14           = (k2_xboole_0 @ (k1_enumset1 @ X6 @ X5 @ X4) @ 
% 8.93/9.14              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 8.93/9.14      inference('sup+', [status(thm)], ['59', '60'])).
% 8.93/9.14  thf('62', plain,
% 8.93/9.14      (![X49 : $i, X50 : $i, X51 : $i]:
% 8.93/9.14         ((k2_enumset1 @ X49 @ X49 @ X50 @ X51)
% 8.93/9.14           = (k1_enumset1 @ X49 @ X50 @ X51))),
% 8.93/9.14      inference('cnf', [status(esa)], [t71_enumset1])).
% 8.93/9.14  thf(l75_enumset1, axiom,
% 8.93/9.14    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 8.93/9.14     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 8.93/9.14       ( k2_xboole_0 @
% 8.93/9.14         ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ))).
% 8.93/9.14  thf('63', plain,
% 8.93/9.14      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, 
% 8.93/9.14         X16 : $i]:
% 8.93/9.14         ((k6_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16)
% 8.93/9.14           = (k2_xboole_0 @ (k2_enumset1 @ X9 @ X10 @ X11 @ X12) @ 
% 8.93/9.14              (k2_enumset1 @ X13 @ X14 @ X15 @ X16)))),
% 8.93/9.14      inference('cnf', [status(esa)], [l75_enumset1])).
% 8.93/9.14  thf('64', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 8.93/9.14         ((k6_enumset1 @ X2 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3)
% 8.93/9.14           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 8.93/9.14              (k2_enumset1 @ X6 @ X5 @ X4 @ X3)))),
% 8.93/9.14      inference('sup+', [status(thm)], ['62', '63'])).
% 8.93/9.14  thf(t75_enumset1, axiom,
% 8.93/9.14    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 8.93/9.14     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 8.93/9.14       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 8.93/9.14  thf('65', plain,
% 8.93/9.14      (![X67 : $i, X68 : $i, X69 : $i, X70 : $i, X71 : $i, X72 : $i, X73 : $i]:
% 8.93/9.14         ((k6_enumset1 @ X67 @ X67 @ X68 @ X69 @ X70 @ X71 @ X72 @ X73)
% 8.93/9.14           = (k5_enumset1 @ X67 @ X68 @ X69 @ X70 @ X71 @ X72 @ X73))),
% 8.93/9.14      inference('cnf', [status(esa)], [t75_enumset1])).
% 8.93/9.14  thf('66', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 8.93/9.14         ((k5_enumset1 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3)
% 8.93/9.14           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 8.93/9.14              (k2_enumset1 @ X6 @ X5 @ X4 @ X3)))),
% 8.93/9.14      inference('demod', [status(thm)], ['64', '65'])).
% 8.93/9.14  thf('67', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 8.93/9.14         ((k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X3 @ X2 @ X1 @ X0)
% 8.93/9.14           = (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 8.93/9.14      inference('demod', [status(thm)], ['61', '66'])).
% 8.93/9.14  thf('68', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 8.93/9.14         ((k5_enumset1 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3)
% 8.93/9.14           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 8.93/9.14              (k2_enumset1 @ X6 @ X5 @ X4 @ X3)))),
% 8.93/9.14      inference('demod', [status(thm)], ['64', '65'])).
% 8.93/9.14  thf('69', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 8.93/9.14         ((k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X1 @ X0 @ X2)
% 8.93/9.14           = (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 8.93/9.14      inference('demod', [status(thm)], ['58', '67', '68'])).
% 8.93/9.14  thf('70', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.93/9.14         ((k5_enumset1 @ X0 @ X2 @ X2 @ X2 @ X1 @ X0 @ X0)
% 8.93/9.14           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 8.93/9.14      inference('sup+', [status(thm)], ['55', '69'])).
% 8.93/9.14  thf('71', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.93/9.14         ((k4_enumset1 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0)
% 8.93/9.14           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 8.93/9.14      inference('sup+', [status(thm)], ['34', '35'])).
% 8.93/9.14  thf('72', plain,
% 8.93/9.14      (![X17 : $i, X18 : $i, X19 : $i]:
% 8.93/9.14         ((k1_enumset1 @ X19 @ X17 @ X18) = (k1_enumset1 @ X17 @ X18 @ X19))),
% 8.93/9.14      inference('cnf', [status(esa)], [t100_enumset1])).
% 8.93/9.14  thf('73', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.93/9.14         ((k1_enumset1 @ X0 @ X2 @ X1)
% 8.93/9.14           = (k4_enumset1 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0))),
% 8.93/9.14      inference('sup+', [status(thm)], ['71', '72'])).
% 8.93/9.14  thf('74', plain,
% 8.93/9.14      (![X56 : $i, X57 : $i, X58 : $i, X59 : $i, X60 : $i]:
% 8.93/9.14         ((k4_enumset1 @ X56 @ X56 @ X57 @ X58 @ X59 @ X60)
% 8.93/9.14           = (k3_enumset1 @ X56 @ X57 @ X58 @ X59 @ X60))),
% 8.93/9.14      inference('cnf', [status(esa)], [t73_enumset1])).
% 8.93/9.14  thf('75', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.93/9.14         ((k1_enumset1 @ X2 @ X1 @ X0) = (k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2))),
% 8.93/9.14      inference('sup+', [status(thm)], ['73', '74'])).
% 8.93/9.14  thf('76', plain,
% 8.93/9.14      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, 
% 8.93/9.14         X38 : $i]:
% 8.93/9.14         ((k6_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38)
% 8.93/9.14           = (k2_xboole_0 @ (k1_enumset1 @ X31 @ X32 @ X33) @ 
% 8.93/9.14              (k3_enumset1 @ X34 @ X35 @ X36 @ X37 @ X38)))),
% 8.93/9.14      inference('cnf', [status(esa)], [t64_enumset1])).
% 8.93/9.14  thf('77', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 8.93/9.14         ((k6_enumset1 @ X5 @ X4 @ X3 @ X1 @ X1 @ X1 @ X0 @ X2)
% 8.93/9.14           = (k2_xboole_0 @ (k1_enumset1 @ X5 @ X4 @ X3) @ 
% 8.93/9.14              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 8.93/9.14      inference('sup+', [status(thm)], ['75', '76'])).
% 8.93/9.14  thf('78', plain,
% 8.93/9.14      (![X49 : $i, X50 : $i, X51 : $i]:
% 8.93/9.14         ((k2_enumset1 @ X49 @ X49 @ X50 @ X51)
% 8.93/9.14           = (k1_enumset1 @ X49 @ X50 @ X51))),
% 8.93/9.14      inference('cnf', [status(esa)], [t71_enumset1])).
% 8.93/9.14  thf('79', plain,
% 8.93/9.14      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 8.93/9.14         ((k2_enumset1 @ X20 @ X23 @ X21 @ X22)
% 8.93/9.14           = (k2_enumset1 @ X20 @ X21 @ X22 @ X23))),
% 8.93/9.14      inference('cnf', [status(esa)], [t105_enumset1])).
% 8.93/9.14  thf('80', plain,
% 8.93/9.14      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, 
% 8.93/9.14         X16 : $i]:
% 8.93/9.14         ((k6_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16)
% 8.93/9.14           = (k2_xboole_0 @ (k2_enumset1 @ X9 @ X10 @ X11 @ X12) @ 
% 8.93/9.14              (k2_enumset1 @ X13 @ X14 @ X15 @ X16)))),
% 8.93/9.14      inference('cnf', [status(esa)], [l75_enumset1])).
% 8.93/9.14  thf('81', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 8.93/9.14         ((k6_enumset1 @ X3 @ X1 @ X0 @ X2 @ X7 @ X6 @ X5 @ X4)
% 8.93/9.14           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 8.93/9.14              (k2_enumset1 @ X7 @ X6 @ X5 @ X4)))),
% 8.93/9.14      inference('sup+', [status(thm)], ['79', '80'])).
% 8.93/9.14  thf('82', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 8.93/9.14         ((k6_enumset1 @ X6 @ X4 @ X3 @ X5 @ X2 @ X2 @ X1 @ X0)
% 8.93/9.14           = (k2_xboole_0 @ (k2_enumset1 @ X6 @ X5 @ X4 @ X3) @ 
% 8.93/9.14              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 8.93/9.14      inference('sup+', [status(thm)], ['78', '81'])).
% 8.93/9.14  thf('83', plain,
% 8.93/9.14      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 8.93/9.14         ((k3_enumset1 @ X52 @ X52 @ X53 @ X54 @ X55)
% 8.93/9.14           = (k2_enumset1 @ X52 @ X53 @ X54 @ X55))),
% 8.93/9.14      inference('cnf', [status(esa)], [t72_enumset1])).
% 8.93/9.14  thf('84', plain,
% 8.93/9.14      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 8.93/9.14         ((k2_enumset1 @ X20 @ X23 @ X21 @ X22)
% 8.93/9.14           = (k2_enumset1 @ X20 @ X21 @ X22 @ X23))),
% 8.93/9.14      inference('cnf', [status(esa)], [t105_enumset1])).
% 8.93/9.14  thf('85', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.93/9.14         ((k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0)
% 8.93/9.14           = (k2_enumset1 @ X3 @ X1 @ X0 @ X2))),
% 8.93/9.14      inference('sup+', [status(thm)], ['83', '84'])).
% 8.93/9.14  thf(t66_enumset1, axiom,
% 8.93/9.14    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 8.93/9.14     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 8.93/9.14       ( k2_xboole_0 @
% 8.93/9.14         ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_enumset1 @ F @ G @ H ) ) ))).
% 8.93/9.14  thf('86', plain,
% 8.93/9.14      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, 
% 8.93/9.14         X46 : $i]:
% 8.93/9.14         ((k6_enumset1 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46)
% 8.93/9.14           = (k2_xboole_0 @ (k3_enumset1 @ X39 @ X40 @ X41 @ X42 @ X43) @ 
% 8.93/9.14              (k1_enumset1 @ X44 @ X45 @ X46)))),
% 8.93/9.14      inference('cnf', [status(esa)], [t66_enumset1])).
% 8.93/9.14  thf('87', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 8.93/9.14         ((k6_enumset1 @ X3 @ X3 @ X0 @ X2 @ X1 @ X6 @ X5 @ X4)
% 8.93/9.14           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 8.93/9.14              (k1_enumset1 @ X6 @ X5 @ X4)))),
% 8.93/9.14      inference('sup+', [status(thm)], ['85', '86'])).
% 8.93/9.14  thf('88', plain,
% 8.93/9.14      (![X67 : $i, X68 : $i, X69 : $i, X70 : $i, X71 : $i, X72 : $i, X73 : $i]:
% 8.93/9.14         ((k6_enumset1 @ X67 @ X67 @ X68 @ X69 @ X70 @ X71 @ X72 @ X73)
% 8.93/9.14           = (k5_enumset1 @ X67 @ X68 @ X69 @ X70 @ X71 @ X72 @ X73))),
% 8.93/9.14      inference('cnf', [status(esa)], [t75_enumset1])).
% 8.93/9.14  thf('89', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 8.93/9.14         ((k5_enumset1 @ X3 @ X0 @ X2 @ X1 @ X6 @ X5 @ X4)
% 8.93/9.14           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 8.93/9.14              (k1_enumset1 @ X6 @ X5 @ X4)))),
% 8.93/9.14      inference('demod', [status(thm)], ['87', '88'])).
% 8.93/9.14  thf('90', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 8.93/9.14         ((k6_enumset1 @ X6 @ X4 @ X3 @ X5 @ X2 @ X2 @ X1 @ X0)
% 8.93/9.14           = (k5_enumset1 @ X6 @ X3 @ X5 @ X4 @ X2 @ X1 @ X0))),
% 8.93/9.14      inference('demod', [status(thm)], ['82', '89'])).
% 8.93/9.14  thf('91', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.93/9.14         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 8.93/9.14      inference('sup+', [status(thm)], ['32', '33'])).
% 8.93/9.14  thf('92', plain,
% 8.93/9.14      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, 
% 8.93/9.14         X46 : $i]:
% 8.93/9.14         ((k6_enumset1 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46)
% 8.93/9.14           = (k2_xboole_0 @ (k3_enumset1 @ X39 @ X40 @ X41 @ X42 @ X43) @ 
% 8.93/9.14              (k1_enumset1 @ X44 @ X45 @ X46)))),
% 8.93/9.14      inference('cnf', [status(esa)], [t66_enumset1])).
% 8.93/9.14  thf('93', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 8.93/9.14         ((k6_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3)
% 8.93/9.14           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 8.93/9.14              (k1_enumset1 @ X5 @ X4 @ X3)))),
% 8.93/9.14      inference('sup+', [status(thm)], ['91', '92'])).
% 8.93/9.14  thf('94', plain,
% 8.93/9.14      (![X67 : $i, X68 : $i, X69 : $i, X70 : $i, X71 : $i, X72 : $i, X73 : $i]:
% 8.93/9.14         ((k6_enumset1 @ X67 @ X67 @ X68 @ X69 @ X70 @ X71 @ X72 @ X73)
% 8.93/9.14           = (k5_enumset1 @ X67 @ X68 @ X69 @ X70 @ X71 @ X72 @ X73))),
% 8.93/9.14      inference('cnf', [status(esa)], [t75_enumset1])).
% 8.93/9.14  thf('95', plain,
% 8.93/9.14      (![X61 : $i, X62 : $i, X63 : $i, X64 : $i, X65 : $i, X66 : $i]:
% 8.93/9.14         ((k5_enumset1 @ X61 @ X61 @ X62 @ X63 @ X64 @ X65 @ X66)
% 8.93/9.14           = (k4_enumset1 @ X61 @ X62 @ X63 @ X64 @ X65 @ X66))),
% 8.93/9.14      inference('cnf', [status(esa)], [t74_enumset1])).
% 8.93/9.14  thf('96', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 8.93/9.14         ((k4_enumset1 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3)
% 8.93/9.14           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 8.93/9.14              (k1_enumset1 @ X5 @ X4 @ X3)))),
% 8.93/9.14      inference('demod', [status(thm)], ['93', '94', '95'])).
% 8.93/9.14  thf('97', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 8.93/9.14         ((k5_enumset1 @ X5 @ X3 @ X1 @ X4 @ X1 @ X0 @ X2)
% 8.93/9.14           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 8.93/9.14      inference('demod', [status(thm)], ['77', '90', '96'])).
% 8.93/9.14  thf('98', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i]:
% 8.93/9.14         ((k1_enumset1 @ X1 @ X1 @ X0)
% 8.93/9.14           = (k4_enumset1 @ X0 @ X1 @ X1 @ X0 @ X1 @ X0))),
% 8.93/9.14      inference('sup+', [status(thm)], ['70', '97'])).
% 8.93/9.14  thf('99', plain,
% 8.93/9.14      (![X47 : $i, X48 : $i]:
% 8.93/9.14         ((k1_enumset1 @ X47 @ X47 @ X48) = (k2_tarski @ X47 @ X48))),
% 8.93/9.14      inference('cnf', [status(esa)], [t70_enumset1])).
% 8.93/9.14  thf('100', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i]:
% 8.93/9.14         ((k2_tarski @ X1 @ X0) = (k4_enumset1 @ X0 @ X1 @ X1 @ X0 @ X1 @ X0))),
% 8.93/9.14      inference('demod', [status(thm)], ['98', '99'])).
% 8.93/9.14  thf('101', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i]:
% 8.93/9.14         ((k2_tarski @ X1 @ X0) = (k3_enumset1 @ X0 @ X1 @ X1 @ X1 @ X0))),
% 8.93/9.14      inference('sup+', [status(thm)], ['10', '100'])).
% 8.93/9.14  thf('102', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.93/9.14         ((k3_enumset1 @ X0 @ X2 @ X2 @ X2 @ X1) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 8.93/9.14      inference('sup+', [status(thm)], ['19', '24'])).
% 8.93/9.14  thf('103', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i]:
% 8.93/9.14         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X0))),
% 8.93/9.14      inference('demod', [status(thm)], ['101', '102'])).
% 8.93/9.14  thf('104', plain,
% 8.93/9.14      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 8.93/9.14         ((k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8)
% 8.93/9.14           = (k2_xboole_0 @ (k1_enumset1 @ X4 @ X5 @ X6) @ 
% 8.93/9.14              (k2_tarski @ X7 @ X8)))),
% 8.93/9.14      inference('cnf', [status(esa)], [l57_enumset1])).
% 8.93/9.14  thf('105', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.93/9.14         ((k3_enumset1 @ X1 @ X0 @ X0 @ X3 @ X2)
% 8.93/9.14           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 8.93/9.14      inference('sup+', [status(thm)], ['103', '104'])).
% 8.93/9.14  thf('106', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.93/9.14         ((k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2)
% 8.93/9.14           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 8.93/9.14      inference('sup+', [status(thm)], ['11', '12'])).
% 8.93/9.14  thf('107', plain,
% 8.93/9.14      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 8.93/9.14         ((k3_enumset1 @ X52 @ X52 @ X53 @ X54 @ X55)
% 8.93/9.14           = (k2_enumset1 @ X52 @ X53 @ X54 @ X55))),
% 8.93/9.14      inference('cnf', [status(esa)], [t72_enumset1])).
% 8.93/9.14  thf('108', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.93/9.14         ((k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0))
% 8.93/9.14           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 8.93/9.14      inference('sup+', [status(thm)], ['106', '107'])).
% 8.93/9.14  thf('109', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.93/9.14         ((k3_enumset1 @ X1 @ X0 @ X0 @ X3 @ X2)
% 8.93/9.14           = (k2_enumset1 @ X1 @ X0 @ X3 @ X2))),
% 8.93/9.14      inference('demod', [status(thm)], ['105', '108'])).
% 8.93/9.14  thf('110', plain,
% 8.93/9.14      (![X17 : $i, X18 : $i, X19 : $i]:
% 8.93/9.14         ((k1_enumset1 @ X19 @ X17 @ X18) = (k1_enumset1 @ X17 @ X18 @ X19))),
% 8.93/9.14      inference('cnf', [status(esa)], [t100_enumset1])).
% 8.93/9.14  thf('111', plain,
% 8.93/9.14      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 8.93/9.14         ((k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8)
% 8.93/9.14           = (k2_xboole_0 @ (k1_enumset1 @ X4 @ X5 @ X6) @ 
% 8.93/9.14              (k2_tarski @ X7 @ X8)))),
% 8.93/9.14      inference('cnf', [status(esa)], [l57_enumset1])).
% 8.93/9.14  thf('112', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 8.93/9.14         ((k3_enumset1 @ X1 @ X0 @ X2 @ X4 @ X3)
% 8.93/9.14           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 8.93/9.14              (k2_tarski @ X4 @ X3)))),
% 8.93/9.14      inference('sup+', [status(thm)], ['110', '111'])).
% 8.93/9.14  thf('113', plain,
% 8.93/9.14      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 8.93/9.14         ((k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8)
% 8.93/9.14           = (k2_xboole_0 @ (k1_enumset1 @ X4 @ X5 @ X6) @ 
% 8.93/9.14              (k2_tarski @ X7 @ X8)))),
% 8.93/9.14      inference('cnf', [status(esa)], [l57_enumset1])).
% 8.93/9.14  thf('114', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 8.93/9.14         ((k3_enumset1 @ X2 @ X4 @ X3 @ X1 @ X0)
% 8.93/9.14           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 8.93/9.14      inference('sup+', [status(thm)], ['112', '113'])).
% 8.93/9.14  thf('115', plain,
% 8.93/9.14      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 8.93/9.14         ((k3_enumset1 @ X52 @ X52 @ X53 @ X54 @ X55)
% 8.93/9.14           = (k2_enumset1 @ X52 @ X53 @ X54 @ X55))),
% 8.93/9.14      inference('cnf', [status(esa)], [t72_enumset1])).
% 8.93/9.14  thf('116', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.93/9.14         ((k3_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0)
% 8.93/9.14           = (k2_enumset1 @ X2 @ X3 @ X1 @ X0))),
% 8.93/9.14      inference('sup+', [status(thm)], ['114', '115'])).
% 8.93/9.14  thf('117', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.93/9.14         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X2 @ X3 @ X1 @ X0))),
% 8.93/9.14      inference('sup+', [status(thm)], ['109', '116'])).
% 8.93/9.14  thf('118', plain,
% 8.93/9.14      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 8.93/9.14         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 8.93/9.14      inference('demod', [status(thm)], ['0', '117'])).
% 8.93/9.14  thf('119', plain, ($false), inference('simplify', [status(thm)], ['118'])).
% 8.93/9.14  
% 8.93/9.14  % SZS output end Refutation
% 8.93/9.14  
% 8.93/9.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

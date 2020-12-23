%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PqFXPWFxeS

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:30 EST 2020

% Result     : Theorem 10.52s
% Output     : Refutation 10.52s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 683 expanded)
%              Number of leaves         :   24 ( 238 expanded)
%              Depth                    :   20
%              Number of atoms          : 1640 (7699 expanded)
%              Number of equality atoms :  135 ( 671 expanded)
%              Maximal formula depth    :   16 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ! [X55: $i,X56: $i] :
      ( ( k1_enumset1 @ X55 @ X55 @ X56 )
      = ( k2_tarski @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('2',plain,(
    ! [X55: $i,X56: $i] :
      ( ( k1_enumset1 @ X55 @ X55 @ X56 )
      = ( k2_tarski @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(l62_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_enumset1 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X8 @ X9 @ X10 ) @ ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l62_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X1 @ X1 @ X0 @ X4 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_enumset1 @ X4 @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('5',plain,(
    ! [X64: $i,X65: $i,X66: $i,X67: $i,X68: $i] :
      ( ( k4_enumset1 @ X64 @ X64 @ X65 @ X66 @ X67 @ X68 )
      = ( k3_enumset1 @ X64 @ X65 @ X66 @ X67 @ X68 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X1 @ X0 @ X4 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_enumset1 @ X4 @ X3 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','6'])).

thf('8',plain,(
    ( k3_enumset1 @ sk_B @ sk_A @ sk_C @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','7'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('10',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ( k2_enumset1 @ X57 @ X57 @ X58 @ X59 )
      = ( k1_enumset1 @ X57 @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('11',plain,(
    ! [X55: $i,X56: $i] :
      ( ( k1_enumset1 @ X55 @ X55 @ X56 )
      = ( k2_tarski @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('13',plain,(
    ! [X60: $i,X61: $i,X62: $i,X63: $i] :
      ( ( k3_enumset1 @ X60 @ X60 @ X61 @ X62 @ X63 )
      = ( k2_enumset1 @ X60 @ X61 @ X62 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t55_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ) )).

thf('14',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k4_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 ) @ ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t55_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X64: $i,X65: $i,X66: $i,X67: $i,X68: $i] :
      ( ( k4_enumset1 @ X64 @ X64 @ X65 @ X66 @ X67 @ X68 )
      = ( k3_enumset1 @ X64 @ X65 @ X66 @ X67 @ X68 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['12','17'])).

thf('19',plain,(
    ! [X60: $i,X61: $i,X62: $i,X63: $i] :
      ( ( k3_enumset1 @ X60 @ X60 @ X61 @ X62 @ X63 )
      = ( k2_enumset1 @ X60 @ X61 @ X62 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ( k2_enumset1 @ X57 @ X57 @ X58 @ X59 )
      = ( k1_enumset1 @ X57 @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['9','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ( k3_enumset1 @ sk_B @ sk_A @ sk_C @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['8','25'])).

thf('27',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ( k2_enumset1 @ X57 @ X57 @ X58 @ X59 )
      = ( k1_enumset1 @ X57 @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X60: $i,X61: $i,X62: $i,X63: $i] :
      ( ( k3_enumset1 @ X60 @ X60 @ X61 @ X62 @ X63 )
      = ( k2_enumset1 @ X60 @ X61 @ X62 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('31',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k2_enumset1 @ X14 @ X15 @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k1_tarski @ X14 ) @ ( k1_enumset1 @ X15 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30','33'])).

thf('35',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ( k2_enumset1 @ X57 @ X57 @ X58 @ X59 )
      = ( k1_enumset1 @ X57 @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X55: $i,X56: $i] :
      ( ( k1_enumset1 @ X55 @ X55 @ X56 )
      = ( k2_tarski @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('38',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_enumset1 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X8 @ X9 @ X10 ) @ ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l62_enumset1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('41',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('42',plain,(
    ! [X55: $i,X56: $i] :
      ( ( k1_enumset1 @ X55 @ X55 @ X56 )
      = ( k2_tarski @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('43',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k2_enumset1 @ X14 @ X15 @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k1_tarski @ X14 ) @ ( k1_enumset1 @ X15 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['41','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_enumset1 @ X0 @ X1 @ X1 @ X0 ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X0 @ X1 @ X1 @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['40','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X0 @ X1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k3_enumset1 @ X0 @ X1 @ X1 @ X0 @ X0 ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k4_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 ) @ ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t55_enumset1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 ) )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_enumset1 @ X0 @ X1 @ X1 @ X0 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X0 @ X1 @ X1 ) @ ( k2_tarski @ X0 @ X0 ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','60'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('62',plain,(
    ! [X54: $i] :
      ( ( k2_tarski @ X54 @ X54 )
      = ( k1_tarski @ X54 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X1 @ X1 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X0 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X60: $i,X61: $i,X62: $i,X63: $i] :
      ( ( k3_enumset1 @ X60 @ X60 @ X61 @ X62 @ X63 )
      = ( k2_enumset1 @ X60 @ X61 @ X62 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['9','22'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X0 @ X2 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['36','70'])).

thf('72',plain,(
    ( k3_enumset1 @ sk_B @ sk_A @ sk_C @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['26','71'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('73',plain,(
    ! [X69: $i,X70: $i,X71: $i,X72: $i,X73: $i,X74: $i] :
      ( ( k5_enumset1 @ X69 @ X69 @ X70 @ X71 @ X72 @ X73 @ X74 )
      = ( k4_enumset1 @ X69 @ X70 @ X71 @ X72 @ X73 @ X74 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('74',plain,(
    ! [X60: $i,X61: $i,X62: $i,X63: $i] :
      ( ( k3_enumset1 @ X60 @ X60 @ X61 @ X62 @ X63 )
      = ( k2_enumset1 @ X60 @ X61 @ X62 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t57_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k3_enumset1 @ C @ D @ E @ F @ G ) ) ) )).

thf('75',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k5_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 )
      = ( k2_xboole_0 @ ( k2_tarski @ X31 @ X32 ) @ ( k3_enumset1 @ X33 @ X34 @ X35 @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t57_enumset1])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X5 @ X4 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['73','76'])).

thf('78',plain,(
    ! [X54: $i] :
      ( ( k2_tarski @ X54 @ X54 )
      = ( k1_tarski @ X54 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X1 @ X1 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('81',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_enumset1 @ X1 @ X1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ( k2_enumset1 @ X57 @ X57 @ X58 @ X59 )
      = ( k1_enumset1 @ X57 @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('84',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_enumset1 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X8 @ X9 @ X10 ) @ ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l62_enumset1])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) @ ( k1_enumset1 @ X5 @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X0 @ X1 @ X1 @ X4 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_enumset1 @ X4 @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['82','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X1 @ X0 @ X4 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_enumset1 @ X4 @ X3 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X0 @ X1 @ X1 @ X4 @ X3 @ X2 )
      = ( k3_enumset1 @ X1 @ X0 @ X4 @ X3 @ X2 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X60: $i,X61: $i,X62: $i,X63: $i] :
      ( ( k3_enumset1 @ X60 @ X60 @ X61 @ X62 @ X63 )
      = ( k2_enumset1 @ X60 @ X61 @ X62 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 ) )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X64: $i,X65: $i,X66: $i,X67: $i,X68: $i] :
      ( ( k4_enumset1 @ X64 @ X64 @ X65 @ X66 @ X67 @ X68 )
      = ( k3_enumset1 @ X64 @ X65 @ X66 @ X67 @ X68 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X4 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 ) ) ),
    inference(demod,[status(thm)],['79','88','93'])).

thf('95',plain,(
    ( k3_enumset1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['72','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_enumset1 @ X0 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X1 @ X0 @ X0 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('102',plain,(
    ! [X60: $i,X61: $i,X62: $i,X63: $i] :
      ( ( k3_enumset1 @ X60 @ X60 @ X61 @ X62 @ X63 )
      = ( k2_enumset1 @ X60 @ X61 @ X62 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X1 @ X0 @ X0 @ X1 @ X2 )
      = ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k4_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 ) @ ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t55_enumset1])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X2 @ X1 @ X1 @ X2 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('107',plain,(
    ! [X60: $i,X61: $i,X62: $i,X63: $i] :
      ( ( k3_enumset1 @ X60 @ X60 @ X61 @ X62 @ X63 )
      = ( k2_enumset1 @ X60 @ X61 @ X62 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X2 @ X1 @ X1 @ X2 @ X0 @ X3 )
      = ( k2_enumset1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X0 @ X1 @ X1 @ X4 @ X3 @ X2 )
      = ( k3_enumset1 @ X1 @ X0 @ X4 @ X3 @ X2 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X2 @ X2 @ X0 @ X3 )
      = ( k2_enumset1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X0 @ X2 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X1 @ X1 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_enumset1 @ X1 @ X1 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ( k2_enumset1 @ X57 @ X57 @ X58 @ X59 )
      = ( k1_enumset1 @ X57 @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('116',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k2_enumset1 @ X14 @ X15 @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k1_tarski @ X14 ) @ ( k1_enumset1 @ X15 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['114','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X1 @ X2 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['111','118'])).

thf('120',plain,(
    ( k1_enumset1 @ sk_B @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['95','110','119'])).

thf('121',plain,(
    $false ),
    inference(simplify,[status(thm)],['120'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PqFXPWFxeS
% 0.17/0.38  % Computer   : n017.cluster.edu
% 0.17/0.38  % Model      : x86_64 x86_64
% 0.17/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.38  % Memory     : 8042.1875MB
% 0.17/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.38  % CPULimit   : 60
% 0.17/0.38  % DateTime   : Tue Dec  1 11:19:01 EST 2020
% 0.17/0.38  % CPUTime    : 
% 0.17/0.38  % Running portfolio for 600 s
% 0.17/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.39  % Number of cores: 8
% 0.17/0.39  % Python version: Python 3.6.8
% 0.17/0.39  % Running in FO mode
% 10.52/10.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 10.52/10.72  % Solved by: fo/fo7.sh
% 10.52/10.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 10.52/10.72  % done 10955 iterations in 10.226s
% 10.52/10.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 10.52/10.72  % SZS output start Refutation
% 10.52/10.72  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 10.52/10.72  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 10.52/10.72  thf(sk_A_type, type, sk_A: $i).
% 10.52/10.72  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 10.52/10.72  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 10.52/10.72  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 10.52/10.72  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 10.52/10.72  thf(sk_B_type, type, sk_B: $i).
% 10.52/10.72  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 10.52/10.72  thf(sk_C_type, type, sk_C: $i).
% 10.52/10.72  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 10.52/10.72  thf(t137_enumset1, conjecture,
% 10.52/10.72    (![A:$i,B:$i,C:$i]:
% 10.52/10.72     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 10.52/10.72       ( k1_enumset1 @ A @ B @ C ) ))).
% 10.52/10.72  thf(zf_stmt_0, negated_conjecture,
% 10.52/10.72    (~( ![A:$i,B:$i,C:$i]:
% 10.52/10.72        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 10.52/10.72          ( k1_enumset1 @ A @ B @ C ) ) )),
% 10.52/10.72    inference('cnf.neg', [status(esa)], [t137_enumset1])).
% 10.52/10.72  thf('0', plain,
% 10.52/10.72      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 10.52/10.72         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 10.52/10.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.52/10.72  thf(t70_enumset1, axiom,
% 10.52/10.72    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 10.52/10.72  thf('1', plain,
% 10.52/10.72      (![X55 : $i, X56 : $i]:
% 10.52/10.72         ((k1_enumset1 @ X55 @ X55 @ X56) = (k2_tarski @ X55 @ X56))),
% 10.52/10.72      inference('cnf', [status(esa)], [t70_enumset1])).
% 10.52/10.72  thf('2', plain,
% 10.52/10.72      (![X55 : $i, X56 : $i]:
% 10.52/10.72         ((k1_enumset1 @ X55 @ X55 @ X56) = (k2_tarski @ X55 @ X56))),
% 10.52/10.72      inference('cnf', [status(esa)], [t70_enumset1])).
% 10.52/10.72  thf(l62_enumset1, axiom,
% 10.52/10.72    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 10.52/10.72     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 10.52/10.72       ( k2_xboole_0 @
% 10.52/10.72         ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ))).
% 10.52/10.72  thf('3', plain,
% 10.52/10.72      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 10.52/10.72         ((k4_enumset1 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13)
% 10.52/10.72           = (k2_xboole_0 @ (k1_enumset1 @ X8 @ X9 @ X10) @ 
% 10.52/10.72              (k1_enumset1 @ X11 @ X12 @ X13)))),
% 10.52/10.72      inference('cnf', [status(esa)], [l62_enumset1])).
% 10.52/10.72  thf('4', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 10.52/10.72         ((k4_enumset1 @ X1 @ X1 @ X0 @ X4 @ X3 @ X2)
% 10.52/10.72           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 10.52/10.72              (k1_enumset1 @ X4 @ X3 @ X2)))),
% 10.52/10.72      inference('sup+', [status(thm)], ['2', '3'])).
% 10.52/10.72  thf(t73_enumset1, axiom,
% 10.52/10.72    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 10.52/10.72     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 10.52/10.72       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 10.52/10.72  thf('5', plain,
% 10.52/10.72      (![X64 : $i, X65 : $i, X66 : $i, X67 : $i, X68 : $i]:
% 10.52/10.72         ((k4_enumset1 @ X64 @ X64 @ X65 @ X66 @ X67 @ X68)
% 10.52/10.72           = (k3_enumset1 @ X64 @ X65 @ X66 @ X67 @ X68))),
% 10.52/10.72      inference('cnf', [status(esa)], [t73_enumset1])).
% 10.52/10.72  thf('6', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 10.52/10.72         ((k3_enumset1 @ X1 @ X0 @ X4 @ X3 @ X2)
% 10.52/10.72           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 10.52/10.72              (k1_enumset1 @ X4 @ X3 @ X2)))),
% 10.52/10.72      inference('demod', [status(thm)], ['4', '5'])).
% 10.52/10.72  thf('7', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.52/10.72         ((k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0)
% 10.52/10.72           = (k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0)))),
% 10.52/10.72      inference('sup+', [status(thm)], ['1', '6'])).
% 10.52/10.72  thf('8', plain,
% 10.52/10.72      (((k3_enumset1 @ sk_B @ sk_A @ sk_C @ sk_C @ sk_A)
% 10.52/10.72         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 10.52/10.72      inference('demod', [status(thm)], ['0', '7'])).
% 10.52/10.72  thf(commutativity_k2_tarski, axiom,
% 10.52/10.72    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 10.52/10.72  thf('9', plain,
% 10.52/10.72      (![X6 : $i, X7 : $i]: ((k2_tarski @ X7 @ X6) = (k2_tarski @ X6 @ X7))),
% 10.52/10.72      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 10.52/10.72  thf(t71_enumset1, axiom,
% 10.52/10.72    (![A:$i,B:$i,C:$i]:
% 10.52/10.72     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 10.52/10.72  thf('10', plain,
% 10.52/10.72      (![X57 : $i, X58 : $i, X59 : $i]:
% 10.52/10.72         ((k2_enumset1 @ X57 @ X57 @ X58 @ X59)
% 10.52/10.72           = (k1_enumset1 @ X57 @ X58 @ X59))),
% 10.52/10.72      inference('cnf', [status(esa)], [t71_enumset1])).
% 10.52/10.72  thf('11', plain,
% 10.52/10.72      (![X55 : $i, X56 : $i]:
% 10.52/10.72         ((k1_enumset1 @ X55 @ X55 @ X56) = (k2_tarski @ X55 @ X56))),
% 10.52/10.72      inference('cnf', [status(esa)], [t70_enumset1])).
% 10.52/10.72  thf('12', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i]:
% 10.52/10.72         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 10.52/10.72      inference('sup+', [status(thm)], ['10', '11'])).
% 10.52/10.72  thf(t72_enumset1, axiom,
% 10.52/10.72    (![A:$i,B:$i,C:$i,D:$i]:
% 10.52/10.72     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 10.52/10.72  thf('13', plain,
% 10.52/10.72      (![X60 : $i, X61 : $i, X62 : $i, X63 : $i]:
% 10.52/10.72         ((k3_enumset1 @ X60 @ X60 @ X61 @ X62 @ X63)
% 10.52/10.72           = (k2_enumset1 @ X60 @ X61 @ X62 @ X63))),
% 10.52/10.72      inference('cnf', [status(esa)], [t72_enumset1])).
% 10.52/10.72  thf(t55_enumset1, axiom,
% 10.52/10.72    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 10.52/10.72     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 10.52/10.72       ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ))).
% 10.52/10.72  thf('14', plain,
% 10.52/10.72      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 10.52/10.72         ((k4_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23)
% 10.52/10.72           = (k2_xboole_0 @ (k3_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22) @ 
% 10.52/10.72              (k1_tarski @ X23)))),
% 10.52/10.72      inference('cnf', [status(esa)], [t55_enumset1])).
% 10.52/10.72  thf('15', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 10.52/10.72         ((k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4)
% 10.52/10.72           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 10.52/10.72              (k1_tarski @ X4)))),
% 10.52/10.72      inference('sup+', [status(thm)], ['13', '14'])).
% 10.52/10.72  thf('16', plain,
% 10.52/10.72      (![X64 : $i, X65 : $i, X66 : $i, X67 : $i, X68 : $i]:
% 10.52/10.72         ((k4_enumset1 @ X64 @ X64 @ X65 @ X66 @ X67 @ X68)
% 10.52/10.72           = (k3_enumset1 @ X64 @ X65 @ X66 @ X67 @ X68))),
% 10.52/10.72      inference('cnf', [status(esa)], [t73_enumset1])).
% 10.52/10.72  thf('17', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 10.52/10.72         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 10.52/10.72           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 10.52/10.72              (k1_tarski @ X4)))),
% 10.52/10.72      inference('demod', [status(thm)], ['15', '16'])).
% 10.52/10.72  thf('18', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.52/10.72         ((k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2)
% 10.52/10.72           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 10.52/10.72      inference('sup+', [status(thm)], ['12', '17'])).
% 10.52/10.72  thf('19', plain,
% 10.52/10.72      (![X60 : $i, X61 : $i, X62 : $i, X63 : $i]:
% 10.52/10.72         ((k3_enumset1 @ X60 @ X60 @ X61 @ X62 @ X63)
% 10.52/10.72           = (k2_enumset1 @ X60 @ X61 @ X62 @ X63))),
% 10.52/10.72      inference('cnf', [status(esa)], [t72_enumset1])).
% 10.52/10.72  thf('20', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.52/10.72         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 10.52/10.72           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 10.52/10.72      inference('demod', [status(thm)], ['18', '19'])).
% 10.52/10.72  thf('21', plain,
% 10.52/10.72      (![X57 : $i, X58 : $i, X59 : $i]:
% 10.52/10.72         ((k2_enumset1 @ X57 @ X57 @ X58 @ X59)
% 10.52/10.72           = (k1_enumset1 @ X57 @ X58 @ X59))),
% 10.52/10.72      inference('cnf', [status(esa)], [t71_enumset1])).
% 10.52/10.72  thf('22', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.52/10.72         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 10.52/10.72           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 10.52/10.72      inference('sup+', [status(thm)], ['20', '21'])).
% 10.52/10.72  thf('23', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.52/10.72         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2))
% 10.52/10.72           = (k1_enumset1 @ X0 @ X1 @ X2))),
% 10.52/10.72      inference('sup+', [status(thm)], ['9', '22'])).
% 10.52/10.72  thf('24', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.52/10.72         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 10.52/10.72           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 10.52/10.72      inference('sup+', [status(thm)], ['20', '21'])).
% 10.52/10.72  thf('25', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.52/10.72         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 10.52/10.72      inference('sup+', [status(thm)], ['23', '24'])).
% 10.52/10.72  thf('26', plain,
% 10.52/10.72      (((k3_enumset1 @ sk_B @ sk_A @ sk_C @ sk_C @ sk_A)
% 10.52/10.72         != (k1_enumset1 @ sk_B @ sk_A @ sk_C))),
% 10.52/10.72      inference('demod', [status(thm)], ['8', '25'])).
% 10.52/10.72  thf('27', plain,
% 10.52/10.72      (![X57 : $i, X58 : $i, X59 : $i]:
% 10.52/10.72         ((k2_enumset1 @ X57 @ X57 @ X58 @ X59)
% 10.52/10.72           = (k1_enumset1 @ X57 @ X58 @ X59))),
% 10.52/10.72      inference('cnf', [status(esa)], [t71_enumset1])).
% 10.52/10.72  thf('28', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 10.52/10.72         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 10.52/10.72           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 10.52/10.72              (k1_tarski @ X4)))),
% 10.52/10.72      inference('demod', [status(thm)], ['15', '16'])).
% 10.52/10.72  thf('29', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.52/10.72         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3)
% 10.52/10.72           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 10.52/10.72      inference('sup+', [status(thm)], ['27', '28'])).
% 10.52/10.72  thf('30', plain,
% 10.52/10.72      (![X60 : $i, X61 : $i, X62 : $i, X63 : $i]:
% 10.52/10.72         ((k3_enumset1 @ X60 @ X60 @ X61 @ X62 @ X63)
% 10.52/10.72           = (k2_enumset1 @ X60 @ X61 @ X62 @ X63))),
% 10.52/10.72      inference('cnf', [status(esa)], [t72_enumset1])).
% 10.52/10.72  thf(t44_enumset1, axiom,
% 10.52/10.72    (![A:$i,B:$i,C:$i,D:$i]:
% 10.52/10.72     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 10.52/10.72       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 10.52/10.72  thf('31', plain,
% 10.52/10.72      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 10.52/10.72         ((k2_enumset1 @ X14 @ X15 @ X16 @ X17)
% 10.52/10.72           = (k2_xboole_0 @ (k1_tarski @ X14) @ (k1_enumset1 @ X15 @ X16 @ X17)))),
% 10.52/10.72      inference('cnf', [status(esa)], [t44_enumset1])).
% 10.52/10.72  thf(commutativity_k2_xboole_0, axiom,
% 10.52/10.72    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 10.52/10.72  thf('32', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 10.52/10.72      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 10.52/10.72  thf('33', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.52/10.72         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3))
% 10.52/10.72           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 10.52/10.72      inference('sup+', [status(thm)], ['31', '32'])).
% 10.52/10.72  thf('34', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.52/10.72         ((k2_enumset1 @ X2 @ X1 @ X0 @ X3) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 10.52/10.72      inference('demod', [status(thm)], ['29', '30', '33'])).
% 10.52/10.72  thf('35', plain,
% 10.52/10.72      (![X57 : $i, X58 : $i, X59 : $i]:
% 10.52/10.72         ((k2_enumset1 @ X57 @ X57 @ X58 @ X59)
% 10.52/10.72           = (k1_enumset1 @ X57 @ X58 @ X59))),
% 10.52/10.72      inference('cnf', [status(esa)], [t71_enumset1])).
% 10.52/10.72  thf('36', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.52/10.72         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 10.52/10.72      inference('sup+', [status(thm)], ['34', '35'])).
% 10.52/10.72  thf('37', plain,
% 10.52/10.72      (![X55 : $i, X56 : $i]:
% 10.52/10.72         ((k1_enumset1 @ X55 @ X55 @ X56) = (k2_tarski @ X55 @ X56))),
% 10.52/10.72      inference('cnf', [status(esa)], [t70_enumset1])).
% 10.52/10.72  thf('38', plain,
% 10.52/10.72      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 10.52/10.72         ((k4_enumset1 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13)
% 10.52/10.72           = (k2_xboole_0 @ (k1_enumset1 @ X8 @ X9 @ X10) @ 
% 10.52/10.72              (k1_enumset1 @ X11 @ X12 @ X13)))),
% 10.52/10.72      inference('cnf', [status(esa)], [l62_enumset1])).
% 10.52/10.72  thf('39', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 10.52/10.72         ((k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X1 @ X0)
% 10.52/10.72           = (k2_xboole_0 @ (k1_enumset1 @ X4 @ X3 @ X2) @ 
% 10.52/10.72              (k2_tarski @ X1 @ X0)))),
% 10.52/10.72      inference('sup+', [status(thm)], ['37', '38'])).
% 10.52/10.72  thf('40', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 10.52/10.72      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 10.52/10.72  thf('41', plain,
% 10.52/10.72      (![X6 : $i, X7 : $i]: ((k2_tarski @ X7 @ X6) = (k2_tarski @ X6 @ X7))),
% 10.52/10.72      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 10.52/10.72  thf('42', plain,
% 10.52/10.72      (![X55 : $i, X56 : $i]:
% 10.52/10.72         ((k1_enumset1 @ X55 @ X55 @ X56) = (k2_tarski @ X55 @ X56))),
% 10.52/10.72      inference('cnf', [status(esa)], [t70_enumset1])).
% 10.52/10.72  thf('43', plain,
% 10.52/10.72      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 10.52/10.72         ((k2_enumset1 @ X14 @ X15 @ X16 @ X17)
% 10.52/10.72           = (k2_xboole_0 @ (k1_tarski @ X14) @ (k1_enumset1 @ X15 @ X16 @ X17)))),
% 10.52/10.72      inference('cnf', [status(esa)], [t44_enumset1])).
% 10.52/10.72  thf('44', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.52/10.72         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0)
% 10.52/10.72           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 10.52/10.72      inference('sup+', [status(thm)], ['42', '43'])).
% 10.52/10.72  thf('45', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i]:
% 10.52/10.72         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 10.52/10.72      inference('sup+', [status(thm)], ['10', '11'])).
% 10.52/10.72  thf('46', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i]:
% 10.52/10.72         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 10.52/10.72           = (k2_tarski @ X1 @ X0))),
% 10.52/10.72      inference('sup+', [status(thm)], ['44', '45'])).
% 10.52/10.72  thf('47', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i]:
% 10.52/10.72         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))
% 10.52/10.72           = (k2_tarski @ X0 @ X1))),
% 10.52/10.72      inference('sup+', [status(thm)], ['41', '46'])).
% 10.52/10.72  thf('48', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.52/10.72         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0)
% 10.52/10.72           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 10.52/10.72      inference('sup+', [status(thm)], ['42', '43'])).
% 10.52/10.72  thf('49', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i]:
% 10.52/10.72         ((k2_enumset1 @ X1 @ X0 @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 10.52/10.72      inference('sup+', [status(thm)], ['47', '48'])).
% 10.52/10.72  thf('50', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i]:
% 10.52/10.72         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 10.52/10.72           = (k2_tarski @ X1 @ X0))),
% 10.52/10.72      inference('sup+', [status(thm)], ['44', '45'])).
% 10.52/10.72  thf('51', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i]:
% 10.52/10.72         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k2_enumset1 @ X0 @ X1 @ X1 @ X0))
% 10.52/10.72           = (k2_tarski @ X0 @ X1))),
% 10.52/10.72      inference('sup+', [status(thm)], ['49', '50'])).
% 10.52/10.72  thf('52', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i]:
% 10.52/10.72         ((k2_xboole_0 @ (k2_enumset1 @ X0 @ X1 @ X1 @ X0) @ (k1_tarski @ X0))
% 10.52/10.72           = (k2_tarski @ X0 @ X1))),
% 10.52/10.72      inference('sup+', [status(thm)], ['40', '51'])).
% 10.52/10.72  thf('53', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 10.52/10.72         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 10.52/10.72           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 10.52/10.72              (k1_tarski @ X4)))),
% 10.52/10.72      inference('demod', [status(thm)], ['15', '16'])).
% 10.52/10.72  thf('54', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i]:
% 10.52/10.72         ((k3_enumset1 @ X0 @ X1 @ X1 @ X0 @ X0) = (k2_tarski @ X0 @ X1))),
% 10.52/10.72      inference('demod', [status(thm)], ['52', '53'])).
% 10.52/10.72  thf('55', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i]:
% 10.52/10.72         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 10.52/10.72           = (k2_tarski @ X1 @ X0))),
% 10.52/10.72      inference('sup+', [status(thm)], ['44', '45'])).
% 10.52/10.72  thf('56', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i]:
% 10.52/10.72         ((k2_xboole_0 @ (k1_tarski @ X0) @ 
% 10.52/10.72           (k3_enumset1 @ X0 @ X1 @ X1 @ X0 @ X0)) = (k2_tarski @ X0 @ X1))),
% 10.52/10.72      inference('sup+', [status(thm)], ['54', '55'])).
% 10.52/10.72  thf('57', plain,
% 10.52/10.72      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 10.52/10.72         ((k4_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23)
% 10.52/10.72           = (k2_xboole_0 @ (k3_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22) @ 
% 10.52/10.72              (k1_tarski @ X23)))),
% 10.52/10.72      inference('cnf', [status(esa)], [t55_enumset1])).
% 10.52/10.72  thf('58', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 10.52/10.72      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 10.52/10.72  thf('59', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 10.52/10.72         ((k2_xboole_0 @ (k1_tarski @ X0) @ 
% 10.52/10.72           (k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1))
% 10.52/10.72           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 10.52/10.72      inference('sup+', [status(thm)], ['57', '58'])).
% 10.52/10.72  thf('60', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i]:
% 10.52/10.72         ((k4_enumset1 @ X0 @ X1 @ X1 @ X0 @ X0 @ X0) = (k2_tarski @ X0 @ X1))),
% 10.52/10.72      inference('demod', [status(thm)], ['56', '59'])).
% 10.52/10.72  thf('61', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i]:
% 10.52/10.72         ((k2_xboole_0 @ (k1_enumset1 @ X0 @ X1 @ X1) @ (k2_tarski @ X0 @ X0))
% 10.52/10.72           = (k2_tarski @ X0 @ X1))),
% 10.52/10.72      inference('sup+', [status(thm)], ['39', '60'])).
% 10.52/10.72  thf(t69_enumset1, axiom,
% 10.52/10.72    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 10.52/10.72  thf('62', plain,
% 10.52/10.72      (![X54 : $i]: ((k2_tarski @ X54 @ X54) = (k1_tarski @ X54))),
% 10.52/10.72      inference('cnf', [status(esa)], [t69_enumset1])).
% 10.52/10.72  thf('63', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.52/10.72         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3))
% 10.52/10.72           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 10.52/10.72      inference('sup+', [status(thm)], ['31', '32'])).
% 10.52/10.72  thf('64', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i]:
% 10.52/10.72         ((k2_enumset1 @ X0 @ X0 @ X1 @ X1) = (k2_tarski @ X0 @ X1))),
% 10.52/10.72      inference('demod', [status(thm)], ['61', '62', '63'])).
% 10.52/10.72  thf('65', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 10.52/10.72         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 10.52/10.72           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 10.52/10.72              (k1_tarski @ X4)))),
% 10.52/10.72      inference('demod', [status(thm)], ['15', '16'])).
% 10.52/10.72  thf('66', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.52/10.72         ((k3_enumset1 @ X1 @ X1 @ X0 @ X0 @ X2)
% 10.52/10.72           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 10.52/10.72      inference('sup+', [status(thm)], ['64', '65'])).
% 10.52/10.72  thf('67', plain,
% 10.52/10.72      (![X60 : $i, X61 : $i, X62 : $i, X63 : $i]:
% 10.52/10.72         ((k3_enumset1 @ X60 @ X60 @ X61 @ X62 @ X63)
% 10.52/10.72           = (k2_enumset1 @ X60 @ X61 @ X62 @ X63))),
% 10.52/10.72      inference('cnf', [status(esa)], [t72_enumset1])).
% 10.52/10.72  thf('68', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.52/10.72         ((k2_enumset1 @ X1 @ X0 @ X0 @ X2)
% 10.52/10.72           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 10.52/10.72      inference('demod', [status(thm)], ['66', '67'])).
% 10.52/10.72  thf('69', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.52/10.72         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2))
% 10.52/10.72           = (k1_enumset1 @ X0 @ X1 @ X2))),
% 10.52/10.72      inference('sup+', [status(thm)], ['9', '22'])).
% 10.52/10.72  thf('70', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.52/10.72         ((k2_enumset1 @ X1 @ X0 @ X0 @ X2) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 10.52/10.72      inference('demod', [status(thm)], ['68', '69'])).
% 10.52/10.72  thf('71', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.52/10.72         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 10.52/10.72      inference('sup+', [status(thm)], ['36', '70'])).
% 10.52/10.72  thf('72', plain,
% 10.52/10.72      (((k3_enumset1 @ sk_B @ sk_A @ sk_C @ sk_C @ sk_A)
% 10.52/10.72         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 10.52/10.72      inference('demod', [status(thm)], ['26', '71'])).
% 10.52/10.72  thf(t74_enumset1, axiom,
% 10.52/10.72    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 10.52/10.72     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 10.52/10.72       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 10.52/10.72  thf('73', plain,
% 10.52/10.72      (![X69 : $i, X70 : $i, X71 : $i, X72 : $i, X73 : $i, X74 : $i]:
% 10.52/10.72         ((k5_enumset1 @ X69 @ X69 @ X70 @ X71 @ X72 @ X73 @ X74)
% 10.52/10.72           = (k4_enumset1 @ X69 @ X70 @ X71 @ X72 @ X73 @ X74))),
% 10.52/10.72      inference('cnf', [status(esa)], [t74_enumset1])).
% 10.52/10.72  thf('74', plain,
% 10.52/10.72      (![X60 : $i, X61 : $i, X62 : $i, X63 : $i]:
% 10.52/10.72         ((k3_enumset1 @ X60 @ X60 @ X61 @ X62 @ X63)
% 10.52/10.72           = (k2_enumset1 @ X60 @ X61 @ X62 @ X63))),
% 10.52/10.72      inference('cnf', [status(esa)], [t72_enumset1])).
% 10.52/10.72  thf(t57_enumset1, axiom,
% 10.52/10.72    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 10.52/10.72     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 10.52/10.72       ( k2_xboole_0 @
% 10.52/10.72         ( k2_tarski @ A @ B ) @ ( k3_enumset1 @ C @ D @ E @ F @ G ) ) ))).
% 10.52/10.72  thf('75', plain,
% 10.52/10.72      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 10.52/10.72         ((k5_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37)
% 10.52/10.72           = (k2_xboole_0 @ (k2_tarski @ X31 @ X32) @ 
% 10.52/10.72              (k3_enumset1 @ X33 @ X34 @ X35 @ X36 @ X37)))),
% 10.52/10.72      inference('cnf', [status(esa)], [t57_enumset1])).
% 10.52/10.72  thf('76', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 10.52/10.72         ((k5_enumset1 @ X5 @ X4 @ X3 @ X3 @ X2 @ X1 @ X0)
% 10.52/10.72           = (k2_xboole_0 @ (k2_tarski @ X5 @ X4) @ 
% 10.52/10.72              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 10.52/10.72      inference('sup+', [status(thm)], ['74', '75'])).
% 10.52/10.72  thf('77', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 10.52/10.72         ((k4_enumset1 @ X4 @ X3 @ X3 @ X2 @ X1 @ X0)
% 10.52/10.72           = (k2_xboole_0 @ (k2_tarski @ X4 @ X4) @ 
% 10.52/10.72              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 10.52/10.72      inference('sup+', [status(thm)], ['73', '76'])).
% 10.52/10.72  thf('78', plain,
% 10.52/10.72      (![X54 : $i]: ((k2_tarski @ X54 @ X54) = (k1_tarski @ X54))),
% 10.52/10.72      inference('cnf', [status(esa)], [t69_enumset1])).
% 10.52/10.72  thf('79', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 10.52/10.72         ((k4_enumset1 @ X4 @ X3 @ X3 @ X2 @ X1 @ X0)
% 10.52/10.72           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 10.52/10.72              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 10.52/10.72      inference('demod', [status(thm)], ['77', '78'])).
% 10.52/10.72  thf('80', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i]:
% 10.52/10.72         ((k2_enumset1 @ X0 @ X0 @ X1 @ X1) = (k2_tarski @ X0 @ X1))),
% 10.52/10.72      inference('demod', [status(thm)], ['61', '62', '63'])).
% 10.52/10.72  thf('81', plain,
% 10.52/10.72      (![X6 : $i, X7 : $i]: ((k2_tarski @ X7 @ X6) = (k2_tarski @ X6 @ X7))),
% 10.52/10.72      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 10.52/10.72  thf('82', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i]:
% 10.52/10.72         ((k2_tarski @ X0 @ X1) = (k2_enumset1 @ X1 @ X1 @ X0 @ X0))),
% 10.52/10.72      inference('sup+', [status(thm)], ['80', '81'])).
% 10.52/10.72  thf('83', plain,
% 10.52/10.72      (![X57 : $i, X58 : $i, X59 : $i]:
% 10.52/10.72         ((k2_enumset1 @ X57 @ X57 @ X58 @ X59)
% 10.52/10.72           = (k1_enumset1 @ X57 @ X58 @ X59))),
% 10.52/10.72      inference('cnf', [status(esa)], [t71_enumset1])).
% 10.52/10.72  thf('84', plain,
% 10.52/10.72      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 10.52/10.72         ((k4_enumset1 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13)
% 10.52/10.72           = (k2_xboole_0 @ (k1_enumset1 @ X8 @ X9 @ X10) @ 
% 10.52/10.72              (k1_enumset1 @ X11 @ X12 @ X13)))),
% 10.52/10.72      inference('cnf', [status(esa)], [l62_enumset1])).
% 10.52/10.72  thf('85', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 10.52/10.72         ((k4_enumset1 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3)
% 10.52/10.72           = (k2_xboole_0 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0) @ 
% 10.52/10.72              (k1_enumset1 @ X5 @ X4 @ X3)))),
% 10.52/10.72      inference('sup+', [status(thm)], ['83', '84'])).
% 10.52/10.72  thf('86', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 10.52/10.72         ((k4_enumset1 @ X0 @ X1 @ X1 @ X4 @ X3 @ X2)
% 10.52/10.72           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 10.52/10.72              (k1_enumset1 @ X4 @ X3 @ X2)))),
% 10.52/10.72      inference('sup+', [status(thm)], ['82', '85'])).
% 10.52/10.72  thf('87', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 10.52/10.72         ((k3_enumset1 @ X1 @ X0 @ X4 @ X3 @ X2)
% 10.52/10.72           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 10.52/10.72              (k1_enumset1 @ X4 @ X3 @ X2)))),
% 10.52/10.72      inference('demod', [status(thm)], ['4', '5'])).
% 10.52/10.72  thf('88', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 10.52/10.72         ((k4_enumset1 @ X0 @ X1 @ X1 @ X4 @ X3 @ X2)
% 10.52/10.72           = (k3_enumset1 @ X1 @ X0 @ X4 @ X3 @ X2))),
% 10.52/10.72      inference('demod', [status(thm)], ['86', '87'])).
% 10.52/10.72  thf('89', plain,
% 10.52/10.72      (![X60 : $i, X61 : $i, X62 : $i, X63 : $i]:
% 10.52/10.72         ((k3_enumset1 @ X60 @ X60 @ X61 @ X62 @ X63)
% 10.52/10.72           = (k2_enumset1 @ X60 @ X61 @ X62 @ X63))),
% 10.52/10.72      inference('cnf', [status(esa)], [t72_enumset1])).
% 10.52/10.72  thf('90', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 10.52/10.72         ((k2_xboole_0 @ (k1_tarski @ X0) @ 
% 10.52/10.72           (k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1))
% 10.52/10.72           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 10.52/10.72      inference('sup+', [status(thm)], ['57', '58'])).
% 10.52/10.72  thf('91', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 10.52/10.72         ((k2_xboole_0 @ (k1_tarski @ X4) @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 10.52/10.72           = (k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4))),
% 10.52/10.72      inference('sup+', [status(thm)], ['89', '90'])).
% 10.52/10.72  thf('92', plain,
% 10.52/10.72      (![X64 : $i, X65 : $i, X66 : $i, X67 : $i, X68 : $i]:
% 10.52/10.72         ((k4_enumset1 @ X64 @ X64 @ X65 @ X66 @ X67 @ X68)
% 10.52/10.72           = (k3_enumset1 @ X64 @ X65 @ X66 @ X67 @ X68))),
% 10.52/10.72      inference('cnf', [status(esa)], [t73_enumset1])).
% 10.52/10.72  thf('93', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 10.52/10.72         ((k2_xboole_0 @ (k1_tarski @ X4) @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 10.52/10.72           = (k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4))),
% 10.52/10.72      inference('demod', [status(thm)], ['91', '92'])).
% 10.52/10.72  thf('94', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 10.52/10.72         ((k3_enumset1 @ X3 @ X4 @ X2 @ X1 @ X0)
% 10.52/10.72           = (k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4))),
% 10.52/10.72      inference('demod', [status(thm)], ['79', '88', '93'])).
% 10.52/10.72  thf('95', plain,
% 10.52/10.72      (((k3_enumset1 @ sk_B @ sk_C @ sk_C @ sk_A @ sk_A)
% 10.52/10.72         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 10.52/10.72      inference('demod', [status(thm)], ['72', '94'])).
% 10.52/10.72  thf('96', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i]:
% 10.52/10.72         ((k2_enumset1 @ X1 @ X0 @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 10.52/10.72      inference('sup+', [status(thm)], ['47', '48'])).
% 10.52/10.72  thf('97', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i]:
% 10.52/10.72         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 10.52/10.72      inference('sup+', [status(thm)], ['10', '11'])).
% 10.52/10.72  thf('98', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i]:
% 10.52/10.72         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1) = (k2_enumset1 @ X0 @ X1 @ X1 @ X0))),
% 10.52/10.72      inference('sup+', [status(thm)], ['96', '97'])).
% 10.52/10.72  thf('99', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 10.52/10.72         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 10.52/10.72           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 10.52/10.72              (k1_tarski @ X4)))),
% 10.52/10.72      inference('demod', [status(thm)], ['15', '16'])).
% 10.52/10.72  thf('100', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.52/10.72         ((k3_enumset1 @ X1 @ X0 @ X0 @ X1 @ X2)
% 10.52/10.72           = (k2_xboole_0 @ (k2_enumset1 @ X1 @ X1 @ X1 @ X0) @ 
% 10.52/10.72              (k1_tarski @ X2)))),
% 10.52/10.72      inference('sup+', [status(thm)], ['98', '99'])).
% 10.52/10.72  thf('101', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 10.52/10.72         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 10.52/10.72           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 10.52/10.72              (k1_tarski @ X4)))),
% 10.52/10.72      inference('demod', [status(thm)], ['15', '16'])).
% 10.52/10.72  thf('102', plain,
% 10.52/10.72      (![X60 : $i, X61 : $i, X62 : $i, X63 : $i]:
% 10.52/10.72         ((k3_enumset1 @ X60 @ X60 @ X61 @ X62 @ X63)
% 10.52/10.72           = (k2_enumset1 @ X60 @ X61 @ X62 @ X63))),
% 10.52/10.72      inference('cnf', [status(esa)], [t72_enumset1])).
% 10.52/10.72  thf('103', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.52/10.72         ((k3_enumset1 @ X1 @ X0 @ X0 @ X1 @ X2)
% 10.52/10.72           = (k2_enumset1 @ X1 @ X1 @ X0 @ X2))),
% 10.52/10.72      inference('demod', [status(thm)], ['100', '101', '102'])).
% 10.52/10.72  thf('104', plain,
% 10.52/10.72      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 10.52/10.72         ((k4_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23)
% 10.52/10.72           = (k2_xboole_0 @ (k3_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22) @ 
% 10.52/10.72              (k1_tarski @ X23)))),
% 10.52/10.72      inference('cnf', [status(esa)], [t55_enumset1])).
% 10.52/10.72  thf('105', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.52/10.72         ((k4_enumset1 @ X2 @ X1 @ X1 @ X2 @ X0 @ X3)
% 10.52/10.72           = (k2_xboole_0 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0) @ 
% 10.52/10.72              (k1_tarski @ X3)))),
% 10.52/10.72      inference('sup+', [status(thm)], ['103', '104'])).
% 10.52/10.72  thf('106', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 10.52/10.72         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 10.52/10.72           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 10.52/10.72              (k1_tarski @ X4)))),
% 10.52/10.72      inference('demod', [status(thm)], ['15', '16'])).
% 10.52/10.72  thf('107', plain,
% 10.52/10.72      (![X60 : $i, X61 : $i, X62 : $i, X63 : $i]:
% 10.52/10.72         ((k3_enumset1 @ X60 @ X60 @ X61 @ X62 @ X63)
% 10.52/10.72           = (k2_enumset1 @ X60 @ X61 @ X62 @ X63))),
% 10.52/10.72      inference('cnf', [status(esa)], [t72_enumset1])).
% 10.52/10.72  thf('108', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.52/10.72         ((k4_enumset1 @ X2 @ X1 @ X1 @ X2 @ X0 @ X3)
% 10.52/10.72           = (k2_enumset1 @ X2 @ X1 @ X0 @ X3))),
% 10.52/10.72      inference('demod', [status(thm)], ['105', '106', '107'])).
% 10.52/10.72  thf('109', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 10.52/10.72         ((k4_enumset1 @ X0 @ X1 @ X1 @ X4 @ X3 @ X2)
% 10.52/10.72           = (k3_enumset1 @ X1 @ X0 @ X4 @ X3 @ X2))),
% 10.52/10.72      inference('demod', [status(thm)], ['86', '87'])).
% 10.52/10.72  thf('110', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.52/10.72         ((k3_enumset1 @ X1 @ X2 @ X2 @ X0 @ X3)
% 10.52/10.72           = (k2_enumset1 @ X2 @ X1 @ X0 @ X3))),
% 10.52/10.72      inference('demod', [status(thm)], ['108', '109'])).
% 10.52/10.72  thf('111', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.52/10.72         ((k2_enumset1 @ X1 @ X0 @ X0 @ X2) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 10.52/10.72      inference('demod', [status(thm)], ['68', '69'])).
% 10.52/10.72  thf('112', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i]:
% 10.52/10.72         ((k2_enumset1 @ X0 @ X0 @ X1 @ X1) = (k2_tarski @ X0 @ X1))),
% 10.52/10.72      inference('demod', [status(thm)], ['61', '62', '63'])).
% 10.52/10.72  thf('113', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.52/10.72         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0)
% 10.52/10.72           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 10.52/10.72      inference('sup+', [status(thm)], ['42', '43'])).
% 10.52/10.72  thf('114', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.52/10.72         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0)
% 10.52/10.72           = (k2_xboole_0 @ (k1_tarski @ X2) @ 
% 10.52/10.72              (k2_enumset1 @ X1 @ X1 @ X0 @ X0)))),
% 10.52/10.72      inference('sup+', [status(thm)], ['112', '113'])).
% 10.52/10.72  thf('115', plain,
% 10.52/10.72      (![X57 : $i, X58 : $i, X59 : $i]:
% 10.52/10.72         ((k2_enumset1 @ X57 @ X57 @ X58 @ X59)
% 10.52/10.72           = (k1_enumset1 @ X57 @ X58 @ X59))),
% 10.52/10.72      inference('cnf', [status(esa)], [t71_enumset1])).
% 10.52/10.72  thf('116', plain,
% 10.52/10.72      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 10.52/10.72         ((k2_enumset1 @ X14 @ X15 @ X16 @ X17)
% 10.52/10.72           = (k2_xboole_0 @ (k1_tarski @ X14) @ (k1_enumset1 @ X15 @ X16 @ X17)))),
% 10.52/10.72      inference('cnf', [status(esa)], [t44_enumset1])).
% 10.52/10.72  thf('117', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.52/10.72         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 10.52/10.72           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 10.52/10.72              (k2_enumset1 @ X2 @ X2 @ X1 @ X0)))),
% 10.52/10.72      inference('sup+', [status(thm)], ['115', '116'])).
% 10.52/10.72  thf('118', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.52/10.72         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0) = (k2_enumset1 @ X2 @ X1 @ X0 @ X0))),
% 10.52/10.72      inference('demod', [status(thm)], ['114', '117'])).
% 10.52/10.72  thf('119', plain,
% 10.52/10.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.52/10.72         ((k1_enumset1 @ X2 @ X1 @ X0) = (k2_enumset1 @ X1 @ X2 @ X0 @ X0))),
% 10.52/10.72      inference('sup+', [status(thm)], ['111', '118'])).
% 10.52/10.72  thf('120', plain,
% 10.52/10.72      (((k1_enumset1 @ sk_B @ sk_C @ sk_A)
% 10.52/10.72         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 10.52/10.72      inference('demod', [status(thm)], ['95', '110', '119'])).
% 10.52/10.72  thf('121', plain, ($false), inference('simplify', [status(thm)], ['120'])).
% 10.52/10.72  
% 10.52/10.72  % SZS output end Refutation
% 10.52/10.72  
% 10.52/10.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

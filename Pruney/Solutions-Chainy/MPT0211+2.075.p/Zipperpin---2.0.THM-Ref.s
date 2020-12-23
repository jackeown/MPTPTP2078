%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jqOjjTb5ex

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:40 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 177 expanded)
%              Number of leaves         :   22 (  67 expanded)
%              Depth                    :   12
%              Number of atoms          : 1018 (1986 expanded)
%              Number of equality atoms :   86 ( 165 expanded)
%              Maximal formula depth    :   16 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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

thf(t100_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ B @ C @ A ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k1_enumset1 @ X4 @ X2 @ X3 )
      = ( k1_enumset1 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('2',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k1_enumset1 @ X4 @ X2 @ X3 )
      = ( k1_enumset1 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('3',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k2_tarski @ sk_C @ sk_A ) )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('4',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k2_enumset1 @ X24 @ X24 @ X25 @ X26 )
      = ( k1_enumset1 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k1_enumset1 @ X22 @ X22 @ X23 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('7',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( k3_enumset1 @ X27 @ X27 @ X28 @ X29 @ X30 )
      = ( k2_enumset1 @ X27 @ X28 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t60_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k5_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 ) @ ( k2_tarski @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t60_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X5 @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('10',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( k5_enumset1 @ X36 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 )
      = ( k4_enumset1 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X5 @ X4 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X1 @ X1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['6','11'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('13',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k4_enumset1 @ X31 @ X31 @ X32 @ X33 @ X34 @ X35 )
      = ( k3_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('14',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( k3_enumset1 @ X27 @ X27 @ X28 @ X29 @ X30 )
      = ( k2_enumset1 @ X27 @ X28 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,(
    ( k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['3','16'])).

thf('18',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k2_enumset1 @ X24 @ X24 @ X25 @ X26 )
      = ( k1_enumset1 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t102_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ C @ B @ A ) ) )).

thf('19',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k1_enumset1 @ X7 @ X6 @ X5 )
      = ( k1_enumset1 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t102_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( k3_enumset1 @ X27 @ X27 @ X28 @ X29 @ X30 )
      = ( k2_enumset1 @ X27 @ X28 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t55_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ) )).

thf('22',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_enumset1 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X8 @ X9 @ X10 @ X11 @ X12 ) @ ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t55_enumset1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X0 @ X0 @ X0 @ X1 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k2_enumset1 @ X24 @ X24 @ X25 @ X26 )
      = ( k1_enumset1 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('28',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k1_enumset1 @ X4 @ X2 @ X3 )
      = ( k1_enumset1 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X0 @ X0 @ X0 @ X2 @ X1 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X1 @ X2 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','33'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('35',plain,(
    ! [X21: $i] :
      ( ( k2_tarski @ X21 @ X21 )
      = ( k1_tarski @ X21 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('37',plain,(
    ! [X21: $i] :
      ( ( k2_tarski @ X21 @ X21 )
      = ( k1_tarski @ X21 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X5 @ X4 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X1 @ X1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k2_enumset1 @ X24 @ X24 @ X25 @ X26 )
      = ( k1_enumset1 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('48',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k1_enumset1 @ X4 @ X2 @ X3 )
      = ( k1_enumset1 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('49',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k1_enumset1 @ X22 @ X22 @ X23 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X5 @ X4 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_enumset1 @ X0 @ X0 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['51','56'])).

thf('58',plain,(
    ! [X21: $i] :
      ( ( k2_tarski @ X21 @ X21 )
      = ( k1_tarski @ X21 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['46','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X2 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k2_enumset1 @ X24 @ X24 @ X25 @ X26 )
      = ( k1_enumset1 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X2 @ X0 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['61','68'])).

thf('70',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k1_enumset1 @ X7 @ X6 @ X5 )
      = ( k1_enumset1 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t102_enumset1])).

thf('71',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k1_enumset1 @ X4 @ X2 @ X3 )
      = ( k1_enumset1 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ( k1_enumset1 @ sk_B @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['17','34','69','72'])).

thf('74',plain,(
    $false ),
    inference(simplify,[status(thm)],['73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jqOjjTb5ex
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:25:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.65/1.83  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.65/1.83  % Solved by: fo/fo7.sh
% 1.65/1.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.65/1.83  % done 2728 iterations in 1.374s
% 1.65/1.83  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.65/1.83  % SZS output start Refutation
% 1.65/1.83  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.65/1.83  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 1.65/1.83  thf(sk_A_type, type, sk_A: $i).
% 1.65/1.83  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 1.65/1.83  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.65/1.83  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 1.65/1.83  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 1.65/1.83  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.65/1.83  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.65/1.83  thf(sk_C_type, type, sk_C: $i).
% 1.65/1.83  thf(sk_B_type, type, sk_B: $i).
% 1.65/1.83  thf(t137_enumset1, conjecture,
% 1.65/1.83    (![A:$i,B:$i,C:$i]:
% 1.65/1.83     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 1.65/1.83       ( k1_enumset1 @ A @ B @ C ) ))).
% 1.65/1.83  thf(zf_stmt_0, negated_conjecture,
% 1.65/1.83    (~( ![A:$i,B:$i,C:$i]:
% 1.65/1.83        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 1.65/1.83          ( k1_enumset1 @ A @ B @ C ) ) )),
% 1.65/1.83    inference('cnf.neg', [status(esa)], [t137_enumset1])).
% 1.65/1.83  thf('0', plain,
% 1.65/1.83      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 1.65/1.83         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf(t100_enumset1, axiom,
% 1.65/1.83    (![A:$i,B:$i,C:$i]:
% 1.65/1.83     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ B @ C @ A ) ))).
% 1.65/1.83  thf('1', plain,
% 1.65/1.83      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.65/1.83         ((k1_enumset1 @ X4 @ X2 @ X3) = (k1_enumset1 @ X2 @ X3 @ X4))),
% 1.65/1.83      inference('cnf', [status(esa)], [t100_enumset1])).
% 1.65/1.83  thf('2', plain,
% 1.65/1.83      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.65/1.83         ((k1_enumset1 @ X4 @ X2 @ X3) = (k1_enumset1 @ X2 @ X3 @ X4))),
% 1.65/1.83      inference('cnf', [status(esa)], [t100_enumset1])).
% 1.65/1.83  thf('3', plain,
% 1.65/1.83      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 1.65/1.83         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 1.65/1.83      inference('demod', [status(thm)], ['0', '1', '2'])).
% 1.65/1.83  thf(t71_enumset1, axiom,
% 1.65/1.83    (![A:$i,B:$i,C:$i]:
% 1.65/1.83     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 1.65/1.83  thf('4', plain,
% 1.65/1.83      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.65/1.83         ((k2_enumset1 @ X24 @ X24 @ X25 @ X26)
% 1.65/1.83           = (k1_enumset1 @ X24 @ X25 @ X26))),
% 1.65/1.83      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.65/1.83  thf(t70_enumset1, axiom,
% 1.65/1.83    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.65/1.83  thf('5', plain,
% 1.65/1.83      (![X22 : $i, X23 : $i]:
% 1.65/1.83         ((k1_enumset1 @ X22 @ X22 @ X23) = (k2_tarski @ X22 @ X23))),
% 1.65/1.83      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.65/1.83  thf('6', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i]:
% 1.65/1.83         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 1.65/1.83      inference('sup+', [status(thm)], ['4', '5'])).
% 1.65/1.83  thf(t72_enumset1, axiom,
% 1.65/1.83    (![A:$i,B:$i,C:$i,D:$i]:
% 1.65/1.83     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 1.65/1.83  thf('7', plain,
% 1.65/1.83      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 1.65/1.83         ((k3_enumset1 @ X27 @ X27 @ X28 @ X29 @ X30)
% 1.65/1.83           = (k2_enumset1 @ X27 @ X28 @ X29 @ X30))),
% 1.65/1.83      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.65/1.83  thf(t60_enumset1, axiom,
% 1.65/1.83    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 1.65/1.83     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 1.65/1.83       ( k2_xboole_0 @
% 1.65/1.83         ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ))).
% 1.65/1.83  thf('8', plain,
% 1.65/1.83      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.65/1.83         ((k5_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20)
% 1.65/1.83           = (k2_xboole_0 @ (k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18) @ 
% 1.65/1.83              (k2_tarski @ X19 @ X20)))),
% 1.65/1.83      inference('cnf', [status(esa)], [t60_enumset1])).
% 1.65/1.83  thf('9', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.65/1.83         ((k5_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4)
% 1.65/1.83           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 1.65/1.83              (k2_tarski @ X5 @ X4)))),
% 1.65/1.83      inference('sup+', [status(thm)], ['7', '8'])).
% 1.65/1.83  thf(t74_enumset1, axiom,
% 1.65/1.83    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.65/1.83     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 1.65/1.83       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 1.65/1.83  thf('10', plain,
% 1.65/1.83      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 1.65/1.83         ((k5_enumset1 @ X36 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41)
% 1.65/1.83           = (k4_enumset1 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41))),
% 1.65/1.83      inference('cnf', [status(esa)], [t74_enumset1])).
% 1.65/1.83  thf('11', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.65/1.83         ((k4_enumset1 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4)
% 1.65/1.83           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 1.65/1.83              (k2_tarski @ X5 @ X4)))),
% 1.65/1.83      inference('demod', [status(thm)], ['9', '10'])).
% 1.65/1.83  thf('12', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.65/1.83         ((k4_enumset1 @ X1 @ X1 @ X1 @ X0 @ X3 @ X2)
% 1.65/1.83           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 1.65/1.83      inference('sup+', [status(thm)], ['6', '11'])).
% 1.65/1.83  thf(t73_enumset1, axiom,
% 1.65/1.83    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.65/1.83     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 1.65/1.83       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 1.65/1.83  thf('13', plain,
% 1.65/1.83      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 1.65/1.83         ((k4_enumset1 @ X31 @ X31 @ X32 @ X33 @ X34 @ X35)
% 1.65/1.83           = (k3_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35))),
% 1.65/1.83      inference('cnf', [status(esa)], [t73_enumset1])).
% 1.65/1.83  thf('14', plain,
% 1.65/1.83      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 1.65/1.83         ((k3_enumset1 @ X27 @ X27 @ X28 @ X29 @ X30)
% 1.65/1.83           = (k2_enumset1 @ X27 @ X28 @ X29 @ X30))),
% 1.65/1.83      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.65/1.83  thf('15', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.65/1.83         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 1.65/1.83           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 1.65/1.83      inference('sup+', [status(thm)], ['13', '14'])).
% 1.65/1.83  thf('16', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.65/1.83         ((k2_enumset1 @ X1 @ X0 @ X3 @ X2)
% 1.65/1.83           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 1.65/1.83      inference('demod', [status(thm)], ['12', '15'])).
% 1.65/1.83  thf('17', plain,
% 1.65/1.83      (((k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A)
% 1.65/1.83         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 1.65/1.83      inference('demod', [status(thm)], ['3', '16'])).
% 1.65/1.83  thf('18', plain,
% 1.65/1.83      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.65/1.83         ((k2_enumset1 @ X24 @ X24 @ X25 @ X26)
% 1.65/1.83           = (k1_enumset1 @ X24 @ X25 @ X26))),
% 1.65/1.83      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.65/1.83  thf(t102_enumset1, axiom,
% 1.65/1.83    (![A:$i,B:$i,C:$i]:
% 1.65/1.83     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ C @ B @ A ) ))).
% 1.65/1.83  thf('19', plain,
% 1.65/1.83      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.65/1.83         ((k1_enumset1 @ X7 @ X6 @ X5) = (k1_enumset1 @ X5 @ X6 @ X7))),
% 1.65/1.83      inference('cnf', [status(esa)], [t102_enumset1])).
% 1.65/1.83  thf('20', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.83         ((k1_enumset1 @ X0 @ X1 @ X2) = (k2_enumset1 @ X2 @ X2 @ X1 @ X0))),
% 1.65/1.83      inference('sup+', [status(thm)], ['18', '19'])).
% 1.65/1.83  thf('21', plain,
% 1.65/1.83      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 1.65/1.83         ((k3_enumset1 @ X27 @ X27 @ X28 @ X29 @ X30)
% 1.65/1.83           = (k2_enumset1 @ X27 @ X28 @ X29 @ X30))),
% 1.65/1.83      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.65/1.83  thf(t55_enumset1, axiom,
% 1.65/1.83    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.65/1.83     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 1.65/1.83       ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ))).
% 1.65/1.83  thf('22', plain,
% 1.65/1.83      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 1.65/1.83         ((k4_enumset1 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13)
% 1.65/1.83           = (k2_xboole_0 @ (k3_enumset1 @ X8 @ X9 @ X10 @ X11 @ X12) @ 
% 1.65/1.83              (k1_tarski @ X13)))),
% 1.65/1.83      inference('cnf', [status(esa)], [t55_enumset1])).
% 1.65/1.83  thf('23', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.65/1.83         ((k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4)
% 1.65/1.83           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 1.65/1.83              (k1_tarski @ X4)))),
% 1.65/1.83      inference('sup+', [status(thm)], ['21', '22'])).
% 1.65/1.83  thf('24', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.65/1.83         ((k4_enumset1 @ X0 @ X0 @ X0 @ X1 @ X2 @ X3)
% 1.65/1.83           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 1.65/1.83      inference('sup+', [status(thm)], ['20', '23'])).
% 1.65/1.83  thf('25', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.65/1.83         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 1.65/1.83           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 1.65/1.83      inference('sup+', [status(thm)], ['13', '14'])).
% 1.65/1.83  thf('26', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.65/1.83         ((k2_enumset1 @ X0 @ X1 @ X2 @ X3)
% 1.65/1.83           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 1.65/1.83      inference('demod', [status(thm)], ['24', '25'])).
% 1.65/1.83  thf('27', plain,
% 1.65/1.83      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.65/1.83         ((k2_enumset1 @ X24 @ X24 @ X25 @ X26)
% 1.65/1.83           = (k1_enumset1 @ X24 @ X25 @ X26))),
% 1.65/1.83      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.65/1.83  thf('28', plain,
% 1.65/1.83      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.65/1.83         ((k1_enumset1 @ X4 @ X2 @ X3) = (k1_enumset1 @ X2 @ X3 @ X4))),
% 1.65/1.83      inference('cnf', [status(esa)], [t100_enumset1])).
% 1.65/1.83  thf('29', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.83         ((k2_enumset1 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 1.65/1.83      inference('sup+', [status(thm)], ['27', '28'])).
% 1.65/1.83  thf('30', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.65/1.83         ((k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4)
% 1.65/1.83           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 1.65/1.83              (k1_tarski @ X4)))),
% 1.65/1.83      inference('sup+', [status(thm)], ['21', '22'])).
% 1.65/1.83  thf('31', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.65/1.83         ((k4_enumset1 @ X0 @ X0 @ X0 @ X2 @ X1 @ X3)
% 1.65/1.83           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 1.65/1.83      inference('sup+', [status(thm)], ['29', '30'])).
% 1.65/1.83  thf('32', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.65/1.83         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 1.65/1.83           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 1.65/1.83      inference('sup+', [status(thm)], ['13', '14'])).
% 1.65/1.83  thf('33', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.65/1.83         ((k2_enumset1 @ X0 @ X2 @ X1 @ X3)
% 1.65/1.83           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 1.65/1.83      inference('demod', [status(thm)], ['31', '32'])).
% 1.65/1.83  thf('34', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.65/1.83         ((k2_enumset1 @ X3 @ X1 @ X2 @ X0) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 1.65/1.83      inference('sup+', [status(thm)], ['26', '33'])).
% 1.65/1.83  thf(t69_enumset1, axiom,
% 1.65/1.83    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.65/1.83  thf('35', plain,
% 1.65/1.83      (![X21 : $i]: ((k2_tarski @ X21 @ X21) = (k1_tarski @ X21))),
% 1.65/1.83      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.65/1.83  thf('36', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i]:
% 1.65/1.83         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 1.65/1.83      inference('sup+', [status(thm)], ['4', '5'])).
% 1.65/1.83  thf('37', plain,
% 1.65/1.83      (![X21 : $i]: ((k2_tarski @ X21 @ X21) = (k1_tarski @ X21))),
% 1.65/1.83      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.65/1.83  thf('38', plain,
% 1.65/1.83      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 1.65/1.83      inference('sup+', [status(thm)], ['36', '37'])).
% 1.65/1.83  thf('39', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.65/1.83         ((k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4)
% 1.65/1.83           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 1.65/1.83              (k1_tarski @ X4)))),
% 1.65/1.83      inference('sup+', [status(thm)], ['21', '22'])).
% 1.65/1.83  thf('40', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i]:
% 1.65/1.83         ((k4_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X1)
% 1.65/1.83           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 1.65/1.83      inference('sup+', [status(thm)], ['38', '39'])).
% 1.65/1.83  thf('41', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.65/1.83         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 1.65/1.83           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 1.65/1.83      inference('sup+', [status(thm)], ['13', '14'])).
% 1.65/1.83  thf('42', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i]:
% 1.65/1.83         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 1.65/1.83           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 1.65/1.83      inference('demod', [status(thm)], ['40', '41'])).
% 1.65/1.83  thf('43', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.65/1.83         ((k4_enumset1 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4)
% 1.65/1.83           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 1.65/1.83              (k2_tarski @ X5 @ X4)))),
% 1.65/1.83      inference('demod', [status(thm)], ['9', '10'])).
% 1.65/1.83  thf('44', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.65/1.83         ((k4_enumset1 @ X1 @ X1 @ X1 @ X0 @ X3 @ X2)
% 1.65/1.83           = (k2_xboole_0 @ 
% 1.65/1.83              (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)) @ 
% 1.65/1.83              (k2_tarski @ X3 @ X2)))),
% 1.65/1.83      inference('sup+', [status(thm)], ['42', '43'])).
% 1.65/1.83  thf('45', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.65/1.83         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 1.65/1.83           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 1.65/1.83      inference('sup+', [status(thm)], ['13', '14'])).
% 1.65/1.83  thf('46', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.65/1.83         ((k2_enumset1 @ X1 @ X0 @ X3 @ X2)
% 1.65/1.83           = (k2_xboole_0 @ 
% 1.65/1.83              (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)) @ 
% 1.65/1.83              (k2_tarski @ X3 @ X2)))),
% 1.65/1.83      inference('demod', [status(thm)], ['44', '45'])).
% 1.65/1.83  thf('47', plain,
% 1.65/1.83      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.65/1.83         ((k2_enumset1 @ X24 @ X24 @ X25 @ X26)
% 1.65/1.83           = (k1_enumset1 @ X24 @ X25 @ X26))),
% 1.65/1.83      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.65/1.83  thf('48', plain,
% 1.65/1.83      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.65/1.83         ((k1_enumset1 @ X4 @ X2 @ X3) = (k1_enumset1 @ X2 @ X3 @ X4))),
% 1.65/1.83      inference('cnf', [status(esa)], [t100_enumset1])).
% 1.65/1.83  thf('49', plain,
% 1.65/1.83      (![X22 : $i, X23 : $i]:
% 1.65/1.83         ((k1_enumset1 @ X22 @ X22 @ X23) = (k2_tarski @ X22 @ X23))),
% 1.65/1.83      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.65/1.83  thf('50', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i]:
% 1.65/1.83         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X0 @ X1))),
% 1.65/1.83      inference('sup+', [status(thm)], ['48', '49'])).
% 1.65/1.83  thf('51', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i]:
% 1.65/1.83         ((k2_enumset1 @ X1 @ X1 @ X0 @ X0) = (k2_tarski @ X0 @ X1))),
% 1.65/1.83      inference('sup+', [status(thm)], ['47', '50'])).
% 1.65/1.83  thf('52', plain,
% 1.65/1.83      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 1.65/1.83      inference('sup+', [status(thm)], ['36', '37'])).
% 1.65/1.83  thf('53', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.65/1.83         ((k4_enumset1 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4)
% 1.65/1.83           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 1.65/1.83              (k2_tarski @ X5 @ X4)))),
% 1.65/1.83      inference('demod', [status(thm)], ['9', '10'])).
% 1.65/1.83  thf('54', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.83         ((k4_enumset1 @ X0 @ X0 @ X0 @ X0 @ X2 @ X1)
% 1.65/1.83           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 1.65/1.83      inference('sup+', [status(thm)], ['52', '53'])).
% 1.65/1.83  thf('55', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.65/1.83         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 1.65/1.83           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 1.65/1.83      inference('sup+', [status(thm)], ['13', '14'])).
% 1.65/1.83  thf('56', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.83         ((k2_enumset1 @ X0 @ X0 @ X2 @ X1)
% 1.65/1.83           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 1.65/1.83      inference('demod', [status(thm)], ['54', '55'])).
% 1.65/1.83  thf('57', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i]:
% 1.65/1.83         ((k2_tarski @ X1 @ X0)
% 1.65/1.83           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X1)))),
% 1.65/1.83      inference('sup+', [status(thm)], ['51', '56'])).
% 1.65/1.83  thf('58', plain,
% 1.65/1.83      (![X21 : $i]: ((k2_tarski @ X21 @ X21) = (k1_tarski @ X21))),
% 1.65/1.83      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.65/1.83  thf('59', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i]:
% 1.65/1.83         ((k2_tarski @ X1 @ X0)
% 1.65/1.83           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 1.65/1.83      inference('demod', [status(thm)], ['57', '58'])).
% 1.65/1.83  thf('60', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.65/1.83         ((k2_enumset1 @ X1 @ X0 @ X3 @ X2)
% 1.65/1.83           = (k2_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X3 @ X2)))),
% 1.65/1.83      inference('demod', [status(thm)], ['46', '59'])).
% 1.65/1.83  thf('61', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.83         ((k2_enumset1 @ X1 @ X2 @ X0 @ X0)
% 1.65/1.83           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)))),
% 1.65/1.83      inference('sup+', [status(thm)], ['35', '60'])).
% 1.65/1.83  thf('62', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i]:
% 1.65/1.83         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 1.65/1.83      inference('sup+', [status(thm)], ['4', '5'])).
% 1.65/1.83  thf('63', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.65/1.83         ((k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4)
% 1.65/1.83           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 1.65/1.83              (k1_tarski @ X4)))),
% 1.65/1.83      inference('sup+', [status(thm)], ['21', '22'])).
% 1.65/1.83  thf('64', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.83         ((k4_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 @ X2)
% 1.65/1.83           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 1.65/1.83      inference('sup+', [status(thm)], ['62', '63'])).
% 1.65/1.83  thf('65', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.65/1.83         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 1.65/1.83           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 1.65/1.83      inference('sup+', [status(thm)], ['13', '14'])).
% 1.65/1.83  thf('66', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.83         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 1.65/1.83           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 1.65/1.83      inference('demod', [status(thm)], ['64', '65'])).
% 1.65/1.83  thf('67', plain,
% 1.65/1.83      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.65/1.83         ((k2_enumset1 @ X24 @ X24 @ X25 @ X26)
% 1.65/1.83           = (k1_enumset1 @ X24 @ X25 @ X26))),
% 1.65/1.83      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.65/1.83  thf('68', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.83         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 1.65/1.83           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 1.65/1.83      inference('sup+', [status(thm)], ['66', '67'])).
% 1.65/1.83  thf('69', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.83         ((k2_enumset1 @ X1 @ X2 @ X0 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 1.65/1.83      inference('demod', [status(thm)], ['61', '68'])).
% 1.65/1.83  thf('70', plain,
% 1.65/1.83      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.65/1.83         ((k1_enumset1 @ X7 @ X6 @ X5) = (k1_enumset1 @ X5 @ X6 @ X7))),
% 1.65/1.83      inference('cnf', [status(esa)], [t102_enumset1])).
% 1.65/1.83  thf('71', plain,
% 1.65/1.83      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.65/1.83         ((k1_enumset1 @ X4 @ X2 @ X3) = (k1_enumset1 @ X2 @ X3 @ X4))),
% 1.65/1.83      inference('cnf', [status(esa)], [t100_enumset1])).
% 1.65/1.83  thf('72', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.83         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 1.65/1.83      inference('sup+', [status(thm)], ['70', '71'])).
% 1.65/1.83  thf('73', plain,
% 1.65/1.83      (((k1_enumset1 @ sk_B @ sk_C @ sk_A)
% 1.65/1.83         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 1.65/1.83      inference('demod', [status(thm)], ['17', '34', '69', '72'])).
% 1.65/1.83  thf('74', plain, ($false), inference('simplify', [status(thm)], ['73'])).
% 1.65/1.83  
% 1.65/1.83  % SZS output end Refutation
% 1.65/1.83  
% 1.65/1.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

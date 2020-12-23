%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QcLPAehl32

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:27 EST 2020

% Result     : Theorem 13.29s
% Output     : Refutation 13.29s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 225 expanded)
%              Number of leaves         :   23 (  86 expanded)
%              Depth                    :   17
%              Number of atoms          : 1256 (3251 expanded)
%              Number of equality atoms :   71 ( 209 expanded)
%              Maximal formula depth    :   21 (  13 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_enumset1_type,type,(
    k7_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_I_type,type,(
    sk_I: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(t132_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_enumset1 @ G @ H @ I ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
        ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I )
        = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_enumset1 @ G @ H @ I ) ) ) ),
    inference('cnf.neg',[status(esa)],[t132_enumset1])).

thf('0',plain,(
    ( k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I )
 != ( k2_xboole_0 @ ( k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_enumset1 @ sk_G @ sk_H @ sk_I ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l62_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( k4_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X17 @ X18 @ X19 ) @ ( k1_enumset1 @ X20 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[l62_enumset1])).

thf('2',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( k4_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X17 @ X18 @ X19 ) @ ( k1_enumset1 @ X20 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[l62_enumset1])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X6 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X5 @ X4 @ X3 ) @ ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X6 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ ( k4_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X8 @ X7 @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('6',plain,(
    ( k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I )
 != ( k2_xboole_0 @ ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) @ ( k4_enumset1 @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf(t84_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_enumset1 @ A @ A @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('7',plain,(
    ! [X62: $i,X63: $i,X64: $i] :
      ( ( k4_enumset1 @ X62 @ X62 @ X62 @ X62 @ X63 @ X64 )
      = ( k1_enumset1 @ X62 @ X63 @ X64 ) ) ),
    inference(cnf,[status(esa)],[t84_enumset1])).

thf(t79_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_enumset1 @ A @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('8',plain,(
    ! [X58: $i,X59: $i,X60: $i,X61: $i] :
      ( ( k4_enumset1 @ X58 @ X58 @ X58 @ X59 @ X60 @ X61 )
      = ( k2_enumset1 @ X58 @ X59 @ X60 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t79_enumset1])).

thf('9',plain,(
    ! [X62: $i,X63: $i,X64: $i] :
      ( ( k2_enumset1 @ X62 @ X62 @ X63 @ X64 )
      = ( k1_enumset1 @ X62 @ X63 @ X64 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(l142_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k3_enumset1 @ E @ F @ G @ H @ I ) ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k7_enumset1 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X8 @ X9 @ X10 @ X11 ) @ ( k3_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[l142_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k7_enumset1 @ X2 @ X2 @ X1 @ X0 @ X7 @ X6 @ X5 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k3_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X62: $i,X63: $i,X64: $i] :
      ( ( k2_enumset1 @ X62 @ X62 @ X63 @ X64 )
      = ( k1_enumset1 @ X62 @ X63 @ X64 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t131_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_enumset1 @ F @ G @ H @ I ) ) ) )).

thf('13',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( k7_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 ) @ ( k2_enumset1 @ X37 @ X38 @ X39 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t131_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k7_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X6 @ X5 @ X4 ) @ ( k3_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X6 @ X6 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X58: $i,X59: $i,X60: $i,X61: $i] :
      ( ( k4_enumset1 @ X58 @ X58 @ X58 @ X59 @ X60 @ X61 )
      = ( k2_enumset1 @ X58 @ X59 @ X60 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t79_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('17',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( k4_enumset1 @ X47 @ X47 @ X48 @ X49 @ X50 @ X51 )
      = ( k3_enumset1 @ X47 @ X48 @ X49 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('18',plain,(
    ! [X58: $i,X59: $i,X60: $i,X61: $i] :
      ( ( k3_enumset1 @ X58 @ X58 @ X59 @ X60 @ X61 )
      = ( k2_enumset1 @ X58 @ X59 @ X60 @ X61 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X6 @ X5 @ X4 ) @ ( k3_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X6 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( k4_enumset1 @ X47 @ X47 @ X48 @ X49 @ X50 @ X51 )
      = ( k3_enumset1 @ X47 @ X48 @ X49 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('21',plain,(
    ! [X62: $i,X63: $i,X64: $i] :
      ( ( k2_enumset1 @ X62 @ X62 @ X63 @ X64 )
      = ( k1_enumset1 @ X62 @ X63 @ X64 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('22',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( k4_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X17 @ X18 @ X19 ) @ ( k1_enumset1 @ X20 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[l62_enumset1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) @ ( k1_enumset1 @ X5 @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X58: $i,X59: $i,X60: $i,X61: $i] :
      ( ( k3_enumset1 @ X58 @ X58 @ X59 @ X60 @ X61 )
      = ( k2_enumset1 @ X58 @ X59 @ X60 @ X61 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k7_enumset1 @ X2 @ X2 @ X1 @ X0 @ X7 @ X6 @ X5 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k3_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k7_enumset1 @ X6 @ X6 @ X5 @ X4 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X6 @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k7_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X5 @ X4 @ X3 ) @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X62: $i,X63: $i,X64: $i] :
      ( ( k2_enumset1 @ X62 @ X62 @ X63 @ X64 )
      = ( k1_enumset1 @ X62 @ X63 @ X64 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('30',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( k4_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X17 @ X18 @ X19 ) @ ( k1_enumset1 @ X20 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[l62_enumset1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X5 @ X4 @ X3 ) @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X58: $i,X59: $i,X60: $i,X61: $i] :
      ( ( k3_enumset1 @ X58 @ X58 @ X59 @ X60 @ X61 )
      = ( k2_enumset1 @ X58 @ X59 @ X60 @ X61 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X4 @ X3 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','33'])).

thf('35',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( k4_enumset1 @ X47 @ X47 @ X48 @ X49 @ X50 @ X51 )
      = ( k3_enumset1 @ X47 @ X48 @ X49 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X4 @ X3 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','36'])).

thf('38',plain,(
    ! [X58: $i,X59: $i,X60: $i,X61: $i] :
      ( ( k3_enumset1 @ X58 @ X58 @ X59 @ X60 @ X61 )
      = ( k2_enumset1 @ X58 @ X59 @ X60 @ X61 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X6 @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X6 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k7_enumset1 @ X2 @ X2 @ X1 @ X0 @ X7 @ X6 @ X5 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k3_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('42',plain,(
    ! [X58: $i,X59: $i,X60: $i,X61: $i] :
      ( ( k3_enumset1 @ X58 @ X58 @ X59 @ X60 @ X61 )
      = ( k2_enumset1 @ X58 @ X59 @ X60 @ X61 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('43',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( k7_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 ) @ ( k2_enumset1 @ X37 @ X38 @ X39 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t131_enumset1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k7_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X7 @ X6 @ X5 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_enumset1 @ X7 @ X6 @ X5 @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X62: $i,X63: $i,X64: $i] :
      ( ( k2_enumset1 @ X62 @ X62 @ X63 @ X64 )
      = ( k1_enumset1 @ X62 @ X63 @ X64 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) @ ( k1_enumset1 @ X5 @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X5 @ X5 @ X4 @ X3 ) @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k7_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X5 @ X5 @ X4 ) @ ( k3_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X5 @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X6 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X5 @ X5 @ X4 ) @ ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X6 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ ( k4_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X8 @ X8 @ X7 ) @ ( k2_xboole_0 @ ( k1_enumset1 @ X6 @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['40','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ ( k4_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X8 @ X7 @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X6 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X5 @ X4 @ X3 ) @ ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X6 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('57',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( k4_enumset1 @ X47 @ X47 @ X48 @ X49 @ X50 @ X51 )
      = ( k3_enumset1 @ X47 @ X48 @ X49 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X8 @ X7 @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['54','55','56','57'])).

thf('59',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( k7_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 ) @ ( k2_enumset1 @ X37 @ X38 @ X39 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t131_enumset1])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X8 @ X7 @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k7_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ( k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I )
 != ( k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) ),
    inference(demod,[status(thm)],['6','60'])).

thf('62',plain,(
    $false ),
    inference(simplify,[status(thm)],['61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QcLPAehl32
% 0.13/0.37  % Computer   : n020.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 19:19:07 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 13.29/13.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 13.29/13.48  % Solved by: fo/fo7.sh
% 13.29/13.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 13.29/13.48  % done 4567 iterations in 13.008s
% 13.29/13.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 13.29/13.48  % SZS output start Refutation
% 13.29/13.48  thf(k7_enumset1_type, type, k7_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 13.29/13.48                                           $i > $i > $i).
% 13.29/13.48  thf(sk_C_type, type, sk_C: $i).
% 13.29/13.48  thf(sk_F_type, type, sk_F: $i).
% 13.29/13.48  thf(sk_D_type, type, sk_D: $i).
% 13.29/13.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 13.29/13.48  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 13.29/13.48  thf(sk_G_type, type, sk_G: $i).
% 13.29/13.48  thf(sk_I_type, type, sk_I: $i).
% 13.29/13.48  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 13.29/13.48  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 13.29/13.48  thf(sk_B_type, type, sk_B: $i).
% 13.29/13.48  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 13.29/13.48  thf(sk_A_type, type, sk_A: $i).
% 13.29/13.48  thf(sk_E_type, type, sk_E: $i).
% 13.29/13.48  thf(sk_H_type, type, sk_H: $i).
% 13.29/13.48  thf(t132_enumset1, conjecture,
% 13.29/13.48    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 13.29/13.48     ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) =
% 13.29/13.48       ( k2_xboole_0 @
% 13.29/13.48         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_enumset1 @ G @ H @ I ) ) ))).
% 13.29/13.48  thf(zf_stmt_0, negated_conjecture,
% 13.29/13.48    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 13.29/13.48        ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) =
% 13.29/13.48          ( k2_xboole_0 @
% 13.29/13.48            ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ 
% 13.29/13.48            ( k1_enumset1 @ G @ H @ I ) ) ) )),
% 13.29/13.48    inference('cnf.neg', [status(esa)], [t132_enumset1])).
% 13.29/13.48  thf('0', plain,
% 13.29/13.48      (((k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ 
% 13.29/13.48         sk_I)
% 13.29/13.48         != (k2_xboole_0 @ 
% 13.29/13.48             (k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 13.29/13.48             (k1_enumset1 @ sk_G @ sk_H @ sk_I)))),
% 13.29/13.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.29/13.48  thf(l62_enumset1, axiom,
% 13.29/13.48    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 13.29/13.48     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 13.29/13.48       ( k2_xboole_0 @
% 13.29/13.48         ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ))).
% 13.29/13.48  thf('1', plain,
% 13.29/13.48      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 13.29/13.48         ((k4_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22)
% 13.29/13.48           = (k2_xboole_0 @ (k1_enumset1 @ X17 @ X18 @ X19) @ 
% 13.29/13.48              (k1_enumset1 @ X20 @ X21 @ X22)))),
% 13.29/13.48      inference('cnf', [status(esa)], [l62_enumset1])).
% 13.29/13.48  thf('2', plain,
% 13.29/13.48      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 13.29/13.48         ((k4_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22)
% 13.29/13.48           = (k2_xboole_0 @ (k1_enumset1 @ X17 @ X18 @ X19) @ 
% 13.29/13.48              (k1_enumset1 @ X20 @ X21 @ X22)))),
% 13.29/13.48      inference('cnf', [status(esa)], [l62_enumset1])).
% 13.29/13.48  thf(t4_xboole_1, axiom,
% 13.29/13.48    (![A:$i,B:$i,C:$i]:
% 13.29/13.48     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 13.29/13.48       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 13.29/13.48  thf('3', plain,
% 13.29/13.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.29/13.48         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 13.29/13.48           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 13.29/13.48      inference('cnf', [status(esa)], [t4_xboole_1])).
% 13.29/13.48  thf('4', plain,
% 13.29/13.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 13.29/13.48         ((k2_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ X6)
% 13.29/13.48           = (k2_xboole_0 @ (k1_enumset1 @ X5 @ X4 @ X3) @ 
% 13.29/13.48              (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X6)))),
% 13.29/13.48      inference('sup+', [status(thm)], ['2', '3'])).
% 13.29/13.48  thf('5', plain,
% 13.29/13.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 13.29/13.48         X7 : $i, X8 : $i]:
% 13.29/13.48         ((k2_xboole_0 @ (k4_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 @ X3) @ 
% 13.29/13.48           (k1_enumset1 @ X2 @ X1 @ X0))
% 13.29/13.48           = (k2_xboole_0 @ (k1_enumset1 @ X8 @ X7 @ X6) @ 
% 13.29/13.48              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 13.29/13.48      inference('sup+', [status(thm)], ['1', '4'])).
% 13.29/13.48  thf('6', plain,
% 13.29/13.48      (((k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ 
% 13.29/13.48         sk_I)
% 13.29/13.48         != (k2_xboole_0 @ (k1_enumset1 @ sk_A @ sk_B @ sk_C) @ 
% 13.29/13.48             (k4_enumset1 @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I)))),
% 13.29/13.48      inference('demod', [status(thm)], ['0', '5'])).
% 13.29/13.48  thf(t84_enumset1, axiom,
% 13.29/13.48    (![A:$i,B:$i,C:$i]:
% 13.29/13.48     ( ( k4_enumset1 @ A @ A @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 13.29/13.48  thf('7', plain,
% 13.29/13.48      (![X62 : $i, X63 : $i, X64 : $i]:
% 13.29/13.48         ((k4_enumset1 @ X62 @ X62 @ X62 @ X62 @ X63 @ X64)
% 13.29/13.48           = (k1_enumset1 @ X62 @ X63 @ X64))),
% 13.29/13.48      inference('cnf', [status(esa)], [t84_enumset1])).
% 13.29/13.48  thf(t79_enumset1, axiom,
% 13.29/13.48    (![A:$i,B:$i,C:$i,D:$i]:
% 13.29/13.48     ( ( k4_enumset1 @ A @ A @ A @ B @ C @ D ) =
% 13.29/13.48       ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 13.29/13.48  thf('8', plain,
% 13.29/13.48      (![X58 : $i, X59 : $i, X60 : $i, X61 : $i]:
% 13.29/13.48         ((k4_enumset1 @ X58 @ X58 @ X58 @ X59 @ X60 @ X61)
% 13.29/13.48           = (k2_enumset1 @ X58 @ X59 @ X60 @ X61))),
% 13.29/13.48      inference('cnf', [status(esa)], [t79_enumset1])).
% 13.29/13.48  thf('9', plain,
% 13.29/13.48      (![X62 : $i, X63 : $i, X64 : $i]:
% 13.29/13.48         ((k2_enumset1 @ X62 @ X62 @ X63 @ X64)
% 13.29/13.48           = (k1_enumset1 @ X62 @ X63 @ X64))),
% 13.29/13.48      inference('demod', [status(thm)], ['7', '8'])).
% 13.29/13.48  thf(l142_enumset1, axiom,
% 13.29/13.48    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 13.29/13.48     ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) =
% 13.29/13.48       ( k2_xboole_0 @
% 13.29/13.48         ( k2_enumset1 @ A @ B @ C @ D ) @ ( k3_enumset1 @ E @ F @ G @ H @ I ) ) ))).
% 13.29/13.48  thf('10', plain,
% 13.29/13.48      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, 
% 13.29/13.48         X15 : $i, X16 : $i]:
% 13.29/13.48         ((k7_enumset1 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16)
% 13.29/13.48           = (k2_xboole_0 @ (k2_enumset1 @ X8 @ X9 @ X10 @ X11) @ 
% 13.29/13.48              (k3_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16)))),
% 13.29/13.48      inference('cnf', [status(esa)], [l142_enumset1])).
% 13.29/13.48  thf('11', plain,
% 13.29/13.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 13.29/13.48         ((k7_enumset1 @ X2 @ X2 @ X1 @ X0 @ X7 @ X6 @ X5 @ X4 @ X3)
% 13.29/13.48           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 13.29/13.48              (k3_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3)))),
% 13.29/13.48      inference('sup+', [status(thm)], ['9', '10'])).
% 13.29/13.48  thf('12', plain,
% 13.29/13.48      (![X62 : $i, X63 : $i, X64 : $i]:
% 13.29/13.48         ((k2_enumset1 @ X62 @ X62 @ X63 @ X64)
% 13.29/13.48           = (k1_enumset1 @ X62 @ X63 @ X64))),
% 13.29/13.48      inference('demod', [status(thm)], ['7', '8'])).
% 13.29/13.48  thf(t131_enumset1, axiom,
% 13.29/13.48    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 13.29/13.48     ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) =
% 13.29/13.48       ( k2_xboole_0 @
% 13.29/13.48         ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_enumset1 @ F @ G @ H @ I ) ) ))).
% 13.29/13.48  thf('13', plain,
% 13.29/13.48      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, 
% 13.29/13.48         X39 : $i, X40 : $i]:
% 13.29/13.48         ((k7_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40)
% 13.29/13.48           = (k2_xboole_0 @ (k3_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36) @ 
% 13.29/13.48              (k2_enumset1 @ X37 @ X38 @ X39 @ X40)))),
% 13.29/13.48      inference('cnf', [status(esa)], [t131_enumset1])).
% 13.29/13.48  thf('14', plain,
% 13.29/13.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 13.29/13.48         ((k7_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X2 @ X1 @ X0)
% 13.29/13.48           = (k2_xboole_0 @ (k3_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3) @ 
% 13.29/13.48              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 13.29/13.48      inference('sup+', [status(thm)], ['12', '13'])).
% 13.29/13.48  thf('15', plain,
% 13.29/13.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 13.29/13.48         ((k2_xboole_0 @ (k1_enumset1 @ X6 @ X5 @ X4) @ 
% 13.29/13.48           (k3_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0))
% 13.29/13.48           = (k2_xboole_0 @ (k3_enumset1 @ X6 @ X6 @ X5 @ X4 @ X3) @ 
% 13.29/13.48              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 13.29/13.48      inference('sup+', [status(thm)], ['11', '14'])).
% 13.29/13.48  thf('16', plain,
% 13.29/13.48      (![X58 : $i, X59 : $i, X60 : $i, X61 : $i]:
% 13.29/13.48         ((k4_enumset1 @ X58 @ X58 @ X58 @ X59 @ X60 @ X61)
% 13.29/13.48           = (k2_enumset1 @ X58 @ X59 @ X60 @ X61))),
% 13.29/13.48      inference('cnf', [status(esa)], [t79_enumset1])).
% 13.29/13.48  thf(t73_enumset1, axiom,
% 13.29/13.48    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 13.29/13.48     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 13.29/13.48       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 13.29/13.48  thf('17', plain,
% 13.29/13.48      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 13.29/13.48         ((k4_enumset1 @ X47 @ X47 @ X48 @ X49 @ X50 @ X51)
% 13.29/13.48           = (k3_enumset1 @ X47 @ X48 @ X49 @ X50 @ X51))),
% 13.29/13.48      inference('cnf', [status(esa)], [t73_enumset1])).
% 13.29/13.48  thf('18', plain,
% 13.29/13.48      (![X58 : $i, X59 : $i, X60 : $i, X61 : $i]:
% 13.29/13.48         ((k3_enumset1 @ X58 @ X58 @ X59 @ X60 @ X61)
% 13.29/13.48           = (k2_enumset1 @ X58 @ X59 @ X60 @ X61))),
% 13.29/13.48      inference('demod', [status(thm)], ['16', '17'])).
% 13.29/13.48  thf('19', plain,
% 13.29/13.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 13.29/13.48         ((k2_xboole_0 @ (k1_enumset1 @ X6 @ X5 @ X4) @ 
% 13.29/13.48           (k3_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0))
% 13.29/13.48           = (k2_xboole_0 @ (k2_enumset1 @ X6 @ X5 @ X4 @ X3) @ 
% 13.29/13.48              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 13.29/13.48      inference('demod', [status(thm)], ['15', '18'])).
% 13.29/13.48  thf('20', plain,
% 13.29/13.48      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 13.29/13.48         ((k4_enumset1 @ X47 @ X47 @ X48 @ X49 @ X50 @ X51)
% 13.29/13.48           = (k3_enumset1 @ X47 @ X48 @ X49 @ X50 @ X51))),
% 13.29/13.48      inference('cnf', [status(esa)], [t73_enumset1])).
% 13.29/13.48  thf('21', plain,
% 13.29/13.48      (![X62 : $i, X63 : $i, X64 : $i]:
% 13.29/13.48         ((k2_enumset1 @ X62 @ X62 @ X63 @ X64)
% 13.29/13.48           = (k1_enumset1 @ X62 @ X63 @ X64))),
% 13.29/13.48      inference('demod', [status(thm)], ['7', '8'])).
% 13.29/13.48  thf('22', plain,
% 13.29/13.48      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 13.29/13.48         ((k4_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22)
% 13.29/13.48           = (k2_xboole_0 @ (k1_enumset1 @ X17 @ X18 @ X19) @ 
% 13.29/13.48              (k1_enumset1 @ X20 @ X21 @ X22)))),
% 13.29/13.48      inference('cnf', [status(esa)], [l62_enumset1])).
% 13.29/13.48  thf('23', plain,
% 13.29/13.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 13.29/13.48         ((k4_enumset1 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3)
% 13.29/13.48           = (k2_xboole_0 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0) @ 
% 13.29/13.48              (k1_enumset1 @ X5 @ X4 @ X3)))),
% 13.29/13.48      inference('sup+', [status(thm)], ['21', '22'])).
% 13.29/13.48  thf('24', plain,
% 13.29/13.48      (![X58 : $i, X59 : $i, X60 : $i, X61 : $i]:
% 13.29/13.48         ((k3_enumset1 @ X58 @ X58 @ X59 @ X60 @ X61)
% 13.29/13.48           = (k2_enumset1 @ X58 @ X59 @ X60 @ X61))),
% 13.29/13.48      inference('demod', [status(thm)], ['16', '17'])).
% 13.29/13.48  thf('25', plain,
% 13.29/13.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 13.29/13.48         ((k7_enumset1 @ X2 @ X2 @ X1 @ X0 @ X7 @ X6 @ X5 @ X4 @ X3)
% 13.29/13.48           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 13.29/13.48              (k3_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3)))),
% 13.29/13.48      inference('sup+', [status(thm)], ['9', '10'])).
% 13.29/13.48  thf('26', plain,
% 13.29/13.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 13.29/13.48         ((k7_enumset1 @ X6 @ X6 @ X5 @ X4 @ X3 @ X3 @ X2 @ X1 @ X0)
% 13.29/13.48           = (k2_xboole_0 @ (k1_enumset1 @ X6 @ X5 @ X4) @ 
% 13.29/13.48              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 13.29/13.48      inference('sup+', [status(thm)], ['24', '25'])).
% 13.29/13.48  thf('27', plain,
% 13.29/13.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 13.29/13.48         ((k7_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X2 @ X1 @ X0)
% 13.29/13.48           = (k2_xboole_0 @ (k3_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3) @ 
% 13.29/13.48              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 13.29/13.48      inference('sup+', [status(thm)], ['12', '13'])).
% 13.29/13.48  thf('28', plain,
% 13.29/13.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 13.29/13.48         ((k2_xboole_0 @ (k1_enumset1 @ X5 @ X4 @ X3) @ 
% 13.29/13.48           (k2_enumset1 @ X2 @ X2 @ X1 @ X0))
% 13.29/13.48           = (k2_xboole_0 @ (k3_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2) @ 
% 13.29/13.48              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 13.29/13.48      inference('sup+', [status(thm)], ['26', '27'])).
% 13.29/13.48  thf('29', plain,
% 13.29/13.48      (![X62 : $i, X63 : $i, X64 : $i]:
% 13.29/13.48         ((k2_enumset1 @ X62 @ X62 @ X63 @ X64)
% 13.29/13.48           = (k1_enumset1 @ X62 @ X63 @ X64))),
% 13.29/13.48      inference('demod', [status(thm)], ['7', '8'])).
% 13.29/13.48  thf('30', plain,
% 13.29/13.48      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 13.29/13.48         ((k4_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22)
% 13.29/13.48           = (k2_xboole_0 @ (k1_enumset1 @ X17 @ X18 @ X19) @ 
% 13.29/13.48              (k1_enumset1 @ X20 @ X21 @ X22)))),
% 13.29/13.48      inference('cnf', [status(esa)], [l62_enumset1])).
% 13.29/13.48  thf('31', plain,
% 13.29/13.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 13.29/13.48         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 13.29/13.48           = (k2_xboole_0 @ (k1_enumset1 @ X5 @ X4 @ X3) @ 
% 13.29/13.48              (k2_enumset1 @ X2 @ X2 @ X1 @ X0)))),
% 13.29/13.48      inference('sup+', [status(thm)], ['29', '30'])).
% 13.29/13.48  thf('32', plain,
% 13.29/13.48      (![X58 : $i, X59 : $i, X60 : $i, X61 : $i]:
% 13.29/13.48         ((k3_enumset1 @ X58 @ X58 @ X59 @ X60 @ X61)
% 13.29/13.48           = (k2_enumset1 @ X58 @ X59 @ X60 @ X61))),
% 13.29/13.48      inference('demod', [status(thm)], ['16', '17'])).
% 13.29/13.48  thf('33', plain,
% 13.29/13.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 13.29/13.48         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 13.29/13.48           = (k2_xboole_0 @ (k2_enumset1 @ X5 @ X4 @ X3 @ X2) @ 
% 13.29/13.48              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 13.29/13.48      inference('demod', [status(thm)], ['28', '31', '32'])).
% 13.29/13.48  thf('34', plain,
% 13.29/13.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 13.29/13.48         ((k4_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 13.29/13.48           = (k4_enumset1 @ X4 @ X3 @ X2 @ X2 @ X1 @ X0))),
% 13.29/13.48      inference('sup+', [status(thm)], ['23', '33'])).
% 13.29/13.48  thf('35', plain,
% 13.29/13.48      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 13.29/13.48         ((k4_enumset1 @ X47 @ X47 @ X48 @ X49 @ X50 @ X51)
% 13.29/13.48           = (k3_enumset1 @ X47 @ X48 @ X49 @ X50 @ X51))),
% 13.29/13.48      inference('cnf', [status(esa)], [t73_enumset1])).
% 13.29/13.48  thf('36', plain,
% 13.29/13.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 13.29/13.48         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 13.29/13.48           = (k4_enumset1 @ X4 @ X3 @ X2 @ X2 @ X1 @ X0))),
% 13.29/13.48      inference('demod', [status(thm)], ['34', '35'])).
% 13.29/13.48  thf('37', plain,
% 13.29/13.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 13.29/13.48         ((k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0)
% 13.29/13.48           = (k3_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0))),
% 13.29/13.48      inference('sup+', [status(thm)], ['20', '36'])).
% 13.29/13.48  thf('38', plain,
% 13.29/13.48      (![X58 : $i, X59 : $i, X60 : $i, X61 : $i]:
% 13.29/13.48         ((k3_enumset1 @ X58 @ X58 @ X59 @ X60 @ X61)
% 13.29/13.48           = (k2_enumset1 @ X58 @ X59 @ X60 @ X61))),
% 13.29/13.48      inference('demod', [status(thm)], ['16', '17'])).
% 13.29/13.48  thf('39', plain,
% 13.29/13.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 13.29/13.48         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 13.29/13.48           = (k3_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0))),
% 13.29/13.48      inference('demod', [status(thm)], ['37', '38'])).
% 13.29/13.48  thf('40', plain,
% 13.29/13.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 13.29/13.48         ((k2_xboole_0 @ (k1_enumset1 @ X6 @ X5 @ X4) @ 
% 13.29/13.48           (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 13.29/13.48           = (k2_xboole_0 @ (k2_enumset1 @ X6 @ X5 @ X4 @ X3) @ 
% 13.29/13.48              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 13.29/13.48      inference('demod', [status(thm)], ['19', '39'])).
% 13.29/13.48  thf('41', plain,
% 13.29/13.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 13.29/13.48         ((k7_enumset1 @ X2 @ X2 @ X1 @ X0 @ X7 @ X6 @ X5 @ X4 @ X3)
% 13.29/13.48           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 13.29/13.48              (k3_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3)))),
% 13.29/13.48      inference('sup+', [status(thm)], ['9', '10'])).
% 13.29/13.48  thf('42', plain,
% 13.29/13.48      (![X58 : $i, X59 : $i, X60 : $i, X61 : $i]:
% 13.29/13.48         ((k3_enumset1 @ X58 @ X58 @ X59 @ X60 @ X61)
% 13.29/13.48           = (k2_enumset1 @ X58 @ X59 @ X60 @ X61))),
% 13.29/13.48      inference('demod', [status(thm)], ['16', '17'])).
% 13.29/13.48  thf('43', plain,
% 13.29/13.48      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, 
% 13.29/13.48         X39 : $i, X40 : $i]:
% 13.29/13.48         ((k7_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40)
% 13.29/13.48           = (k2_xboole_0 @ (k3_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36) @ 
% 13.29/13.48              (k2_enumset1 @ X37 @ X38 @ X39 @ X40)))),
% 13.29/13.48      inference('cnf', [status(esa)], [t131_enumset1])).
% 13.29/13.48  thf('44', plain,
% 13.29/13.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 13.29/13.48         ((k7_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X7 @ X6 @ X5 @ X4)
% 13.29/13.48           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 13.29/13.48              (k2_enumset1 @ X7 @ X6 @ X5 @ X4)))),
% 13.29/13.48      inference('sup+', [status(thm)], ['42', '43'])).
% 13.29/13.48  thf('45', plain,
% 13.29/13.48      (![X62 : $i, X63 : $i, X64 : $i]:
% 13.29/13.48         ((k2_enumset1 @ X62 @ X62 @ X63 @ X64)
% 13.29/13.48           = (k1_enumset1 @ X62 @ X63 @ X64))),
% 13.29/13.48      inference('demod', [status(thm)], ['7', '8'])).
% 13.29/13.48  thf('46', plain,
% 13.29/13.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 13.29/13.48         ((k4_enumset1 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3)
% 13.29/13.48           = (k2_xboole_0 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0) @ 
% 13.29/13.48              (k1_enumset1 @ X5 @ X4 @ X3)))),
% 13.29/13.48      inference('sup+', [status(thm)], ['21', '22'])).
% 13.29/13.48  thf('47', plain,
% 13.29/13.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 13.29/13.48         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 13.29/13.48           = (k2_xboole_0 @ (k2_enumset1 @ X5 @ X5 @ X4 @ X3) @ 
% 13.29/13.48              (k2_enumset1 @ X2 @ X2 @ X1 @ X0)))),
% 13.29/13.48      inference('sup+', [status(thm)], ['45', '46'])).
% 13.29/13.48  thf('48', plain,
% 13.29/13.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 13.29/13.48         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 13.29/13.48           = (k7_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X2 @ X1 @ X0))),
% 13.29/13.48      inference('sup+', [status(thm)], ['44', '47'])).
% 13.29/13.48  thf('49', plain,
% 13.29/13.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 13.29/13.48         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 13.29/13.48           = (k2_xboole_0 @ (k1_enumset1 @ X5 @ X5 @ X4) @ 
% 13.29/13.48              (k3_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0)))),
% 13.29/13.48      inference('sup+', [status(thm)], ['41', '48'])).
% 13.29/13.48  thf('50', plain,
% 13.29/13.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 13.29/13.48         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 13.29/13.48           = (k3_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0))),
% 13.29/13.48      inference('demod', [status(thm)], ['37', '38'])).
% 13.29/13.48  thf('51', plain,
% 13.29/13.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 13.29/13.48         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 13.29/13.48           = (k2_xboole_0 @ (k1_enumset1 @ X5 @ X5 @ X4) @ 
% 13.29/13.48              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 13.29/13.48      inference('demod', [status(thm)], ['49', '50'])).
% 13.29/13.48  thf('52', plain,
% 13.29/13.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.29/13.48         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 13.29/13.48           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 13.29/13.48      inference('cnf', [status(esa)], [t4_xboole_1])).
% 13.29/13.48  thf('53', plain,
% 13.29/13.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 13.29/13.48         ((k2_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ X6)
% 13.29/13.48           = (k2_xboole_0 @ (k1_enumset1 @ X5 @ X5 @ X4) @ 
% 13.29/13.48              (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X6)))),
% 13.29/13.48      inference('sup+', [status(thm)], ['51', '52'])).
% 13.29/13.48  thf('54', plain,
% 13.29/13.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 13.29/13.48         X7 : $i, X8 : $i]:
% 13.29/13.48         ((k2_xboole_0 @ (k4_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 @ X3) @ 
% 13.29/13.48           (k1_enumset1 @ X2 @ X1 @ X0))
% 13.29/13.48           = (k2_xboole_0 @ (k1_enumset1 @ X8 @ X8 @ X7) @ 
% 13.29/13.48              (k2_xboole_0 @ (k1_enumset1 @ X6 @ X5 @ X4) @ 
% 13.29/13.48               (k2_enumset1 @ X3 @ X2 @ X1 @ X0))))),
% 13.29/13.48      inference('sup+', [status(thm)], ['40', '53'])).
% 13.29/13.48  thf('55', plain,
% 13.29/13.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 13.29/13.48         X7 : $i, X8 : $i]:
% 13.29/13.48         ((k2_xboole_0 @ (k4_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 @ X3) @ 
% 13.29/13.48           (k1_enumset1 @ X2 @ X1 @ X0))
% 13.29/13.48           = (k2_xboole_0 @ (k1_enumset1 @ X8 @ X7 @ X6) @ 
% 13.29/13.48              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 13.29/13.48      inference('sup+', [status(thm)], ['1', '4'])).
% 13.29/13.48  thf('56', plain,
% 13.29/13.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 13.29/13.48         ((k2_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ X6)
% 13.29/13.48           = (k2_xboole_0 @ (k1_enumset1 @ X5 @ X4 @ X3) @ 
% 13.29/13.48              (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X6)))),
% 13.29/13.48      inference('sup+', [status(thm)], ['2', '3'])).
% 13.29/13.48  thf('57', plain,
% 13.29/13.48      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 13.29/13.48         ((k4_enumset1 @ X47 @ X47 @ X48 @ X49 @ X50 @ X51)
% 13.29/13.48           = (k3_enumset1 @ X47 @ X48 @ X49 @ X50 @ X51))),
% 13.29/13.48      inference('cnf', [status(esa)], [t73_enumset1])).
% 13.29/13.48  thf('58', plain,
% 13.29/13.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 13.29/13.48         X7 : $i, X8 : $i]:
% 13.29/13.48         ((k2_xboole_0 @ (k1_enumset1 @ X8 @ X7 @ X6) @ 
% 13.29/13.48           (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 13.29/13.48           = (k2_xboole_0 @ (k3_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4) @ 
% 13.29/13.48              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 13.29/13.48      inference('demod', [status(thm)], ['54', '55', '56', '57'])).
% 13.29/13.48  thf('59', plain,
% 13.29/13.48      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, 
% 13.29/13.48         X39 : $i, X40 : $i]:
% 13.29/13.48         ((k7_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40)
% 13.29/13.48           = (k2_xboole_0 @ (k3_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36) @ 
% 13.29/13.48              (k2_enumset1 @ X37 @ X38 @ X39 @ X40)))),
% 13.29/13.48      inference('cnf', [status(esa)], [t131_enumset1])).
% 13.29/13.48  thf('60', plain,
% 13.29/13.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 13.29/13.48         X7 : $i, X8 : $i]:
% 13.29/13.48         ((k2_xboole_0 @ (k1_enumset1 @ X8 @ X7 @ X6) @ 
% 13.29/13.48           (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 13.29/13.48           = (k7_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 13.29/13.48      inference('demod', [status(thm)], ['58', '59'])).
% 13.29/13.48  thf('61', plain,
% 13.29/13.48      (((k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ 
% 13.29/13.48         sk_I)
% 13.29/13.48         != (k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ 
% 13.29/13.48             sk_H @ sk_I))),
% 13.29/13.48      inference('demod', [status(thm)], ['6', '60'])).
% 13.29/13.48  thf('62', plain, ($false), inference('simplify', [status(thm)], ['61'])).
% 13.29/13.48  
% 13.29/13.48  % SZS output end Refutation
% 13.29/13.48  
% 13.29/13.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

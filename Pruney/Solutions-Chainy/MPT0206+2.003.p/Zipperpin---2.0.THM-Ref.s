%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.55HHmUFPHp

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:27 EST 2020

% Result     : Theorem 5.71s
% Output     : Refutation 5.71s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 198 expanded)
%              Number of leaves         :   25 (  78 expanded)
%              Depth                    :   19
%              Number of atoms          : 1126 (2635 expanded)
%              Number of equality atoms :   70 ( 181 expanded)
%              Maximal formula depth    :   21 (  11 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_enumset1_type,type,(
    k7_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_I_type,type,(
    sk_I: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_enumset1 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X8 @ X9 @ X10 ) @ ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l62_enumset1])).

thf('2',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_enumset1 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X8 @ X9 @ X10 ) @ ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ) ),
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

thf(t51_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ) )).

thf('7',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k4_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 )
      = ( k2_xboole_0 @ ( k1_tarski @ X32 ) @ ( k3_enumset1 @ X33 @ X34 @ X35 @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t51_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('8',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( k2_enumset1 @ X44 @ X44 @ X45 @ X46 )
      = ( k1_enumset1 @ X44 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('9',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( k3_enumset1 @ X47 @ X47 @ X48 @ X49 @ X50 )
      = ( k2_enumset1 @ X47 @ X48 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t55_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ) )).

thf('10',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( k4_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42 ) @ ( k1_tarski @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t55_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('12',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( k4_enumset1 @ X51 @ X51 @ X52 @ X53 @ X54 @ X55 )
      = ( k3_enumset1 @ X51 @ X52 @ X53 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( k3_enumset1 @ X47 @ X47 @ X48 @ X49 @ X50 )
      = ( k2_enumset1 @ X47 @ X48 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X8 @ X7 @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X8 @ X7 @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','18'])).

thf('20',plain,(
    ( k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I )
 != ( k2_xboole_0 @ ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k3_enumset1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) ) ),
    inference(demod,[status(thm)],['6','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('22',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( k2_enumset1 @ X44 @ X44 @ X45 @ X46 )
      = ( k1_enumset1 @ X44 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('23',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( k3_enumset1 @ X47 @ X47 @ X48 @ X49 @ X50 )
      = ( k2_enumset1 @ X47 @ X48 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('24',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k4_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 )
      = ( k2_xboole_0 @ ( k1_tarski @ X32 ) @ ( k3_enumset1 @ X33 @ X34 @ X35 @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t51_enumset1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( k2_enumset1 @ X44 @ X44 @ X45 @ X46 )
      = ( k1_enumset1 @ X44 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('28',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( k4_enumset1 @ X51 @ X51 @ X52 @ X53 @ X54 @ X55 )
      = ( k3_enumset1 @ X51 @ X52 @ X53 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( k3_enumset1 @ X47 @ X47 @ X48 @ X49 @ X50 )
      = ( k2_enumset1 @ X47 @ X48 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('32',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( k2_enumset1 @ X44 @ X44 @ X45 @ X46 )
      = ( k1_enumset1 @ X44 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_enumset1 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X8 @ X9 @ X10 ) @ ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l62_enumset1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_enumset1 @ X0 @ X4 @ X3 ) )
      = ( k4_enumset1 @ X2 @ X2 @ X1 @ X0 @ X4 @ X3 ) ) ),
    inference('sup+',[status(thm)],['27','37'])).

thf('39',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k4_enumset1 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X8 @ X9 @ X10 ) @ ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l62_enumset1])).

thf('40',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( k4_enumset1 @ X51 @ X51 @ X52 @ X53 @ X54 @ X55 )
      = ( k3_enumset1 @ X51 @ X52 @ X53 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X2 @ X1 @ X0 @ X0 @ X4 @ X3 )
      = ( k3_enumset1 @ X2 @ X1 @ X0 @ X4 @ X3 ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','41'])).

thf('43',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( k4_enumset1 @ X51 @ X51 @ X52 @ X53 @ X54 @ X55 )
      = ( k3_enumset1 @ X51 @ X52 @ X53 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X2 @ X1 @ X0 @ X0 @ X4 @ X3 )
      = ( k3_enumset1 @ X2 @ X1 @ X0 @ X4 @ X3 ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( k3_enumset1 @ X47 @ X47 @ X48 @ X49 @ X50 )
      = ( k2_enumset1 @ X47 @ X48 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['42','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X5 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 ) @ ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X8 @ X7 @ X6 @ X5 ) @ ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X8 @ X7 @ X6 @ X5 ) @ ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['21','54'])).

thf(t131_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_enumset1 @ F @ G @ H @ I ) ) ) )).

thf('56',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k7_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 ) @ ( k2_enumset1 @ X28 @ X29 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t131_enumset1])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k7_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X8 @ X7 @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ( k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I )
 != ( k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) ),
    inference(demod,[status(thm)],['20','58'])).

thf('60',plain,(
    $false ),
    inference(simplify,[status(thm)],['59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.55HHmUFPHp
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:30:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 5.71/5.93  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.71/5.93  % Solved by: fo/fo7.sh
% 5.71/5.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.71/5.93  % done 4018 iterations in 5.479s
% 5.71/5.93  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.71/5.93  % SZS output start Refutation
% 5.71/5.93  thf(sk_C_type, type, sk_C: $i).
% 5.71/5.93  thf(sk_F_type, type, sk_F: $i).
% 5.71/5.93  thf(sk_G_type, type, sk_G: $i).
% 5.71/5.93  thf(sk_A_type, type, sk_A: $i).
% 5.71/5.93  thf(k7_enumset1_type, type, k7_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 5.71/5.93                                           $i > $i > $i).
% 5.71/5.93  thf(sk_H_type, type, sk_H: $i).
% 5.71/5.93  thf(sk_D_type, type, sk_D: $i).
% 5.71/5.93  thf(sk_E_type, type, sk_E: $i).
% 5.71/5.93  thf(sk_I_type, type, sk_I: $i).
% 5.71/5.93  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 5.71/5.93  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 5.71/5.93  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 5.71/5.93  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 5.71/5.93  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 5.71/5.93  thf(sk_B_type, type, sk_B: $i).
% 5.71/5.93  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 5.71/5.93  thf(t132_enumset1, conjecture,
% 5.71/5.93    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 5.71/5.93     ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) =
% 5.71/5.93       ( k2_xboole_0 @
% 5.71/5.93         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_enumset1 @ G @ H @ I ) ) ))).
% 5.71/5.93  thf(zf_stmt_0, negated_conjecture,
% 5.71/5.93    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 5.71/5.93        ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) =
% 5.71/5.93          ( k2_xboole_0 @
% 5.71/5.93            ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ 
% 5.71/5.93            ( k1_enumset1 @ G @ H @ I ) ) ) )),
% 5.71/5.93    inference('cnf.neg', [status(esa)], [t132_enumset1])).
% 5.71/5.93  thf('0', plain,
% 5.71/5.93      (((k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ 
% 5.71/5.93         sk_I)
% 5.71/5.93         != (k2_xboole_0 @ 
% 5.71/5.93             (k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 5.71/5.93             (k1_enumset1 @ sk_G @ sk_H @ sk_I)))),
% 5.71/5.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.71/5.93  thf(l62_enumset1, axiom,
% 5.71/5.93    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 5.71/5.93     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 5.71/5.93       ( k2_xboole_0 @
% 5.71/5.93         ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ))).
% 5.71/5.93  thf('1', plain,
% 5.71/5.93      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 5.71/5.93         ((k4_enumset1 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13)
% 5.71/5.93           = (k2_xboole_0 @ (k1_enumset1 @ X8 @ X9 @ X10) @ 
% 5.71/5.93              (k1_enumset1 @ X11 @ X12 @ X13)))),
% 5.71/5.93      inference('cnf', [status(esa)], [l62_enumset1])).
% 5.71/5.93  thf('2', plain,
% 5.71/5.93      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 5.71/5.93         ((k4_enumset1 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13)
% 5.71/5.93           = (k2_xboole_0 @ (k1_enumset1 @ X8 @ X9 @ X10) @ 
% 5.71/5.93              (k1_enumset1 @ X11 @ X12 @ X13)))),
% 5.71/5.93      inference('cnf', [status(esa)], [l62_enumset1])).
% 5.71/5.93  thf(t4_xboole_1, axiom,
% 5.71/5.93    (![A:$i,B:$i,C:$i]:
% 5.71/5.93     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 5.71/5.93       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 5.71/5.93  thf('3', plain,
% 5.71/5.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.71/5.93         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 5.71/5.93           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 5.71/5.93      inference('cnf', [status(esa)], [t4_xboole_1])).
% 5.71/5.93  thf('4', plain,
% 5.71/5.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 5.71/5.93         ((k2_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ X6)
% 5.71/5.93           = (k2_xboole_0 @ (k1_enumset1 @ X5 @ X4 @ X3) @ 
% 5.71/5.93              (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X6)))),
% 5.71/5.93      inference('sup+', [status(thm)], ['2', '3'])).
% 5.71/5.93  thf('5', plain,
% 5.71/5.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 5.71/5.93         X7 : $i, X8 : $i]:
% 5.71/5.93         ((k2_xboole_0 @ (k4_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 @ X3) @ 
% 5.71/5.93           (k1_enumset1 @ X2 @ X1 @ X0))
% 5.71/5.93           = (k2_xboole_0 @ (k1_enumset1 @ X8 @ X7 @ X6) @ 
% 5.71/5.93              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 5.71/5.93      inference('sup+', [status(thm)], ['1', '4'])).
% 5.71/5.93  thf('6', plain,
% 5.71/5.93      (((k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ 
% 5.71/5.93         sk_I)
% 5.71/5.93         != (k2_xboole_0 @ (k1_enumset1 @ sk_A @ sk_B @ sk_C) @ 
% 5.71/5.93             (k4_enumset1 @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I)))),
% 5.71/5.93      inference('demod', [status(thm)], ['0', '5'])).
% 5.71/5.93  thf(t51_enumset1, axiom,
% 5.71/5.93    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 5.71/5.93     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 5.71/5.93       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ))).
% 5.71/5.93  thf('7', plain,
% 5.71/5.93      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 5.71/5.93         ((k4_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37)
% 5.71/5.93           = (k2_xboole_0 @ (k1_tarski @ X32) @ 
% 5.71/5.93              (k3_enumset1 @ X33 @ X34 @ X35 @ X36 @ X37)))),
% 5.71/5.93      inference('cnf', [status(esa)], [t51_enumset1])).
% 5.71/5.93  thf(t71_enumset1, axiom,
% 5.71/5.93    (![A:$i,B:$i,C:$i]:
% 5.71/5.93     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 5.71/5.93  thf('8', plain,
% 5.71/5.93      (![X44 : $i, X45 : $i, X46 : $i]:
% 5.71/5.93         ((k2_enumset1 @ X44 @ X44 @ X45 @ X46)
% 5.71/5.93           = (k1_enumset1 @ X44 @ X45 @ X46))),
% 5.71/5.93      inference('cnf', [status(esa)], [t71_enumset1])).
% 5.71/5.93  thf(t72_enumset1, axiom,
% 5.71/5.93    (![A:$i,B:$i,C:$i,D:$i]:
% 5.71/5.93     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 5.71/5.93  thf('9', plain,
% 5.71/5.93      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 5.71/5.93         ((k3_enumset1 @ X47 @ X47 @ X48 @ X49 @ X50)
% 5.71/5.93           = (k2_enumset1 @ X47 @ X48 @ X49 @ X50))),
% 5.71/5.93      inference('cnf', [status(esa)], [t72_enumset1])).
% 5.71/5.93  thf(t55_enumset1, axiom,
% 5.71/5.93    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 5.71/5.93     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 5.71/5.93       ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ))).
% 5.71/5.93  thf('10', plain,
% 5.71/5.93      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 5.71/5.93         ((k4_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43)
% 5.71/5.93           = (k2_xboole_0 @ (k3_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42) @ 
% 5.71/5.93              (k1_tarski @ X43)))),
% 5.71/5.93      inference('cnf', [status(esa)], [t55_enumset1])).
% 5.71/5.93  thf('11', plain,
% 5.71/5.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 5.71/5.93         ((k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4)
% 5.71/5.93           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 5.71/5.93              (k1_tarski @ X4)))),
% 5.71/5.93      inference('sup+', [status(thm)], ['9', '10'])).
% 5.71/5.93  thf(t73_enumset1, axiom,
% 5.71/5.93    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 5.71/5.93     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 5.71/5.93       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 5.71/5.93  thf('12', plain,
% 5.71/5.93      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 5.71/5.93         ((k4_enumset1 @ X51 @ X51 @ X52 @ X53 @ X54 @ X55)
% 5.71/5.93           = (k3_enumset1 @ X51 @ X52 @ X53 @ X54 @ X55))),
% 5.71/5.93      inference('cnf', [status(esa)], [t73_enumset1])).
% 5.71/5.93  thf('13', plain,
% 5.71/5.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 5.71/5.93         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 5.71/5.93           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 5.71/5.93              (k1_tarski @ X4)))),
% 5.71/5.93      inference('demod', [status(thm)], ['11', '12'])).
% 5.71/5.93  thf('14', plain,
% 5.71/5.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.71/5.93         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3)
% 5.71/5.93           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 5.71/5.93      inference('sup+', [status(thm)], ['8', '13'])).
% 5.71/5.93  thf('15', plain,
% 5.71/5.93      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 5.71/5.93         ((k3_enumset1 @ X47 @ X47 @ X48 @ X49 @ X50)
% 5.71/5.93           = (k2_enumset1 @ X47 @ X48 @ X49 @ X50))),
% 5.71/5.93      inference('cnf', [status(esa)], [t72_enumset1])).
% 5.71/5.93  thf('16', plain,
% 5.71/5.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.71/5.93         ((k2_enumset1 @ X2 @ X1 @ X0 @ X3)
% 5.71/5.93           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 5.71/5.93      inference('demod', [status(thm)], ['14', '15'])).
% 5.71/5.93  thf('17', plain,
% 5.71/5.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.71/5.93         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 5.71/5.93           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 5.71/5.93      inference('cnf', [status(esa)], [t4_xboole_1])).
% 5.71/5.93  thf('18', plain,
% 5.71/5.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 5.71/5.93         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4)
% 5.71/5.93           = (k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ 
% 5.71/5.93              (k2_xboole_0 @ (k1_tarski @ X0) @ X4)))),
% 5.71/5.93      inference('sup+', [status(thm)], ['16', '17'])).
% 5.71/5.93  thf('19', plain,
% 5.71/5.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 5.71/5.93         X7 : $i, X8 : $i]:
% 5.71/5.93         ((k2_xboole_0 @ (k2_enumset1 @ X8 @ X7 @ X6 @ X5) @ 
% 5.71/5.93           (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 5.71/5.93           = (k2_xboole_0 @ (k1_enumset1 @ X8 @ X7 @ X6) @ 
% 5.71/5.93              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 5.71/5.93      inference('sup+', [status(thm)], ['7', '18'])).
% 5.71/5.93  thf('20', plain,
% 5.71/5.93      (((k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ 
% 5.71/5.93         sk_I)
% 5.71/5.93         != (k2_xboole_0 @ (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 5.71/5.93             (k3_enumset1 @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I)))),
% 5.71/5.93      inference('demod', [status(thm)], ['6', '19'])).
% 5.71/5.93  thf('21', plain,
% 5.71/5.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.71/5.93         ((k2_enumset1 @ X2 @ X1 @ X0 @ X3)
% 5.71/5.93           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 5.71/5.93      inference('demod', [status(thm)], ['14', '15'])).
% 5.71/5.93  thf('22', plain,
% 5.71/5.93      (![X44 : $i, X45 : $i, X46 : $i]:
% 5.71/5.93         ((k2_enumset1 @ X44 @ X44 @ X45 @ X46)
% 5.71/5.93           = (k1_enumset1 @ X44 @ X45 @ X46))),
% 5.71/5.93      inference('cnf', [status(esa)], [t71_enumset1])).
% 5.71/5.93  thf('23', plain,
% 5.71/5.93      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 5.71/5.93         ((k3_enumset1 @ X47 @ X47 @ X48 @ X49 @ X50)
% 5.71/5.93           = (k2_enumset1 @ X47 @ X48 @ X49 @ X50))),
% 5.71/5.93      inference('cnf', [status(esa)], [t72_enumset1])).
% 5.71/5.93  thf('24', plain,
% 5.71/5.93      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 5.71/5.93         ((k4_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37)
% 5.71/5.93           = (k2_xboole_0 @ (k1_tarski @ X32) @ 
% 5.71/5.93              (k3_enumset1 @ X33 @ X34 @ X35 @ X36 @ X37)))),
% 5.71/5.93      inference('cnf', [status(esa)], [t51_enumset1])).
% 5.71/5.93  thf('25', plain,
% 5.71/5.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 5.71/5.93         ((k4_enumset1 @ X4 @ X3 @ X3 @ X2 @ X1 @ X0)
% 5.71/5.93           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 5.71/5.93              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 5.71/5.93      inference('sup+', [status(thm)], ['23', '24'])).
% 5.71/5.93  thf('26', plain,
% 5.71/5.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.71/5.93         ((k4_enumset1 @ X3 @ X2 @ X2 @ X2 @ X1 @ X0)
% 5.71/5.93           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 5.71/5.93      inference('sup+', [status(thm)], ['22', '25'])).
% 5.71/5.93  thf('27', plain,
% 5.71/5.93      (![X44 : $i, X45 : $i, X46 : $i]:
% 5.71/5.93         ((k2_enumset1 @ X44 @ X44 @ X45 @ X46)
% 5.71/5.93           = (k1_enumset1 @ X44 @ X45 @ X46))),
% 5.71/5.93      inference('cnf', [status(esa)], [t71_enumset1])).
% 5.71/5.93  thf('28', plain,
% 5.71/5.93      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 5.71/5.93         ((k4_enumset1 @ X51 @ X51 @ X52 @ X53 @ X54 @ X55)
% 5.71/5.93           = (k3_enumset1 @ X51 @ X52 @ X53 @ X54 @ X55))),
% 5.71/5.93      inference('cnf', [status(esa)], [t73_enumset1])).
% 5.71/5.93  thf('29', plain,
% 5.71/5.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.71/5.93         ((k4_enumset1 @ X3 @ X2 @ X2 @ X2 @ X1 @ X0)
% 5.71/5.93           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 5.71/5.93      inference('sup+', [status(thm)], ['22', '25'])).
% 5.71/5.93  thf('30', plain,
% 5.71/5.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.71/5.93         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0)
% 5.71/5.93           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 5.71/5.93      inference('sup+', [status(thm)], ['28', '29'])).
% 5.71/5.93  thf('31', plain,
% 5.71/5.93      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 5.71/5.93         ((k3_enumset1 @ X47 @ X47 @ X48 @ X49 @ X50)
% 5.71/5.93           = (k2_enumset1 @ X47 @ X48 @ X49 @ X50))),
% 5.71/5.93      inference('cnf', [status(esa)], [t72_enumset1])).
% 5.71/5.93  thf('32', plain,
% 5.71/5.93      (![X44 : $i, X45 : $i, X46 : $i]:
% 5.71/5.93         ((k2_enumset1 @ X44 @ X44 @ X45 @ X46)
% 5.71/5.93           = (k1_enumset1 @ X44 @ X45 @ X46))),
% 5.71/5.93      inference('cnf', [status(esa)], [t71_enumset1])).
% 5.71/5.93  thf('33', plain,
% 5.71/5.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.71/5.93         ((k1_enumset1 @ X2 @ X1 @ X0)
% 5.71/5.93           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 5.71/5.93      inference('demod', [status(thm)], ['30', '31', '32'])).
% 5.71/5.93  thf('34', plain,
% 5.71/5.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 5.71/5.93         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4)
% 5.71/5.93           = (k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ 
% 5.71/5.93              (k2_xboole_0 @ (k1_tarski @ X0) @ X4)))),
% 5.71/5.93      inference('sup+', [status(thm)], ['16', '17'])).
% 5.71/5.93  thf('35', plain,
% 5.71/5.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 5.71/5.93         ((k2_xboole_0 @ (k2_enumset1 @ X5 @ X4 @ X3 @ X2) @ 
% 5.71/5.93           (k1_enumset1 @ X2 @ X1 @ X0))
% 5.71/5.93           = (k2_xboole_0 @ (k1_enumset1 @ X5 @ X4 @ X3) @ 
% 5.71/5.93              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 5.71/5.93      inference('sup+', [status(thm)], ['33', '34'])).
% 5.71/5.93  thf('36', plain,
% 5.71/5.93      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 5.71/5.93         ((k4_enumset1 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13)
% 5.71/5.93           = (k2_xboole_0 @ (k1_enumset1 @ X8 @ X9 @ X10) @ 
% 5.71/5.93              (k1_enumset1 @ X11 @ X12 @ X13)))),
% 5.71/5.93      inference('cnf', [status(esa)], [l62_enumset1])).
% 5.71/5.93  thf('37', plain,
% 5.71/5.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 5.71/5.93         ((k2_xboole_0 @ (k2_enumset1 @ X5 @ X4 @ X3 @ X2) @ 
% 5.71/5.93           (k1_enumset1 @ X2 @ X1 @ X0))
% 5.71/5.93           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 5.71/5.93      inference('demod', [status(thm)], ['35', '36'])).
% 5.71/5.93  thf('38', plain,
% 5.71/5.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 5.71/5.93         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 5.71/5.93           (k1_enumset1 @ X0 @ X4 @ X3))
% 5.71/5.93           = (k4_enumset1 @ X2 @ X2 @ X1 @ X0 @ X4 @ X3))),
% 5.71/5.93      inference('sup+', [status(thm)], ['27', '37'])).
% 5.71/5.93  thf('39', plain,
% 5.71/5.93      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 5.71/5.93         ((k4_enumset1 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13)
% 5.71/5.93           = (k2_xboole_0 @ (k1_enumset1 @ X8 @ X9 @ X10) @ 
% 5.71/5.93              (k1_enumset1 @ X11 @ X12 @ X13)))),
% 5.71/5.93      inference('cnf', [status(esa)], [l62_enumset1])).
% 5.71/5.93  thf('40', plain,
% 5.71/5.93      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 5.71/5.93         ((k4_enumset1 @ X51 @ X51 @ X52 @ X53 @ X54 @ X55)
% 5.71/5.93           = (k3_enumset1 @ X51 @ X52 @ X53 @ X54 @ X55))),
% 5.71/5.93      inference('cnf', [status(esa)], [t73_enumset1])).
% 5.71/5.93  thf('41', plain,
% 5.71/5.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 5.71/5.93         ((k4_enumset1 @ X2 @ X1 @ X0 @ X0 @ X4 @ X3)
% 5.71/5.93           = (k3_enumset1 @ X2 @ X1 @ X0 @ X4 @ X3))),
% 5.71/5.93      inference('demod', [status(thm)], ['38', '39', '40'])).
% 5.71/5.93  thf('42', plain,
% 5.71/5.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.71/5.93         ((k3_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0)
% 5.71/5.93           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 5.71/5.93      inference('demod', [status(thm)], ['26', '41'])).
% 5.71/5.93  thf('43', plain,
% 5.71/5.93      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 5.71/5.93         ((k4_enumset1 @ X51 @ X51 @ X52 @ X53 @ X54 @ X55)
% 5.71/5.93           = (k3_enumset1 @ X51 @ X52 @ X53 @ X54 @ X55))),
% 5.71/5.93      inference('cnf', [status(esa)], [t73_enumset1])).
% 5.71/5.93  thf('44', plain,
% 5.71/5.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 5.71/5.93         ((k4_enumset1 @ X2 @ X1 @ X0 @ X0 @ X4 @ X3)
% 5.71/5.93           = (k3_enumset1 @ X2 @ X1 @ X0 @ X4 @ X3))),
% 5.71/5.93      inference('demod', [status(thm)], ['38', '39', '40'])).
% 5.71/5.93  thf('45', plain,
% 5.71/5.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.71/5.93         ((k3_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0)
% 5.71/5.93           = (k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0))),
% 5.71/5.93      inference('sup+', [status(thm)], ['43', '44'])).
% 5.71/5.93  thf('46', plain,
% 5.71/5.93      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 5.71/5.93         ((k3_enumset1 @ X47 @ X47 @ X48 @ X49 @ X50)
% 5.71/5.93           = (k2_enumset1 @ X47 @ X48 @ X49 @ X50))),
% 5.71/5.93      inference('cnf', [status(esa)], [t72_enumset1])).
% 5.71/5.93  thf('47', plain,
% 5.71/5.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.71/5.93         ((k3_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0)
% 5.71/5.93           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 5.71/5.93      inference('demod', [status(thm)], ['45', '46'])).
% 5.71/5.93  thf('48', plain,
% 5.71/5.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.71/5.93         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 5.71/5.93           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 5.71/5.93      inference('demod', [status(thm)], ['42', '47'])).
% 5.71/5.93  thf('49', plain,
% 5.71/5.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.71/5.93         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 5.71/5.93           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 5.71/5.93      inference('cnf', [status(esa)], [t4_xboole_1])).
% 5.71/5.93  thf('50', plain,
% 5.71/5.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 5.71/5.93         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4)
% 5.71/5.93           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 5.71/5.93              (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X4)))),
% 5.71/5.93      inference('sup+', [status(thm)], ['48', '49'])).
% 5.71/5.93  thf('51', plain,
% 5.71/5.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 5.71/5.93         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 5.71/5.93           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 5.71/5.93              (k1_tarski @ X4)))),
% 5.71/5.93      inference('demod', [status(thm)], ['11', '12'])).
% 5.71/5.93  thf('52', plain,
% 5.71/5.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.71/5.93         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 5.71/5.93           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 5.71/5.93      inference('cnf', [status(esa)], [t4_xboole_1])).
% 5.71/5.93  thf('53', plain,
% 5.71/5.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 5.71/5.93         ((k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ X5)
% 5.71/5.93           = (k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ 
% 5.71/5.93              (k2_xboole_0 @ (k1_tarski @ X0) @ X5)))),
% 5.71/5.93      inference('sup+', [status(thm)], ['51', '52'])).
% 5.71/5.93  thf('54', plain,
% 5.71/5.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 5.71/5.93         X7 : $i, X8 : $i]:
% 5.71/5.93         ((k2_xboole_0 @ (k3_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4) @ 
% 5.71/5.93           (k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ X0))
% 5.71/5.93           = (k2_xboole_0 @ (k2_enumset1 @ X8 @ X7 @ X6 @ X5) @ 
% 5.71/5.93              (k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ X0)))),
% 5.71/5.93      inference('sup+', [status(thm)], ['50', '53'])).
% 5.71/5.93  thf('55', plain,
% 5.71/5.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 5.71/5.93         X7 : $i, X8 : $i]:
% 5.71/5.93         ((k2_xboole_0 @ (k3_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4) @ 
% 5.71/5.93           (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 5.71/5.93           = (k2_xboole_0 @ (k2_enumset1 @ X8 @ X7 @ X6 @ X5) @ 
% 5.71/5.93              (k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ 
% 5.71/5.93               (k1_tarski @ X0))))),
% 5.71/5.93      inference('sup+', [status(thm)], ['21', '54'])).
% 5.71/5.93  thf(t131_enumset1, axiom,
% 5.71/5.93    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 5.71/5.93     ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I ) =
% 5.71/5.93       ( k2_xboole_0 @
% 5.71/5.93         ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_enumset1 @ F @ G @ H @ I ) ) ))).
% 5.71/5.93  thf('56', plain,
% 5.71/5.93      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, 
% 5.71/5.93         X30 : $i, X31 : $i]:
% 5.71/5.93         ((k7_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31)
% 5.71/5.93           = (k2_xboole_0 @ (k3_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27) @ 
% 5.71/5.93              (k2_enumset1 @ X28 @ X29 @ X30 @ X31)))),
% 5.71/5.93      inference('cnf', [status(esa)], [t131_enumset1])).
% 5.71/5.93  thf('57', plain,
% 5.71/5.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 5.71/5.93         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 5.71/5.93           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 5.71/5.93              (k1_tarski @ X4)))),
% 5.71/5.93      inference('demod', [status(thm)], ['11', '12'])).
% 5.71/5.93  thf('58', plain,
% 5.71/5.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, 
% 5.71/5.93         X7 : $i, X8 : $i]:
% 5.71/5.93         ((k7_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 5.71/5.93           = (k2_xboole_0 @ (k2_enumset1 @ X8 @ X7 @ X6 @ X5) @ 
% 5.71/5.93              (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 5.71/5.93      inference('demod', [status(thm)], ['55', '56', '57'])).
% 5.71/5.93  thf('59', plain,
% 5.71/5.93      (((k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ 
% 5.71/5.93         sk_I)
% 5.71/5.93         != (k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ 
% 5.71/5.93             sk_H @ sk_I))),
% 5.71/5.93      inference('demod', [status(thm)], ['20', '58'])).
% 5.71/5.93  thf('60', plain, ($false), inference('simplify', [status(thm)], ['59'])).
% 5.71/5.93  
% 5.71/5.93  % SZS output end Refutation
% 5.71/5.93  
% 5.71/5.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

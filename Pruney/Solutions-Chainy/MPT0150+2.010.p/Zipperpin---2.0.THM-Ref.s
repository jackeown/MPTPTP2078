%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.00zFSvKHhX

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:17 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   69 (  90 expanded)
%              Number of leaves         :   26 (  41 expanded)
%              Depth                    :   13
%              Number of atoms          :  830 (1061 expanded)
%              Number of equality atoms :   51 (  72 expanded)
%              Maximal formula depth    :   19 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(t66_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_enumset1 @ F @ G @ H ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
        ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
        = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_enumset1 @ F @ G @ H ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_enumset1])).

thf('0',plain,(
    ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H )
 != ( k2_xboole_0 @ ( k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_enumset1 @ sk_F @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t59_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_enumset1 @ E @ F @ G ) ) ) )).

thf('1',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( k5_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X28 @ X29 @ X30 @ X31 ) @ ( k1_enumset1 @ X32 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t59_enumset1])).

thf(t47_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k2_enumset1 @ X11 @ X12 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

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
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X5 )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k2_enumset1 @ X11 @ X12 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_tarski @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('8',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_tarski @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ ( k2_tarski @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X6 @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','15'])).

thf(t51_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ) )).

thf('17',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k4_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_xboole_0 @ ( k1_tarski @ X15 ) @ ( k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t51_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t56_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k4_enumset1 @ B @ C @ D @ E @ F @ G ) ) ) )).

thf('20',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k5_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 )
      = ( k2_xboole_0 @ ( k1_tarski @ X21 ) @ ( k4_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t56_enumset1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X6 @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ ( k2_tarski @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) @ X4 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X4 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X4 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X7 @ X6 ) @ ( k2_xboole_0 @ ( k2_tarski @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','29'])).

thf('31',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k2_enumset1 @ X11 @ X12 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k4_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_xboole_0 @ ( k1_tarski @ X15 ) @ ( k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t51_enumset1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X7 @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','35'])).

thf(t63_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k4_enumset1 @ C @ D @ E @ F @ G @ H ) ) ) )).

thf('37',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k6_enumset1 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 )
      = ( k2_xboole_0 @ ( k2_tarski @ X35 @ X36 ) @ ( k4_enumset1 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t63_enumset1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','38'])).

thf('40',plain,(
    ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H )
 != ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['0','39'])).

thf('41',plain,(
    $false ),
    inference(simplify,[status(thm)],['40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.00zFSvKHhX
% 0.14/0.33  % Computer   : n021.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 11:05:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.34/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.34/0.52  % Solved by: fo/fo7.sh
% 0.34/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.52  % done 63 iterations in 0.064s
% 0.34/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.34/0.52  % SZS output start Refutation
% 0.34/0.52  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.34/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.52  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.34/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.34/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.34/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.34/0.52  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.34/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.34/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.34/0.52  thf(sk_E_type, type, sk_E: $i).
% 0.34/0.52  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.34/0.52  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.34/0.52                                           $i > $i).
% 0.34/0.52  thf(sk_H_type, type, sk_H: $i).
% 0.34/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.34/0.52  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.34/0.52  thf(sk_G_type, type, sk_G: $i).
% 0.34/0.52  thf(sk_F_type, type, sk_F: $i).
% 0.34/0.52  thf(t66_enumset1, conjecture,
% 0.34/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.34/0.52     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.34/0.52       ( k2_xboole_0 @
% 0.34/0.52         ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_enumset1 @ F @ G @ H ) ) ))).
% 0.34/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.52    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.34/0.52        ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.34/0.52          ( k2_xboole_0 @
% 0.34/0.52            ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_enumset1 @ F @ G @ H ) ) ) )),
% 0.34/0.52    inference('cnf.neg', [status(esa)], [t66_enumset1])).
% 0.34/0.52  thf('0', plain,
% 0.34/0.52      (((k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.34/0.52         != (k2_xboole_0 @ (k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.34/0.52             (k1_enumset1 @ sk_F @ sk_G @ sk_H)))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf(t59_enumset1, axiom,
% 0.34/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.34/0.52     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.34/0.52       ( k2_xboole_0 @
% 0.34/0.52         ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_enumset1 @ E @ F @ G ) ) ))).
% 0.34/0.52  thf('1', plain,
% 0.34/0.52      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.34/0.52         ((k5_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34)
% 0.34/0.52           = (k2_xboole_0 @ (k2_enumset1 @ X28 @ X29 @ X30 @ X31) @ 
% 0.34/0.52              (k1_enumset1 @ X32 @ X33 @ X34)))),
% 0.34/0.52      inference('cnf', [status(esa)], [t59_enumset1])).
% 0.34/0.52  thf(t47_enumset1, axiom,
% 0.34/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.34/0.52     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.34/0.52       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ))).
% 0.34/0.52  thf('2', plain,
% 0.34/0.52      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.34/0.52         ((k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14)
% 0.34/0.52           = (k2_xboole_0 @ (k1_tarski @ X10) @ 
% 0.34/0.52              (k2_enumset1 @ X11 @ X12 @ X13 @ X14)))),
% 0.34/0.52      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.34/0.52  thf(t4_xboole_1, axiom,
% 0.34/0.52    (![A:$i,B:$i,C:$i]:
% 0.34/0.52     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.34/0.52       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.34/0.52  thf('3', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.52         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.34/0.52           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.34/0.52      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.34/0.52  thf('4', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.34/0.52         ((k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ X5)
% 0.34/0.52           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 0.34/0.52              (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X5)))),
% 0.34/0.52      inference('sup+', [status(thm)], ['2', '3'])).
% 0.34/0.52  thf('5', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.34/0.52         ((k2_xboole_0 @ (k3_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3) @ 
% 0.34/0.52           (k1_enumset1 @ X2 @ X1 @ X0))
% 0.34/0.52           = (k2_xboole_0 @ (k1_tarski @ X7) @ 
% 0.34/0.52              (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.34/0.52      inference('sup+', [status(thm)], ['1', '4'])).
% 0.34/0.52  thf('6', plain,
% 0.34/0.52      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.34/0.52         ((k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14)
% 0.34/0.52           = (k2_xboole_0 @ (k1_tarski @ X10) @ 
% 0.34/0.52              (k2_enumset1 @ X11 @ X12 @ X13 @ X14)))),
% 0.34/0.52      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.34/0.52  thf(t41_enumset1, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( k2_tarski @ A @ B ) =
% 0.34/0.52       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.34/0.52  thf('7', plain,
% 0.34/0.52      (![X5 : $i, X6 : $i]:
% 0.34/0.52         ((k2_tarski @ X5 @ X6)
% 0.34/0.52           = (k2_xboole_0 @ (k1_tarski @ X5) @ (k1_tarski @ X6)))),
% 0.34/0.52      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.34/0.52  thf('8', plain,
% 0.34/0.52      (![X5 : $i, X6 : $i]:
% 0.34/0.52         ((k2_tarski @ X5 @ X6)
% 0.34/0.52           = (k2_xboole_0 @ (k1_tarski @ X5) @ (k1_tarski @ X6)))),
% 0.34/0.52      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.34/0.52  thf('9', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.52         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.34/0.52           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.34/0.52      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.34/0.52  thf('10', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.52         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.34/0.52           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.34/0.52              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.34/0.52      inference('sup+', [status(thm)], ['8', '9'])).
% 0.34/0.52  thf('11', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.52         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.34/0.52           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.34/0.52      inference('sup+', [status(thm)], ['7', '10'])).
% 0.34/0.52  thf(t42_enumset1, axiom,
% 0.34/0.52    (![A:$i,B:$i,C:$i]:
% 0.34/0.52     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.34/0.52       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.34/0.52  thf('12', plain,
% 0.34/0.52      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.34/0.52         ((k1_enumset1 @ X7 @ X8 @ X9)
% 0.34/0.52           = (k2_xboole_0 @ (k1_tarski @ X7) @ (k2_tarski @ X8 @ X9)))),
% 0.34/0.52      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.34/0.52  thf('13', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.52         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.34/0.52           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.34/0.52      inference('demod', [status(thm)], ['11', '12'])).
% 0.34/0.52  thf('14', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.52         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.34/0.52           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.34/0.52      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.34/0.52  thf('15', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.34/0.52         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.34/0.52           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ 
% 0.34/0.52              (k2_xboole_0 @ (k1_tarski @ X0) @ X3)))),
% 0.34/0.52      inference('sup+', [status(thm)], ['13', '14'])).
% 0.34/0.52  thf('16', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.34/0.52         ((k2_xboole_0 @ (k1_enumset1 @ X6 @ X5 @ X4) @ 
% 0.34/0.52           (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.34/0.52           = (k2_xboole_0 @ (k2_tarski @ X6 @ X5) @ 
% 0.34/0.52              (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.34/0.52      inference('sup+', [status(thm)], ['6', '15'])).
% 0.34/0.52  thf(t51_enumset1, axiom,
% 0.34/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.34/0.52     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.34/0.52       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ))).
% 0.34/0.52  thf('17', plain,
% 0.34/0.52      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.34/0.52         ((k4_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20)
% 0.34/0.52           = (k2_xboole_0 @ (k1_tarski @ X15) @ 
% 0.34/0.52              (k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20)))),
% 0.34/0.52      inference('cnf', [status(esa)], [t51_enumset1])).
% 0.34/0.52  thf('18', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.52         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.34/0.52           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.34/0.52              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.34/0.52      inference('sup+', [status(thm)], ['8', '9'])).
% 0.34/0.52  thf('19', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.34/0.52         ((k2_xboole_0 @ (k2_tarski @ X6 @ X5) @ 
% 0.34/0.52           (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.34/0.52           = (k2_xboole_0 @ (k1_tarski @ X6) @ 
% 0.34/0.52              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.34/0.52      inference('sup+', [status(thm)], ['17', '18'])).
% 0.34/0.52  thf(t56_enumset1, axiom,
% 0.34/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.34/0.52     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.34/0.52       ( k2_xboole_0 @
% 0.34/0.52         ( k1_tarski @ A ) @ ( k4_enumset1 @ B @ C @ D @ E @ F @ G ) ) ))).
% 0.34/0.52  thf('20', plain,
% 0.34/0.52      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.34/0.52         ((k5_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27)
% 0.34/0.52           = (k2_xboole_0 @ (k1_tarski @ X21) @ 
% 0.34/0.52              (k4_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27)))),
% 0.34/0.52      inference('cnf', [status(esa)], [t56_enumset1])).
% 0.34/0.52  thf('21', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.34/0.52         ((k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.34/0.52           = (k2_xboole_0 @ (k2_tarski @ X6 @ X5) @ 
% 0.34/0.52              (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.34/0.52      inference('sup+', [status(thm)], ['19', '20'])).
% 0.34/0.52  thf('22', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.34/0.52         ((k2_xboole_0 @ (k1_enumset1 @ X6 @ X5 @ X4) @ 
% 0.34/0.52           (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.34/0.52           = (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.34/0.52      inference('demod', [status(thm)], ['16', '21'])).
% 0.34/0.52  thf('23', plain,
% 0.34/0.52      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.34/0.52         ((k1_enumset1 @ X7 @ X8 @ X9)
% 0.34/0.52           = (k2_xboole_0 @ (k1_tarski @ X7) @ (k2_tarski @ X8 @ X9)))),
% 0.34/0.52      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.34/0.52  thf('24', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.52         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.34/0.52           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.34/0.52              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.34/0.52      inference('sup+', [status(thm)], ['8', '9'])).
% 0.34/0.52  thf('25', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.34/0.52         ((k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0))
% 0.34/0.52           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.34/0.52      inference('sup+', [status(thm)], ['23', '24'])).
% 0.34/0.52  thf('26', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.52         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.34/0.52           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.34/0.52      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.34/0.52  thf('27', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.34/0.52         ((k2_xboole_0 @ 
% 0.34/0.52           (k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0)) @ X4)
% 0.34/0.52           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 0.34/0.52              (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X4)))),
% 0.34/0.52      inference('sup+', [status(thm)], ['25', '26'])).
% 0.34/0.52  thf('28', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.52         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.34/0.52           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.34/0.52      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.34/0.52  thf('29', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.34/0.52         ((k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ 
% 0.34/0.52           (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X4))
% 0.34/0.52           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 0.34/0.52              (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X4)))),
% 0.34/0.52      inference('demod', [status(thm)], ['27', '28'])).
% 0.34/0.52  thf('30', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.34/0.52         ((k2_xboole_0 @ (k2_tarski @ X7 @ X6) @ 
% 0.34/0.52           (k2_xboole_0 @ (k2_tarski @ X5 @ X4) @ 
% 0.34/0.52            (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))
% 0.34/0.52           = (k2_xboole_0 @ (k1_tarski @ X7) @ 
% 0.34/0.52              (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.34/0.52      inference('sup+', [status(thm)], ['22', '29'])).
% 0.34/0.52  thf('31', plain,
% 0.34/0.52      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.34/0.52         ((k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14)
% 0.34/0.52           = (k2_xboole_0 @ (k1_tarski @ X10) @ 
% 0.34/0.52              (k2_enumset1 @ X11 @ X12 @ X13 @ X14)))),
% 0.34/0.52      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.34/0.52  thf('32', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.52         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.34/0.52           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.34/0.52              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.34/0.52      inference('sup+', [status(thm)], ['8', '9'])).
% 0.34/0.52  thf('33', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.34/0.52         ((k2_xboole_0 @ (k2_tarski @ X5 @ X4) @ 
% 0.34/0.52           (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.34/0.52           = (k2_xboole_0 @ (k1_tarski @ X5) @ 
% 0.34/0.52              (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.34/0.52      inference('sup+', [status(thm)], ['31', '32'])).
% 0.34/0.52  thf('34', plain,
% 0.34/0.52      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.34/0.52         ((k4_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20)
% 0.34/0.52           = (k2_xboole_0 @ (k1_tarski @ X15) @ 
% 0.34/0.52              (k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20)))),
% 0.34/0.52      inference('cnf', [status(esa)], [t51_enumset1])).
% 0.34/0.52  thf('35', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.34/0.52         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.34/0.52           = (k2_xboole_0 @ (k2_tarski @ X5 @ X4) @ 
% 0.34/0.52              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 0.34/0.52      inference('sup+', [status(thm)], ['33', '34'])).
% 0.34/0.52  thf('36', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.34/0.52         ((k2_xboole_0 @ (k2_tarski @ X7 @ X6) @ 
% 0.34/0.52           (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.34/0.52           = (k2_xboole_0 @ (k1_tarski @ X7) @ 
% 0.34/0.52              (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.34/0.52      inference('demod', [status(thm)], ['30', '35'])).
% 0.34/0.52  thf(t63_enumset1, axiom,
% 0.34/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.34/0.52     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.34/0.52       ( k2_xboole_0 @
% 0.34/0.52         ( k2_tarski @ A @ B ) @ ( k4_enumset1 @ C @ D @ E @ F @ G @ H ) ) ))).
% 0.34/0.52  thf('37', plain,
% 0.34/0.52      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, 
% 0.34/0.52         X42 : $i]:
% 0.34/0.52         ((k6_enumset1 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42)
% 0.34/0.52           = (k2_xboole_0 @ (k2_tarski @ X35 @ X36) @ 
% 0.34/0.52              (k4_enumset1 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42)))),
% 0.34/0.52      inference('cnf', [status(esa)], [t63_enumset1])).
% 0.34/0.52  thf('38', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.34/0.52         ((k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.34/0.52           = (k2_xboole_0 @ (k1_tarski @ X7) @ 
% 0.34/0.52              (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.34/0.52      inference('demod', [status(thm)], ['36', '37'])).
% 0.34/0.52  thf('39', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.34/0.52         ((k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.34/0.52           = (k2_xboole_0 @ (k3_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3) @ 
% 0.34/0.52              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.34/0.52      inference('sup+', [status(thm)], ['5', '38'])).
% 0.34/0.52  thf('40', plain,
% 0.34/0.52      (((k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.34/0.52         != (k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ 
% 0.34/0.52             sk_H))),
% 0.34/0.52      inference('demod', [status(thm)], ['0', '39'])).
% 0.34/0.52  thf('41', plain, ($false), inference('simplify', [status(thm)], ['40'])).
% 0.34/0.52  
% 0.34/0.52  % SZS output end Refutation
% 0.34/0.52  
% 0.34/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

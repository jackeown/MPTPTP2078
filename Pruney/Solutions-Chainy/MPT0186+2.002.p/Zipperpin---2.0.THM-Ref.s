%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cwcVGJN58c

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:03 EST 2020

% Result     : Theorem 2.66s
% Output     : Refutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 316 expanded)
%              Number of leaves         :   24 ( 115 expanded)
%              Depth                    :   19
%              Number of atoms          : 1027 (3705 expanded)
%              Number of equality atoms :   79 ( 302 expanded)
%              Maximal formula depth    :   18 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t104_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ C @ B @ D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k2_enumset1 @ A @ B @ C @ D )
        = ( k2_enumset1 @ A @ C @ B @ D ) ) ),
    inference('cnf.neg',[status(esa)],[t104_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_C @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('2',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k4_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27 @ X28 )
      = ( k3_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('3',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k3_enumset1 @ X20 @ X20 @ X21 @ X22 @ X23 )
      = ( k2_enumset1 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k3_enumset1 @ X20 @ X20 @ X21 @ X22 @ X23 )
      = ( k2_enumset1 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k2_enumset1 @ X17 @ X17 @ X18 @ X19 )
      = ( k1_enumset1 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_enumset1 @ X15 @ X15 @ X16 )
      = ( k2_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t66_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_enumset1 @ F @ G @ H ) ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k6_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 ) @ ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t66_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k6_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 @ X4 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('12',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( k6_enumset1 @ X35 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 )
      = ( k5_enumset1 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('13',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( k5_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 )
      = ( k4_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X2 @ X1 @ X0 @ X4 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X4 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X2 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('19',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_enumset1 @ X15 @ X15 @ X16 )
      = ( k2_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('20',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X3 @ X4 ) @ ( k1_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k2_enumset1 @ X17 @ X17 @ X18 @ X19 )
      = ( k1_enumset1 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X2 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k6_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 ) @ ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t66_enumset1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X1 @ X2 @ X0 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 @ X4 @ X5 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_enumset1 @ X5 @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['17','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X2 @ X1 @ X0 @ X4 @ X5 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_enumset1 @ X5 @ X4 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( k6_enumset1 @ X35 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 )
      = ( k5_enumset1 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('34',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k6_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 ) @ ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t66_enumset1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_enumset1 @ X5 @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( k5_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 )
      = ( k4_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X1 @ X2 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','38'])).

thf('40',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k4_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27 @ X28 )
      = ( k3_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_enumset1 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_enumset1 @ X1 @ X1 @ X1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X2 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('45',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X3 @ X4 ) @ ( k1_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X2 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X3 @ X4 ) @ ( k1_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k3_enumset1 @ X20 @ X20 @ X21 @ X22 @ X23 )
      = ( k2_enumset1 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X3 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k4_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27 @ X28 )
      = ( k3_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X2 @ X2 @ X2 @ X3 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X1 @ X2 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','52'])).

thf('54',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_enumset1 @ X15 @ X15 @ X16 )
      = ( k2_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('55',plain,(
    ! [X14: $i] :
      ( ( k2_tarski @ X14 @ X14 )
      = ( k1_tarski @ X14 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X2 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','53','54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X2 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','53','54','55'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X3 @ X4 ) @ ( k1_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X2 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X3 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X1 @ X2 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','65'])).

thf('67',plain,(
    $false ),
    inference(simplify,[status(thm)],['66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cwcVGJN58c
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:03:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.66/2.90  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.66/2.90  % Solved by: fo/fo7.sh
% 2.66/2.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.66/2.90  % done 4015 iterations in 2.436s
% 2.66/2.90  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.66/2.90  % SZS output start Refutation
% 2.66/2.90  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 2.66/2.90  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.66/2.90  thf(sk_D_type, type, sk_D: $i).
% 2.66/2.90  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 2.66/2.90                                           $i > $i).
% 2.66/2.90  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 2.66/2.90  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 2.66/2.90  thf(sk_A_type, type, sk_A: $i).
% 2.66/2.90  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 2.66/2.90  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 2.66/2.90  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.66/2.90  thf(sk_B_type, type, sk_B: $i).
% 2.66/2.90  thf(sk_C_type, type, sk_C: $i).
% 2.66/2.90  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.66/2.90  thf(t104_enumset1, conjecture,
% 2.66/2.90    (![A:$i,B:$i,C:$i,D:$i]:
% 2.66/2.90     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ B @ D ) ))).
% 2.66/2.90  thf(zf_stmt_0, negated_conjecture,
% 2.66/2.90    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 2.66/2.90        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ B @ D ) ) )),
% 2.66/2.90    inference('cnf.neg', [status(esa)], [t104_enumset1])).
% 2.66/2.90  thf('0', plain,
% 2.66/2.90      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 2.66/2.90         != (k2_enumset1 @ sk_A @ sk_C @ sk_B @ sk_D))),
% 2.66/2.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.90  thf(commutativity_k2_tarski, axiom,
% 2.66/2.90    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 2.66/2.90  thf('1', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 2.66/2.90      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 2.66/2.90  thf(t73_enumset1, axiom,
% 2.66/2.90    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 2.66/2.90     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 2.66/2.90       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 2.66/2.90  thf('2', plain,
% 2.66/2.90      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 2.66/2.90         ((k4_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27 @ X28)
% 2.66/2.90           = (k3_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28))),
% 2.66/2.90      inference('cnf', [status(esa)], [t73_enumset1])).
% 2.66/2.90  thf(t72_enumset1, axiom,
% 2.66/2.90    (![A:$i,B:$i,C:$i,D:$i]:
% 2.66/2.90     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 2.66/2.90  thf('3', plain,
% 2.66/2.90      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 2.66/2.90         ((k3_enumset1 @ X20 @ X20 @ X21 @ X22 @ X23)
% 2.66/2.90           = (k2_enumset1 @ X20 @ X21 @ X22 @ X23))),
% 2.66/2.90      inference('cnf', [status(esa)], [t72_enumset1])).
% 2.66/2.90  thf('4', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.66/2.90         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 2.66/2.90           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 2.66/2.90      inference('sup+', [status(thm)], ['2', '3'])).
% 2.66/2.90  thf('5', plain,
% 2.66/2.90      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 2.66/2.90         ((k3_enumset1 @ X20 @ X20 @ X21 @ X22 @ X23)
% 2.66/2.90           = (k2_enumset1 @ X20 @ X21 @ X22 @ X23))),
% 2.66/2.90      inference('cnf', [status(esa)], [t72_enumset1])).
% 2.66/2.90  thf(t71_enumset1, axiom,
% 2.66/2.90    (![A:$i,B:$i,C:$i]:
% 2.66/2.90     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 2.66/2.90  thf('6', plain,
% 2.66/2.90      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.66/2.90         ((k2_enumset1 @ X17 @ X17 @ X18 @ X19)
% 2.66/2.90           = (k1_enumset1 @ X17 @ X18 @ X19))),
% 2.66/2.90      inference('cnf', [status(esa)], [t71_enumset1])).
% 2.66/2.90  thf('7', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.90         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 2.66/2.90      inference('sup+', [status(thm)], ['5', '6'])).
% 2.66/2.90  thf(t70_enumset1, axiom,
% 2.66/2.90    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 2.66/2.90  thf('8', plain,
% 2.66/2.90      (![X15 : $i, X16 : $i]:
% 2.66/2.90         ((k1_enumset1 @ X15 @ X15 @ X16) = (k2_tarski @ X15 @ X16))),
% 2.66/2.90      inference('cnf', [status(esa)], [t70_enumset1])).
% 2.66/2.90  thf(t66_enumset1, axiom,
% 2.66/2.90    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 2.66/2.90     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 2.66/2.90       ( k2_xboole_0 @
% 2.66/2.90         ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_enumset1 @ F @ G @ H ) ) ))).
% 2.66/2.90  thf('9', plain,
% 2.66/2.90      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, 
% 2.66/2.90         X13 : $i]:
% 2.66/2.90         ((k6_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13)
% 2.66/2.90           = (k2_xboole_0 @ (k3_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10) @ 
% 2.66/2.90              (k1_enumset1 @ X11 @ X12 @ X13)))),
% 2.66/2.90      inference('cnf', [status(esa)], [t66_enumset1])).
% 2.66/2.90  thf('10', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 2.66/2.90         ((k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X1 @ X0)
% 2.66/2.90           = (k2_xboole_0 @ (k3_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2) @ 
% 2.66/2.90              (k2_tarski @ X1 @ X0)))),
% 2.66/2.90      inference('sup+', [status(thm)], ['8', '9'])).
% 2.66/2.90  thf('11', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 2.66/2.90         ((k6_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 @ X4 @ X4 @ X3)
% 2.66/2.90           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 2.66/2.90              (k2_tarski @ X4 @ X3)))),
% 2.66/2.90      inference('sup+', [status(thm)], ['7', '10'])).
% 2.66/2.90  thf(t75_enumset1, axiom,
% 2.66/2.90    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 2.66/2.90     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 2.66/2.90       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 2.66/2.90  thf('12', plain,
% 2.66/2.90      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 2.66/2.90         ((k6_enumset1 @ X35 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41)
% 2.66/2.90           = (k5_enumset1 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41))),
% 2.66/2.90      inference('cnf', [status(esa)], [t75_enumset1])).
% 2.66/2.90  thf(t74_enumset1, axiom,
% 2.66/2.90    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.66/2.90     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 2.66/2.90       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 2.66/2.90  thf('13', plain,
% 2.66/2.90      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 2.66/2.90         ((k5_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34)
% 2.66/2.90           = (k4_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34))),
% 2.66/2.90      inference('cnf', [status(esa)], [t74_enumset1])).
% 2.66/2.90  thf('14', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 2.66/2.90         ((k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 2.66/2.90           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 2.66/2.90      inference('sup+', [status(thm)], ['12', '13'])).
% 2.66/2.90  thf('15', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 2.66/2.90         ((k4_enumset1 @ X2 @ X1 @ X0 @ X4 @ X4 @ X3)
% 2.66/2.90           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 2.66/2.90              (k2_tarski @ X4 @ X3)))),
% 2.66/2.90      inference('demod', [status(thm)], ['11', '14'])).
% 2.66/2.90  thf('16', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.90         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0)
% 2.66/2.90           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X2 @ X2) @ 
% 2.66/2.90              (k2_tarski @ X1 @ X0)))),
% 2.66/2.90      inference('sup+', [status(thm)], ['4', '15'])).
% 2.66/2.90  thf('17', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.90         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 2.66/2.90      inference('sup+', [status(thm)], ['5', '6'])).
% 2.66/2.90  thf('18', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 2.66/2.90      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 2.66/2.90  thf('19', plain,
% 2.66/2.90      (![X15 : $i, X16 : $i]:
% 2.66/2.90         ((k1_enumset1 @ X15 @ X15 @ X16) = (k2_tarski @ X15 @ X16))),
% 2.66/2.90      inference('cnf', [status(esa)], [t70_enumset1])).
% 2.66/2.90  thf(t46_enumset1, axiom,
% 2.66/2.90    (![A:$i,B:$i,C:$i,D:$i]:
% 2.66/2.90     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 2.66/2.90       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 2.66/2.90  thf('20', plain,
% 2.66/2.90      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 2.66/2.90         ((k2_enumset1 @ X2 @ X3 @ X4 @ X5)
% 2.66/2.90           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X3 @ X4) @ (k1_tarski @ X5)))),
% 2.66/2.90      inference('cnf', [status(esa)], [t46_enumset1])).
% 2.66/2.90  thf('21', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.90         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 2.66/2.90           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 2.66/2.90      inference('sup+', [status(thm)], ['19', '20'])).
% 2.66/2.90  thf('22', plain,
% 2.66/2.90      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.66/2.90         ((k2_enumset1 @ X17 @ X17 @ X18 @ X19)
% 2.66/2.90           = (k1_enumset1 @ X17 @ X18 @ X19))),
% 2.66/2.90      inference('cnf', [status(esa)], [t71_enumset1])).
% 2.66/2.90  thf('23', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.90         ((k1_enumset1 @ X1 @ X0 @ X2)
% 2.66/2.90           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 2.66/2.90      inference('demod', [status(thm)], ['21', '22'])).
% 2.66/2.90  thf('24', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.90         ((k1_enumset1 @ X0 @ X1 @ X2)
% 2.66/2.90           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 2.66/2.90      inference('sup+', [status(thm)], ['18', '23'])).
% 2.66/2.90  thf('25', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.90         ((k1_enumset1 @ X1 @ X0 @ X2)
% 2.66/2.90           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 2.66/2.90      inference('demod', [status(thm)], ['21', '22'])).
% 2.66/2.90  thf('26', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.90         ((k1_enumset1 @ X1 @ X2 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 2.66/2.90      inference('sup+', [status(thm)], ['24', '25'])).
% 2.66/2.90  thf('27', plain,
% 2.66/2.90      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, 
% 2.66/2.90         X13 : $i]:
% 2.66/2.90         ((k6_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13)
% 2.66/2.90           = (k2_xboole_0 @ (k3_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10) @ 
% 2.66/2.90              (k1_enumset1 @ X11 @ X12 @ X13)))),
% 2.66/2.90      inference('cnf', [status(esa)], [t66_enumset1])).
% 2.66/2.90  thf('28', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 2.66/2.90         ((k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X1 @ X2 @ X0)
% 2.66/2.90           = (k2_xboole_0 @ (k3_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3) @ 
% 2.66/2.90              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 2.66/2.90      inference('sup+', [status(thm)], ['26', '27'])).
% 2.66/2.90  thf('29', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 2.66/2.90         ((k6_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 @ X4 @ X5 @ X3)
% 2.66/2.90           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 2.66/2.90              (k1_enumset1 @ X5 @ X4 @ X3)))),
% 2.66/2.90      inference('sup+', [status(thm)], ['17', '28'])).
% 2.66/2.90  thf('30', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 2.66/2.90         ((k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 2.66/2.90           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 2.66/2.90      inference('sup+', [status(thm)], ['12', '13'])).
% 2.66/2.90  thf('31', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 2.66/2.90         ((k4_enumset1 @ X2 @ X1 @ X0 @ X4 @ X5 @ X3)
% 2.66/2.90           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 2.66/2.90              (k1_enumset1 @ X5 @ X4 @ X3)))),
% 2.66/2.90      inference('demod', [status(thm)], ['29', '30'])).
% 2.66/2.90  thf('32', plain,
% 2.66/2.90      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 2.66/2.90         ((k6_enumset1 @ X35 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41)
% 2.66/2.90           = (k5_enumset1 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41))),
% 2.66/2.90      inference('cnf', [status(esa)], [t75_enumset1])).
% 2.66/2.90  thf('33', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.90         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 2.66/2.90      inference('sup+', [status(thm)], ['5', '6'])).
% 2.66/2.90  thf('34', plain,
% 2.66/2.90      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, 
% 2.66/2.90         X13 : $i]:
% 2.66/2.90         ((k6_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13)
% 2.66/2.90           = (k2_xboole_0 @ (k3_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10) @ 
% 2.66/2.90              (k1_enumset1 @ X11 @ X12 @ X13)))),
% 2.66/2.90      inference('cnf', [status(esa)], [t66_enumset1])).
% 2.66/2.90  thf('35', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 2.66/2.90         ((k6_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3)
% 2.66/2.90           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 2.66/2.90              (k1_enumset1 @ X5 @ X4 @ X3)))),
% 2.66/2.90      inference('sup+', [status(thm)], ['33', '34'])).
% 2.66/2.90  thf('36', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 2.66/2.90         ((k5_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 2.66/2.90           = (k2_xboole_0 @ (k1_enumset1 @ X5 @ X4 @ X3) @ 
% 2.66/2.90              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 2.66/2.90      inference('sup+', [status(thm)], ['32', '35'])).
% 2.66/2.90  thf('37', plain,
% 2.66/2.90      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 2.66/2.90         ((k5_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34)
% 2.66/2.90           = (k4_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34))),
% 2.66/2.90      inference('cnf', [status(esa)], [t74_enumset1])).
% 2.66/2.90  thf('38', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 2.66/2.90         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 2.66/2.90           = (k2_xboole_0 @ (k1_enumset1 @ X5 @ X4 @ X3) @ 
% 2.66/2.90              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 2.66/2.90      inference('demod', [status(thm)], ['36', '37'])).
% 2.66/2.90  thf('39', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 2.66/2.90         ((k4_enumset1 @ X5 @ X4 @ X3 @ X1 @ X2 @ X0)
% 2.66/2.90           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 2.66/2.90      inference('sup+', [status(thm)], ['31', '38'])).
% 2.66/2.90  thf('40', plain,
% 2.66/2.90      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 2.66/2.90         ((k4_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27 @ X28)
% 2.66/2.90           = (k3_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28))),
% 2.66/2.90      inference('cnf', [status(esa)], [t73_enumset1])).
% 2.66/2.90  thf('41', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.90         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 2.66/2.90      inference('sup+', [status(thm)], ['5', '6'])).
% 2.66/2.90  thf('42', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.90         ((k4_enumset1 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0)
% 2.66/2.90           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 2.66/2.90      inference('sup+', [status(thm)], ['40', '41'])).
% 2.66/2.90  thf('43', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.90         ((k4_enumset1 @ X1 @ X1 @ X1 @ X2 @ X1 @ X0)
% 2.66/2.90           = (k1_enumset1 @ X1 @ X2 @ X0))),
% 2.66/2.90      inference('sup+', [status(thm)], ['39', '42'])).
% 2.66/2.90  thf('44', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.90         ((k1_enumset1 @ X1 @ X2 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 2.66/2.90      inference('sup+', [status(thm)], ['24', '25'])).
% 2.66/2.90  thf('45', plain,
% 2.66/2.90      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 2.66/2.90         ((k2_enumset1 @ X2 @ X3 @ X4 @ X5)
% 2.66/2.90           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X3 @ X4) @ (k1_tarski @ X5)))),
% 2.66/2.90      inference('cnf', [status(esa)], [t46_enumset1])).
% 2.66/2.90  thf('46', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.66/2.90         ((k2_enumset1 @ X1 @ X2 @ X0 @ X3)
% 2.66/2.90           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 2.66/2.90      inference('sup+', [status(thm)], ['44', '45'])).
% 2.66/2.90  thf('47', plain,
% 2.66/2.90      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 2.66/2.90         ((k2_enumset1 @ X2 @ X3 @ X4 @ X5)
% 2.66/2.90           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X3 @ X4) @ (k1_tarski @ X5)))),
% 2.66/2.90      inference('cnf', [status(esa)], [t46_enumset1])).
% 2.66/2.90  thf('48', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.66/2.90         ((k2_enumset1 @ X2 @ X3 @ X1 @ X0) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 2.66/2.90      inference('sup+', [status(thm)], ['46', '47'])).
% 2.66/2.90  thf('49', plain,
% 2.66/2.90      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 2.66/2.90         ((k3_enumset1 @ X20 @ X20 @ X21 @ X22 @ X23)
% 2.66/2.90           = (k2_enumset1 @ X20 @ X21 @ X22 @ X23))),
% 2.66/2.90      inference('cnf', [status(esa)], [t72_enumset1])).
% 2.66/2.90  thf('50', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.66/2.90         ((k3_enumset1 @ X2 @ X2 @ X3 @ X1 @ X0)
% 2.66/2.90           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 2.66/2.90      inference('sup+', [status(thm)], ['48', '49'])).
% 2.66/2.90  thf('51', plain,
% 2.66/2.90      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 2.66/2.90         ((k4_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27 @ X28)
% 2.66/2.90           = (k3_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28))),
% 2.66/2.90      inference('cnf', [status(esa)], [t73_enumset1])).
% 2.66/2.90  thf('52', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.66/2.90         ((k4_enumset1 @ X2 @ X2 @ X2 @ X3 @ X1 @ X0)
% 2.66/2.90           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 2.66/2.90      inference('sup+', [status(thm)], ['50', '51'])).
% 2.66/2.90  thf('53', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.90         ((k1_enumset1 @ X2 @ X1 @ X0) = (k2_enumset1 @ X1 @ X2 @ X2 @ X0))),
% 2.66/2.90      inference('sup+', [status(thm)], ['43', '52'])).
% 2.66/2.90  thf('54', plain,
% 2.66/2.90      (![X15 : $i, X16 : $i]:
% 2.66/2.90         ((k1_enumset1 @ X15 @ X15 @ X16) = (k2_tarski @ X15 @ X16))),
% 2.66/2.90      inference('cnf', [status(esa)], [t70_enumset1])).
% 2.66/2.90  thf(t69_enumset1, axiom,
% 2.66/2.90    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 2.66/2.90  thf('55', plain,
% 2.66/2.90      (![X14 : $i]: ((k2_tarski @ X14 @ X14) = (k1_tarski @ X14))),
% 2.66/2.90      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.66/2.90  thf('56', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.90         ((k1_enumset1 @ X1 @ X2 @ X0)
% 2.66/2.90           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 2.66/2.90      inference('demod', [status(thm)], ['16', '53', '54', '55'])).
% 2.66/2.90  thf('57', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.90         ((k1_enumset1 @ X0 @ X2 @ X1)
% 2.66/2.90           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 2.66/2.90      inference('sup+', [status(thm)], ['1', '56'])).
% 2.66/2.90  thf('58', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.90         ((k1_enumset1 @ X1 @ X2 @ X0)
% 2.66/2.90           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 2.66/2.90      inference('demod', [status(thm)], ['16', '53', '54', '55'])).
% 2.66/2.90  thf('59', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.90         ((k1_enumset1 @ X0 @ X1 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 2.66/2.90      inference('sup+', [status(thm)], ['57', '58'])).
% 2.66/2.90  thf('60', plain,
% 2.66/2.90      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 2.66/2.90         ((k2_enumset1 @ X2 @ X3 @ X4 @ X5)
% 2.66/2.90           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X3 @ X4) @ (k1_tarski @ X5)))),
% 2.66/2.90      inference('cnf', [status(esa)], [t46_enumset1])).
% 2.66/2.90  thf('61', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.66/2.90         ((k2_enumset1 @ X0 @ X1 @ X2 @ X3)
% 2.66/2.90           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 2.66/2.90      inference('sup+', [status(thm)], ['59', '60'])).
% 2.66/2.90  thf('62', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.66/2.90         ((k2_enumset1 @ X1 @ X2 @ X0 @ X3)
% 2.66/2.90           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 2.66/2.90      inference('sup+', [status(thm)], ['44', '45'])).
% 2.66/2.90  thf('63', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.66/2.90         ((k2_enumset1 @ X2 @ X1 @ X3 @ X0) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 2.66/2.90      inference('sup+', [status(thm)], ['61', '62'])).
% 2.66/2.90  thf('64', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.66/2.90         ((k2_enumset1 @ X2 @ X3 @ X1 @ X0) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 2.66/2.90      inference('sup+', [status(thm)], ['46', '47'])).
% 2.66/2.90  thf('65', plain,
% 2.66/2.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.66/2.90         ((k2_enumset1 @ X3 @ X1 @ X2 @ X0) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 2.66/2.90      inference('sup+', [status(thm)], ['63', '64'])).
% 2.66/2.90  thf('66', plain,
% 2.66/2.90      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 2.66/2.90         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 2.66/2.90      inference('demod', [status(thm)], ['0', '65'])).
% 2.66/2.90  thf('67', plain, ($false), inference('simplify', [status(thm)], ['66'])).
% 2.66/2.90  
% 2.66/2.90  % SZS output end Refutation
% 2.66/2.90  
% 2.66/2.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

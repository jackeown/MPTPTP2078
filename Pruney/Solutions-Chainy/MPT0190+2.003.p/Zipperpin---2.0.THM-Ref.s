%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JD3OobDHkn

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:11 EST 2020

% Result     : Theorem 3.21s
% Output     : Refutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 348 expanded)
%              Number of leaves         :   19 ( 123 expanded)
%              Depth                    :   15
%              Number of atoms          : 1072 (3621 expanded)
%              Number of equality atoms :   99 ( 337 expanded)
%              Maximal formula depth    :   12 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t109_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ B @ A @ D @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k2_enumset1 @ A @ B @ C @ D )
        = ( k2_enumset1 @ B @ A @ D @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t109_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_B @ sk_A @ sk_D @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('1',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k3_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26 )
      = ( k2_enumset1 @ X23 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k2_enumset1 @ X20 @ X20 @ X21 @ X22 )
      = ( k1_enumset1 @ X20 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t83_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_enumset1 @ A @ A @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k3_enumset1 @ X32 @ X32 @ X32 @ X32 @ X33 )
      = ( k2_tarski @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t83_enumset1])).

thf('5',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k3_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26 )
      = ( k2_enumset1 @ X23 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k2_enumset1 @ X20 @ X20 @ X21 @ X22 )
      = ( k1_enumset1 @ X20 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t102_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ C @ B @ A ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X9 @ X8 @ X7 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t102_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','10'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('12',plain,(
    ! [X19: $i] :
      ( ( k2_tarski @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l57_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) )).

thf('13',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X3 @ X4 ) @ ( k2_tarski @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X9 @ X8 @ X7 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t102_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X10 @ X11 @ X12 ) @ ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_enumset1 @ X1 @ X2 @ X3 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('21',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X9 @ X8 @ X7 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t102_enumset1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k3_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26 )
      = ( k2_enumset1 @ X23 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X0 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X9 @ X8 @ X7 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t102_enumset1])).

thf('27',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X3 @ X4 ) @ ( k2_tarski @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X0 @ X1 @ X2 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X1 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('31',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X3 @ X4 ) @ ( k2_tarski @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k3_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26 )
      = ( k2_enumset1 @ X23 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X1 @ X3 @ X2 )
      = ( k2_enumset1 @ X1 @ X0 @ X3 @ X2 ) ) ),
    inference(demod,[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k3_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26 )
      = ( k2_enumset1 @ X23 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X2 @ X3 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['0','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','24'])).

thf('40',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X10 @ X11 @ X12 ) @ ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('46',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X10 @ X11 @ X12 ) @ ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k2_enumset1 @ X20 @ X20 @ X21 @ X22 )
      = ( k1_enumset1 @ X20 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X1 @ X2 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['44','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['41','50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','24'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf(t48_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ) )).

thf('55',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k2_tarski @ X14 @ X15 ) @ ( k1_enumset1 @ X16 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t48_enumset1])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X0 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X0 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','10'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k2_tarski @ X1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X19: $i] :
      ( ( k2_tarski @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('63',plain,(
    ! [X19: $i] :
      ( ( k2_tarski @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ! [X19: $i] :
      ( ( k2_tarski @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','69'])).

thf('71',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k3_enumset1 @ X32 @ X32 @ X32 @ X32 @ X33 )
      = ( k2_tarski @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t83_enumset1])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X19: $i] :
      ( ( k2_tarski @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['70','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X19: $i] :
      ( ( k2_tarski @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k1_enumset1 @ X0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['76','81'])).

thf('83',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k2_tarski @ X14 @ X15 ) @ ( k1_enumset1 @ X16 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t48_enumset1])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X1 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['58','86'])).

thf('88',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['38','87'])).

thf('89',plain,(
    $false ),
    inference(simplify,[status(thm)],['88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JD3OobDHkn
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:17:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.21/3.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.21/3.46  % Solved by: fo/fo7.sh
% 3.21/3.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.21/3.46  % done 5433 iterations in 3.035s
% 3.21/3.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.21/3.46  % SZS output start Refutation
% 3.21/3.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.21/3.46  thf(sk_C_type, type, sk_C: $i).
% 3.21/3.46  thf(sk_D_type, type, sk_D: $i).
% 3.21/3.46  thf(sk_A_type, type, sk_A: $i).
% 3.21/3.46  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 3.21/3.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.21/3.46  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 3.21/3.46  thf(sk_B_type, type, sk_B: $i).
% 3.21/3.46  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 3.21/3.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.21/3.46  thf(t109_enumset1, conjecture,
% 3.21/3.46    (![A:$i,B:$i,C:$i,D:$i]:
% 3.21/3.46     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ A @ D @ C ) ))).
% 3.21/3.46  thf(zf_stmt_0, negated_conjecture,
% 3.21/3.46    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 3.21/3.46        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ A @ D @ C ) ) )),
% 3.21/3.46    inference('cnf.neg', [status(esa)], [t109_enumset1])).
% 3.21/3.46  thf('0', plain,
% 3.21/3.46      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 3.21/3.46         != (k2_enumset1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 3.21/3.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.46  thf(t72_enumset1, axiom,
% 3.21/3.46    (![A:$i,B:$i,C:$i,D:$i]:
% 3.21/3.46     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 3.21/3.46  thf('1', plain,
% 3.21/3.46      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 3.21/3.46         ((k3_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26)
% 3.21/3.46           = (k2_enumset1 @ X23 @ X24 @ X25 @ X26))),
% 3.21/3.46      inference('cnf', [status(esa)], [t72_enumset1])).
% 3.21/3.46  thf(t71_enumset1, axiom,
% 3.21/3.46    (![A:$i,B:$i,C:$i]:
% 3.21/3.46     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 3.21/3.46  thf('2', plain,
% 3.21/3.46      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.21/3.46         ((k2_enumset1 @ X20 @ X20 @ X21 @ X22)
% 3.21/3.46           = (k1_enumset1 @ X20 @ X21 @ X22))),
% 3.21/3.46      inference('cnf', [status(esa)], [t71_enumset1])).
% 3.21/3.46  thf('3', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.21/3.46         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 3.21/3.46      inference('sup+', [status(thm)], ['1', '2'])).
% 3.21/3.46  thf(t83_enumset1, axiom,
% 3.21/3.46    (![A:$i,B:$i]:
% 3.21/3.46     ( ( k3_enumset1 @ A @ A @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 3.21/3.46  thf('4', plain,
% 3.21/3.46      (![X32 : $i, X33 : $i]:
% 3.21/3.46         ((k3_enumset1 @ X32 @ X32 @ X32 @ X32 @ X33) = (k2_tarski @ X32 @ X33))),
% 3.21/3.46      inference('cnf', [status(esa)], [t83_enumset1])).
% 3.21/3.46  thf('5', plain,
% 3.21/3.46      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 3.21/3.46         ((k3_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26)
% 3.21/3.46           = (k2_enumset1 @ X23 @ X24 @ X25 @ X26))),
% 3.21/3.46      inference('cnf', [status(esa)], [t72_enumset1])).
% 3.21/3.46  thf('6', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i]:
% 3.21/3.46         ((k2_tarski @ X1 @ X0) = (k2_enumset1 @ X1 @ X1 @ X1 @ X0))),
% 3.21/3.46      inference('sup+', [status(thm)], ['4', '5'])).
% 3.21/3.46  thf('7', plain,
% 3.21/3.46      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.21/3.46         ((k2_enumset1 @ X20 @ X20 @ X21 @ X22)
% 3.21/3.46           = (k1_enumset1 @ X20 @ X21 @ X22))),
% 3.21/3.46      inference('cnf', [status(esa)], [t71_enumset1])).
% 3.21/3.46  thf('8', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i]:
% 3.21/3.46         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 3.21/3.46      inference('demod', [status(thm)], ['6', '7'])).
% 3.21/3.46  thf(t102_enumset1, axiom,
% 3.21/3.46    (![A:$i,B:$i,C:$i]:
% 3.21/3.46     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ C @ B @ A ) ))).
% 3.21/3.46  thf('9', plain,
% 3.21/3.46      (![X7 : $i, X8 : $i, X9 : $i]:
% 3.21/3.46         ((k1_enumset1 @ X9 @ X8 @ X7) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 3.21/3.46      inference('cnf', [status(esa)], [t102_enumset1])).
% 3.21/3.46  thf('10', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i]:
% 3.21/3.46         ((k1_enumset1 @ X0 @ X1 @ X1) = (k2_tarski @ X1 @ X0))),
% 3.21/3.46      inference('sup+', [status(thm)], ['8', '9'])).
% 3.21/3.46  thf('11', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i]:
% 3.21/3.46         ((k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X0) = (k2_tarski @ X0 @ X1))),
% 3.21/3.46      inference('sup+', [status(thm)], ['3', '10'])).
% 3.21/3.46  thf(t69_enumset1, axiom,
% 3.21/3.46    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 3.21/3.46  thf('12', plain,
% 3.21/3.46      (![X19 : $i]: ((k2_tarski @ X19 @ X19) = (k1_tarski @ X19))),
% 3.21/3.46      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.21/3.46  thf(l57_enumset1, axiom,
% 3.21/3.46    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 3.21/3.46     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 3.21/3.46       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ))).
% 3.21/3.46  thf('13', plain,
% 3.21/3.46      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 3.21/3.46         ((k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6)
% 3.21/3.46           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X3 @ X4) @ 
% 3.21/3.46              (k2_tarski @ X5 @ X6)))),
% 3.21/3.46      inference('cnf', [status(esa)], [l57_enumset1])).
% 3.21/3.46  thf('14', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.21/3.46         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0)
% 3.21/3.46           = (k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0)))),
% 3.21/3.46      inference('sup+', [status(thm)], ['12', '13'])).
% 3.21/3.46  thf('15', plain,
% 3.21/3.46      (![X7 : $i, X8 : $i, X9 : $i]:
% 3.21/3.46         ((k1_enumset1 @ X9 @ X8 @ X7) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 3.21/3.46      inference('cnf', [status(esa)], [t102_enumset1])).
% 3.21/3.46  thf(t46_enumset1, axiom,
% 3.21/3.46    (![A:$i,B:$i,C:$i,D:$i]:
% 3.21/3.46     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 3.21/3.46       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 3.21/3.46  thf('16', plain,
% 3.21/3.46      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 3.21/3.46         ((k2_enumset1 @ X10 @ X11 @ X12 @ X13)
% 3.21/3.46           = (k2_xboole_0 @ (k1_enumset1 @ X10 @ X11 @ X12) @ (k1_tarski @ X13)))),
% 3.21/3.46      inference('cnf', [status(esa)], [t46_enumset1])).
% 3.21/3.46  thf('17', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.21/3.46         ((k2_enumset1 @ X0 @ X1 @ X2 @ X3)
% 3.21/3.46           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 3.21/3.46      inference('sup+', [status(thm)], ['15', '16'])).
% 3.21/3.46  thf('18', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.21/3.46         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0)
% 3.21/3.46           = (k2_enumset1 @ X1 @ X2 @ X3 @ X0))),
% 3.21/3.46      inference('demod', [status(thm)], ['14', '17'])).
% 3.21/3.46  thf('19', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i]:
% 3.21/3.46         ((k2_tarski @ X1 @ X0) = (k2_enumset1 @ X0 @ X0 @ X0 @ X1))),
% 3.21/3.46      inference('sup+', [status(thm)], ['11', '18'])).
% 3.21/3.46  thf('20', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.21/3.46         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 3.21/3.46      inference('sup+', [status(thm)], ['1', '2'])).
% 3.21/3.46  thf('21', plain,
% 3.21/3.46      (![X7 : $i, X8 : $i, X9 : $i]:
% 3.21/3.46         ((k1_enumset1 @ X9 @ X8 @ X7) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 3.21/3.46      inference('cnf', [status(esa)], [t102_enumset1])).
% 3.21/3.46  thf('22', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.21/3.46         ((k1_enumset1 @ X0 @ X1 @ X2) = (k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0))),
% 3.21/3.46      inference('sup+', [status(thm)], ['20', '21'])).
% 3.21/3.46  thf('23', plain,
% 3.21/3.46      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 3.21/3.46         ((k3_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26)
% 3.21/3.46           = (k2_enumset1 @ X23 @ X24 @ X25 @ X26))),
% 3.21/3.46      inference('cnf', [status(esa)], [t72_enumset1])).
% 3.21/3.46  thf('24', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.21/3.46         ((k1_enumset1 @ X2 @ X1 @ X0) = (k2_enumset1 @ X0 @ X0 @ X1 @ X2))),
% 3.21/3.46      inference('sup+', [status(thm)], ['22', '23'])).
% 3.21/3.46  thf('25', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i]:
% 3.21/3.46         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X0))),
% 3.21/3.46      inference('demod', [status(thm)], ['19', '24'])).
% 3.21/3.46  thf('26', plain,
% 3.21/3.46      (![X7 : $i, X8 : $i, X9 : $i]:
% 3.21/3.46         ((k1_enumset1 @ X9 @ X8 @ X7) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 3.21/3.46      inference('cnf', [status(esa)], [t102_enumset1])).
% 3.21/3.46  thf('27', plain,
% 3.21/3.46      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 3.21/3.46         ((k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6)
% 3.21/3.46           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X3 @ X4) @ 
% 3.21/3.46              (k2_tarski @ X5 @ X6)))),
% 3.21/3.46      inference('cnf', [status(esa)], [l57_enumset1])).
% 3.21/3.46  thf('28', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 3.21/3.46         ((k3_enumset1 @ X0 @ X1 @ X2 @ X4 @ X3)
% 3.21/3.46           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 3.21/3.46              (k2_tarski @ X4 @ X3)))),
% 3.21/3.46      inference('sup+', [status(thm)], ['26', '27'])).
% 3.21/3.46  thf('29', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.21/3.46         ((k3_enumset1 @ X0 @ X0 @ X1 @ X3 @ X2)
% 3.21/3.46           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 3.21/3.46      inference('sup+', [status(thm)], ['25', '28'])).
% 3.21/3.46  thf('30', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i]:
% 3.21/3.46         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 3.21/3.46      inference('demod', [status(thm)], ['6', '7'])).
% 3.21/3.46  thf('31', plain,
% 3.21/3.46      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 3.21/3.46         ((k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6)
% 3.21/3.46           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X3 @ X4) @ 
% 3.21/3.46              (k2_tarski @ X5 @ X6)))),
% 3.21/3.46      inference('cnf', [status(esa)], [l57_enumset1])).
% 3.21/3.46  thf('32', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.21/3.46         ((k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2)
% 3.21/3.46           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 3.21/3.46      inference('sup+', [status(thm)], ['30', '31'])).
% 3.21/3.46  thf('33', plain,
% 3.21/3.46      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 3.21/3.46         ((k3_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26)
% 3.21/3.46           = (k2_enumset1 @ X23 @ X24 @ X25 @ X26))),
% 3.21/3.46      inference('cnf', [status(esa)], [t72_enumset1])).
% 3.21/3.46  thf('34', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.21/3.46         ((k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0))
% 3.21/3.46           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 3.21/3.46      inference('sup+', [status(thm)], ['32', '33'])).
% 3.21/3.46  thf('35', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.21/3.46         ((k3_enumset1 @ X0 @ X0 @ X1 @ X3 @ X2)
% 3.21/3.46           = (k2_enumset1 @ X1 @ X0 @ X3 @ X2))),
% 3.21/3.46      inference('demod', [status(thm)], ['29', '34'])).
% 3.21/3.46  thf('36', plain,
% 3.21/3.46      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 3.21/3.46         ((k3_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26)
% 3.21/3.46           = (k2_enumset1 @ X23 @ X24 @ X25 @ X26))),
% 3.21/3.46      inference('cnf', [status(esa)], [t72_enumset1])).
% 3.21/3.46  thf('37', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.21/3.46         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X2 @ X3 @ X1 @ X0))),
% 3.21/3.46      inference('sup+', [status(thm)], ['35', '36'])).
% 3.21/3.46  thf('38', plain,
% 3.21/3.46      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 3.21/3.46         != (k2_enumset1 @ sk_A @ sk_B @ sk_D @ sk_C))),
% 3.21/3.46      inference('demod', [status(thm)], ['0', '37'])).
% 3.21/3.46  thf('39', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i]:
% 3.21/3.46         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X0))),
% 3.21/3.46      inference('demod', [status(thm)], ['19', '24'])).
% 3.21/3.46  thf('40', plain,
% 3.21/3.46      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 3.21/3.46         ((k2_enumset1 @ X10 @ X11 @ X12 @ X13)
% 3.21/3.46           = (k2_xboole_0 @ (k1_enumset1 @ X10 @ X11 @ X12) @ (k1_tarski @ X13)))),
% 3.21/3.46      inference('cnf', [status(esa)], [t46_enumset1])).
% 3.21/3.46  thf('41', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.21/3.46         ((k2_enumset1 @ X1 @ X0 @ X0 @ X2)
% 3.21/3.46           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 3.21/3.46      inference('sup+', [status(thm)], ['39', '40'])).
% 3.21/3.46  thf('42', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i]:
% 3.21/3.46         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 3.21/3.46      inference('demod', [status(thm)], ['6', '7'])).
% 3.21/3.46  thf('43', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.21/3.46         ((k2_enumset1 @ X0 @ X1 @ X2 @ X3)
% 3.21/3.46           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 3.21/3.46      inference('sup+', [status(thm)], ['15', '16'])).
% 3.21/3.46  thf('44', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.21/3.46         ((k2_enumset1 @ X0 @ X1 @ X1 @ X2)
% 3.21/3.46           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 3.21/3.46      inference('sup+', [status(thm)], ['42', '43'])).
% 3.21/3.46  thf('45', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i]:
% 3.21/3.46         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 3.21/3.46      inference('demod', [status(thm)], ['6', '7'])).
% 3.21/3.46  thf('46', plain,
% 3.21/3.46      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 3.21/3.46         ((k2_enumset1 @ X10 @ X11 @ X12 @ X13)
% 3.21/3.46           = (k2_xboole_0 @ (k1_enumset1 @ X10 @ X11 @ X12) @ (k1_tarski @ X13)))),
% 3.21/3.46      inference('cnf', [status(esa)], [t46_enumset1])).
% 3.21/3.46  thf('47', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.21/3.46         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 3.21/3.46           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 3.21/3.46      inference('sup+', [status(thm)], ['45', '46'])).
% 3.21/3.46  thf('48', plain,
% 3.21/3.46      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.21/3.46         ((k2_enumset1 @ X20 @ X20 @ X21 @ X22)
% 3.21/3.46           = (k1_enumset1 @ X20 @ X21 @ X22))),
% 3.21/3.46      inference('cnf', [status(esa)], [t71_enumset1])).
% 3.21/3.46  thf('49', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.21/3.46         ((k1_enumset1 @ X1 @ X0 @ X2)
% 3.21/3.46           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 3.21/3.46      inference('demod', [status(thm)], ['47', '48'])).
% 3.21/3.46  thf('50', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.21/3.46         ((k2_enumset1 @ X0 @ X1 @ X1 @ X2) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 3.21/3.46      inference('demod', [status(thm)], ['44', '49'])).
% 3.21/3.46  thf('51', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.21/3.46         ((k1_enumset1 @ X1 @ X0 @ X2)
% 3.21/3.46           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 3.21/3.46      inference('demod', [status(thm)], ['47', '48'])).
% 3.21/3.46  thf('52', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.21/3.46         ((k1_enumset1 @ X0 @ X1 @ X2) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 3.21/3.46      inference('demod', [status(thm)], ['41', '50', '51'])).
% 3.21/3.46  thf('53', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i]:
% 3.21/3.46         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X0))),
% 3.21/3.46      inference('demod', [status(thm)], ['19', '24'])).
% 3.21/3.46  thf('54', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i]:
% 3.21/3.46         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X0))),
% 3.21/3.46      inference('sup+', [status(thm)], ['52', '53'])).
% 3.21/3.46  thf(t48_enumset1, axiom,
% 3.21/3.46    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 3.21/3.46     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 3.21/3.46       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ))).
% 3.21/3.46  thf('55', plain,
% 3.21/3.46      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 3.21/3.46         ((k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18)
% 3.21/3.46           = (k2_xboole_0 @ (k2_tarski @ X14 @ X15) @ 
% 3.21/3.46              (k1_enumset1 @ X16 @ X17 @ X18)))),
% 3.21/3.46      inference('cnf', [status(esa)], [t48_enumset1])).
% 3.21/3.46  thf('56', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.21/3.46         ((k3_enumset1 @ X3 @ X2 @ X0 @ X1 @ X0)
% 3.21/3.46           = (k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0)))),
% 3.21/3.46      inference('sup+', [status(thm)], ['54', '55'])).
% 3.21/3.46  thf('57', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.21/3.46         ((k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0))
% 3.21/3.46           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 3.21/3.46      inference('sup+', [status(thm)], ['32', '33'])).
% 3.21/3.46  thf('58', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.21/3.46         ((k3_enumset1 @ X3 @ X2 @ X0 @ X1 @ X0)
% 3.21/3.46           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 3.21/3.46      inference('demod', [status(thm)], ['56', '57'])).
% 3.21/3.46  thf('59', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i]:
% 3.21/3.46         ((k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X0) = (k2_tarski @ X0 @ X1))),
% 3.21/3.46      inference('sup+', [status(thm)], ['3', '10'])).
% 3.21/3.46  thf('60', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.21/3.46         ((k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2)
% 3.21/3.46           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 3.21/3.46      inference('sup+', [status(thm)], ['30', '31'])).
% 3.21/3.46  thf('61', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i]:
% 3.21/3.46         ((k2_tarski @ X1 @ X0)
% 3.21/3.46           = (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k2_tarski @ X1 @ X1)))),
% 3.21/3.46      inference('sup+', [status(thm)], ['59', '60'])).
% 3.21/3.46  thf('62', plain,
% 3.21/3.46      (![X19 : $i]: ((k2_tarski @ X19 @ X19) = (k1_tarski @ X19))),
% 3.21/3.46      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.21/3.46  thf('63', plain,
% 3.21/3.46      (![X19 : $i]: ((k2_tarski @ X19 @ X19) = (k1_tarski @ X19))),
% 3.21/3.46      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.21/3.46  thf('64', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i]:
% 3.21/3.46         ((k2_tarski @ X1 @ X0)
% 3.21/3.46           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 3.21/3.46      inference('demod', [status(thm)], ['61', '62', '63'])).
% 3.21/3.46  thf('65', plain,
% 3.21/3.46      (![X19 : $i]: ((k2_tarski @ X19 @ X19) = (k1_tarski @ X19))),
% 3.21/3.46      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.21/3.46  thf('66', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.21/3.46         ((k1_enumset1 @ X1 @ X0 @ X2)
% 3.21/3.46           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 3.21/3.46      inference('demod', [status(thm)], ['47', '48'])).
% 3.21/3.46  thf('67', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i]:
% 3.21/3.46         ((k1_enumset1 @ X0 @ X0 @ X1)
% 3.21/3.46           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 3.21/3.46      inference('sup+', [status(thm)], ['65', '66'])).
% 3.21/3.46  thf('68', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i]:
% 3.21/3.46         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 3.21/3.46      inference('demod', [status(thm)], ['6', '7'])).
% 3.21/3.46  thf('69', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i]:
% 3.21/3.46         ((k2_tarski @ X0 @ X1)
% 3.21/3.46           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 3.21/3.46      inference('demod', [status(thm)], ['67', '68'])).
% 3.21/3.46  thf('70', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i]: ((k2_tarski @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 3.21/3.46      inference('sup+', [status(thm)], ['64', '69'])).
% 3.21/3.46  thf('71', plain,
% 3.21/3.46      (![X32 : $i, X33 : $i]:
% 3.21/3.46         ((k3_enumset1 @ X32 @ X32 @ X32 @ X32 @ X33) = (k2_tarski @ X32 @ X33))),
% 3.21/3.46      inference('cnf', [status(esa)], [t83_enumset1])).
% 3.21/3.46  thf('72', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.21/3.46         ((k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2)
% 3.21/3.46           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 3.21/3.46      inference('sup+', [status(thm)], ['30', '31'])).
% 3.21/3.46  thf('73', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i]:
% 3.21/3.46         ((k2_tarski @ X1 @ X0)
% 3.21/3.46           = (k2_xboole_0 @ (k2_tarski @ X1 @ X1) @ (k2_tarski @ X1 @ X0)))),
% 3.21/3.46      inference('sup+', [status(thm)], ['71', '72'])).
% 3.21/3.46  thf('74', plain,
% 3.21/3.46      (![X19 : $i]: ((k2_tarski @ X19 @ X19) = (k1_tarski @ X19))),
% 3.21/3.46      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.21/3.46  thf('75', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i]:
% 3.21/3.46         ((k2_tarski @ X1 @ X0)
% 3.21/3.46           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0)))),
% 3.21/3.46      inference('demod', [status(thm)], ['73', '74'])).
% 3.21/3.46  thf('76', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i]:
% 3.21/3.46         ((k2_tarski @ X0 @ X1)
% 3.21/3.46           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0)))),
% 3.21/3.46      inference('sup+', [status(thm)], ['70', '75'])).
% 3.21/3.46  thf('77', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.21/3.46         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 3.21/3.46      inference('sup+', [status(thm)], ['1', '2'])).
% 3.21/3.46  thf('78', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.21/3.46         ((k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2)
% 3.21/3.46           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 3.21/3.46      inference('sup+', [status(thm)], ['30', '31'])).
% 3.21/3.46  thf('79', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.21/3.46         ((k1_enumset1 @ X2 @ X1 @ X0)
% 3.21/3.46           = (k2_xboole_0 @ (k2_tarski @ X2 @ X2) @ (k2_tarski @ X1 @ X0)))),
% 3.21/3.46      inference('sup+', [status(thm)], ['77', '78'])).
% 3.21/3.46  thf('80', plain,
% 3.21/3.46      (![X19 : $i]: ((k2_tarski @ X19 @ X19) = (k1_tarski @ X19))),
% 3.21/3.46      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.21/3.46  thf('81', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.21/3.46         ((k1_enumset1 @ X2 @ X1 @ X0)
% 3.21/3.46           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 3.21/3.46      inference('demod', [status(thm)], ['79', '80'])).
% 3.21/3.46  thf('82', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i]:
% 3.21/3.46         ((k2_tarski @ X0 @ X1) = (k1_enumset1 @ X0 @ X1 @ X0))),
% 3.21/3.46      inference('demod', [status(thm)], ['76', '81'])).
% 3.21/3.46  thf('83', plain,
% 3.21/3.46      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 3.21/3.46         ((k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18)
% 3.21/3.46           = (k2_xboole_0 @ (k2_tarski @ X14 @ X15) @ 
% 3.21/3.46              (k1_enumset1 @ X16 @ X17 @ X18)))),
% 3.21/3.46      inference('cnf', [status(esa)], [t48_enumset1])).
% 3.21/3.46  thf('84', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.21/3.46         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X1)
% 3.21/3.46           = (k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0)))),
% 3.21/3.46      inference('sup+', [status(thm)], ['82', '83'])).
% 3.21/3.46  thf('85', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.21/3.46         ((k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0))
% 3.21/3.46           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 3.21/3.46      inference('sup+', [status(thm)], ['32', '33'])).
% 3.21/3.46  thf('86', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.21/3.46         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X1)
% 3.21/3.46           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 3.21/3.46      inference('demod', [status(thm)], ['84', '85'])).
% 3.21/3.46  thf('87', plain,
% 3.21/3.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.21/3.46         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X3 @ X2 @ X0 @ X1))),
% 3.21/3.46      inference('sup+', [status(thm)], ['58', '86'])).
% 3.21/3.46  thf('88', plain,
% 3.21/3.46      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 3.21/3.46         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 3.21/3.46      inference('demod', [status(thm)], ['38', '87'])).
% 3.21/3.46  thf('89', plain, ($false), inference('simplify', [status(thm)], ['88'])).
% 3.21/3.46  
% 3.21/3.46  % SZS output end Refutation
% 3.21/3.46  
% 3.30/3.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

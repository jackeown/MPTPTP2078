%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vXBoKA4y0B

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:38 EST 2020

% Result     : Theorem 3.71s
% Output     : Refutation 3.71s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 163 expanded)
%              Number of leaves         :   20 (  62 expanded)
%              Depth                    :   10
%              Number of atoms          : 1015 (1709 expanded)
%              Number of equality atoms :   88 ( 152 expanded)
%              Maximal formula depth    :   15 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X9 @ X7 @ X8 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('2',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X9 @ X7 @ X8 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('3',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k2_tarski @ sk_C @ sk_A ) )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf('4',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X9 @ X7 @ X8 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_enumset1 @ X20 @ X20 @ X21 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(l57_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X3 @ X4 ) @ ( k2_tarski @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X0 @ X1 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ( k3_enumset1 @ sk_B @ sk_A @ sk_B @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['3','8'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('10',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k2_enumset1 @ X22 @ X22 @ X23 @ X24 )
      = ( k1_enumset1 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k2_enumset1 @ X22 @ X22 @ X23 @ X24 )
      = ( k1_enumset1 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('14',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_enumset1 @ X20 @ X20 @ X21 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_enumset1 @ X0 @ X0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k2_enumset1 @ X22 @ X22 @ X23 @ X24 )
      = ( k1_enumset1 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('18',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X3 @ X4 ) @ ( k2_tarski @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X2 @ X1 @ X0 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X0 @ X1 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X2 @ X1 @ X0 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X0 @ X1 @ X3 @ X2 )
      = ( k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('23',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k3_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28 )
      = ( k2_enumset1 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X0 @ X1 @ X3 @ X2 )
      = ( k2_enumset1 @ X1 @ X0 @ X3 @ X2 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ( k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['9','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('27',plain,(
    ! [X19: $i] :
      ( ( k2_tarski @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('30',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X3 @ X4 ) @ ( k2_tarski @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X3 @ X2 ) @ ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X19: $i] :
      ( ( k2_tarski @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('34',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X9 @ X7 @ X8 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('35',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X3 @ X4 ) @ ( k2_tarski @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X0 @ X2 @ X1 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X3 @ X2 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k2_enumset1 @ X22 @ X22 @ X23 @ X24 )
      = ( k1_enumset1 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('39',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k3_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28 )
      = ( k2_enumset1 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t55_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ) )).

thf('40',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k4_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 ) @ ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t55_enumset1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('43',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( k4_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 @ X33 )
      = ( k3_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('44',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k3_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28 )
      = ( k2_enumset1 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference(demod,[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X3 @ X2 @ X0 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['37','46'])).

thf(t102_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ C @ B @ A ) ) )).

thf('48',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k1_enumset1 @ X12 @ X11 @ X10 )
      = ( k1_enumset1 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t102_enumset1])).

thf('49',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X9 @ X7 @ X8 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k2_enumset1 @ X22 @ X22 @ X23 @ X24 )
      = ( k1_enumset1 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X2 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X1 @ X1 @ X1 @ X2 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X2 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X3 @ X0 )
      = ( k2_enumset1 @ X2 @ X3 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','47','56'])).

thf('58',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k3_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28 )
      = ( k2_enumset1 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('59',plain,(
    ! [X19: $i] :
      ( ( k2_tarski @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('60',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X3 @ X4 ) @ ( k2_tarski @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_enumset1 @ X20 @ X20 @ X21 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k2_enumset1 @ X22 @ X22 @ X23 @ X24 )
      = ( k1_enumset1 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['64','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('76',plain,(
    ( k1_enumset1 @ sk_B @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['25','57','74','75'])).

thf('77',plain,(
    $false ),
    inference(simplify,[status(thm)],['76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vXBoKA4y0B
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:02:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.71/3.92  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.71/3.92  % Solved by: fo/fo7.sh
% 3.71/3.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.71/3.92  % done 5027 iterations in 3.464s
% 3.71/3.92  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.71/3.92  % SZS output start Refutation
% 3.71/3.92  thf(sk_A_type, type, sk_A: $i).
% 3.71/3.92  thf(sk_C_type, type, sk_C: $i).
% 3.71/3.92  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 3.71/3.92  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.71/3.92  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 3.71/3.92  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 3.71/3.92  thf(sk_B_type, type, sk_B: $i).
% 3.71/3.92  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.71/3.92  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 3.71/3.92  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.71/3.92  thf(t137_enumset1, conjecture,
% 3.71/3.92    (![A:$i,B:$i,C:$i]:
% 3.71/3.92     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 3.71/3.92       ( k1_enumset1 @ A @ B @ C ) ))).
% 3.71/3.92  thf(zf_stmt_0, negated_conjecture,
% 3.71/3.92    (~( ![A:$i,B:$i,C:$i]:
% 3.71/3.92        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 3.71/3.92          ( k1_enumset1 @ A @ B @ C ) ) )),
% 3.71/3.92    inference('cnf.neg', [status(esa)], [t137_enumset1])).
% 3.71/3.92  thf('0', plain,
% 3.71/3.92      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 3.71/3.92         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 3.71/3.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.71/3.92  thf(t100_enumset1, axiom,
% 3.71/3.92    (![A:$i,B:$i,C:$i]:
% 3.71/3.92     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ B @ C @ A ) ))).
% 3.71/3.92  thf('1', plain,
% 3.71/3.92      (![X7 : $i, X8 : $i, X9 : $i]:
% 3.71/3.92         ((k1_enumset1 @ X9 @ X7 @ X8) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 3.71/3.92      inference('cnf', [status(esa)], [t100_enumset1])).
% 3.71/3.92  thf('2', plain,
% 3.71/3.92      (![X7 : $i, X8 : $i, X9 : $i]:
% 3.71/3.92         ((k1_enumset1 @ X9 @ X7 @ X8) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 3.71/3.92      inference('cnf', [status(esa)], [t100_enumset1])).
% 3.71/3.92  thf('3', plain,
% 3.71/3.92      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 3.71/3.92         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 3.71/3.92      inference('demod', [status(thm)], ['0', '1', '2'])).
% 3.71/3.92  thf('4', plain,
% 3.71/3.92      (![X7 : $i, X8 : $i, X9 : $i]:
% 3.71/3.92         ((k1_enumset1 @ X9 @ X7 @ X8) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 3.71/3.92      inference('cnf', [status(esa)], [t100_enumset1])).
% 3.71/3.92  thf(t70_enumset1, axiom,
% 3.71/3.92    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 3.71/3.92  thf('5', plain,
% 3.71/3.92      (![X20 : $i, X21 : $i]:
% 3.71/3.92         ((k1_enumset1 @ X20 @ X20 @ X21) = (k2_tarski @ X20 @ X21))),
% 3.71/3.92      inference('cnf', [status(esa)], [t70_enumset1])).
% 3.71/3.92  thf('6', plain,
% 3.71/3.92      (![X0 : $i, X1 : $i]:
% 3.71/3.92         ((k1_enumset1 @ X0 @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 3.71/3.92      inference('sup+', [status(thm)], ['4', '5'])).
% 3.71/3.92  thf(l57_enumset1, axiom,
% 3.71/3.92    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 3.71/3.92     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 3.71/3.92       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ))).
% 3.71/3.92  thf('7', plain,
% 3.71/3.92      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 3.71/3.92         ((k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6)
% 3.71/3.92           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X3 @ X4) @ 
% 3.71/3.92              (k2_tarski @ X5 @ X6)))),
% 3.71/3.92      inference('cnf', [status(esa)], [l57_enumset1])).
% 3.71/3.92  thf('8', plain,
% 3.71/3.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.71/3.92         ((k3_enumset1 @ X1 @ X0 @ X1 @ X3 @ X2)
% 3.71/3.92           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 3.71/3.92      inference('sup+', [status(thm)], ['6', '7'])).
% 3.71/3.92  thf('9', plain,
% 3.71/3.92      (((k3_enumset1 @ sk_B @ sk_A @ sk_B @ sk_C @ sk_A)
% 3.71/3.92         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 3.71/3.92      inference('demod', [status(thm)], ['3', '8'])).
% 3.71/3.92  thf(t71_enumset1, axiom,
% 3.71/3.92    (![A:$i,B:$i,C:$i]:
% 3.71/3.92     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 3.71/3.92  thf('10', plain,
% 3.71/3.92      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.71/3.92         ((k2_enumset1 @ X22 @ X22 @ X23 @ X24)
% 3.71/3.92           = (k1_enumset1 @ X22 @ X23 @ X24))),
% 3.71/3.92      inference('cnf', [status(esa)], [t71_enumset1])).
% 3.71/3.92  thf('11', plain,
% 3.71/3.92      (![X0 : $i, X1 : $i]:
% 3.71/3.92         ((k1_enumset1 @ X0 @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 3.71/3.92      inference('sup+', [status(thm)], ['4', '5'])).
% 3.71/3.92  thf('12', plain,
% 3.71/3.92      (![X0 : $i, X1 : $i]:
% 3.71/3.92         ((k2_enumset1 @ X0 @ X0 @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 3.71/3.92      inference('sup+', [status(thm)], ['10', '11'])).
% 3.71/3.92  thf('13', plain,
% 3.71/3.92      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.71/3.92         ((k2_enumset1 @ X22 @ X22 @ X23 @ X24)
% 3.71/3.92           = (k1_enumset1 @ X22 @ X23 @ X24))),
% 3.71/3.92      inference('cnf', [status(esa)], [t71_enumset1])).
% 3.71/3.92  thf('14', plain,
% 3.71/3.92      (![X20 : $i, X21 : $i]:
% 3.71/3.92         ((k1_enumset1 @ X20 @ X20 @ X21) = (k2_tarski @ X20 @ X21))),
% 3.71/3.92      inference('cnf', [status(esa)], [t70_enumset1])).
% 3.71/3.92  thf('15', plain,
% 3.71/3.92      (![X0 : $i, X1 : $i]:
% 3.71/3.92         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 3.71/3.92      inference('sup+', [status(thm)], ['13', '14'])).
% 3.71/3.92  thf('16', plain,
% 3.71/3.92      (![X0 : $i, X1 : $i]:
% 3.71/3.92         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1) = (k2_enumset1 @ X0 @ X0 @ X1 @ X0))),
% 3.71/3.92      inference('sup+', [status(thm)], ['12', '15'])).
% 3.71/3.92  thf('17', plain,
% 3.71/3.92      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.71/3.92         ((k2_enumset1 @ X22 @ X22 @ X23 @ X24)
% 3.71/3.92           = (k1_enumset1 @ X22 @ X23 @ X24))),
% 3.71/3.92      inference('cnf', [status(esa)], [t71_enumset1])).
% 3.71/3.92  thf('18', plain,
% 3.71/3.92      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 3.71/3.92         ((k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6)
% 3.71/3.92           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X3 @ X4) @ 
% 3.71/3.92              (k2_tarski @ X5 @ X6)))),
% 3.71/3.92      inference('cnf', [status(esa)], [l57_enumset1])).
% 3.71/3.92  thf('19', plain,
% 3.71/3.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 3.71/3.92         ((k3_enumset1 @ X2 @ X1 @ X0 @ X4 @ X3)
% 3.71/3.92           = (k2_xboole_0 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0) @ 
% 3.71/3.92              (k2_tarski @ X4 @ X3)))),
% 3.71/3.92      inference('sup+', [status(thm)], ['17', '18'])).
% 3.71/3.92  thf('20', plain,
% 3.71/3.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.71/3.92         ((k3_enumset1 @ X1 @ X0 @ X1 @ X3 @ X2)
% 3.71/3.92           = (k2_xboole_0 @ (k2_enumset1 @ X1 @ X1 @ X1 @ X0) @ 
% 3.71/3.92              (k2_tarski @ X3 @ X2)))),
% 3.71/3.92      inference('sup+', [status(thm)], ['16', '19'])).
% 3.71/3.92  thf('21', plain,
% 3.71/3.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 3.71/3.92         ((k3_enumset1 @ X2 @ X1 @ X0 @ X4 @ X3)
% 3.71/3.92           = (k2_xboole_0 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0) @ 
% 3.71/3.92              (k2_tarski @ X4 @ X3)))),
% 3.71/3.92      inference('sup+', [status(thm)], ['17', '18'])).
% 3.71/3.92  thf('22', plain,
% 3.71/3.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.71/3.92         ((k3_enumset1 @ X1 @ X0 @ X1 @ X3 @ X2)
% 3.71/3.92           = (k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2))),
% 3.71/3.92      inference('demod', [status(thm)], ['20', '21'])).
% 3.71/3.92  thf(t72_enumset1, axiom,
% 3.71/3.92    (![A:$i,B:$i,C:$i,D:$i]:
% 3.71/3.92     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 3.71/3.92  thf('23', plain,
% 3.71/3.92      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 3.71/3.92         ((k3_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28)
% 3.71/3.92           = (k2_enumset1 @ X25 @ X26 @ X27 @ X28))),
% 3.71/3.92      inference('cnf', [status(esa)], [t72_enumset1])).
% 3.71/3.92  thf('24', plain,
% 3.71/3.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.71/3.92         ((k3_enumset1 @ X1 @ X0 @ X1 @ X3 @ X2)
% 3.71/3.92           = (k2_enumset1 @ X1 @ X0 @ X3 @ X2))),
% 3.71/3.92      inference('demod', [status(thm)], ['22', '23'])).
% 3.71/3.92  thf('25', plain,
% 3.71/3.92      (((k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A)
% 3.71/3.92         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 3.71/3.92      inference('demod', [status(thm)], ['9', '24'])).
% 3.71/3.92  thf('26', plain,
% 3.71/3.92      (![X0 : $i, X1 : $i]:
% 3.71/3.92         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 3.71/3.92      inference('sup+', [status(thm)], ['13', '14'])).
% 3.71/3.92  thf(t69_enumset1, axiom,
% 3.71/3.92    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 3.71/3.92  thf('27', plain,
% 3.71/3.92      (![X19 : $i]: ((k2_tarski @ X19 @ X19) = (k1_tarski @ X19))),
% 3.71/3.92      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.71/3.92  thf('28', plain,
% 3.71/3.92      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 3.71/3.92      inference('sup+', [status(thm)], ['26', '27'])).
% 3.71/3.92  thf('29', plain,
% 3.71/3.92      (![X0 : $i, X1 : $i]:
% 3.71/3.92         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 3.71/3.92      inference('sup+', [status(thm)], ['13', '14'])).
% 3.71/3.92  thf('30', plain,
% 3.71/3.92      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 3.71/3.92         ((k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6)
% 3.71/3.92           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X3 @ X4) @ 
% 3.71/3.92              (k2_tarski @ X5 @ X6)))),
% 3.71/3.92      inference('cnf', [status(esa)], [l57_enumset1])).
% 3.71/3.92  thf('31', plain,
% 3.71/3.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 3.71/3.92         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 3.71/3.92           = (k2_xboole_0 @ (k1_enumset1 @ X4 @ X3 @ X2) @ 
% 3.71/3.92              (k2_enumset1 @ X1 @ X1 @ X1 @ X0)))),
% 3.71/3.92      inference('sup+', [status(thm)], ['29', '30'])).
% 3.71/3.92  thf('32', plain,
% 3.71/3.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.71/3.92         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0)
% 3.71/3.92           = (k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0)))),
% 3.71/3.92      inference('sup+', [status(thm)], ['28', '31'])).
% 3.71/3.92  thf('33', plain,
% 3.71/3.92      (![X19 : $i]: ((k2_tarski @ X19 @ X19) = (k1_tarski @ X19))),
% 3.71/3.92      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.71/3.92  thf('34', plain,
% 3.71/3.92      (![X7 : $i, X8 : $i, X9 : $i]:
% 3.71/3.92         ((k1_enumset1 @ X9 @ X7 @ X8) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 3.71/3.92      inference('cnf', [status(esa)], [t100_enumset1])).
% 3.71/3.92  thf('35', plain,
% 3.71/3.92      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 3.71/3.92         ((k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6)
% 3.71/3.92           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X3 @ X4) @ 
% 3.71/3.92              (k2_tarski @ X5 @ X6)))),
% 3.71/3.92      inference('cnf', [status(esa)], [l57_enumset1])).
% 3.71/3.92  thf('36', plain,
% 3.71/3.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 3.71/3.92         ((k3_enumset1 @ X0 @ X2 @ X1 @ X4 @ X3)
% 3.71/3.92           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 3.71/3.92              (k2_tarski @ X4 @ X3)))),
% 3.71/3.92      inference('sup+', [status(thm)], ['34', '35'])).
% 3.71/3.92  thf('37', plain,
% 3.71/3.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.71/3.92         ((k3_enumset1 @ X1 @ X3 @ X2 @ X0 @ X0)
% 3.71/3.92           = (k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0)))),
% 3.71/3.92      inference('sup+', [status(thm)], ['33', '36'])).
% 3.71/3.92  thf('38', plain,
% 3.71/3.92      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.71/3.92         ((k2_enumset1 @ X22 @ X22 @ X23 @ X24)
% 3.71/3.92           = (k1_enumset1 @ X22 @ X23 @ X24))),
% 3.71/3.92      inference('cnf', [status(esa)], [t71_enumset1])).
% 3.71/3.92  thf('39', plain,
% 3.71/3.92      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 3.71/3.92         ((k3_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28)
% 3.71/3.92           = (k2_enumset1 @ X25 @ X26 @ X27 @ X28))),
% 3.71/3.92      inference('cnf', [status(esa)], [t72_enumset1])).
% 3.71/3.92  thf(t55_enumset1, axiom,
% 3.71/3.92    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.71/3.92     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 3.71/3.92       ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ))).
% 3.71/3.92  thf('40', plain,
% 3.71/3.92      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 3.71/3.92         ((k4_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18)
% 3.71/3.92           = (k2_xboole_0 @ (k3_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17) @ 
% 3.71/3.92              (k1_tarski @ X18)))),
% 3.71/3.92      inference('cnf', [status(esa)], [t55_enumset1])).
% 3.71/3.92  thf('41', plain,
% 3.71/3.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 3.71/3.92         ((k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4)
% 3.71/3.92           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 3.71/3.92              (k1_tarski @ X4)))),
% 3.71/3.92      inference('sup+', [status(thm)], ['39', '40'])).
% 3.71/3.92  thf('42', plain,
% 3.71/3.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.71/3.92         ((k4_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 @ X3)
% 3.71/3.92           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 3.71/3.92      inference('sup+', [status(thm)], ['38', '41'])).
% 3.71/3.92  thf(t73_enumset1, axiom,
% 3.71/3.92    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 3.71/3.92     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 3.71/3.92       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 3.71/3.92  thf('43', plain,
% 3.71/3.92      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 3.71/3.92         ((k4_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 @ X33)
% 3.71/3.92           = (k3_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33))),
% 3.71/3.92      inference('cnf', [status(esa)], [t73_enumset1])).
% 3.71/3.92  thf('44', plain,
% 3.71/3.92      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 3.71/3.92         ((k3_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28)
% 3.71/3.92           = (k2_enumset1 @ X25 @ X26 @ X27 @ X28))),
% 3.71/3.92      inference('cnf', [status(esa)], [t72_enumset1])).
% 3.71/3.92  thf('45', plain,
% 3.71/3.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.71/3.92         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 3.71/3.92           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 3.71/3.92      inference('sup+', [status(thm)], ['43', '44'])).
% 3.71/3.92  thf('46', plain,
% 3.71/3.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.71/3.92         ((k2_enumset1 @ X2 @ X1 @ X0 @ X3)
% 3.71/3.92           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 3.71/3.92      inference('demod', [status(thm)], ['42', '45'])).
% 3.71/3.92  thf('47', plain,
% 3.71/3.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.71/3.92         ((k3_enumset1 @ X1 @ X3 @ X2 @ X0 @ X0)
% 3.71/3.92           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 3.71/3.92      inference('demod', [status(thm)], ['37', '46'])).
% 3.71/3.92  thf(t102_enumset1, axiom,
% 3.71/3.92    (![A:$i,B:$i,C:$i]:
% 3.71/3.92     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ C @ B @ A ) ))).
% 3.71/3.92  thf('48', plain,
% 3.71/3.92      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.71/3.92         ((k1_enumset1 @ X12 @ X11 @ X10) = (k1_enumset1 @ X10 @ X11 @ X12))),
% 3.71/3.92      inference('cnf', [status(esa)], [t102_enumset1])).
% 3.71/3.92  thf('49', plain,
% 3.71/3.92      (![X7 : $i, X8 : $i, X9 : $i]:
% 3.71/3.92         ((k1_enumset1 @ X9 @ X7 @ X8) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 3.71/3.92      inference('cnf', [status(esa)], [t100_enumset1])).
% 3.71/3.92  thf('50', plain,
% 3.71/3.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.71/3.92         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 3.71/3.92      inference('sup+', [status(thm)], ['48', '49'])).
% 3.71/3.92  thf('51', plain,
% 3.71/3.92      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.71/3.92         ((k2_enumset1 @ X22 @ X22 @ X23 @ X24)
% 3.71/3.92           = (k1_enumset1 @ X22 @ X23 @ X24))),
% 3.71/3.92      inference('cnf', [status(esa)], [t71_enumset1])).
% 3.71/3.92  thf('52', plain,
% 3.71/3.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.71/3.92         ((k2_enumset1 @ X1 @ X1 @ X2 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 3.71/3.92      inference('sup+', [status(thm)], ['50', '51'])).
% 3.71/3.92  thf('53', plain,
% 3.71/3.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 3.71/3.92         ((k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4)
% 3.71/3.92           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 3.71/3.92              (k1_tarski @ X4)))),
% 3.71/3.92      inference('sup+', [status(thm)], ['39', '40'])).
% 3.71/3.92  thf('54', plain,
% 3.71/3.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.71/3.92         ((k4_enumset1 @ X1 @ X1 @ X1 @ X2 @ X0 @ X3)
% 3.71/3.92           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 3.71/3.92      inference('sup+', [status(thm)], ['52', '53'])).
% 3.71/3.92  thf('55', plain,
% 3.71/3.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.71/3.92         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 3.71/3.92           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 3.71/3.92      inference('sup+', [status(thm)], ['43', '44'])).
% 3.71/3.92  thf('56', plain,
% 3.71/3.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.71/3.92         ((k2_enumset1 @ X1 @ X2 @ X0 @ X3)
% 3.71/3.92           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 3.71/3.92      inference('demod', [status(thm)], ['54', '55'])).
% 3.71/3.92  thf('57', plain,
% 3.71/3.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.71/3.92         ((k2_enumset1 @ X2 @ X1 @ X3 @ X0) = (k2_enumset1 @ X2 @ X3 @ X1 @ X0))),
% 3.71/3.92      inference('demod', [status(thm)], ['32', '47', '56'])).
% 3.71/3.92  thf('58', plain,
% 3.71/3.92      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 3.71/3.92         ((k3_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28)
% 3.71/3.92           = (k2_enumset1 @ X25 @ X26 @ X27 @ X28))),
% 3.71/3.92      inference('cnf', [status(esa)], [t72_enumset1])).
% 3.71/3.92  thf('59', plain,
% 3.71/3.92      (![X19 : $i]: ((k2_tarski @ X19 @ X19) = (k1_tarski @ X19))),
% 3.71/3.92      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.71/3.92  thf('60', plain,
% 3.71/3.92      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 3.71/3.92         ((k3_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6)
% 3.71/3.92           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X3 @ X4) @ 
% 3.71/3.92              (k2_tarski @ X5 @ X6)))),
% 3.71/3.92      inference('cnf', [status(esa)], [l57_enumset1])).
% 3.71/3.92  thf('61', plain,
% 3.71/3.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.71/3.92         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0)
% 3.71/3.92           = (k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0)))),
% 3.71/3.92      inference('sup+', [status(thm)], ['59', '60'])).
% 3.71/3.92  thf('62', plain,
% 3.71/3.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.71/3.92         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0)
% 3.71/3.92           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X2 @ X1) @ (k1_tarski @ X0)))),
% 3.71/3.92      inference('sup+', [status(thm)], ['58', '61'])).
% 3.71/3.92  thf('63', plain,
% 3.71/3.92      (![X20 : $i, X21 : $i]:
% 3.71/3.92         ((k1_enumset1 @ X20 @ X20 @ X21) = (k2_tarski @ X20 @ X21))),
% 3.71/3.92      inference('cnf', [status(esa)], [t70_enumset1])).
% 3.71/3.92  thf('64', plain,
% 3.71/3.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.71/3.92         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0)
% 3.71/3.92           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)))),
% 3.71/3.92      inference('demod', [status(thm)], ['62', '63'])).
% 3.71/3.92  thf('65', plain,
% 3.71/3.92      (![X0 : $i, X1 : $i]:
% 3.71/3.92         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 3.71/3.92      inference('sup+', [status(thm)], ['13', '14'])).
% 3.71/3.92  thf('66', plain,
% 3.71/3.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 3.71/3.92         ((k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4)
% 3.71/3.92           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 3.71/3.92              (k1_tarski @ X4)))),
% 3.71/3.92      inference('sup+', [status(thm)], ['39', '40'])).
% 3.71/3.92  thf('67', plain,
% 3.71/3.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.71/3.92         ((k4_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 @ X2)
% 3.71/3.92           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 3.71/3.92      inference('sup+', [status(thm)], ['65', '66'])).
% 3.71/3.92  thf('68', plain,
% 3.71/3.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.71/3.92         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 3.71/3.92           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 3.71/3.92      inference('sup+', [status(thm)], ['43', '44'])).
% 3.71/3.92  thf('69', plain,
% 3.71/3.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.71/3.92         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 3.71/3.92           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 3.71/3.92      inference('demod', [status(thm)], ['67', '68'])).
% 3.71/3.92  thf('70', plain,
% 3.71/3.92      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.71/3.92         ((k2_enumset1 @ X22 @ X22 @ X23 @ X24)
% 3.71/3.92           = (k1_enumset1 @ X22 @ X23 @ X24))),
% 3.71/3.92      inference('cnf', [status(esa)], [t71_enumset1])).
% 3.71/3.92  thf('71', plain,
% 3.71/3.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.71/3.92         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 3.71/3.92           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 3.71/3.92      inference('sup+', [status(thm)], ['69', '70'])).
% 3.71/3.92  thf('72', plain,
% 3.71/3.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.71/3.92         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 3.71/3.92      inference('demod', [status(thm)], ['64', '71'])).
% 3.71/3.92  thf('73', plain,
% 3.71/3.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.71/3.92         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 3.71/3.92      inference('sup+', [status(thm)], ['48', '49'])).
% 3.71/3.92  thf('74', plain,
% 3.71/3.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.71/3.92         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 3.71/3.92      inference('sup+', [status(thm)], ['72', '73'])).
% 3.71/3.92  thf('75', plain,
% 3.71/3.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.71/3.92         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 3.71/3.92      inference('sup+', [status(thm)], ['48', '49'])).
% 3.71/3.92  thf('76', plain,
% 3.71/3.92      (((k1_enumset1 @ sk_B @ sk_C @ sk_A)
% 3.71/3.92         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 3.71/3.92      inference('demod', [status(thm)], ['25', '57', '74', '75'])).
% 3.71/3.92  thf('77', plain, ($false), inference('simplify', [status(thm)], ['76'])).
% 3.71/3.92  
% 3.71/3.92  % SZS output end Refutation
% 3.71/3.92  
% 3.71/3.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6hMlV7v7q8

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:17 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 424 expanded)
%              Number of leaves         :   24 ( 153 expanded)
%              Depth                    :   18
%              Number of atoms          : 1078 (5084 expanded)
%              Number of equality atoms :   71 ( 407 expanded)
%              Maximal formula depth    :   19 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(t67_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
        ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
        = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ) ),
    inference('cnf.neg',[status(esa)],[t67_enumset1])).

thf('0',plain,(
    ( k6_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H )
 != ( k2_xboole_0 @ ( k4_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k2_tarski @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_tarski @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X12 ) @ ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t43_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k1_enumset1 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k2_tarski @ X14 @ X15 ) @ ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k2_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k2_enumset1 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X17 @ X18 @ X19 ) @ ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('9',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k2_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k2_enumset1 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X17 @ X18 @ X19 ) @ ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('13',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k2_enumset1 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X17 @ X18 @ X19 ) @ ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('14',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k1_enumset1 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k2_tarski @ X14 @ X15 ) @ ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('15',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_tarski @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X12 ) @ ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('16',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_tarski @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X12 ) @ ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('17',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k2_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k1_enumset1 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k2_tarski @ X14 @ X15 ) @ ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k2_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','23'])).

thf('25',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k2_enumset1 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X17 @ X18 @ X19 ) @ ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k2_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','28'])).

thf(t50_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ) )).

thf('30',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( k3_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X21 @ X22 @ X23 @ X24 ) @ ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','30','37'])).

thf('39',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k2_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X5 )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','40'])).

thf(t55_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ) )).

thf('42',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k4_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 ) @ ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t55_enumset1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('46',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k2_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X6 )
      = ( k2_xboole_0 @ ( k2_tarski @ X5 @ X4 ) @ ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X6 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k4_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X7 @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf('49',plain,(
    ( k6_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H )
 != ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k4_enumset1 @ sk_C_1 @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(demod,[status(thm)],['0','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('51',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k2_enumset1 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X17 @ X18 @ X19 ) @ ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('52',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k2_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X5 )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X7 @ X6 ) @ ( k2_xboole_0 @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf(t66_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_enumset1 @ F @ G @ H ) ) ) )).

thf('57',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( k6_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 ) @ ( k1_enumset1 @ X37 @ X38 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t66_enumset1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X7 @ X6 ) @ ( k2_xboole_0 @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','43'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X7 @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ( k6_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H )
 != ( k6_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['49','60'])).

thf('62',plain,(
    $false ),
    inference(simplify,[status(thm)],['61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6hMlV7v7q8
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:26:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.58  % Solved by: fo/fo7.sh
% 0.36/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.58  % done 127 iterations in 0.122s
% 0.36/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.58  % SZS output start Refutation
% 0.36/0.58  thf(sk_D_type, type, sk_D: $i).
% 0.36/0.58  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.36/0.58  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.36/0.58                                           $i > $i).
% 0.36/0.58  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.36/0.58  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.36/0.58  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.36/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.58  thf(sk_F_type, type, sk_F: $i).
% 0.36/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.58  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.36/0.58  thf(sk_G_type, type, sk_G: $i).
% 0.36/0.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.58  thf(sk_E_type, type, sk_E: $i).
% 0.36/0.58  thf(sk_H_type, type, sk_H: $i).
% 0.36/0.58  thf(t67_enumset1, conjecture,
% 0.36/0.58    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.36/0.58     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.36/0.58       ( k2_xboole_0 @
% 0.36/0.58         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ))).
% 0.36/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.58    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.36/0.58        ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.36/0.58          ( k2_xboole_0 @
% 0.36/0.58            ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ) )),
% 0.36/0.58    inference('cnf.neg', [status(esa)], [t67_enumset1])).
% 0.36/0.58  thf('0', plain,
% 0.36/0.58      (((k6_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.36/0.58         != (k2_xboole_0 @ 
% 0.36/0.58             (k4_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.36/0.58             (k2_tarski @ sk_G @ sk_H)))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf(t41_enumset1, axiom,
% 0.36/0.58    (![A:$i,B:$i]:
% 0.36/0.58     ( ( k2_tarski @ A @ B ) =
% 0.36/0.58       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.36/0.58  thf('1', plain,
% 0.36/0.58      (![X12 : $i, X13 : $i]:
% 0.36/0.58         ((k2_tarski @ X12 @ X13)
% 0.36/0.58           = (k2_xboole_0 @ (k1_tarski @ X12) @ (k1_tarski @ X13)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.36/0.58  thf(t43_enumset1, axiom,
% 0.36/0.58    (![A:$i,B:$i,C:$i]:
% 0.36/0.58     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.36/0.58       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ))).
% 0.36/0.58  thf('2', plain,
% 0.36/0.58      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.36/0.58         ((k1_enumset1 @ X14 @ X15 @ X16)
% 0.36/0.58           = (k2_xboole_0 @ (k2_tarski @ X14 @ X15) @ (k1_tarski @ X16)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.36/0.58  thf(t4_xboole_1, axiom,
% 0.36/0.58    (![A:$i,B:$i,C:$i]:
% 0.36/0.58     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.36/0.58       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.36/0.58  thf('3', plain,
% 0.36/0.58      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.58         ((k2_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ X6)
% 0.36/0.58           = (k2_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.36/0.58  thf('4', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.58         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.36/0.58           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ 
% 0.36/0.58              (k2_xboole_0 @ (k1_tarski @ X0) @ X3)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['2', '3'])).
% 0.36/0.58  thf('5', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.58         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 0.36/0.58           = (k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['1', '4'])).
% 0.36/0.58  thf(t46_enumset1, axiom,
% 0.36/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.58     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.36/0.58       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.36/0.58  thf('6', plain,
% 0.36/0.58      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.36/0.58         ((k2_enumset1 @ X17 @ X18 @ X19 @ X20)
% 0.36/0.58           = (k2_xboole_0 @ (k1_enumset1 @ X17 @ X18 @ X19) @ (k1_tarski @ X20)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.36/0.58  thf('7', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.58         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 0.36/0.58           = (k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['5', '6'])).
% 0.36/0.58  thf('8', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.58         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 0.36/0.58           = (k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['5', '6'])).
% 0.36/0.58  thf('9', plain,
% 0.36/0.58      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.58         ((k2_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ X6)
% 0.36/0.58           = (k2_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.36/0.58  thf('10', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.58         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4)
% 0.36/0.58           = (k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ 
% 0.36/0.58              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X4)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['8', '9'])).
% 0.36/0.58  thf('11', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.58         ((k2_xboole_0 @ (k2_enumset1 @ X5 @ X4 @ X3 @ X2) @ 
% 0.36/0.58           (k2_tarski @ X1 @ X0))
% 0.36/0.58           = (k2_xboole_0 @ (k2_tarski @ X5 @ X4) @ 
% 0.36/0.58              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['7', '10'])).
% 0.36/0.58  thf('12', plain,
% 0.36/0.58      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.36/0.58         ((k2_enumset1 @ X17 @ X18 @ X19 @ X20)
% 0.36/0.58           = (k2_xboole_0 @ (k1_enumset1 @ X17 @ X18 @ X19) @ (k1_tarski @ X20)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.36/0.58  thf('13', plain,
% 0.36/0.58      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.36/0.58         ((k2_enumset1 @ X17 @ X18 @ X19 @ X20)
% 0.36/0.58           = (k2_xboole_0 @ (k1_enumset1 @ X17 @ X18 @ X19) @ (k1_tarski @ X20)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.36/0.58  thf('14', plain,
% 0.36/0.58      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.36/0.58         ((k1_enumset1 @ X14 @ X15 @ X16)
% 0.36/0.58           = (k2_xboole_0 @ (k2_tarski @ X14 @ X15) @ (k1_tarski @ X16)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.36/0.58  thf('15', plain,
% 0.36/0.58      (![X12 : $i, X13 : $i]:
% 0.36/0.58         ((k2_tarski @ X12 @ X13)
% 0.36/0.58           = (k2_xboole_0 @ (k1_tarski @ X12) @ (k1_tarski @ X13)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.36/0.58  thf('16', plain,
% 0.36/0.58      (![X12 : $i, X13 : $i]:
% 0.36/0.58         ((k2_tarski @ X12 @ X13)
% 0.36/0.58           = (k2_xboole_0 @ (k1_tarski @ X12) @ (k1_tarski @ X13)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.36/0.58  thf('17', plain,
% 0.36/0.58      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.58         ((k2_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ X6)
% 0.36/0.58           = (k2_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.36/0.58  thf('18', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.58         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.36/0.58           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.36/0.58              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['16', '17'])).
% 0.36/0.58  thf('19', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.58         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.36/0.58           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['15', '18'])).
% 0.36/0.58  thf('20', plain,
% 0.36/0.58      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.36/0.58         ((k1_enumset1 @ X14 @ X15 @ X16)
% 0.36/0.58           = (k2_xboole_0 @ (k2_tarski @ X14 @ X15) @ (k1_tarski @ X16)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.36/0.58  thf('21', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.58         ((k1_enumset1 @ X2 @ X1 @ X0)
% 0.36/0.58           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.36/0.58      inference('demod', [status(thm)], ['19', '20'])).
% 0.36/0.58  thf('22', plain,
% 0.36/0.58      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.58         ((k2_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ X6)
% 0.36/0.58           = (k2_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.36/0.58  thf('23', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.58         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.36/0.58           = (k2_xboole_0 @ (k1_tarski @ X2) @ 
% 0.36/0.58              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X3)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['21', '22'])).
% 0.36/0.58  thf('24', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.58         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 0.36/0.58           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['14', '23'])).
% 0.36/0.58  thf('25', plain,
% 0.36/0.58      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.36/0.58         ((k2_enumset1 @ X17 @ X18 @ X19 @ X20)
% 0.36/0.58           = (k2_xboole_0 @ (k1_enumset1 @ X17 @ X18 @ X19) @ (k1_tarski @ X20)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.36/0.58  thf('26', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.58         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 0.36/0.58           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.36/0.58      inference('demod', [status(thm)], ['24', '25'])).
% 0.36/0.58  thf('27', plain,
% 0.36/0.58      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.58         ((k2_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ X6)
% 0.36/0.58           = (k2_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.36/0.58  thf('28', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.58         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4)
% 0.36/0.58           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 0.36/0.58              (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X4)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['26', '27'])).
% 0.36/0.58  thf('29', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.58         ((k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 0.36/0.58           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 0.36/0.58              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['13', '28'])).
% 0.36/0.58  thf(t50_enumset1, axiom,
% 0.36/0.58    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.36/0.58     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.36/0.58       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ))).
% 0.36/0.58  thf('30', plain,
% 0.36/0.58      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.36/0.58         ((k3_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25)
% 0.36/0.58           = (k2_xboole_0 @ (k2_enumset1 @ X21 @ X22 @ X23 @ X24) @ 
% 0.36/0.58              (k1_tarski @ X25)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t50_enumset1])).
% 0.36/0.58  thf('31', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.58         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 0.36/0.58           = (k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['5', '6'])).
% 0.36/0.58  thf('32', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.58         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.36/0.58           = (k2_xboole_0 @ (k1_tarski @ X2) @ 
% 0.36/0.58              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X3)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['21', '22'])).
% 0.36/0.58  thf('33', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.58         ((k2_xboole_0 @ (k1_enumset1 @ X4 @ X3 @ X2) @ (k2_tarski @ X1 @ X0))
% 0.36/0.58           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 0.36/0.58              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['31', '32'])).
% 0.36/0.58  thf('34', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.58         ((k1_enumset1 @ X2 @ X1 @ X0)
% 0.36/0.58           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.36/0.58      inference('demod', [status(thm)], ['19', '20'])).
% 0.36/0.58  thf('35', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.58         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.36/0.58           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ 
% 0.36/0.58              (k2_xboole_0 @ (k1_tarski @ X0) @ X3)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['2', '3'])).
% 0.36/0.58  thf('36', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.58         ((k2_xboole_0 @ (k1_enumset1 @ X4 @ X3 @ X2) @ (k2_tarski @ X1 @ X0))
% 0.36/0.58           = (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ 
% 0.36/0.58              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['34', '35'])).
% 0.36/0.58  thf('37', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.58         ((k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.36/0.58           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 0.36/0.58              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 0.36/0.58      inference('demod', [status(thm)], ['33', '36'])).
% 0.36/0.58  thf('38', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.58         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.36/0.58           = (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ 
% 0.36/0.58              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.36/0.58      inference('demod', [status(thm)], ['29', '30', '37'])).
% 0.36/0.58  thf('39', plain,
% 0.36/0.58      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.58         ((k2_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ X6)
% 0.36/0.58           = (k2_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.36/0.58  thf('40', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.58         ((k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ X5)
% 0.36/0.58           = (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ 
% 0.36/0.58              (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X5)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['38', '39'])).
% 0.36/0.58  thf('41', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.58         ((k2_xboole_0 @ (k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 0.36/0.58           (k1_tarski @ X0))
% 0.36/0.58           = (k2_xboole_0 @ (k2_tarski @ X5 @ X4) @ 
% 0.36/0.58              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['12', '40'])).
% 0.36/0.58  thf(t55_enumset1, axiom,
% 0.36/0.58    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.36/0.58     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.36/0.58       ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ))).
% 0.36/0.58  thf('42', plain,
% 0.36/0.58      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.36/0.58         ((k4_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31)
% 0.36/0.58           = (k2_xboole_0 @ (k3_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30) @ 
% 0.36/0.58              (k1_tarski @ X31)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t55_enumset1])).
% 0.36/0.58  thf('43', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.58         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.36/0.58           = (k2_xboole_0 @ (k2_tarski @ X5 @ X4) @ 
% 0.36/0.58              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['41', '42'])).
% 0.36/0.58  thf('44', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.58         ((k2_xboole_0 @ (k2_enumset1 @ X5 @ X4 @ X3 @ X2) @ 
% 0.36/0.58           (k2_tarski @ X1 @ X0)) = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.36/0.58      inference('demod', [status(thm)], ['11', '43'])).
% 0.36/0.58  thf('45', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.58         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.36/0.58           = (k2_xboole_0 @ (k2_tarski @ X5 @ X4) @ 
% 0.36/0.58              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['41', '42'])).
% 0.36/0.58  thf('46', plain,
% 0.36/0.58      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.58         ((k2_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ X6)
% 0.36/0.58           = (k2_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.36/0.58  thf('47', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.58         ((k2_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ X6)
% 0.36/0.58           = (k2_xboole_0 @ (k2_tarski @ X5 @ X4) @ 
% 0.36/0.58              (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X6)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['45', '46'])).
% 0.36/0.58  thf('48', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.36/0.58         ((k2_xboole_0 @ (k4_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2) @ 
% 0.36/0.58           (k2_tarski @ X1 @ X0))
% 0.36/0.58           = (k2_xboole_0 @ (k2_tarski @ X7 @ X6) @ 
% 0.36/0.58              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['44', '47'])).
% 0.36/0.58  thf('49', plain,
% 0.36/0.58      (((k6_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.36/0.58         != (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 0.36/0.58             (k4_enumset1 @ sk_C_1 @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)))),
% 0.36/0.58      inference('demod', [status(thm)], ['0', '48'])).
% 0.36/0.58  thf('50', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.58         ((k1_enumset1 @ X2 @ X1 @ X0)
% 0.36/0.58           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.36/0.58      inference('demod', [status(thm)], ['19', '20'])).
% 0.36/0.58  thf('51', plain,
% 0.36/0.58      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.36/0.58         ((k2_enumset1 @ X17 @ X18 @ X19 @ X20)
% 0.36/0.58           = (k2_xboole_0 @ (k1_enumset1 @ X17 @ X18 @ X19) @ (k1_tarski @ X20)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.36/0.58  thf('52', plain,
% 0.36/0.58      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.58         ((k2_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ X6)
% 0.36/0.58           = (k2_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.36/0.58  thf('53', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.58         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4)
% 0.36/0.58           = (k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ 
% 0.36/0.58              (k2_xboole_0 @ (k1_tarski @ X0) @ X4)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['51', '52'])).
% 0.36/0.58  thf('54', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.58         ((k2_xboole_0 @ (k2_enumset1 @ X5 @ X4 @ X3 @ X2) @ 
% 0.36/0.58           (k2_tarski @ X1 @ X0))
% 0.36/0.58           = (k2_xboole_0 @ (k1_enumset1 @ X5 @ X4 @ X3) @ 
% 0.36/0.58              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['50', '53'])).
% 0.36/0.58  thf('55', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.58         ((k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ X5)
% 0.36/0.58           = (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ 
% 0.36/0.58              (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X5)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['38', '39'])).
% 0.36/0.58  thf('56', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.36/0.58         ((k2_xboole_0 @ (k3_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3) @ 
% 0.36/0.58           (k1_enumset1 @ X2 @ X1 @ X0))
% 0.36/0.58           = (k2_xboole_0 @ (k2_tarski @ X7 @ X6) @ 
% 0.36/0.58              (k2_xboole_0 @ (k2_enumset1 @ X5 @ X4 @ X3 @ X2) @ 
% 0.36/0.58               (k2_tarski @ X1 @ X0))))),
% 0.36/0.58      inference('sup+', [status(thm)], ['54', '55'])).
% 0.36/0.58  thf(t66_enumset1, axiom,
% 0.36/0.58    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.36/0.58     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.36/0.58       ( k2_xboole_0 @
% 0.36/0.58         ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_enumset1 @ F @ G @ H ) ) ))).
% 0.36/0.58  thf('57', plain,
% 0.36/0.58      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, 
% 0.36/0.58         X39 : $i]:
% 0.36/0.58         ((k6_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 @ X39)
% 0.36/0.58           = (k2_xboole_0 @ (k3_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36) @ 
% 0.36/0.58              (k1_enumset1 @ X37 @ X38 @ X39)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t66_enumset1])).
% 0.36/0.58  thf('58', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.36/0.58         ((k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.36/0.58           = (k2_xboole_0 @ (k2_tarski @ X7 @ X6) @ 
% 0.36/0.58              (k2_xboole_0 @ (k2_enumset1 @ X5 @ X4 @ X3 @ X2) @ 
% 0.36/0.58               (k2_tarski @ X1 @ X0))))),
% 0.36/0.58      inference('demod', [status(thm)], ['56', '57'])).
% 0.36/0.58  thf('59', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.58         ((k2_xboole_0 @ (k2_enumset1 @ X5 @ X4 @ X3 @ X2) @ 
% 0.36/0.58           (k2_tarski @ X1 @ X0)) = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.36/0.58      inference('demod', [status(thm)], ['11', '43'])).
% 0.36/0.58  thf('60', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.36/0.58         ((k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.36/0.58           = (k2_xboole_0 @ (k2_tarski @ X7 @ X6) @ 
% 0.36/0.58              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.36/0.58      inference('demod', [status(thm)], ['58', '59'])).
% 0.36/0.58  thf('61', plain,
% 0.36/0.58      (((k6_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.36/0.58         != (k6_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F @ sk_G @ 
% 0.36/0.58             sk_H))),
% 0.36/0.58      inference('demod', [status(thm)], ['49', '60'])).
% 0.36/0.58  thf('62', plain, ($false), inference('simplify', [status(thm)], ['61'])).
% 0.36/0.58  
% 0.36/0.58  % SZS output end Refutation
% 0.36/0.58  
% 0.36/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

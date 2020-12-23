%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TTcIj4nZwa

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:55 EST 2020

% Result     : Theorem 18.99s
% Output     : Refutation 18.99s
% Verified   : 
% Statistics : Number of formulae       :  204 (1806 expanded)
%              Number of leaves         :   20 ( 630 expanded)
%              Depth                    :   30
%              Number of atoms          : 1791 (14183 expanded)
%              Number of equality atoms :  196 (1798 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t94_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ A @ B )
        = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t94_xboole_1])).

thf('0',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('2',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('10',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('15',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','16'])).

thf('18',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('21',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('26',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('27',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t24_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) ) )).

thf('31',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ ( k2_xboole_0 @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t24_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['24','36'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('38',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k4_xboole_0 @ X26 @ ( k4_xboole_0 @ X27 @ X28 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X26 @ X27 ) @ ( k3_xboole_0 @ X26 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X2 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X2 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['19','41'])).

thf('43',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('44',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('45',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('51',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('53',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('59',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ ( k2_xboole_0 @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t24_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('61',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['59','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','15'])).

thf('68',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['69','70','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('76',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('79',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('80',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X23 @ X24 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['65','66','74','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['58','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('85',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k4_xboole_0 @ X26 @ ( k4_xboole_0 @ X27 @ X28 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X26 @ X27 ) @ ( k3_xboole_0 @ X26 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['83','84','85','86'])).

thf('88',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['57','89'])).

thf('91',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k4_xboole_0 @ X26 @ ( k4_xboole_0 @ X27 @ X28 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X26 @ X27 ) @ ( k3_xboole_0 @ X26 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','15'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['90','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['65','66','74','81'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['50','98'])).

thf('100',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['49','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['42','43','44','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','35'])).

thf('107',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['105','115'])).

thf('117',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k4_xboole_0 @ X26 @ ( k4_xboole_0 @ X27 @ X28 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X26 @ X27 ) @ ( k3_xboole_0 @ X26 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('118',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('119',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ ( k2_xboole_0 @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t24_xboole_1])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['117','122'])).

thf('124',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('125',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['124','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['24','36'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('132',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['130','133'])).

thf('135',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('138',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['123','134','135','136','137','138'])).

thf('140',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('141',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X23 @ X24 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('145',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X23 @ X24 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['142','143','148','149'])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['139','150'])).

thf('152',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['154','155','156','157'])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['151','160'])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['116','161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['42','43','44','104'])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['69','70','73'])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('171',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['151','160'])).

thf('172',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('173',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k4_xboole_0 @ X26 @ ( k4_xboole_0 @ X27 @ X28 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X26 @ X27 ) @ ( k3_xboole_0 @ X26 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('174',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['169','170','171','174','175'])).

thf('177',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['162','178'])).

thf('180',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('181',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','179','180'])).

thf('182',plain,(
    $false ),
    inference(simplify,[status(thm)],['181'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TTcIj4nZwa
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:23:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 18.99/19.19  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 18.99/19.19  % Solved by: fo/fo7.sh
% 18.99/19.19  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 18.99/19.19  % done 10432 iterations in 18.727s
% 18.99/19.19  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 18.99/19.19  % SZS output start Refutation
% 18.99/19.19  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 18.99/19.19  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 18.99/19.19  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 18.99/19.19  thf(sk_B_type, type, sk_B: $i).
% 18.99/19.19  thf(sk_A_type, type, sk_A: $i).
% 18.99/19.19  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 18.99/19.19  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 18.99/19.19  thf(t94_xboole_1, conjecture,
% 18.99/19.19    (![A:$i,B:$i]:
% 18.99/19.19     ( ( k2_xboole_0 @ A @ B ) =
% 18.99/19.19       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 18.99/19.19  thf(zf_stmt_0, negated_conjecture,
% 18.99/19.19    (~( ![A:$i,B:$i]:
% 18.99/19.19        ( ( k2_xboole_0 @ A @ B ) =
% 18.99/19.19          ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 18.99/19.19    inference('cnf.neg', [status(esa)], [t94_xboole_1])).
% 18.99/19.19  thf('0', plain,
% 18.99/19.19      (((k2_xboole_0 @ sk_A @ sk_B)
% 18.99/19.19         != (k5_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ 
% 18.99/19.19             (k3_xboole_0 @ sk_A @ sk_B)))),
% 18.99/19.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.99/19.19  thf(d6_xboole_0, axiom,
% 18.99/19.19    (![A:$i,B:$i]:
% 18.99/19.19     ( ( k5_xboole_0 @ A @ B ) =
% 18.99/19.19       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 18.99/19.19  thf('1', plain,
% 18.99/19.19      (![X4 : $i, X5 : $i]:
% 18.99/19.19         ((k5_xboole_0 @ X4 @ X5)
% 18.99/19.19           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 18.99/19.19      inference('cnf', [status(esa)], [d6_xboole_0])).
% 18.99/19.19  thf(t3_boole, axiom,
% 18.99/19.19    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 18.99/19.19  thf('2', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 18.99/19.19      inference('cnf', [status(esa)], [t3_boole])).
% 18.99/19.19  thf(t48_xboole_1, axiom,
% 18.99/19.19    (![A:$i,B:$i]:
% 18.99/19.19     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 18.99/19.19  thf('3', plain,
% 18.99/19.19      (![X21 : $i, X22 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 18.99/19.19           = (k3_xboole_0 @ X21 @ X22))),
% 18.99/19.19      inference('cnf', [status(esa)], [t48_xboole_1])).
% 18.99/19.19  thf('4', plain,
% 18.99/19.19      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 18.99/19.19      inference('sup+', [status(thm)], ['2', '3'])).
% 18.99/19.19  thf(t2_boole, axiom,
% 18.99/19.19    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 18.99/19.19  thf('5', plain,
% 18.99/19.19      (![X9 : $i]: ((k3_xboole_0 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 18.99/19.19      inference('cnf', [status(esa)], [t2_boole])).
% 18.99/19.19  thf('6', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 18.99/19.19      inference('demod', [status(thm)], ['4', '5'])).
% 18.99/19.19  thf(t41_xboole_1, axiom,
% 18.99/19.19    (![A:$i,B:$i,C:$i]:
% 18.99/19.19     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 18.99/19.19       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 18.99/19.19  thf('7', plain,
% 18.99/19.19      (![X13 : $i, X14 : $i, X15 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 18.99/19.19           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 18.99/19.19      inference('cnf', [status(esa)], [t41_xboole_1])).
% 18.99/19.19  thf('8', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 18.99/19.19           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 18.99/19.19      inference('sup+', [status(thm)], ['6', '7'])).
% 18.99/19.19  thf(commutativity_k3_xboole_0, axiom,
% 18.99/19.19    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 18.99/19.19  thf('9', plain,
% 18.99/19.19      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 18.99/19.19      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 18.99/19.19  thf('10', plain,
% 18.99/19.19      (![X9 : $i]: ((k3_xboole_0 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 18.99/19.19      inference('cnf', [status(esa)], [t2_boole])).
% 18.99/19.19  thf('11', plain,
% 18.99/19.19      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 18.99/19.19      inference('sup+', [status(thm)], ['9', '10'])).
% 18.99/19.19  thf(t47_xboole_1, axiom,
% 18.99/19.19    (![A:$i,B:$i]:
% 18.99/19.19     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 18.99/19.19  thf('12', plain,
% 18.99/19.19      (![X19 : $i, X20 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ X19 @ (k3_xboole_0 @ X19 @ X20))
% 18.99/19.19           = (k4_xboole_0 @ X19 @ X20))),
% 18.99/19.19      inference('cnf', [status(esa)], [t47_xboole_1])).
% 18.99/19.19  thf('13', plain,
% 18.99/19.19      (![X0 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 18.99/19.19           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 18.99/19.19      inference('sup+', [status(thm)], ['11', '12'])).
% 18.99/19.19  thf('14', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 18.99/19.19      inference('cnf', [status(esa)], [t3_boole])).
% 18.99/19.19  thf('15', plain,
% 18.99/19.19      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 18.99/19.19      inference('demod', [status(thm)], ['13', '14'])).
% 18.99/19.19  thf('16', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 18.99/19.19      inference('demod', [status(thm)], ['8', '15'])).
% 18.99/19.19  thf('17', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k1_xboole_0)
% 18.99/19.19           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)))),
% 18.99/19.19      inference('sup+', [status(thm)], ['1', '16'])).
% 18.99/19.19  thf('18', plain,
% 18.99/19.19      (![X13 : $i, X14 : $i, X15 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 18.99/19.19           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 18.99/19.19      inference('cnf', [status(esa)], [t41_xboole_1])).
% 18.99/19.19  thf('19', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k1_xboole_0)
% 18.99/19.19           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 18.99/19.19      inference('demod', [status(thm)], ['17', '18'])).
% 18.99/19.19  thf(t40_xboole_1, axiom,
% 18.99/19.19    (![A:$i,B:$i]:
% 18.99/19.19     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 18.99/19.19  thf('20', plain,
% 18.99/19.19      (![X11 : $i, X12 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ X12)
% 18.99/19.19           = (k4_xboole_0 @ X11 @ X12))),
% 18.99/19.19      inference('cnf', [status(esa)], [t40_xboole_1])).
% 18.99/19.19  thf('21', plain,
% 18.99/19.19      (![X21 : $i, X22 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 18.99/19.19           = (k3_xboole_0 @ X21 @ X22))),
% 18.99/19.19      inference('cnf', [status(esa)], [t48_xboole_1])).
% 18.99/19.19  thf('22', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 18.99/19.19           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 18.99/19.19      inference('sup+', [status(thm)], ['20', '21'])).
% 18.99/19.19  thf('23', plain,
% 18.99/19.19      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 18.99/19.19      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 18.99/19.19  thf('24', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 18.99/19.19           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 18.99/19.19      inference('demod', [status(thm)], ['22', '23'])).
% 18.99/19.19  thf(commutativity_k2_xboole_0, axiom,
% 18.99/19.19    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 18.99/19.19  thf('25', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 18.99/19.19      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 18.99/19.19  thf('26', plain,
% 18.99/19.19      (![X11 : $i, X12 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ X12)
% 18.99/19.19           = (k4_xboole_0 @ X11 @ X12))),
% 18.99/19.19      inference('cnf', [status(esa)], [t40_xboole_1])).
% 18.99/19.19  thf('27', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 18.99/19.19      inference('cnf', [status(esa)], [t3_boole])).
% 18.99/19.19  thf('28', plain,
% 18.99/19.19      (![X0 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 18.99/19.19      inference('sup+', [status(thm)], ['26', '27'])).
% 18.99/19.19  thf('29', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 18.99/19.19      inference('cnf', [status(esa)], [t3_boole])).
% 18.99/19.19  thf('30', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 18.99/19.19      inference('sup+', [status(thm)], ['28', '29'])).
% 18.99/19.19  thf(t24_xboole_1, axiom,
% 18.99/19.19    (![A:$i,B:$i,C:$i]:
% 18.99/19.19     ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 18.99/19.19       ( k3_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) ))).
% 18.99/19.19  thf('31', plain,
% 18.99/19.19      (![X6 : $i, X7 : $i, X8 : $i]:
% 18.99/19.19         ((k2_xboole_0 @ X6 @ (k3_xboole_0 @ X7 @ X8))
% 18.99/19.19           = (k3_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ (k2_xboole_0 @ X6 @ X8)))),
% 18.99/19.19      inference('cnf', [status(esa)], [t24_xboole_1])).
% 18.99/19.19  thf('32', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ X1))
% 18.99/19.19           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 18.99/19.19      inference('sup+', [status(thm)], ['30', '31'])).
% 18.99/19.19  thf('33', plain,
% 18.99/19.19      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 18.99/19.19      inference('sup+', [status(thm)], ['9', '10'])).
% 18.99/19.19  thf('34', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 18.99/19.19      inference('sup+', [status(thm)], ['28', '29'])).
% 18.99/19.19  thf('35', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 18.99/19.19      inference('demod', [status(thm)], ['32', '33', '34'])).
% 18.99/19.19  thf('36', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 18.99/19.19      inference('sup+', [status(thm)], ['25', '35'])).
% 18.99/19.19  thf('37', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 18.99/19.19           = (X0))),
% 18.99/19.19      inference('demod', [status(thm)], ['24', '36'])).
% 18.99/19.19  thf(t52_xboole_1, axiom,
% 18.99/19.19    (![A:$i,B:$i,C:$i]:
% 18.99/19.19     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 18.99/19.19       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 18.99/19.19  thf('38', plain,
% 18.99/19.19      (![X26 : $i, X27 : $i, X28 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ X26 @ (k4_xboole_0 @ X27 @ X28))
% 18.99/19.19           = (k2_xboole_0 @ (k4_xboole_0 @ X26 @ X27) @ 
% 18.99/19.19              (k3_xboole_0 @ X26 @ X28)))),
% 18.99/19.19      inference('cnf', [status(esa)], [t52_xboole_1])).
% 18.99/19.19  thf('39', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ (k2_xboole_0 @ X2 @ X0) @ 
% 18.99/19.19           (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1))
% 18.99/19.19           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ (k2_xboole_0 @ X2 @ X0) @ X1)))),
% 18.99/19.19      inference('sup+', [status(thm)], ['37', '38'])).
% 18.99/19.19  thf('40', plain,
% 18.99/19.19      (![X13 : $i, X14 : $i, X15 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 18.99/19.19           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 18.99/19.19      inference('cnf', [status(esa)], [t41_xboole_1])).
% 18.99/19.19  thf('41', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ (k2_xboole_0 @ X2 @ X0) @ 
% 18.99/19.19           (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1)))
% 18.99/19.19           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ (k2_xboole_0 @ X2 @ X0) @ X1)))),
% 18.99/19.19      inference('demod', [status(thm)], ['39', '40'])).
% 18.99/19.19  thf('42', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 18.99/19.19           = (k2_xboole_0 @ X0 @ 
% 18.99/19.19              (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))))),
% 18.99/19.19      inference('sup+', [status(thm)], ['19', '41'])).
% 18.99/19.19  thf('43', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 18.99/19.19      inference('cnf', [status(esa)], [t3_boole])).
% 18.99/19.19  thf('44', plain,
% 18.99/19.19      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 18.99/19.19      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 18.99/19.19  thf('45', plain,
% 18.99/19.19      (![X4 : $i, X5 : $i]:
% 18.99/19.19         ((k5_xboole_0 @ X4 @ X5)
% 18.99/19.19           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 18.99/19.19      inference('cnf', [status(esa)], [d6_xboole_0])).
% 18.99/19.19  thf('46', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 18.99/19.19      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 18.99/19.19  thf('47', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 18.99/19.19           = (k5_xboole_0 @ X1 @ X0))),
% 18.99/19.19      inference('sup+', [status(thm)], ['45', '46'])).
% 18.99/19.19  thf('48', plain,
% 18.99/19.19      (![X4 : $i, X5 : $i]:
% 18.99/19.19         ((k5_xboole_0 @ X4 @ X5)
% 18.99/19.19           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 18.99/19.19      inference('cnf', [status(esa)], [d6_xboole_0])).
% 18.99/19.19  thf('49', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 18.99/19.19      inference('sup+', [status(thm)], ['47', '48'])).
% 18.99/19.19  thf('50', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 18.99/19.19      inference('sup+', [status(thm)], ['47', '48'])).
% 18.99/19.19  thf('51', plain,
% 18.99/19.19      (![X4 : $i, X5 : $i]:
% 18.99/19.19         ((k5_xboole_0 @ X4 @ X5)
% 18.99/19.19           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 18.99/19.19      inference('cnf', [status(esa)], [d6_xboole_0])).
% 18.99/19.19  thf('52', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 18.99/19.19      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 18.99/19.19  thf('53', plain,
% 18.99/19.19      (![X11 : $i, X12 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ X12)
% 18.99/19.19           = (k4_xboole_0 @ X11 @ X12))),
% 18.99/19.19      inference('cnf', [status(esa)], [t40_xboole_1])).
% 18.99/19.19  thf('54', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 18.99/19.19           = (k4_xboole_0 @ X0 @ X1))),
% 18.99/19.19      inference('sup+', [status(thm)], ['52', '53'])).
% 18.99/19.19  thf('55', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 18.99/19.19           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 18.99/19.19      inference('sup+', [status(thm)], ['51', '54'])).
% 18.99/19.19  thf('56', plain,
% 18.99/19.19      (![X13 : $i, X14 : $i, X15 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 18.99/19.19           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 18.99/19.19      inference('cnf', [status(esa)], [t41_xboole_1])).
% 18.99/19.19  thf('57', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 18.99/19.19           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))))),
% 18.99/19.19      inference('demod', [status(thm)], ['55', '56'])).
% 18.99/19.19  thf('58', plain,
% 18.99/19.19      (![X21 : $i, X22 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 18.99/19.19           = (k3_xboole_0 @ X21 @ X22))),
% 18.99/19.19      inference('cnf', [status(esa)], [t48_xboole_1])).
% 18.99/19.19  thf('59', plain,
% 18.99/19.19      (![X6 : $i, X7 : $i, X8 : $i]:
% 18.99/19.19         ((k2_xboole_0 @ X6 @ (k3_xboole_0 @ X7 @ X8))
% 18.99/19.19           = (k3_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ (k2_xboole_0 @ X6 @ X8)))),
% 18.99/19.19      inference('cnf', [status(esa)], [t24_xboole_1])).
% 18.99/19.19  thf('60', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k1_xboole_0)
% 18.99/19.19           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 18.99/19.19      inference('demod', [status(thm)], ['17', '18'])).
% 18.99/19.19  thf('61', plain,
% 18.99/19.19      (![X21 : $i, X22 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 18.99/19.19           = (k3_xboole_0 @ X21 @ X22))),
% 18.99/19.19      inference('cnf', [status(esa)], [t48_xboole_1])).
% 18.99/19.19  thf('62', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 18.99/19.19           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 18.99/19.19      inference('sup+', [status(thm)], ['60', '61'])).
% 18.99/19.19  thf('63', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 18.99/19.19      inference('cnf', [status(esa)], [t3_boole])).
% 18.99/19.19  thf('64', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((X1)
% 18.99/19.19           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 18.99/19.19      inference('demod', [status(thm)], ['62', '63'])).
% 18.99/19.19  thf('65', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k2_xboole_0 @ X0 @ X1)
% 18.99/19.19           = (k2_xboole_0 @ X0 @ 
% 18.99/19.19              (k3_xboole_0 @ X1 @ (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))))),
% 18.99/19.19      inference('sup+', [status(thm)], ['59', '64'])).
% 18.99/19.19  thf('66', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 18.99/19.19      inference('sup+', [status(thm)], ['47', '48'])).
% 18.99/19.19  thf('67', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 18.99/19.19      inference('demod', [status(thm)], ['8', '15'])).
% 18.99/19.19  thf('68', plain,
% 18.99/19.19      (![X4 : $i, X5 : $i]:
% 18.99/19.19         ((k5_xboole_0 @ X4 @ X5)
% 18.99/19.19           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 18.99/19.19      inference('cnf', [status(esa)], [d6_xboole_0])).
% 18.99/19.19  thf('69', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 18.99/19.19           = (k2_xboole_0 @ k1_xboole_0 @ 
% 18.99/19.19              (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)))),
% 18.99/19.19      inference('sup+', [status(thm)], ['67', '68'])).
% 18.99/19.19  thf('70', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 18.99/19.19           = (k4_xboole_0 @ X0 @ X1))),
% 18.99/19.19      inference('sup+', [status(thm)], ['52', '53'])).
% 18.99/19.19  thf('71', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 18.99/19.19      inference('sup+', [status(thm)], ['28', '29'])).
% 18.99/19.19  thf('72', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 18.99/19.19      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 18.99/19.19  thf('73', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 18.99/19.19      inference('sup+', [status(thm)], ['71', '72'])).
% 18.99/19.19  thf('74', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 18.99/19.19           = (k4_xboole_0 @ X1 @ X0))),
% 18.99/19.19      inference('demod', [status(thm)], ['69', '70', '73'])).
% 18.99/19.19  thf('75', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 18.99/19.19      inference('demod', [status(thm)], ['4', '5'])).
% 18.99/19.19  thf('76', plain,
% 18.99/19.19      (![X21 : $i, X22 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 18.99/19.19           = (k3_xboole_0 @ X21 @ X22))),
% 18.99/19.19      inference('cnf', [status(esa)], [t48_xboole_1])).
% 18.99/19.19  thf('77', plain,
% 18.99/19.19      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 18.99/19.19      inference('sup+', [status(thm)], ['75', '76'])).
% 18.99/19.19  thf('78', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 18.99/19.19      inference('cnf', [status(esa)], [t3_boole])).
% 18.99/19.19  thf('79', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 18.99/19.19      inference('demod', [status(thm)], ['77', '78'])).
% 18.99/19.19  thf(t49_xboole_1, axiom,
% 18.99/19.19    (![A:$i,B:$i,C:$i]:
% 18.99/19.19     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 18.99/19.19       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 18.99/19.19  thf('80', plain,
% 18.99/19.19      (![X23 : $i, X24 : $i, X25 : $i]:
% 18.99/19.19         ((k3_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X25))
% 18.99/19.19           = (k4_xboole_0 @ (k3_xboole_0 @ X23 @ X24) @ X25))),
% 18.99/19.19      inference('cnf', [status(esa)], [t49_xboole_1])).
% 18.99/19.19  thf('81', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 18.99/19.19           = (k4_xboole_0 @ X0 @ X1))),
% 18.99/19.19      inference('sup+', [status(thm)], ['79', '80'])).
% 18.99/19.19  thf('82', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k2_xboole_0 @ X0 @ X1)
% 18.99/19.19           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 18.99/19.19      inference('demod', [status(thm)], ['65', '66', '74', '81'])).
% 18.99/19.19  thf('83', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 18.99/19.19           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 18.99/19.19      inference('sup+', [status(thm)], ['58', '82'])).
% 18.99/19.19  thf('84', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 18.99/19.19      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 18.99/19.19  thf('85', plain,
% 18.99/19.19      (![X26 : $i, X27 : $i, X28 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ X26 @ (k4_xboole_0 @ X27 @ X28))
% 18.99/19.19           = (k2_xboole_0 @ (k4_xboole_0 @ X26 @ X27) @ 
% 18.99/19.19              (k3_xboole_0 @ X26 @ X28)))),
% 18.99/19.19      inference('cnf', [status(esa)], [t52_xboole_1])).
% 18.99/19.19  thf('86', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 18.99/19.19      inference('demod', [status(thm)], ['4', '5'])).
% 18.99/19.19  thf('87', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 18.99/19.19           = (k4_xboole_0 @ X1 @ k1_xboole_0))),
% 18.99/19.19      inference('demod', [status(thm)], ['83', '84', '85', '86'])).
% 18.99/19.19  thf('88', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 18.99/19.19      inference('cnf', [status(esa)], [t3_boole])).
% 18.99/19.19  thf('89', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 18.99/19.19      inference('demod', [status(thm)], ['87', '88'])).
% 18.99/19.19  thf('90', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 18.99/19.19           = (k4_xboole_0 @ X0 @ X1))),
% 18.99/19.19      inference('demod', [status(thm)], ['57', '89'])).
% 18.99/19.19  thf('91', plain,
% 18.99/19.19      (![X26 : $i, X27 : $i, X28 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ X26 @ (k4_xboole_0 @ X27 @ X28))
% 18.99/19.19           = (k2_xboole_0 @ (k4_xboole_0 @ X26 @ X27) @ 
% 18.99/19.19              (k3_xboole_0 @ X26 @ X28)))),
% 18.99/19.19      inference('cnf', [status(esa)], [t52_xboole_1])).
% 18.99/19.19  thf('92', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 18.99/19.19      inference('demod', [status(thm)], ['8', '15'])).
% 18.99/19.19  thf('93', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.99/19.19         ((k1_xboole_0)
% 18.99/19.19           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ 
% 18.99/19.19              (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 18.99/19.19      inference('sup+', [status(thm)], ['91', '92'])).
% 18.99/19.19  thf('94', plain,
% 18.99/19.19      (![X13 : $i, X14 : $i, X15 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 18.99/19.19           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 18.99/19.19      inference('cnf', [status(esa)], [t41_xboole_1])).
% 18.99/19.19  thf('95', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.99/19.19         ((k1_xboole_0)
% 18.99/19.19           = (k4_xboole_0 @ X2 @ 
% 18.99/19.19              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))))),
% 18.99/19.19      inference('demod', [status(thm)], ['93', '94'])).
% 18.99/19.19  thf('96', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k1_xboole_0)
% 18.99/19.19           = (k4_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ 
% 18.99/19.19              (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 18.99/19.19      inference('sup+', [status(thm)], ['90', '95'])).
% 18.99/19.19  thf('97', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k2_xboole_0 @ X0 @ X1)
% 18.99/19.19           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 18.99/19.19      inference('demod', [status(thm)], ['65', '66', '74', '81'])).
% 18.99/19.19  thf('98', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k1_xboole_0)
% 18.99/19.19           = (k4_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X0 @ X1)))),
% 18.99/19.19      inference('demod', [status(thm)], ['96', '97'])).
% 18.99/19.19  thf('99', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k1_xboole_0)
% 18.99/19.19           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X1)))),
% 18.99/19.19      inference('sup+', [status(thm)], ['50', '98'])).
% 18.99/19.19  thf('100', plain,
% 18.99/19.19      (![X21 : $i, X22 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 18.99/19.19           = (k3_xboole_0 @ X21 @ X22))),
% 18.99/19.19      inference('cnf', [status(esa)], [t48_xboole_1])).
% 18.99/19.19  thf('101', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 18.99/19.19           = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0)))),
% 18.99/19.19      inference('sup+', [status(thm)], ['99', '100'])).
% 18.99/19.19  thf('102', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 18.99/19.19      inference('cnf', [status(esa)], [t3_boole])).
% 18.99/19.19  thf('103', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k5_xboole_0 @ X0 @ X1)
% 18.99/19.19           = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0)))),
% 18.99/19.19      inference('demod', [status(thm)], ['101', '102'])).
% 18.99/19.19  thf('104', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k5_xboole_0 @ X0 @ X1)
% 18.99/19.19           = (k3_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 18.99/19.19      inference('sup+', [status(thm)], ['49', '103'])).
% 18.99/19.19  thf('105', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k2_xboole_0 @ X1 @ X0)
% 18.99/19.19           = (k2_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 18.99/19.19      inference('demod', [status(thm)], ['42', '43', '44', '104'])).
% 18.99/19.19  thf('106', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 18.99/19.19      inference('sup+', [status(thm)], ['25', '35'])).
% 18.99/19.19  thf('107', plain,
% 18.99/19.19      (![X19 : $i, X20 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ X19 @ (k3_xboole_0 @ X19 @ X20))
% 18.99/19.19           = (k4_xboole_0 @ X19 @ X20))),
% 18.99/19.19      inference('cnf', [status(esa)], [t47_xboole_1])).
% 18.99/19.19  thf('108', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ X0 @ X0)
% 18.99/19.19           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 18.99/19.19      inference('sup+', [status(thm)], ['106', '107'])).
% 18.99/19.19  thf('109', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 18.99/19.19      inference('demod', [status(thm)], ['4', '5'])).
% 18.99/19.19  thf('110', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k1_xboole_0) = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 18.99/19.19      inference('demod', [status(thm)], ['108', '109'])).
% 18.99/19.19  thf('111', plain,
% 18.99/19.19      (![X4 : $i, X5 : $i]:
% 18.99/19.19         ((k5_xboole_0 @ X4 @ X5)
% 18.99/19.19           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 18.99/19.19      inference('cnf', [status(esa)], [d6_xboole_0])).
% 18.99/19.19  thf('112', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 18.99/19.19           = (k2_xboole_0 @ k1_xboole_0 @ 
% 18.99/19.19              (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)))),
% 18.99/19.19      inference('sup+', [status(thm)], ['110', '111'])).
% 18.99/19.19  thf('113', plain,
% 18.99/19.19      (![X11 : $i, X12 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ X12)
% 18.99/19.19           = (k4_xboole_0 @ X11 @ X12))),
% 18.99/19.19      inference('cnf', [status(esa)], [t40_xboole_1])).
% 18.99/19.19  thf('114', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 18.99/19.19      inference('sup+', [status(thm)], ['71', '72'])).
% 18.99/19.19  thf('115', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 18.99/19.19           = (k4_xboole_0 @ X1 @ X0))),
% 18.99/19.19      inference('demod', [status(thm)], ['112', '113', '114'])).
% 18.99/19.19  thf('116', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k5_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 18.99/19.19           = (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 18.99/19.19      inference('sup+', [status(thm)], ['105', '115'])).
% 18.99/19.19  thf('117', plain,
% 18.99/19.19      (![X26 : $i, X27 : $i, X28 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ X26 @ (k4_xboole_0 @ X27 @ X28))
% 18.99/19.19           = (k2_xboole_0 @ (k4_xboole_0 @ X26 @ X27) @ 
% 18.99/19.19              (k3_xboole_0 @ X26 @ X28)))),
% 18.99/19.19      inference('cnf', [status(esa)], [t52_xboole_1])).
% 18.99/19.19  thf('118', plain,
% 18.99/19.19      (![X4 : $i, X5 : $i]:
% 18.99/19.19         ((k5_xboole_0 @ X4 @ X5)
% 18.99/19.19           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 18.99/19.19      inference('cnf', [status(esa)], [d6_xboole_0])).
% 18.99/19.19  thf('119', plain,
% 18.99/19.19      (![X6 : $i, X7 : $i, X8 : $i]:
% 18.99/19.19         ((k2_xboole_0 @ X6 @ (k3_xboole_0 @ X7 @ X8))
% 18.99/19.19           = (k3_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ (k2_xboole_0 @ X6 @ X8)))),
% 18.99/19.19      inference('cnf', [status(esa)], [t24_xboole_1])).
% 18.99/19.19  thf('120', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.99/19.19         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 18.99/19.19           (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))
% 18.99/19.19           = (k3_xboole_0 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2) @ 
% 18.99/19.19              (k5_xboole_0 @ X1 @ X0)))),
% 18.99/19.19      inference('sup+', [status(thm)], ['118', '119'])).
% 18.99/19.19  thf('121', plain,
% 18.99/19.19      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 18.99/19.19      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 18.99/19.19  thf('122', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.99/19.19         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 18.99/19.19           (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))
% 18.99/19.19           = (k3_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ 
% 18.99/19.19              (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 18.99/19.19      inference('demod', [status(thm)], ['120', '121'])).
% 18.99/19.19  thf('123', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))
% 18.99/19.19           = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ 
% 18.99/19.19              (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)))),
% 18.99/19.19      inference('sup+', [status(thm)], ['117', '122'])).
% 18.99/19.19  thf('124', plain,
% 18.99/19.19      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 18.99/19.19      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 18.99/19.19  thf('125', plain,
% 18.99/19.19      (![X21 : $i, X22 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 18.99/19.19           = (k3_xboole_0 @ X21 @ X22))),
% 18.99/19.19      inference('cnf', [status(esa)], [t48_xboole_1])).
% 18.99/19.19  thf('126', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 18.99/19.19      inference('demod', [status(thm)], ['87', '88'])).
% 18.99/19.19  thf('127', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 18.99/19.19      inference('sup+', [status(thm)], ['125', '126'])).
% 18.99/19.19  thf('128', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 18.99/19.19      inference('sup+', [status(thm)], ['124', '127'])).
% 18.99/19.19  thf('129', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 18.99/19.19           = (X0))),
% 18.99/19.19      inference('demod', [status(thm)], ['24', '36'])).
% 18.99/19.19  thf('130', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 18.99/19.19           = (k3_xboole_0 @ X1 @ X0))),
% 18.99/19.19      inference('sup+', [status(thm)], ['128', '129'])).
% 18.99/19.19  thf('131', plain,
% 18.99/19.19      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 18.99/19.19      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 18.99/19.19  thf('132', plain,
% 18.99/19.19      (![X19 : $i, X20 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ X19 @ (k3_xboole_0 @ X19 @ X20))
% 18.99/19.19           = (k4_xboole_0 @ X19 @ X20))),
% 18.99/19.19      inference('cnf', [status(esa)], [t47_xboole_1])).
% 18.99/19.19  thf('133', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 18.99/19.19           = (k4_xboole_0 @ X0 @ X1))),
% 18.99/19.19      inference('sup+', [status(thm)], ['131', '132'])).
% 18.99/19.19  thf('134', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 18.99/19.19           = (k3_xboole_0 @ X1 @ X0))),
% 18.99/19.19      inference('demod', [status(thm)], ['130', '133'])).
% 18.99/19.19  thf('135', plain,
% 18.99/19.19      (![X19 : $i, X20 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ X19 @ (k3_xboole_0 @ X19 @ X20))
% 18.99/19.19           = (k4_xboole_0 @ X19 @ X20))),
% 18.99/19.19      inference('cnf', [status(esa)], [t47_xboole_1])).
% 18.99/19.19  thf('136', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 18.99/19.19      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 18.99/19.19  thf('137', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 18.99/19.19      inference('demod', [status(thm)], ['87', '88'])).
% 18.99/19.19  thf('138', plain,
% 18.99/19.19      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 18.99/19.19      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 18.99/19.19  thf('139', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ X0 @ X1)
% 18.99/19.19           = (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 18.99/19.19      inference('demod', [status(thm)],
% 18.99/19.19                ['123', '134', '135', '136', '137', '138'])).
% 18.99/19.19  thf('140', plain,
% 18.99/19.19      (![X19 : $i, X20 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ X19 @ (k3_xboole_0 @ X19 @ X20))
% 18.99/19.19           = (k4_xboole_0 @ X19 @ X20))),
% 18.99/19.19      inference('cnf', [status(esa)], [t47_xboole_1])).
% 18.99/19.19  thf('141', plain,
% 18.99/19.19      (![X4 : $i, X5 : $i]:
% 18.99/19.19         ((k5_xboole_0 @ X4 @ X5)
% 18.99/19.19           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 18.99/19.19      inference('cnf', [status(esa)], [d6_xboole_0])).
% 18.99/19.19  thf('142', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 18.99/19.19           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 18.99/19.19              (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)))),
% 18.99/19.19      inference('sup+', [status(thm)], ['140', '141'])).
% 18.99/19.19  thf('143', plain,
% 18.99/19.19      (![X23 : $i, X24 : $i, X25 : $i]:
% 18.99/19.19         ((k3_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X25))
% 18.99/19.19           = (k4_xboole_0 @ (k3_xboole_0 @ X23 @ X24) @ X25))),
% 18.99/19.19      inference('cnf', [status(esa)], [t49_xboole_1])).
% 18.99/19.19  thf('144', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 18.99/19.19      inference('demod', [status(thm)], ['4', '5'])).
% 18.99/19.19  thf('145', plain,
% 18.99/19.19      (![X23 : $i, X24 : $i, X25 : $i]:
% 18.99/19.19         ((k3_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X25))
% 18.99/19.19           = (k4_xboole_0 @ (k3_xboole_0 @ X23 @ X24) @ X25))),
% 18.99/19.19      inference('cnf', [status(esa)], [t49_xboole_1])).
% 18.99/19.19  thf('146', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 18.99/19.19           = (k1_xboole_0))),
% 18.99/19.19      inference('sup+', [status(thm)], ['144', '145'])).
% 18.99/19.19  thf('147', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 18.99/19.19           = (k4_xboole_0 @ X0 @ X1))),
% 18.99/19.19      inference('sup+', [status(thm)], ['131', '132'])).
% 18.99/19.19  thf('148', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 18.99/19.19      inference('demod', [status(thm)], ['146', '147'])).
% 18.99/19.19  thf('149', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 18.99/19.19      inference('sup+', [status(thm)], ['28', '29'])).
% 18.99/19.19  thf('150', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 18.99/19.19           = (k4_xboole_0 @ X1 @ X0))),
% 18.99/19.19      inference('demod', [status(thm)], ['142', '143', '148', '149'])).
% 18.99/19.19  thf('151', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 18.99/19.19           = (k4_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 18.99/19.19      inference('sup+', [status(thm)], ['139', '150'])).
% 18.99/19.19  thf('152', plain,
% 18.99/19.19      (![X21 : $i, X22 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 18.99/19.19           = (k3_xboole_0 @ X21 @ X22))),
% 18.99/19.19      inference('cnf', [status(esa)], [t48_xboole_1])).
% 18.99/19.19  thf('153', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 18.99/19.19           = (k5_xboole_0 @ X1 @ X0))),
% 18.99/19.19      inference('sup+', [status(thm)], ['45', '46'])).
% 18.99/19.19  thf('154', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 18.99/19.19           (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))
% 18.99/19.19           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 18.99/19.19      inference('sup+', [status(thm)], ['152', '153'])).
% 18.99/19.19  thf('155', plain,
% 18.99/19.19      (![X13 : $i, X14 : $i, X15 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 18.99/19.19           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 18.99/19.19      inference('cnf', [status(esa)], [t41_xboole_1])).
% 18.99/19.19  thf('156', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k1_xboole_0) = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 18.99/19.19      inference('demod', [status(thm)], ['108', '109'])).
% 18.99/19.19  thf('157', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 18.99/19.19      inference('sup+', [status(thm)], ['28', '29'])).
% 18.99/19.19  thf('158', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k3_xboole_0 @ X1 @ X0)
% 18.99/19.19           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 18.99/19.19      inference('demod', [status(thm)], ['154', '155', '156', '157'])).
% 18.99/19.19  thf('159', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 18.99/19.19      inference('sup+', [status(thm)], ['47', '48'])).
% 18.99/19.19  thf('160', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k3_xboole_0 @ X1 @ X0)
% 18.99/19.19           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 18.99/19.19      inference('demod', [status(thm)], ['158', '159'])).
% 18.99/19.19  thf('161', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k3_xboole_0 @ X1 @ X0)
% 18.99/19.19           = (k4_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 18.99/19.19      inference('demod', [status(thm)], ['151', '160'])).
% 18.99/19.19  thf('162', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k5_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 18.99/19.19           = (k3_xboole_0 @ X0 @ X1))),
% 18.99/19.19      inference('demod', [status(thm)], ['116', '161'])).
% 18.99/19.19  thf('163', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k2_xboole_0 @ X1 @ X0)
% 18.99/19.19           = (k2_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 18.99/19.19      inference('demod', [status(thm)], ['42', '43', '44', '104'])).
% 18.99/19.19  thf('164', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 18.99/19.19           = (k4_xboole_0 @ X1 @ X0))),
% 18.99/19.19      inference('demod', [status(thm)], ['69', '70', '73'])).
% 18.99/19.19  thf('165', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 18.99/19.19           = (k4_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ X0))),
% 18.99/19.19      inference('sup+', [status(thm)], ['163', '164'])).
% 18.99/19.19  thf('166', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 18.99/19.19           = (k4_xboole_0 @ X1 @ X0))),
% 18.99/19.19      inference('demod', [status(thm)], ['112', '113', '114'])).
% 18.99/19.19  thf('167', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ X1 @ X0)
% 18.99/19.19           = (k4_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ X0))),
% 18.99/19.19      inference('demod', [status(thm)], ['165', '166'])).
% 18.99/19.19  thf('168', plain,
% 18.99/19.19      (![X4 : $i, X5 : $i]:
% 18.99/19.19         ((k5_xboole_0 @ X4 @ X5)
% 18.99/19.19           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 18.99/19.19      inference('cnf', [status(esa)], [d6_xboole_0])).
% 18.99/19.19  thf('169', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k5_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ X0)
% 18.99/19.19           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 18.99/19.19              (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1))))),
% 18.99/19.19      inference('sup+', [status(thm)], ['167', '168'])).
% 18.99/19.19  thf('170', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 18.99/19.19      inference('sup+', [status(thm)], ['47', '48'])).
% 18.99/19.19  thf('171', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k3_xboole_0 @ X1 @ X0)
% 18.99/19.19           = (k4_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 18.99/19.19      inference('demod', [status(thm)], ['151', '160'])).
% 18.99/19.19  thf('172', plain,
% 18.99/19.19      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 18.99/19.19      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 18.99/19.19  thf('173', plain,
% 18.99/19.19      (![X26 : $i, X27 : $i, X28 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ X26 @ (k4_xboole_0 @ X27 @ X28))
% 18.99/19.19           = (k2_xboole_0 @ (k4_xboole_0 @ X26 @ X27) @ 
% 18.99/19.19              (k3_xboole_0 @ X26 @ X28)))),
% 18.99/19.19      inference('cnf', [status(esa)], [t52_xboole_1])).
% 18.99/19.19  thf('174', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.99/19.19         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))
% 18.99/19.19           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ (k3_xboole_0 @ X1 @ X0)))),
% 18.99/19.19      inference('sup+', [status(thm)], ['172', '173'])).
% 18.99/19.19  thf('175', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 18.99/19.19      inference('demod', [status(thm)], ['4', '5'])).
% 18.99/19.19  thf('176', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1))
% 18.99/19.19           = (k4_xboole_0 @ X1 @ k1_xboole_0))),
% 18.99/19.19      inference('demod', [status(thm)], ['169', '170', '171', '174', '175'])).
% 18.99/19.19  thf('177', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 18.99/19.19      inference('cnf', [status(esa)], [t3_boole])).
% 18.99/19.19  thf('178', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)) = (X1))),
% 18.99/19.19      inference('demod', [status(thm)], ['176', '177'])).
% 18.99/19.19  thf('179', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]:
% 18.99/19.19         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 18.99/19.19           = (k2_xboole_0 @ X0 @ X1))),
% 18.99/19.19      inference('sup+', [status(thm)], ['162', '178'])).
% 18.99/19.19  thf('180', plain,
% 18.99/19.19      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 18.99/19.19      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 18.99/19.19  thf('181', plain,
% 18.99/19.19      (((k2_xboole_0 @ sk_A @ sk_B) != (k2_xboole_0 @ sk_A @ sk_B))),
% 18.99/19.19      inference('demod', [status(thm)], ['0', '179', '180'])).
% 18.99/19.19  thf('182', plain, ($false), inference('simplify', [status(thm)], ['181'])).
% 18.99/19.19  
% 18.99/19.19  % SZS output end Refutation
% 18.99/19.19  
% 18.99/19.20  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

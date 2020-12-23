%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0Wv0F5fFfF

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:58 EST 2020

% Result     : Theorem 0.66s
% Output     : Refutation 0.66s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 428 expanded)
%              Number of leaves         :   17 ( 150 expanded)
%              Depth                    :   19
%              Number of atoms          : 1024 (4405 expanded)
%              Number of equality atoms :   97 ( 418 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t99_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ B @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k1_enumset1 @ A @ B @ C )
        = ( k1_enumset1 @ B @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t99_enumset1])).

thf('0',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_B @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X32: $i] :
      ( ( k2_tarski @ X32 @ X32 )
      = ( k1_tarski @ X32 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l57_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k3_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X6 @ X7 @ X8 ) @ ( k2_tarski @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_enumset1 @ X33 @ X33 @ X34 )
      = ( k2_tarski @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_tarski @ X5 @ X4 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('6',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k3_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X6 @ X7 @ X8 ) @ ( k2_tarski @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_tarski @ X5 @ X4 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('10',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_enumset1 @ X33 @ X33 @ X34 )
      = ( k2_tarski @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('11',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k3_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X6 @ X7 @ X8 ) @ ( k2_tarski @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('13',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( k3_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 )
      = ( k2_enumset1 @ X38 @ X39 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) )
      = ( k2_enumset1 @ X0 @ X1 @ X3 @ X2 ) ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X0 @ X2 @ X3 )
      = ( k2_enumset1 @ X0 @ X1 @ X3 @ X2 ) ) ),
    inference(demod,[status(thm)],['8','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_enumset1 @ X1 @ X2 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','16'])).

thf('18',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_tarski @ X5 @ X4 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('19',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( k2_enumset1 @ X35 @ X35 @ X36 @ X37 )
      = ( k1_enumset1 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t50_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ) )).

thf('20',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k3_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X19 @ X20 @ X21 @ X22 ) @ ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X32: $i] :
      ( ( k2_tarski @ X32 @ X32 )
      = ( k1_tarski @ X32 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('23',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( k3_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 )
      = ( k2_enumset1 @ X38 @ X39 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('24',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( k2_enumset1 @ X35 @ X35 @ X36 @ X37 )
      = ( k1_enumset1 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X32: $i] :
      ( ( k2_tarski @ X32 @ X32 )
      = ( k1_tarski @ X32 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('32',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_enumset1 @ X33 @ X33 @ X34 )
      = ( k2_tarski @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X1 @ X1 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_tarski @ X5 @ X4 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X32: $i] :
      ( ( k2_tarski @ X32 @ X32 )
      = ( k1_tarski @ X32 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k1_enumset1 @ X0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X32: $i] :
      ( ( k2_tarski @ X32 @ X32 )
      = ( k1_tarski @ X32 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','49'])).

thf('51',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_enumset1 @ X33 @ X33 @ X34 )
      = ( k2_tarski @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_enumset1 @ X33 @ X33 @ X34 )
      = ( k2_tarski @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X1 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['53','58'])).

thf('60',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_tarski @ X5 @ X4 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X0 @ X1 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X0 @ X1 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X0 @ X1 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X2 @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_enumset1 @ X33 @ X33 @ X34 )
      = ( k2_tarski @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k1_enumset1 @ X0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('75',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k3_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X6 @ X7 @ X8 ) @ ( k2_tarski @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X0 @ X1 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) )
      = ( k2_enumset1 @ X0 @ X1 @ X3 @ X2 ) ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X0 @ X1 @ X3 @ X2 )
      = ( k2_enumset1 @ X0 @ X1 @ X3 @ X2 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X1 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['73','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k1_enumset1 @ X0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['17','65','72','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X0 @ X1 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X2 @ X1 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X0 @ X1 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('87',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','85','86'])).

thf('88',plain,(
    $false ),
    inference(simplify,[status(thm)],['87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0Wv0F5fFfF
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:10:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.66/0.84  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.66/0.84  % Solved by: fo/fo7.sh
% 0.66/0.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.66/0.84  % done 592 iterations in 0.380s
% 0.66/0.84  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.66/0.84  % SZS output start Refutation
% 0.66/0.84  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.66/0.84  thf(sk_C_type, type, sk_C: $i).
% 0.66/0.84  thf(sk_B_type, type, sk_B: $i).
% 0.66/0.84  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.66/0.84  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.66/0.84  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.66/0.84  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.66/0.84  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.66/0.84  thf(sk_A_type, type, sk_A: $i).
% 0.66/0.84  thf(t99_enumset1, conjecture,
% 0.66/0.84    (![A:$i,B:$i,C:$i]:
% 0.66/0.84     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ B @ A @ C ) ))).
% 0.66/0.84  thf(zf_stmt_0, negated_conjecture,
% 0.66/0.84    (~( ![A:$i,B:$i,C:$i]:
% 0.66/0.84        ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ B @ A @ C ) ) )),
% 0.66/0.84    inference('cnf.neg', [status(esa)], [t99_enumset1])).
% 0.66/0.84  thf('0', plain,
% 0.66/0.84      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.66/0.84         != (k1_enumset1 @ sk_B @ sk_A @ sk_C))),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf(t69_enumset1, axiom,
% 0.66/0.84    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.66/0.84  thf('1', plain, (![X32 : $i]: ((k2_tarski @ X32 @ X32) = (k1_tarski @ X32))),
% 0.66/0.84      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.66/0.84  thf(l57_enumset1, axiom,
% 0.66/0.84    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.66/0.84     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.66/0.84       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ))).
% 0.66/0.84  thf('2', plain,
% 0.66/0.84      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.66/0.84         ((k3_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10)
% 0.66/0.84           = (k2_xboole_0 @ (k1_enumset1 @ X6 @ X7 @ X8) @ 
% 0.66/0.84              (k2_tarski @ X9 @ X10)))),
% 0.66/0.84      inference('cnf', [status(esa)], [l57_enumset1])).
% 0.66/0.84  thf('3', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.66/0.84         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0)
% 0.66/0.84           = (k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['1', '2'])).
% 0.66/0.84  thf(t70_enumset1, axiom,
% 0.66/0.84    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.66/0.84  thf('4', plain,
% 0.66/0.84      (![X33 : $i, X34 : $i]:
% 0.66/0.84         ((k1_enumset1 @ X33 @ X33 @ X34) = (k2_tarski @ X33 @ X34))),
% 0.66/0.84      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.66/0.84  thf(commutativity_k2_tarski, axiom,
% 0.66/0.84    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.66/0.84  thf('5', plain,
% 0.66/0.84      (![X4 : $i, X5 : $i]: ((k2_tarski @ X5 @ X4) = (k2_tarski @ X4 @ X5))),
% 0.66/0.84      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.66/0.84  thf('6', plain,
% 0.66/0.84      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.66/0.84         ((k3_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10)
% 0.66/0.84           = (k2_xboole_0 @ (k1_enumset1 @ X6 @ X7 @ X8) @ 
% 0.66/0.84              (k2_tarski @ X9 @ X10)))),
% 0.66/0.84      inference('cnf', [status(esa)], [l57_enumset1])).
% 0.66/0.84  thf('7', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.66/0.84         ((k3_enumset1 @ X4 @ X3 @ X2 @ X0 @ X1)
% 0.66/0.84           = (k2_xboole_0 @ (k1_enumset1 @ X4 @ X3 @ X2) @ 
% 0.66/0.84              (k2_tarski @ X1 @ X0)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['5', '6'])).
% 0.66/0.84  thf('8', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.66/0.84         ((k3_enumset1 @ X1 @ X1 @ X0 @ X2 @ X3)
% 0.66/0.84           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['4', '7'])).
% 0.66/0.84  thf('9', plain,
% 0.66/0.84      (![X4 : $i, X5 : $i]: ((k2_tarski @ X5 @ X4) = (k2_tarski @ X4 @ X5))),
% 0.66/0.84      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.66/0.84  thf('10', plain,
% 0.66/0.84      (![X33 : $i, X34 : $i]:
% 0.66/0.84         ((k1_enumset1 @ X33 @ X33 @ X34) = (k2_tarski @ X33 @ X34))),
% 0.66/0.84      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.66/0.84  thf('11', plain,
% 0.66/0.84      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.66/0.84         ((k3_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10)
% 0.66/0.84           = (k2_xboole_0 @ (k1_enumset1 @ X6 @ X7 @ X8) @ 
% 0.66/0.84              (k2_tarski @ X9 @ X10)))),
% 0.66/0.84      inference('cnf', [status(esa)], [l57_enumset1])).
% 0.66/0.84  thf('12', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.66/0.84         ((k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2)
% 0.66/0.84           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['10', '11'])).
% 0.66/0.84  thf(t72_enumset1, axiom,
% 0.66/0.84    (![A:$i,B:$i,C:$i,D:$i]:
% 0.66/0.84     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.66/0.84  thf('13', plain,
% 0.66/0.84      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.66/0.84         ((k3_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41)
% 0.66/0.84           = (k2_enumset1 @ X38 @ X39 @ X40 @ X41))),
% 0.66/0.84      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.66/0.84  thf('14', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.66/0.84         ((k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0))
% 0.66/0.84           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.66/0.84      inference('sup+', [status(thm)], ['12', '13'])).
% 0.66/0.84  thf('15', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.66/0.84         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2))
% 0.66/0.84           = (k2_enumset1 @ X0 @ X1 @ X3 @ X2))),
% 0.66/0.84      inference('sup+', [status(thm)], ['9', '14'])).
% 0.66/0.84  thf('16', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.66/0.84         ((k3_enumset1 @ X1 @ X1 @ X0 @ X2 @ X3)
% 0.66/0.84           = (k2_enumset1 @ X0 @ X1 @ X3 @ X2))),
% 0.66/0.84      inference('demod', [status(thm)], ['8', '15'])).
% 0.66/0.84  thf('17', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X2 @ X1) @ (k1_tarski @ X0))
% 0.66/0.84           = (k2_enumset1 @ X1 @ X2 @ X0 @ X0))),
% 0.66/0.84      inference('sup+', [status(thm)], ['3', '16'])).
% 0.66/0.84  thf('18', plain,
% 0.66/0.84      (![X4 : $i, X5 : $i]: ((k2_tarski @ X5 @ X4) = (k2_tarski @ X4 @ X5))),
% 0.66/0.84      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.66/0.84  thf(t71_enumset1, axiom,
% 0.66/0.84    (![A:$i,B:$i,C:$i]:
% 0.66/0.84     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.66/0.84  thf('19', plain,
% 0.66/0.84      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.66/0.84         ((k2_enumset1 @ X35 @ X35 @ X36 @ X37)
% 0.66/0.84           = (k1_enumset1 @ X35 @ X36 @ X37))),
% 0.66/0.84      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.66/0.84  thf(t50_enumset1, axiom,
% 0.66/0.84    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.66/0.84     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.66/0.84       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ))).
% 0.66/0.84  thf('20', plain,
% 0.66/0.84      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.66/0.84         ((k3_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23)
% 0.66/0.84           = (k2_xboole_0 @ (k2_enumset1 @ X19 @ X20 @ X21 @ X22) @ 
% 0.66/0.84              (k1_tarski @ X23)))),
% 0.66/0.84      inference('cnf', [status(esa)], [t50_enumset1])).
% 0.66/0.84  thf('21', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.66/0.84         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3)
% 0.66/0.84           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['19', '20'])).
% 0.66/0.84  thf('22', plain,
% 0.66/0.84      (![X32 : $i]: ((k2_tarski @ X32 @ X32) = (k1_tarski @ X32))),
% 0.66/0.84      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.66/0.84  thf('23', plain,
% 0.66/0.84      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.66/0.84         ((k3_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41)
% 0.66/0.84           = (k2_enumset1 @ X38 @ X39 @ X40 @ X41))),
% 0.66/0.84      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.66/0.84  thf('24', plain,
% 0.66/0.84      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.66/0.84         ((k2_enumset1 @ X35 @ X35 @ X36 @ X37)
% 0.66/0.84           = (k1_enumset1 @ X35 @ X36 @ X37))),
% 0.66/0.84      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.66/0.84  thf('25', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.66/0.84      inference('sup+', [status(thm)], ['23', '24'])).
% 0.66/0.84  thf('26', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.66/0.84         ((k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2)
% 0.66/0.84           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['10', '11'])).
% 0.66/0.84  thf('27', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         ((k1_enumset1 @ X2 @ X1 @ X0)
% 0.66/0.84           = (k2_xboole_0 @ (k2_tarski @ X2 @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['25', '26'])).
% 0.66/0.84  thf('28', plain,
% 0.66/0.84      (![X32 : $i]: ((k2_tarski @ X32 @ X32) = (k1_tarski @ X32))),
% 0.66/0.84      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.66/0.84  thf('29', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         ((k1_enumset1 @ X2 @ X1 @ X0)
% 0.66/0.84           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.66/0.84      inference('demod', [status(thm)], ['27', '28'])).
% 0.66/0.84  thf('30', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k1_enumset1 @ X1 @ X0 @ X0)
% 0.66/0.84           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['22', '29'])).
% 0.66/0.84  thf('31', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.66/0.84      inference('sup+', [status(thm)], ['23', '24'])).
% 0.66/0.84  thf('32', plain,
% 0.66/0.84      (![X33 : $i, X34 : $i]:
% 0.66/0.84         ((k1_enumset1 @ X33 @ X33 @ X34) = (k2_tarski @ X33 @ X34))),
% 0.66/0.84      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.66/0.84  thf('33', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.66/0.84      inference('sup+', [status(thm)], ['31', '32'])).
% 0.66/0.84  thf('34', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.66/0.84         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3)
% 0.66/0.84           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['19', '20'])).
% 0.66/0.84  thf('35', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k2_tarski @ X1 @ X0)
% 0.66/0.84           = (k2_xboole_0 @ (k1_enumset1 @ X1 @ X1 @ X1) @ (k1_tarski @ X0)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['33', '34'])).
% 0.66/0.84  thf('36', plain,
% 0.66/0.84      (![X4 : $i, X5 : $i]: ((k2_tarski @ X5 @ X4) = (k2_tarski @ X4 @ X5))),
% 0.66/0.84      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.66/0.84  thf('37', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.66/0.84      inference('sup+', [status(thm)], ['31', '32'])).
% 0.66/0.84  thf('38', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.66/0.84         ((k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2)
% 0.66/0.84           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['10', '11'])).
% 0.66/0.84  thf('39', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k2_tarski @ X1 @ X0)
% 0.66/0.84           = (k2_xboole_0 @ (k2_tarski @ X1 @ X1) @ (k2_tarski @ X1 @ X0)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['37', '38'])).
% 0.66/0.84  thf('40', plain,
% 0.66/0.84      (![X32 : $i]: ((k2_tarski @ X32 @ X32) = (k1_tarski @ X32))),
% 0.66/0.84      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.66/0.84  thf('41', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k2_tarski @ X1 @ X0)
% 0.66/0.84           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0)))),
% 0.66/0.84      inference('demod', [status(thm)], ['39', '40'])).
% 0.66/0.84  thf('42', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k2_tarski @ X0 @ X1)
% 0.66/0.84           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['36', '41'])).
% 0.66/0.84  thf('43', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         ((k1_enumset1 @ X2 @ X1 @ X0)
% 0.66/0.84           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.66/0.84      inference('demod', [status(thm)], ['27', '28'])).
% 0.66/0.84  thf('44', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k2_tarski @ X0 @ X1) = (k1_enumset1 @ X0 @ X1 @ X0))),
% 0.66/0.84      inference('demod', [status(thm)], ['42', '43'])).
% 0.66/0.84  thf('45', plain,
% 0.66/0.84      (![X32 : $i]: ((k2_tarski @ X32 @ X32) = (k1_tarski @ X32))),
% 0.66/0.84      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.66/0.84  thf('46', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k2_tarski @ X1 @ X0)
% 0.66/0.84           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.66/0.84      inference('demod', [status(thm)], ['35', '44', '45'])).
% 0.66/0.84  thf('47', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.66/0.84      inference('demod', [status(thm)], ['30', '46'])).
% 0.66/0.84  thf('48', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.66/0.84      inference('sup+', [status(thm)], ['23', '24'])).
% 0.66/0.84  thf('49', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.66/0.84      inference('sup+', [status(thm)], ['47', '48'])).
% 0.66/0.84  thf('50', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k2_xboole_0 @ (k1_enumset1 @ X1 @ X1 @ X0) @ (k1_tarski @ X0))
% 0.66/0.84           = (k2_tarski @ X1 @ X0))),
% 0.66/0.84      inference('sup+', [status(thm)], ['21', '49'])).
% 0.66/0.84  thf('51', plain,
% 0.66/0.84      (![X33 : $i, X34 : $i]:
% 0.66/0.84         ((k1_enumset1 @ X33 @ X33 @ X34) = (k2_tarski @ X33 @ X34))),
% 0.66/0.84      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.66/0.84  thf('52', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0))
% 0.66/0.84           = (k2_tarski @ X1 @ X0))),
% 0.66/0.84      inference('demod', [status(thm)], ['50', '51'])).
% 0.66/0.84  thf('53', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 0.66/0.84           = (k2_tarski @ X0 @ X1))),
% 0.66/0.84      inference('sup+', [status(thm)], ['18', '52'])).
% 0.66/0.84  thf('54', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.66/0.84      inference('sup+', [status(thm)], ['23', '24'])).
% 0.66/0.84  thf('55', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.66/0.84         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3)
% 0.66/0.84           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['19', '20'])).
% 0.66/0.84  thf('56', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         ((k1_enumset1 @ X2 @ X1 @ X0)
% 0.66/0.84           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X2 @ X1) @ (k1_tarski @ X0)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['54', '55'])).
% 0.66/0.84  thf('57', plain,
% 0.66/0.84      (![X33 : $i, X34 : $i]:
% 0.66/0.84         ((k1_enumset1 @ X33 @ X33 @ X34) = (k2_tarski @ X33 @ X34))),
% 0.66/0.84      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.66/0.84  thf('58', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         ((k1_enumset1 @ X2 @ X1 @ X0)
% 0.66/0.84           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)))),
% 0.66/0.84      inference('demod', [status(thm)], ['56', '57'])).
% 0.66/0.84  thf('59', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k1_enumset1 @ X1 @ X0 @ X1) = (k2_tarski @ X0 @ X1))),
% 0.66/0.84      inference('demod', [status(thm)], ['53', '58'])).
% 0.66/0.84  thf('60', plain,
% 0.66/0.84      (![X4 : $i, X5 : $i]: ((k2_tarski @ X5 @ X4) = (k2_tarski @ X4 @ X5))),
% 0.66/0.84      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.66/0.84  thf('61', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         ((k1_enumset1 @ X2 @ X1 @ X0)
% 0.66/0.84           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.66/0.84      inference('demod', [status(thm)], ['27', '28'])).
% 0.66/0.84  thf('62', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         ((k1_enumset1 @ X2 @ X0 @ X1)
% 0.66/0.84           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['60', '61'])).
% 0.66/0.84  thf('63', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         ((k1_enumset1 @ X2 @ X1 @ X0)
% 0.66/0.84           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.66/0.84      inference('demod', [status(thm)], ['27', '28'])).
% 0.66/0.84  thf('64', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         ((k1_enumset1 @ X2 @ X0 @ X1) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.66/0.84      inference('sup+', [status(thm)], ['62', '63'])).
% 0.66/0.84  thf('65', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k1_enumset1 @ X0 @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 0.66/0.84      inference('sup+', [status(thm)], ['59', '64'])).
% 0.66/0.84  thf('66', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         ((k1_enumset1 @ X2 @ X0 @ X1) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.66/0.84      inference('sup+', [status(thm)], ['62', '63'])).
% 0.66/0.84  thf('67', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.66/0.84      inference('sup+', [status(thm)], ['23', '24'])).
% 0.66/0.84  thf('68', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         ((k3_enumset1 @ X2 @ X2 @ X2 @ X0 @ X1) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.66/0.84      inference('sup+', [status(thm)], ['66', '67'])).
% 0.66/0.84  thf('69', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.66/0.84         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3)
% 0.66/0.84           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['19', '20'])).
% 0.66/0.84  thf('70', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         ((k1_enumset1 @ X2 @ X1 @ X0)
% 0.66/0.84           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X2 @ X0) @ (k1_tarski @ X1)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['68', '69'])).
% 0.66/0.84  thf('71', plain,
% 0.66/0.84      (![X33 : $i, X34 : $i]:
% 0.66/0.84         ((k1_enumset1 @ X33 @ X33 @ X34) = (k2_tarski @ X33 @ X34))),
% 0.66/0.84      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.66/0.84  thf('72', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         ((k1_enumset1 @ X2 @ X1 @ X0)
% 0.66/0.84           = (k2_xboole_0 @ (k2_tarski @ X2 @ X0) @ (k1_tarski @ X1)))),
% 0.66/0.84      inference('demod', [status(thm)], ['70', '71'])).
% 0.66/0.84  thf('73', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.66/0.84         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0)
% 0.66/0.84           = (k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['1', '2'])).
% 0.66/0.84  thf('74', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k2_tarski @ X0 @ X1) = (k1_enumset1 @ X0 @ X1 @ X0))),
% 0.66/0.84      inference('demod', [status(thm)], ['42', '43'])).
% 0.66/0.84  thf('75', plain,
% 0.66/0.84      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.66/0.84         ((k3_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10)
% 0.66/0.84           = (k2_xboole_0 @ (k1_enumset1 @ X6 @ X7 @ X8) @ 
% 0.66/0.84              (k2_tarski @ X9 @ X10)))),
% 0.66/0.84      inference('cnf', [status(esa)], [l57_enumset1])).
% 0.66/0.84  thf('76', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.66/0.84         ((k3_enumset1 @ X1 @ X0 @ X1 @ X3 @ X2)
% 0.66/0.84           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['74', '75'])).
% 0.66/0.84  thf('77', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.66/0.84         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2))
% 0.66/0.84           = (k2_enumset1 @ X0 @ X1 @ X3 @ X2))),
% 0.66/0.84      inference('sup+', [status(thm)], ['9', '14'])).
% 0.66/0.84  thf('78', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.66/0.84         ((k3_enumset1 @ X1 @ X0 @ X1 @ X3 @ X2)
% 0.66/0.84           = (k2_enumset1 @ X0 @ X1 @ X3 @ X2))),
% 0.66/0.84      inference('demod', [status(thm)], ['76', '77'])).
% 0.66/0.84  thf('79', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         ((k2_xboole_0 @ (k1_enumset1 @ X1 @ X2 @ X1) @ (k1_tarski @ X0))
% 0.66/0.84           = (k2_enumset1 @ X2 @ X1 @ X0 @ X0))),
% 0.66/0.84      inference('sup+', [status(thm)], ['73', '78'])).
% 0.66/0.84  thf('80', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((k2_tarski @ X0 @ X1) = (k1_enumset1 @ X0 @ X1 @ X0))),
% 0.66/0.84      inference('demod', [status(thm)], ['42', '43'])).
% 0.66/0.84  thf('81', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         ((k1_enumset1 @ X2 @ X1 @ X0)
% 0.66/0.84           = (k2_xboole_0 @ (k2_tarski @ X2 @ X0) @ (k1_tarski @ X1)))),
% 0.66/0.84      inference('demod', [status(thm)], ['70', '71'])).
% 0.66/0.84  thf('82', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         ((k1_enumset1 @ X1 @ X0 @ X2) = (k2_enumset1 @ X2 @ X1 @ X0 @ X0))),
% 0.66/0.84      inference('demod', [status(thm)], ['79', '80', '81'])).
% 0.66/0.84  thf('83', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         ((k1_enumset1 @ X1 @ X0 @ X2) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 0.66/0.84      inference('demod', [status(thm)], ['17', '65', '72', '82'])).
% 0.66/0.84  thf('84', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         ((k1_enumset1 @ X2 @ X0 @ X1) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.66/0.84      inference('sup+', [status(thm)], ['62', '63'])).
% 0.66/0.84  thf('85', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         ((k1_enumset1 @ X0 @ X2 @ X1) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.66/0.84      inference('sup+', [status(thm)], ['83', '84'])).
% 0.66/0.84  thf('86', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.84         ((k1_enumset1 @ X2 @ X0 @ X1) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.66/0.84      inference('sup+', [status(thm)], ['62', '63'])).
% 0.66/0.84  thf('87', plain,
% 0.66/0.84      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.66/0.84         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.66/0.84      inference('demod', [status(thm)], ['0', '85', '86'])).
% 0.66/0.84  thf('88', plain, ($false), inference('simplify', [status(thm)], ['87'])).
% 0.66/0.84  
% 0.66/0.84  % SZS output end Refutation
% 0.66/0.84  
% 0.66/0.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

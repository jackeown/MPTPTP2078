%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hKgp3PoJM4

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:56 EST 2020

% Result     : Theorem 7.51s
% Output     : Refutation 7.51s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 316 expanded)
%              Number of leaves         :   15 ( 116 expanded)
%              Depth                    :   10
%              Number of atoms          : 1068 (3283 expanded)
%              Number of equality atoms :   93 ( 306 expanded)
%              Maximal formula depth    :   11 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t45_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k2_enumset1 @ A @ B @ C @ D )
        = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t45_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_tarski @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_xboole_0 @ X2 @ ( k1_tarski @ X1 ) ) )
      = ( k2_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_tarski @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('8',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X3 @ X1 ) @ ( k2_xboole_0 @ X0 @ X2 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['5','10'])).

thf('12',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_tarski @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_tarski @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ ( k2_tarski @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X0 @ X2 ) @ X1 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X0 @ X2 ) @ X1 )
      = ( k2_xboole_0 @ X1 @ ( k2_tarski @ X2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['19','27'])).

thf('29',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ ( k2_tarski @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ ( k2_tarski @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('33',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('36',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k1_enumset1 @ X3 @ X1 @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X0 @ X1 ) )
      = ( k2_enumset1 @ X0 @ X3 @ X1 @ X2 ) ) ),
    inference(demod,[status(thm)],['11','14','28','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('42',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_tarski @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X1 @ X2 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X3 @ X1 @ X2 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['47','50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ ( k2_tarski @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('61',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X3 @ X2 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference('sup+',[status(thm)],['52','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X3 @ X2 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('69',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X3 @ X2 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X0 @ X1 ) @ ( k1_tarski @ X2 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('78',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X0 @ X1 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X3 @ X2 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','40','63','71','81','84'])).

thf('86',plain,(
    $false ),
    inference(simplify,[status(thm)],['85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hKgp3PoJM4
% 0.16/0.38  % Computer   : n015.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 20:49:53 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 7.51/7.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 7.51/7.74  % Solved by: fo/fo7.sh
% 7.51/7.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.51/7.74  % done 2193 iterations in 7.249s
% 7.51/7.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 7.51/7.74  % SZS output start Refutation
% 7.51/7.74  thf(sk_C_type, type, sk_C: $i).
% 7.51/7.74  thf(sk_A_type, type, sk_A: $i).
% 7.51/7.74  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 7.51/7.74  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 7.51/7.74  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 7.51/7.74  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 7.51/7.74  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 7.51/7.74  thf(sk_D_type, type, sk_D: $i).
% 7.51/7.74  thf(sk_B_type, type, sk_B: $i).
% 7.51/7.74  thf(t45_enumset1, conjecture,
% 7.51/7.74    (![A:$i,B:$i,C:$i,D:$i]:
% 7.51/7.74     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 7.51/7.74       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 7.51/7.74  thf(zf_stmt_0, negated_conjecture,
% 7.51/7.74    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 7.51/7.74        ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 7.51/7.74          ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )),
% 7.51/7.74    inference('cnf.neg', [status(esa)], [t45_enumset1])).
% 7.51/7.74  thf('0', plain,
% 7.51/7.74      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 7.51/7.74         != (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 7.51/7.74             (k2_tarski @ sk_C @ sk_D)))),
% 7.51/7.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.74  thf(t41_enumset1, axiom,
% 7.51/7.74    (![A:$i,B:$i]:
% 7.51/7.74     ( ( k2_tarski @ A @ B ) =
% 7.51/7.74       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 7.51/7.74  thf('1', plain,
% 7.51/7.74      (![X5 : $i, X6 : $i]:
% 7.51/7.74         ((k2_tarski @ X5 @ X6)
% 7.51/7.74           = (k2_xboole_0 @ (k1_tarski @ X5) @ (k1_tarski @ X6)))),
% 7.51/7.74      inference('cnf', [status(esa)], [t41_enumset1])).
% 7.51/7.74  thf(t4_xboole_1, axiom,
% 7.51/7.74    (![A:$i,B:$i,C:$i]:
% 7.51/7.74     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 7.51/7.74       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 7.51/7.74  thf('2', plain,
% 7.51/7.74      (![X2 : $i, X3 : $i, X4 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ (k2_xboole_0 @ X2 @ X3) @ X4)
% 7.51/7.74           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ X4)))),
% 7.51/7.74      inference('cnf', [status(esa)], [t4_xboole_1])).
% 7.51/7.74  thf(commutativity_k2_xboole_0, axiom,
% 7.51/7.74    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 7.51/7.74  thf('3', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 7.51/7.74      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 7.51/7.74  thf('4', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1))
% 7.51/7.74           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 7.51/7.74      inference('sup+', [status(thm)], ['2', '3'])).
% 7.51/7.74  thf('5', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ (k1_tarski @ X0) @ 
% 7.51/7.74           (k2_xboole_0 @ X2 @ (k1_tarski @ X1)))
% 7.51/7.74           = (k2_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)))),
% 7.51/7.74      inference('sup+', [status(thm)], ['1', '4'])).
% 7.51/7.74  thf('6', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1))
% 7.51/7.74           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 7.51/7.74      inference('sup+', [status(thm)], ['2', '3'])).
% 7.51/7.74  thf('7', plain,
% 7.51/7.74      (![X5 : $i, X6 : $i]:
% 7.51/7.74         ((k2_tarski @ X5 @ X6)
% 7.51/7.74           = (k2_xboole_0 @ (k1_tarski @ X5) @ (k1_tarski @ X6)))),
% 7.51/7.74      inference('cnf', [status(esa)], [t41_enumset1])).
% 7.51/7.74  thf('8', plain,
% 7.51/7.74      (![X2 : $i, X3 : $i, X4 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ (k2_xboole_0 @ X2 @ X3) @ X4)
% 7.51/7.74           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ X4)))),
% 7.51/7.74      inference('cnf', [status(esa)], [t4_xboole_1])).
% 7.51/7.74  thf('9', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 7.51/7.74           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 7.51/7.74              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 7.51/7.74      inference('sup+', [status(thm)], ['7', '8'])).
% 7.51/7.74  thf('10', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ (k2_tarski @ X3 @ X1) @ (k2_xboole_0 @ X0 @ X2))
% 7.51/7.74           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 7.51/7.74              (k2_xboole_0 @ X2 @ (k2_xboole_0 @ (k1_tarski @ X1) @ X0))))),
% 7.51/7.74      inference('sup+', [status(thm)], ['6', '9'])).
% 7.51/7.74  thf('11', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ 
% 7.51/7.74           (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))
% 7.51/7.74           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 7.51/7.74              (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0))))),
% 7.51/7.74      inference('sup+', [status(thm)], ['5', '10'])).
% 7.51/7.74  thf('12', plain,
% 7.51/7.74      (![X5 : $i, X6 : $i]:
% 7.51/7.74         ((k2_tarski @ X5 @ X6)
% 7.51/7.74           = (k2_xboole_0 @ (k1_tarski @ X5) @ (k1_tarski @ X6)))),
% 7.51/7.74      inference('cnf', [status(esa)], [t41_enumset1])).
% 7.51/7.74  thf('13', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 7.51/7.74      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 7.51/7.74  thf('14', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 7.51/7.74           = (k2_tarski @ X1 @ X0))),
% 7.51/7.74      inference('sup+', [status(thm)], ['12', '13'])).
% 7.51/7.74  thf('15', plain,
% 7.51/7.74      (![X5 : $i, X6 : $i]:
% 7.51/7.74         ((k2_tarski @ X5 @ X6)
% 7.51/7.74           = (k2_xboole_0 @ (k1_tarski @ X5) @ (k1_tarski @ X6)))),
% 7.51/7.74      inference('cnf', [status(esa)], [t41_enumset1])).
% 7.51/7.74  thf('16', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 7.51/7.74           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 7.51/7.74              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 7.51/7.74      inference('sup+', [status(thm)], ['7', '8'])).
% 7.51/7.74  thf('17', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 7.51/7.74           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 7.51/7.74      inference('sup+', [status(thm)], ['15', '16'])).
% 7.51/7.74  thf(t42_enumset1, axiom,
% 7.51/7.74    (![A:$i,B:$i,C:$i]:
% 7.51/7.74     ( ( k1_enumset1 @ A @ B @ C ) =
% 7.51/7.74       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 7.51/7.74  thf('18', plain,
% 7.51/7.74      (![X7 : $i, X8 : $i, X9 : $i]:
% 7.51/7.74         ((k1_enumset1 @ X7 @ X8 @ X9)
% 7.51/7.74           = (k2_xboole_0 @ (k1_tarski @ X7) @ (k2_tarski @ X8 @ X9)))),
% 7.51/7.74      inference('cnf', [status(esa)], [t42_enumset1])).
% 7.51/7.74  thf('19', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 7.51/7.74           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 7.51/7.74      inference('demod', [status(thm)], ['17', '18'])).
% 7.51/7.74  thf('20', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 7.51/7.74      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 7.51/7.74  thf('21', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 7.51/7.74           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 7.51/7.74              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 7.51/7.74      inference('sup+', [status(thm)], ['7', '8'])).
% 7.51/7.74  thf('22', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ (k2_tarski @ X0 @ X2) @ X1)
% 7.51/7.74           = (k2_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ X2) @ X1) @ 
% 7.51/7.74              (k1_tarski @ X0)))),
% 7.51/7.74      inference('sup+', [status(thm)], ['20', '21'])).
% 7.51/7.74  thf('23', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1))
% 7.51/7.74           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 7.51/7.74      inference('sup+', [status(thm)], ['2', '3'])).
% 7.51/7.74  thf('24', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 7.51/7.74      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 7.51/7.74  thf('25', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X2) @ X1)
% 7.51/7.74           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 7.51/7.74      inference('sup+', [status(thm)], ['23', '24'])).
% 7.51/7.74  thf('26', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 7.51/7.74           = (k2_tarski @ X1 @ X0))),
% 7.51/7.74      inference('sup+', [status(thm)], ['12', '13'])).
% 7.51/7.74  thf('27', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ (k2_tarski @ X0 @ X2) @ X1)
% 7.51/7.74           = (k2_xboole_0 @ X1 @ (k2_tarski @ X2 @ X0)))),
% 7.51/7.74      inference('demod', [status(thm)], ['22', '25', '26'])).
% 7.51/7.74  thf('28', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.51/7.74         ((k1_enumset1 @ X2 @ X1 @ X0)
% 7.51/7.74           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X2)))),
% 7.51/7.74      inference('sup+', [status(thm)], ['19', '27'])).
% 7.51/7.74  thf('29', plain,
% 7.51/7.74      (![X7 : $i, X8 : $i, X9 : $i]:
% 7.51/7.74         ((k1_enumset1 @ X7 @ X8 @ X9)
% 7.51/7.74           = (k2_xboole_0 @ (k1_tarski @ X7) @ (k2_tarski @ X8 @ X9)))),
% 7.51/7.74      inference('cnf', [status(esa)], [t42_enumset1])).
% 7.51/7.74  thf('30', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 7.51/7.74      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 7.51/7.74  thf('31', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2))
% 7.51/7.74           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 7.51/7.74      inference('sup+', [status(thm)], ['29', '30'])).
% 7.51/7.74  thf('32', plain,
% 7.51/7.74      (![X7 : $i, X8 : $i, X9 : $i]:
% 7.51/7.74         ((k1_enumset1 @ X7 @ X8 @ X9)
% 7.51/7.74           = (k2_xboole_0 @ (k1_tarski @ X7) @ (k2_tarski @ X8 @ X9)))),
% 7.51/7.74      inference('cnf', [status(esa)], [t42_enumset1])).
% 7.51/7.74  thf('33', plain,
% 7.51/7.74      (![X2 : $i, X3 : $i, X4 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ (k2_xboole_0 @ X2 @ X3) @ X4)
% 7.51/7.74           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ X4)))),
% 7.51/7.74      inference('cnf', [status(esa)], [t4_xboole_1])).
% 7.51/7.74  thf('34', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 7.51/7.74           = (k2_xboole_0 @ (k1_tarski @ X2) @ 
% 7.51/7.74              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X3)))),
% 7.51/7.74      inference('sup+', [status(thm)], ['32', '33'])).
% 7.51/7.74  thf('35', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X1 @ X0) @ (k1_tarski @ X2))
% 7.51/7.74           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 7.51/7.74      inference('sup+', [status(thm)], ['31', '34'])).
% 7.51/7.74  thf(t44_enumset1, axiom,
% 7.51/7.74    (![A:$i,B:$i,C:$i,D:$i]:
% 7.51/7.74     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 7.51/7.74       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 7.51/7.74  thf('36', plain,
% 7.51/7.74      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 7.51/7.74         ((k2_enumset1 @ X10 @ X11 @ X12 @ X13)
% 7.51/7.74           = (k2_xboole_0 @ (k1_tarski @ X10) @ (k1_enumset1 @ X11 @ X12 @ X13)))),
% 7.51/7.74      inference('cnf', [status(esa)], [t44_enumset1])).
% 7.51/7.74  thf('37', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X1 @ X0) @ (k1_tarski @ X2))
% 7.51/7.74           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 7.51/7.74      inference('demod', [status(thm)], ['35', '36'])).
% 7.51/7.74  thf('38', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 7.51/7.74      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 7.51/7.74  thf('39', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ (k1_tarski @ X2) @ (k1_enumset1 @ X3 @ X1 @ X0))
% 7.51/7.74           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 7.51/7.74      inference('sup+', [status(thm)], ['37', '38'])).
% 7.51/7.74  thf('40', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X0 @ X1))
% 7.51/7.74           = (k2_enumset1 @ X0 @ X3 @ X1 @ X2))),
% 7.51/7.74      inference('demod', [status(thm)], ['11', '14', '28', '39'])).
% 7.51/7.74  thf('41', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 7.51/7.74           = (k2_tarski @ X1 @ X0))),
% 7.51/7.74      inference('sup+', [status(thm)], ['12', '13'])).
% 7.51/7.74  thf('42', plain,
% 7.51/7.74      (![X5 : $i, X6 : $i]:
% 7.51/7.74         ((k2_tarski @ X5 @ X6)
% 7.51/7.74           = (k2_xboole_0 @ (k1_tarski @ X5) @ (k1_tarski @ X6)))),
% 7.51/7.74      inference('cnf', [status(esa)], [t41_enumset1])).
% 7.51/7.74  thf('43', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i]: ((k2_tarski @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 7.51/7.74      inference('sup+', [status(thm)], ['41', '42'])).
% 7.51/7.74  thf('44', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 7.51/7.74           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 7.51/7.74      inference('demod', [status(thm)], ['17', '18'])).
% 7.51/7.74  thf('45', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2))
% 7.51/7.74           = (k1_enumset1 @ X0 @ X1 @ X2))),
% 7.51/7.74      inference('sup+', [status(thm)], ['43', '44'])).
% 7.51/7.74  thf('46', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 7.51/7.74           = (k2_xboole_0 @ (k1_tarski @ X2) @ 
% 7.51/7.74              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X3)))),
% 7.51/7.74      inference('sup+', [status(thm)], ['32', '33'])).
% 7.51/7.74  thf('47', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X1 @ X2) @ (k1_tarski @ X0))
% 7.51/7.74           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 7.51/7.74      inference('sup+', [status(thm)], ['45', '46'])).
% 7.51/7.74  thf('48', plain,
% 7.51/7.74      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 7.51/7.74         ((k2_enumset1 @ X10 @ X11 @ X12 @ X13)
% 7.51/7.74           = (k2_xboole_0 @ (k1_tarski @ X10) @ (k1_enumset1 @ X11 @ X12 @ X13)))),
% 7.51/7.74      inference('cnf', [status(esa)], [t44_enumset1])).
% 7.51/7.74  thf('49', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 7.51/7.74      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 7.51/7.74  thf('50', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3))
% 7.51/7.74           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 7.51/7.74      inference('sup+', [status(thm)], ['48', '49'])).
% 7.51/7.74  thf('51', plain,
% 7.51/7.74      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 7.51/7.74         ((k2_enumset1 @ X10 @ X11 @ X12 @ X13)
% 7.51/7.74           = (k2_xboole_0 @ (k1_tarski @ X10) @ (k1_enumset1 @ X11 @ X12 @ X13)))),
% 7.51/7.74      inference('cnf', [status(esa)], [t44_enumset1])).
% 7.51/7.74  thf('52', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.51/7.74         ((k2_enumset1 @ X0 @ X3 @ X1 @ X2) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 7.51/7.74      inference('demod', [status(thm)], ['47', '50', '51'])).
% 7.51/7.74  thf('53', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 7.51/7.74           = (k2_tarski @ X1 @ X0))),
% 7.51/7.74      inference('sup+', [status(thm)], ['12', '13'])).
% 7.51/7.74  thf('54', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 7.51/7.74           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 7.51/7.74              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 7.51/7.74      inference('sup+', [status(thm)], ['7', '8'])).
% 7.51/7.74  thf('55', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ (k2_tarski @ X2 @ X0) @ (k1_tarski @ X1))
% 7.51/7.74           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 7.51/7.74      inference('sup+', [status(thm)], ['53', '54'])).
% 7.51/7.74  thf('56', plain,
% 7.51/7.74      (![X7 : $i, X8 : $i, X9 : $i]:
% 7.51/7.74         ((k1_enumset1 @ X7 @ X8 @ X9)
% 7.51/7.74           = (k2_xboole_0 @ (k1_tarski @ X7) @ (k2_tarski @ X8 @ X9)))),
% 7.51/7.74      inference('cnf', [status(esa)], [t42_enumset1])).
% 7.51/7.74  thf('57', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ (k2_tarski @ X2 @ X0) @ (k1_tarski @ X1))
% 7.51/7.74           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 7.51/7.74      inference('demod', [status(thm)], ['55', '56'])).
% 7.51/7.74  thf('58', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 7.51/7.74           = (k2_xboole_0 @ (k1_tarski @ X2) @ 
% 7.51/7.74              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X3)))),
% 7.51/7.74      inference('sup+', [status(thm)], ['32', '33'])).
% 7.51/7.74  thf('59', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X0) @ (k1_tarski @ X1))
% 7.51/7.74           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 7.51/7.74      inference('sup+', [status(thm)], ['57', '58'])).
% 7.51/7.74  thf('60', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3))
% 7.51/7.74           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 7.51/7.74      inference('sup+', [status(thm)], ['48', '49'])).
% 7.51/7.74  thf('61', plain,
% 7.51/7.74      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 7.51/7.74         ((k2_enumset1 @ X10 @ X11 @ X12 @ X13)
% 7.51/7.74           = (k2_xboole_0 @ (k1_tarski @ X10) @ (k1_enumset1 @ X11 @ X12 @ X13)))),
% 7.51/7.74      inference('cnf', [status(esa)], [t44_enumset1])).
% 7.51/7.74  thf('62', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.51/7.74         ((k2_enumset1 @ X1 @ X3 @ X2 @ X0) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 7.51/7.74      inference('demod', [status(thm)], ['59', '60', '61'])).
% 7.51/7.74  thf('63', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.51/7.74         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 7.51/7.74      inference('sup+', [status(thm)], ['52', '62'])).
% 7.51/7.74  thf('64', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.51/7.74         ((k2_enumset1 @ X1 @ X3 @ X2 @ X0) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 7.51/7.74      inference('demod', [status(thm)], ['59', '60', '61'])).
% 7.51/7.74  thf('65', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 7.51/7.74           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 7.51/7.74      inference('demod', [status(thm)], ['17', '18'])).
% 7.51/7.74  thf('66', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 7.51/7.74           = (k2_xboole_0 @ (k1_tarski @ X2) @ 
% 7.51/7.74              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X3)))),
% 7.51/7.74      inference('sup+', [status(thm)], ['32', '33'])).
% 7.51/7.74  thf('67', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 7.51/7.74           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 7.51/7.74      inference('sup+', [status(thm)], ['65', '66'])).
% 7.51/7.74  thf('68', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3))
% 7.51/7.74           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 7.51/7.74      inference('sup+', [status(thm)], ['48', '49'])).
% 7.51/7.74  thf('69', plain,
% 7.51/7.74      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 7.51/7.74         ((k2_enumset1 @ X10 @ X11 @ X12 @ X13)
% 7.51/7.74           = (k2_xboole_0 @ (k1_tarski @ X10) @ (k1_enumset1 @ X11 @ X12 @ X13)))),
% 7.51/7.74      inference('cnf', [status(esa)], [t44_enumset1])).
% 7.51/7.74  thf('70', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.51/7.74         ((k2_enumset1 @ X0 @ X3 @ X2 @ X1) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 7.51/7.74      inference('demod', [status(thm)], ['67', '68', '69'])).
% 7.51/7.74  thf('71', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.51/7.74         ((k2_enumset1 @ X0 @ X1 @ X3 @ X2) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 7.51/7.74      inference('sup+', [status(thm)], ['64', '70'])).
% 7.51/7.74  thf('72', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i]: ((k2_tarski @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 7.51/7.74      inference('sup+', [status(thm)], ['41', '42'])).
% 7.51/7.74  thf('73', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2))
% 7.51/7.74           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 7.51/7.74      inference('sup+', [status(thm)], ['29', '30'])).
% 7.51/7.74  thf('74', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2))
% 7.51/7.74           = (k1_enumset1 @ X2 @ X0 @ X1))),
% 7.51/7.74      inference('sup+', [status(thm)], ['72', '73'])).
% 7.51/7.74  thf('75', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 7.51/7.74           = (k2_xboole_0 @ (k1_tarski @ X2) @ 
% 7.51/7.74              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X3)))),
% 7.51/7.74      inference('sup+', [status(thm)], ['32', '33'])).
% 7.51/7.74  thf('76', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X0 @ X1) @ (k1_tarski @ X2))
% 7.51/7.74           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 7.51/7.74      inference('sup+', [status(thm)], ['74', '75'])).
% 7.51/7.74  thf('77', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.51/7.74         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3))
% 7.51/7.74           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 7.51/7.74      inference('sup+', [status(thm)], ['48', '49'])).
% 7.51/7.74  thf('78', plain,
% 7.51/7.74      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 7.51/7.74         ((k2_enumset1 @ X10 @ X11 @ X12 @ X13)
% 7.51/7.74           = (k2_xboole_0 @ (k1_tarski @ X10) @ (k1_enumset1 @ X11 @ X12 @ X13)))),
% 7.51/7.74      inference('cnf', [status(esa)], [t44_enumset1])).
% 7.51/7.74  thf('79', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.51/7.74         ((k2_enumset1 @ X2 @ X3 @ X0 @ X1) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 7.51/7.74      inference('demod', [status(thm)], ['76', '77', '78'])).
% 7.51/7.74  thf('80', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.51/7.74         ((k2_enumset1 @ X0 @ X3 @ X2 @ X1) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 7.51/7.74      inference('demod', [status(thm)], ['67', '68', '69'])).
% 7.51/7.74  thf('81', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.51/7.74         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X3 @ X0 @ X1 @ X2))),
% 7.51/7.74      inference('sup+', [status(thm)], ['79', '80'])).
% 7.51/7.74  thf('82', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.51/7.74         ((k2_enumset1 @ X1 @ X3 @ X2 @ X0) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 7.51/7.74      inference('demod', [status(thm)], ['59', '60', '61'])).
% 7.51/7.74  thf('83', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.51/7.74         ((k2_enumset1 @ X0 @ X3 @ X2 @ X1) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 7.51/7.74      inference('demod', [status(thm)], ['67', '68', '69'])).
% 7.51/7.74  thf('84', plain,
% 7.51/7.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.51/7.74         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X3 @ X2 @ X0 @ X1))),
% 7.51/7.74      inference('sup+', [status(thm)], ['82', '83'])).
% 7.51/7.74  thf('85', plain,
% 7.51/7.74      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 7.51/7.74         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 7.51/7.74      inference('demod', [status(thm)], ['0', '40', '63', '71', '81', '84'])).
% 7.51/7.74  thf('86', plain, ($false), inference('simplify', [status(thm)], ['85'])).
% 7.51/7.74  
% 7.51/7.74  % SZS output end Refutation
% 7.51/7.74  
% 7.51/7.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

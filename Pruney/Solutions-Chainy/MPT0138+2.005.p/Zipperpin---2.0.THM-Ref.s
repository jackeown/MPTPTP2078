%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mCwqwjdayb

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:02 EST 2020

% Result     : Theorem 11.59s
% Output     : Refutation 11.59s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 219 expanded)
%              Number of leaves         :   21 (  84 expanded)
%              Depth                    :   11
%              Number of atoms          : 1072 (2332 expanded)
%              Number of equality atoms :   82 ( 206 expanded)
%              Maximal formula depth    :   17 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(t54_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_tarski @ E @ F ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
        ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
        = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_tarski @ E @ F ) ) ) ),
    inference('cnf.neg',[status(esa)],[t54_enumset1])).

thf('0',plain,(
    ( k4_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E_1 @ sk_F )
 != ( k2_xboole_0 @ ( k2_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ ( k2_tarski @ sk_E_1 @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('1',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k2_tarski @ X33 @ X34 )
      = ( k2_xboole_0 @ ( k1_tarski @ X33 ) @ ( k1_tarski @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('2',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k2_tarski @ X33 @ X34 )
      = ( k2_xboole_0 @ ( k1_tarski @ X33 ) @ ( k1_tarski @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k2_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t43_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ) )).

thf('6',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( k1_enumset1 @ X35 @ X36 @ X37 )
      = ( k2_xboole_0 @ ( k2_tarski @ X35 @ X36 ) @ ( k1_tarski @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k2_tarski @ X33 @ X34 )
      = ( k2_xboole_0 @ ( k1_tarski @ X33 ) @ ( k1_tarski @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('11',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( k1_enumset1 @ X35 @ X36 @ X37 )
      = ( k2_xboole_0 @ ( k2_tarski @ X35 @ X36 ) @ ( k1_tarski @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('12',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k2_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('15',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( k2_enumset1 @ X38 @ X39 @ X40 @ X41 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X38 @ X39 @ X40 ) @ ( k1_tarski @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','16'])).

thf('18',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k2_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k2_tarski @ X33 @ X34 )
      = ( k2_xboole_0 @ ( k1_tarski @ X33 ) @ ( k1_tarski @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k2_tarski @ X33 @ X34 )
      = ( k2_xboole_0 @ ( k1_tarski @ X33 ) @ ( k1_tarski @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t6_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k2_tarski @ X33 @ X34 )
      = ( k2_xboole_0 @ ( k1_tarski @ X33 ) @ ( k1_tarski @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf(t113_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) @ D )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ ( k2_xboole_0 @ B @ C ) @ D ) ) ) )).

thf('30',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X2 ) @ X3 ) @ X4 )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X3 ) @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t113_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X3 @ X2 ) @ X1 ) @ X0 )
      = ( k2_xboole_0 @ X3 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X3 @ X2 ) @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X2 ) @ X3 ) @ X4 )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X3 ) @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t113_xboole_1])).

thf('33',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X2 ) @ X3 ) @ X4 )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X3 ) @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t113_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X3 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ X3 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ ( k2_xboole_0 @ X3 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k2_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('36',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k2_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('37',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k2_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X3 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X3 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X3 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['34','35','36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X3 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) )
      = ( k2_xboole_0 @ X3 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ ( k2_xboole_0 @ X3 @ ( k2_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['28','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','27'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X3 @ ( k2_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X3 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ ( k2_xboole_0 @ X3 @ ( k2_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X3 @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ ( k2_xboole_0 @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['19','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('47',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k2_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf(l62_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ) )).

thf('49',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k4_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X27 @ X28 @ X29 ) @ ( k1_enumset1 @ X30 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[l62_enumset1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('53',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k2_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k1_tarski @ X0 ) ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( k1_enumset1 @ X35 @ X36 @ X37 )
      = ( k2_xboole_0 @ ( k2_tarski @ X35 @ X36 ) @ ( k1_tarski @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('58',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k2_tarski @ X33 @ X34 )
      = ( k2_xboole_0 @ ( k1_tarski @ X33 ) @ ( k1_tarski @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_enumset1 @ X0 @ X1 @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_enumset1 @ X1 @ X0 @ X1 ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['51','59'])).

thf('61',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('62',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k2_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k2_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('65',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k2_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ ( k1_enumset1 @ X0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ ( k2_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['60','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_enumset1 @ X1 @ X0 @ X1 ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['51','59'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ ( k2_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['42','45','48','49','50','69'])).

thf('71',plain,(
    ( k4_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E_1 @ sk_F )
 != ( k4_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E_1 @ sk_F ) ),
    inference(demod,[status(thm)],['0','70'])).

thf('72',plain,(
    $false ),
    inference(simplify,[status(thm)],['71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mCwqwjdayb
% 0.12/0.35  % Computer   : n012.cluster.edu
% 0.12/0.35  % Model      : x86_64 x86_64
% 0.12/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.35  % Memory     : 8042.1875MB
% 0.12/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.35  % CPULimit   : 60
% 0.12/0.35  % DateTime   : Tue Dec  1 14:02:07 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 11.59/11.81  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 11.59/11.81  % Solved by: fo/fo7.sh
% 11.59/11.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 11.59/11.81  % done 6621 iterations in 11.354s
% 11.59/11.81  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 11.59/11.81  % SZS output start Refutation
% 11.59/11.81  thf(sk_D_type, type, sk_D: $i).
% 11.59/11.81  thf(sk_E_1_type, type, sk_E_1: $i).
% 11.59/11.81  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 11.59/11.81  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 11.59/11.81  thf(sk_A_type, type, sk_A: $i).
% 11.59/11.81  thf(sk_B_type, type, sk_B: $i).
% 11.59/11.81  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 11.59/11.81  thf(sk_C_1_type, type, sk_C_1: $i).
% 11.59/11.81  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 11.59/11.81  thf(sk_F_type, type, sk_F: $i).
% 11.59/11.81  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 11.59/11.81  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 11.59/11.81  thf(t54_enumset1, conjecture,
% 11.59/11.81    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 11.59/11.81     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 11.59/11.81       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_tarski @ E @ F ) ) ))).
% 11.59/11.81  thf(zf_stmt_0, negated_conjecture,
% 11.59/11.81    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 11.59/11.81        ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 11.59/11.81          ( k2_xboole_0 @
% 11.59/11.81            ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_tarski @ E @ F ) ) ) )),
% 11.59/11.81    inference('cnf.neg', [status(esa)], [t54_enumset1])).
% 11.59/11.81  thf('0', plain,
% 11.59/11.81      (((k4_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E_1 @ sk_F)
% 11.59/11.81         != (k2_xboole_0 @ (k2_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D) @ 
% 11.59/11.81             (k2_tarski @ sk_E_1 @ sk_F)))),
% 11.59/11.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.59/11.81  thf(t41_enumset1, axiom,
% 11.59/11.81    (![A:$i,B:$i]:
% 11.59/11.81     ( ( k2_tarski @ A @ B ) =
% 11.59/11.81       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 11.59/11.81  thf('1', plain,
% 11.59/11.81      (![X33 : $i, X34 : $i]:
% 11.59/11.81         ((k2_tarski @ X33 @ X34)
% 11.59/11.81           = (k2_xboole_0 @ (k1_tarski @ X33) @ (k1_tarski @ X34)))),
% 11.59/11.81      inference('cnf', [status(esa)], [t41_enumset1])).
% 11.59/11.81  thf('2', plain,
% 11.59/11.81      (![X33 : $i, X34 : $i]:
% 11.59/11.81         ((k2_tarski @ X33 @ X34)
% 11.59/11.81           = (k2_xboole_0 @ (k1_tarski @ X33) @ (k1_tarski @ X34)))),
% 11.59/11.81      inference('cnf', [status(esa)], [t41_enumset1])).
% 11.59/11.81  thf(t4_xboole_1, axiom,
% 11.59/11.81    (![A:$i,B:$i,C:$i]:
% 11.59/11.81     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 11.59/11.81       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 11.59/11.81  thf('3', plain,
% 11.59/11.81      (![X5 : $i, X6 : $i, X7 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ (k2_xboole_0 @ X5 @ X6) @ X7)
% 11.59/11.81           = (k2_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 11.59/11.81      inference('cnf', [status(esa)], [t4_xboole_1])).
% 11.59/11.81  thf('4', plain,
% 11.59/11.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 11.59/11.81           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 11.59/11.81              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 11.59/11.81      inference('sup+', [status(thm)], ['2', '3'])).
% 11.59/11.81  thf('5', plain,
% 11.59/11.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 11.59/11.81           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 11.59/11.81      inference('sup+', [status(thm)], ['1', '4'])).
% 11.59/11.81  thf(t43_enumset1, axiom,
% 11.59/11.81    (![A:$i,B:$i,C:$i]:
% 11.59/11.81     ( ( k1_enumset1 @ A @ B @ C ) =
% 11.59/11.81       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ))).
% 11.59/11.81  thf('6', plain,
% 11.59/11.81      (![X35 : $i, X36 : $i, X37 : $i]:
% 11.59/11.81         ((k1_enumset1 @ X35 @ X36 @ X37)
% 11.59/11.81           = (k2_xboole_0 @ (k2_tarski @ X35 @ X36) @ (k1_tarski @ X37)))),
% 11.59/11.81      inference('cnf', [status(esa)], [t43_enumset1])).
% 11.59/11.81  thf('7', plain,
% 11.59/11.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.59/11.81         ((k1_enumset1 @ X2 @ X1 @ X0)
% 11.59/11.81           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 11.59/11.81      inference('demod', [status(thm)], ['5', '6'])).
% 11.59/11.81  thf('8', plain,
% 11.59/11.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 11.59/11.81           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 11.59/11.81              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 11.59/11.81      inference('sup+', [status(thm)], ['2', '3'])).
% 11.59/11.81  thf('9', plain,
% 11.59/11.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0))
% 11.59/11.81           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 11.59/11.81      inference('sup+', [status(thm)], ['7', '8'])).
% 11.59/11.81  thf('10', plain,
% 11.59/11.81      (![X33 : $i, X34 : $i]:
% 11.59/11.81         ((k2_tarski @ X33 @ X34)
% 11.59/11.81           = (k2_xboole_0 @ (k1_tarski @ X33) @ (k1_tarski @ X34)))),
% 11.59/11.81      inference('cnf', [status(esa)], [t41_enumset1])).
% 11.59/11.81  thf('11', plain,
% 11.59/11.81      (![X35 : $i, X36 : $i, X37 : $i]:
% 11.59/11.81         ((k1_enumset1 @ X35 @ X36 @ X37)
% 11.59/11.81           = (k2_xboole_0 @ (k2_tarski @ X35 @ X36) @ (k1_tarski @ X37)))),
% 11.59/11.81      inference('cnf', [status(esa)], [t43_enumset1])).
% 11.59/11.81  thf('12', plain,
% 11.59/11.81      (![X5 : $i, X6 : $i, X7 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ (k2_xboole_0 @ X5 @ X6) @ X7)
% 11.59/11.81           = (k2_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 11.59/11.81      inference('cnf', [status(esa)], [t4_xboole_1])).
% 11.59/11.81  thf('13', plain,
% 11.59/11.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 11.59/11.81           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ 
% 11.59/11.81              (k2_xboole_0 @ (k1_tarski @ X0) @ X3)))),
% 11.59/11.81      inference('sup+', [status(thm)], ['11', '12'])).
% 11.59/11.81  thf('14', plain,
% 11.59/11.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 11.59/11.81           = (k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0)))),
% 11.59/11.81      inference('sup+', [status(thm)], ['10', '13'])).
% 11.59/11.81  thf(t46_enumset1, axiom,
% 11.59/11.81    (![A:$i,B:$i,C:$i,D:$i]:
% 11.59/11.81     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 11.59/11.81       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 11.59/11.81  thf('15', plain,
% 11.59/11.81      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 11.59/11.81         ((k2_enumset1 @ X38 @ X39 @ X40 @ X41)
% 11.59/11.81           = (k2_xboole_0 @ (k1_enumset1 @ X38 @ X39 @ X40) @ (k1_tarski @ X41)))),
% 11.59/11.81      inference('cnf', [status(esa)], [t46_enumset1])).
% 11.59/11.81  thf('16', plain,
% 11.59/11.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.59/11.81         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 11.59/11.81           = (k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0)))),
% 11.59/11.81      inference('sup+', [status(thm)], ['14', '15'])).
% 11.59/11.81  thf('17', plain,
% 11.59/11.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.59/11.81         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 11.59/11.81           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 11.59/11.81      inference('demod', [status(thm)], ['9', '16'])).
% 11.59/11.81  thf('18', plain,
% 11.59/11.81      (![X5 : $i, X6 : $i, X7 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ (k2_xboole_0 @ X5 @ X6) @ X7)
% 11.59/11.81           = (k2_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 11.59/11.81      inference('cnf', [status(esa)], [t4_xboole_1])).
% 11.59/11.81  thf('19', plain,
% 11.59/11.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4)
% 11.59/11.81           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 11.59/11.81              (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X4)))),
% 11.59/11.81      inference('sup+', [status(thm)], ['17', '18'])).
% 11.59/11.81  thf('20', plain,
% 11.59/11.81      (![X33 : $i, X34 : $i]:
% 11.59/11.81         ((k2_tarski @ X33 @ X34)
% 11.59/11.81           = (k2_xboole_0 @ (k1_tarski @ X33) @ (k1_tarski @ X34)))),
% 11.59/11.81      inference('cnf', [status(esa)], [t41_enumset1])).
% 11.59/11.81  thf(idempotence_k2_xboole_0, axiom,
% 11.59/11.81    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 11.59/11.81  thf('21', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 11.59/11.81      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 11.59/11.81  thf('22', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 11.59/11.81      inference('sup+', [status(thm)], ['20', '21'])).
% 11.59/11.81  thf('23', plain,
% 11.59/11.81      (![X33 : $i, X34 : $i]:
% 11.59/11.81         ((k2_tarski @ X33 @ X34)
% 11.59/11.81           = (k2_xboole_0 @ (k1_tarski @ X33) @ (k1_tarski @ X34)))),
% 11.59/11.81      inference('cnf', [status(esa)], [t41_enumset1])).
% 11.59/11.81  thf(t6_xboole_1, axiom,
% 11.59/11.81    (![A:$i,B:$i]:
% 11.59/11.81     ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 11.59/11.81  thf('24', plain,
% 11.59/11.81      (![X8 : $i, X9 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ X8 @ (k2_xboole_0 @ X8 @ X9))
% 11.59/11.81           = (k2_xboole_0 @ X8 @ X9))),
% 11.59/11.81      inference('cnf', [status(esa)], [t6_xboole_1])).
% 11.59/11.81  thf('25', plain,
% 11.59/11.81      (![X0 : $i, X1 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 11.59/11.81           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 11.59/11.81      inference('sup+', [status(thm)], ['23', '24'])).
% 11.59/11.81  thf('26', plain,
% 11.59/11.81      (![X33 : $i, X34 : $i]:
% 11.59/11.81         ((k2_tarski @ X33 @ X34)
% 11.59/11.81           = (k2_xboole_0 @ (k1_tarski @ X33) @ (k1_tarski @ X34)))),
% 11.59/11.81      inference('cnf', [status(esa)], [t41_enumset1])).
% 11.59/11.81  thf('27', plain,
% 11.59/11.81      (![X0 : $i, X1 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 11.59/11.81           = (k2_tarski @ X1 @ X0))),
% 11.59/11.81      inference('demod', [status(thm)], ['25', '26'])).
% 11.59/11.81  thf('28', plain,
% 11.59/11.81      (![X0 : $i, X1 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k2_tarski @ X0 @ X1))
% 11.59/11.81           = (k2_tarski @ X0 @ X1))),
% 11.59/11.81      inference('sup+', [status(thm)], ['22', '27'])).
% 11.59/11.81  thf('29', plain,
% 11.59/11.81      (![X8 : $i, X9 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ X8 @ (k2_xboole_0 @ X8 @ X9))
% 11.59/11.81           = (k2_xboole_0 @ X8 @ X9))),
% 11.59/11.81      inference('cnf', [status(esa)], [t6_xboole_1])).
% 11.59/11.81  thf(t113_xboole_1, axiom,
% 11.59/11.81    (![A:$i,B:$i,C:$i,D:$i]:
% 11.59/11.81     ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) @ D ) =
% 11.59/11.81       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ ( k2_xboole_0 @ B @ C ) @ D ) ) ))).
% 11.59/11.81  thf('30', plain,
% 11.59/11.81      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ X3) @ X4)
% 11.59/11.81           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X3) @ X4)))),
% 11.59/11.81      inference('cnf', [status(esa)], [t113_xboole_1])).
% 11.59/11.81  thf('31', plain,
% 11.59/11.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ (k2_xboole_0 @ (k2_xboole_0 @ X3 @ X2) @ X1) @ X0)
% 11.59/11.81           = (k2_xboole_0 @ X3 @ 
% 11.59/11.81              (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ 
% 11.59/11.81               (k2_xboole_0 @ (k2_xboole_0 @ (k2_xboole_0 @ X3 @ X2) @ X1) @ X0))))),
% 11.59/11.81      inference('sup+', [status(thm)], ['29', '30'])).
% 11.59/11.81  thf('32', plain,
% 11.59/11.81      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ X3) @ X4)
% 11.59/11.81           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X3) @ X4)))),
% 11.59/11.81      inference('cnf', [status(esa)], [t113_xboole_1])).
% 11.59/11.81  thf('33', plain,
% 11.59/11.81      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ X3) @ X4)
% 11.59/11.81           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X3) @ X4)))),
% 11.59/11.81      inference('cnf', [status(esa)], [t113_xboole_1])).
% 11.59/11.81  thf('34', plain,
% 11.59/11.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ X3 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))
% 11.59/11.81           = (k2_xboole_0 @ X3 @ 
% 11.59/11.81              (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ 
% 11.59/11.81               (k2_xboole_0 @ X3 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)))))),
% 11.59/11.81      inference('demod', [status(thm)], ['31', '32', '33'])).
% 11.59/11.81  thf('35', plain,
% 11.59/11.81      (![X5 : $i, X6 : $i, X7 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ (k2_xboole_0 @ X5 @ X6) @ X7)
% 11.59/11.81           = (k2_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 11.59/11.81      inference('cnf', [status(esa)], [t4_xboole_1])).
% 11.59/11.81  thf('36', plain,
% 11.59/11.81      (![X5 : $i, X6 : $i, X7 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ (k2_xboole_0 @ X5 @ X6) @ X7)
% 11.59/11.81           = (k2_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 11.59/11.81      inference('cnf', [status(esa)], [t4_xboole_1])).
% 11.59/11.81  thf('37', plain,
% 11.59/11.81      (![X5 : $i, X6 : $i, X7 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ (k2_xboole_0 @ X5 @ X6) @ X7)
% 11.59/11.81           = (k2_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 11.59/11.81      inference('cnf', [status(esa)], [t4_xboole_1])).
% 11.59/11.81  thf('38', plain,
% 11.59/11.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ X3 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 11.59/11.81           = (k2_xboole_0 @ X3 @ 
% 11.59/11.81              (k2_xboole_0 @ X2 @ 
% 11.59/11.81               (k2_xboole_0 @ X1 @ 
% 11.59/11.81                (k2_xboole_0 @ X3 @ 
% 11.59/11.81                 (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))))),
% 11.59/11.81      inference('demod', [status(thm)], ['34', '35', '36', '37'])).
% 11.59/11.81  thf('39', plain,
% 11.59/11.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ X3 @ 
% 11.59/11.81           (k2_xboole_0 @ X2 @ 
% 11.59/11.81            (k2_xboole_0 @ (k2_tarski @ X1 @ X1) @ (k2_tarski @ X1 @ X0))))
% 11.59/11.81           = (k2_xboole_0 @ X3 @ 
% 11.59/11.81              (k2_xboole_0 @ X2 @ 
% 11.59/11.81               (k2_xboole_0 @ (k2_tarski @ X1 @ X1) @ 
% 11.59/11.81                (k2_xboole_0 @ X3 @ (k2_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)))))))),
% 11.59/11.81      inference('sup+', [status(thm)], ['28', '38'])).
% 11.59/11.81  thf('40', plain,
% 11.59/11.81      (![X0 : $i, X1 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k2_tarski @ X0 @ X1))
% 11.59/11.81           = (k2_tarski @ X0 @ X1))),
% 11.59/11.81      inference('sup+', [status(thm)], ['22', '27'])).
% 11.59/11.81  thf('41', plain,
% 11.59/11.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ X3 @ (k2_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)))
% 11.59/11.81           = (k2_xboole_0 @ X3 @ 
% 11.59/11.81              (k2_xboole_0 @ X2 @ 
% 11.59/11.81               (k2_xboole_0 @ (k2_tarski @ X1 @ X1) @ 
% 11.59/11.81                (k2_xboole_0 @ X3 @ (k2_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)))))))),
% 11.59/11.81      inference('demod', [status(thm)], ['39', '40'])).
% 11.59/11.81  thf('42', plain,
% 11.59/11.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ (k1_tarski @ X5) @ 
% 11.59/11.81           (k2_xboole_0 @ (k1_enumset1 @ X4 @ X3 @ X2) @ (k2_tarski @ X1 @ X0)))
% 11.59/11.81           = (k2_xboole_0 @ (k1_tarski @ X5) @ 
% 11.59/11.81              (k2_xboole_0 @ (k1_enumset1 @ X4 @ X3 @ X2) @ 
% 11.59/11.81               (k2_xboole_0 @ (k2_tarski @ X1 @ X1) @ 
% 11.59/11.81                (k2_xboole_0 @ (k2_enumset1 @ X5 @ X4 @ X3 @ X2) @ 
% 11.59/11.81                 (k2_tarski @ X1 @ X0))))))),
% 11.59/11.81      inference('sup+', [status(thm)], ['19', '41'])).
% 11.59/11.81  thf('43', plain,
% 11.59/11.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.59/11.81         ((k1_enumset1 @ X2 @ X1 @ X0)
% 11.59/11.81           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 11.59/11.81      inference('demod', [status(thm)], ['5', '6'])).
% 11.59/11.81  thf('44', plain,
% 11.59/11.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 11.59/11.81           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ 
% 11.59/11.81              (k2_xboole_0 @ (k1_tarski @ X0) @ X3)))),
% 11.59/11.81      inference('sup+', [status(thm)], ['11', '12'])).
% 11.59/11.81  thf('45', plain,
% 11.59/11.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ (k1_enumset1 @ X4 @ X3 @ X2) @ (k2_tarski @ X1 @ X0))
% 11.59/11.81           = (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ 
% 11.59/11.81              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 11.59/11.81      inference('sup+', [status(thm)], ['43', '44'])).
% 11.59/11.81  thf('46', plain,
% 11.59/11.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.59/11.81         ((k1_enumset1 @ X2 @ X1 @ X0)
% 11.59/11.81           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 11.59/11.81      inference('demod', [status(thm)], ['5', '6'])).
% 11.59/11.81  thf('47', plain,
% 11.59/11.81      (![X5 : $i, X6 : $i, X7 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ (k2_xboole_0 @ X5 @ X6) @ X7)
% 11.59/11.81           = (k2_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 11.59/11.81      inference('cnf', [status(esa)], [t4_xboole_1])).
% 11.59/11.81  thf('48', plain,
% 11.59/11.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 11.59/11.81           = (k2_xboole_0 @ (k1_tarski @ X2) @ 
% 11.59/11.81              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X3)))),
% 11.59/11.81      inference('sup+', [status(thm)], ['46', '47'])).
% 11.59/11.81  thf(l62_enumset1, axiom,
% 11.59/11.81    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 11.59/11.81     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 11.59/11.81       ( k2_xboole_0 @
% 11.59/11.81         ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ))).
% 11.59/11.81  thf('49', plain,
% 11.59/11.81      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 11.59/11.81         ((k4_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32)
% 11.59/11.81           = (k2_xboole_0 @ (k1_enumset1 @ X27 @ X28 @ X29) @ 
% 11.59/11.81              (k1_enumset1 @ X30 @ X31 @ X32)))),
% 11.59/11.81      inference('cnf', [status(esa)], [l62_enumset1])).
% 11.59/11.81  thf('50', plain,
% 11.59/11.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4)
% 11.59/11.81           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 11.59/11.81              (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X4)))),
% 11.59/11.81      inference('sup+', [status(thm)], ['17', '18'])).
% 11.59/11.81  thf('51', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 11.59/11.81      inference('sup+', [status(thm)], ['20', '21'])).
% 11.59/11.81  thf('52', plain,
% 11.59/11.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 11.59/11.81           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 11.59/11.81              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 11.59/11.81      inference('sup+', [status(thm)], ['2', '3'])).
% 11.59/11.81  thf('53', plain,
% 11.59/11.81      (![X5 : $i, X6 : $i, X7 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ (k2_xboole_0 @ X5 @ X6) @ X7)
% 11.59/11.81           = (k2_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 11.59/11.81      inference('cnf', [status(esa)], [t4_xboole_1])).
% 11.59/11.81  thf('54', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 11.59/11.81      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 11.59/11.81  thf('55', plain,
% 11.59/11.81      (![X0 : $i, X1 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))
% 11.59/11.81           = (k2_xboole_0 @ X1 @ X0))),
% 11.59/11.81      inference('sup+', [status(thm)], ['53', '54'])).
% 11.59/11.81  thf('56', plain,
% 11.59/11.81      (![X0 : $i, X1 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ (k1_tarski @ X1) @ 
% 11.59/11.81           (k2_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k1_tarski @ X0)))
% 11.59/11.81           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 11.59/11.81      inference('sup+', [status(thm)], ['52', '55'])).
% 11.59/11.81  thf('57', plain,
% 11.59/11.81      (![X35 : $i, X36 : $i, X37 : $i]:
% 11.59/11.81         ((k1_enumset1 @ X35 @ X36 @ X37)
% 11.59/11.81           = (k2_xboole_0 @ (k2_tarski @ X35 @ X36) @ (k1_tarski @ X37)))),
% 11.59/11.81      inference('cnf', [status(esa)], [t43_enumset1])).
% 11.59/11.81  thf('58', plain,
% 11.59/11.81      (![X33 : $i, X34 : $i]:
% 11.59/11.81         ((k2_tarski @ X33 @ X34)
% 11.59/11.81           = (k2_xboole_0 @ (k1_tarski @ X33) @ (k1_tarski @ X34)))),
% 11.59/11.81      inference('cnf', [status(esa)], [t41_enumset1])).
% 11.59/11.81  thf('59', plain,
% 11.59/11.81      (![X0 : $i, X1 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_enumset1 @ X0 @ X1 @ X0))
% 11.59/11.81           = (k2_tarski @ X1 @ X0))),
% 11.59/11.81      inference('demod', [status(thm)], ['56', '57', '58'])).
% 11.59/11.81  thf('60', plain,
% 11.59/11.81      (![X0 : $i, X1 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_enumset1 @ X1 @ X0 @ X1))
% 11.59/11.81           = (k2_tarski @ X0 @ X1))),
% 11.59/11.81      inference('sup+', [status(thm)], ['51', '59'])).
% 11.59/11.81  thf('61', plain,
% 11.59/11.81      (![X8 : $i, X9 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ X8 @ (k2_xboole_0 @ X8 @ X9))
% 11.59/11.81           = (k2_xboole_0 @ X8 @ X9))),
% 11.59/11.81      inference('cnf', [status(esa)], [t6_xboole_1])).
% 11.59/11.81  thf('62', plain,
% 11.59/11.81      (![X5 : $i, X6 : $i, X7 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ (k2_xboole_0 @ X5 @ X6) @ X7)
% 11.59/11.81           = (k2_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 11.59/11.81      inference('cnf', [status(esa)], [t4_xboole_1])).
% 11.59/11.81  thf('63', plain,
% 11.59/11.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)
% 11.59/11.81           = (k2_xboole_0 @ X2 @ 
% 11.59/11.81              (k2_xboole_0 @ X1 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))))),
% 11.59/11.81      inference('sup+', [status(thm)], ['61', '62'])).
% 11.59/11.81  thf('64', plain,
% 11.59/11.81      (![X5 : $i, X6 : $i, X7 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ (k2_xboole_0 @ X5 @ X6) @ X7)
% 11.59/11.81           = (k2_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 11.59/11.81      inference('cnf', [status(esa)], [t4_xboole_1])).
% 11.59/11.81  thf('65', plain,
% 11.59/11.81      (![X5 : $i, X6 : $i, X7 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ (k2_xboole_0 @ X5 @ X6) @ X7)
% 11.59/11.81           = (k2_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 11.59/11.81      inference('cnf', [status(esa)], [t4_xboole_1])).
% 11.59/11.81  thf('66', plain,
% 11.59/11.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 11.59/11.81           = (k2_xboole_0 @ X2 @ 
% 11.59/11.81              (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 11.59/11.81      inference('demod', [status(thm)], ['63', '64', '65'])).
% 11.59/11.81  thf('67', plain,
% 11.59/11.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ X2 @ 
% 11.59/11.81           (k2_xboole_0 @ (k2_tarski @ X1 @ X1) @ (k1_enumset1 @ X0 @ X1 @ X0)))
% 11.59/11.81           = (k2_xboole_0 @ X2 @ 
% 11.59/11.81              (k2_xboole_0 @ (k2_tarski @ X1 @ X1) @ 
% 11.59/11.81               (k2_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)))))),
% 11.59/11.81      inference('sup+', [status(thm)], ['60', '66'])).
% 11.59/11.81  thf('68', plain,
% 11.59/11.81      (![X0 : $i, X1 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_enumset1 @ X1 @ X0 @ X1))
% 11.59/11.81           = (k2_tarski @ X0 @ X1))),
% 11.59/11.81      inference('sup+', [status(thm)], ['51', '59'])).
% 11.59/11.81  thf('69', plain,
% 11.59/11.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.59/11.81         ((k2_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0))
% 11.59/11.81           = (k2_xboole_0 @ X2 @ 
% 11.59/11.81              (k2_xboole_0 @ (k2_tarski @ X1 @ X1) @ 
% 11.59/11.81               (k2_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)))))),
% 11.59/11.81      inference('demod', [status(thm)], ['67', '68'])).
% 11.59/11.81  thf('70', plain,
% 11.59/11.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 11.59/11.81         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 11.59/11.81           = (k2_xboole_0 @ (k2_enumset1 @ X5 @ X4 @ X3 @ X2) @ 
% 11.59/11.81              (k2_tarski @ X1 @ X0)))),
% 11.59/11.81      inference('demod', [status(thm)], ['42', '45', '48', '49', '50', '69'])).
% 11.59/11.81  thf('71', plain,
% 11.59/11.81      (((k4_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E_1 @ sk_F)
% 11.59/11.81         != (k4_enumset1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E_1 @ sk_F))),
% 11.59/11.81      inference('demod', [status(thm)], ['0', '70'])).
% 11.59/11.81  thf('72', plain, ($false), inference('simplify', [status(thm)], ['71'])).
% 11.59/11.81  
% 11.59/11.81  % SZS output end Refutation
% 11.59/11.81  
% 11.59/11.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

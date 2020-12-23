%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.O3yf0cb7Ri

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:48 EST 2020

% Result     : Theorem 31.89s
% Output     : Refutation 31.89s
% Verified   : 
% Statistics : Number of formulae       :  177 (1202 expanded)
%              Number of leaves         :   38 ( 431 expanded)
%              Depth                    :   31
%              Number of atoms          : 1832 (10903 expanded)
%              Number of equality atoms :  151 (1176 expanded)
%              Maximal formula depth    :   18 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t63_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
     => ( r2_hidden @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          = ( k2_tarski @ A @ B ) )
       => ( r2_hidden @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t63_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['1','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('12',plain,
    ( ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('14',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('15',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('17',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('18',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('20',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('21',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','25'])).

thf('27',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['12','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('29',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = ( k5_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('31',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k5_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('39',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ( k5_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) )
    = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['37','45'])).

thf('47',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','25'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('50',plain,
    ( k1_xboole_0
    = ( k5_xboole_0 @ sk_C @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','24'])).

thf('52',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = ( k5_xboole_0 @ sk_C @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('54',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['52','53'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('55',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( k4_enumset1 @ X40 @ X40 @ X41 @ X42 @ X43 @ X44 )
      = ( k3_enumset1 @ X40 @ X41 @ X42 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('56',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ( k6_enumset1 @ X51 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 )
      = ( k5_enumset1 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('57',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( k5_enumset1 @ X45 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 )
      = ( k4_enumset1 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('59',plain,(
    ! [X30: $i] :
      ( ( k2_tarski @ X30 @ X30 )
      = ( k1_tarski @ X30 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t67_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ) )).

thf('60',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( k6_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 ) @ ( k2_tarski @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t67_enumset1])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf(t61_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ) )).

thf('62',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k5_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 ) @ ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t61_enumset1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','63'])).

thf('65',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( k5_enumset1 @ X45 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 )
      = ( k4_enumset1 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('66',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( k4_enumset1 @ X40 @ X40 @ X41 @ X42 @ X43 @ X44 )
      = ( k3_enumset1 @ X40 @ X41 @ X42 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','68'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('70',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( k3_enumset1 @ X36 @ X36 @ X37 @ X38 @ X39 )
      = ( k2_enumset1 @ X36 @ X37 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( k3_enumset1 @ X36 @ X36 @ X37 @ X38 @ X39 )
      = ( k2_enumset1 @ X36 @ X37 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('74',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( k2_enumset1 @ X33 @ X33 @ X34 @ X35 )
      = ( k1_enumset1 @ X33 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t100_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ B @ C @ A ) ) )).

thf('75',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k1_enumset1 @ X14 @ X12 @ X13 )
      = ( k1_enumset1 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('76',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_enumset1 @ X31 @ X31 @ X32 )
      = ( k2_tarski @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('77',plain,(
    ! [X58: $i,X59: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X58 @ X59 ) )
      = ( k2_xboole_0 @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k1_enumset1 @ X1 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['75','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_enumset1 @ X1 @ X1 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['74','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['73','80'])).

thf('82',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( k2_enumset1 @ X33 @ X33 @ X34 @ X35 )
      = ( k1_enumset1 @ X33 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['81','84'])).

thf('86',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['54','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('88',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','25'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = ( k5_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('94',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['52','53'])).

thf('95',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['52','53'])).

thf('96',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = ( k5_xboole_0 @ ( k3_xboole_0 @ sk_C @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k2_xboole_0 @ sk_C @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ sk_C @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k5_xboole_0 @ ( k2_xboole_0 @ sk_C @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ ( k2_xboole_0 @ sk_C @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ X0 ) @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ sk_C @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ sk_C @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k5_xboole_0 @ ( k2_xboole_0 @ sk_C @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X1 ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['100','101','102','103'])).

thf('105',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','25'])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X2 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X2 @ X0 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X1 ) @ ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['104','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('111',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X2 ) @ X1 )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X2 ) @ X1 )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X2 ) @ X1 )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X2 ) @ X1 )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X2 ) @ X1 )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X2 ) @ X1 )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X2 ) @ X1 )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X2 ) @ X1 )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X2 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X2 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['108','111','112','113','114','115','116','117','118','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['92','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','25'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['87','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_C @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['86','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','24'])).

thf('132',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('133',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('134',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ),
    inference('sup+',[status(thm)],['132','133'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('135',plain,(
    ! [X60: $i,X61: $i,X62: $i] :
      ( ( r2_hidden @ X60 @ X61 )
      | ~ ( r1_tarski @ ( k2_tarski @ X60 @ X62 ) @ X61 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('136',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    $false ),
    inference(demod,[status(thm)],['0','136'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.O3yf0cb7Ri
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:52:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.33  % Python version: Python 3.6.8
% 0.13/0.33  % Running in FO mode
% 31.89/32.08  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 31.89/32.08  % Solved by: fo/fo7.sh
% 31.89/32.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 31.89/32.08  % done 5436 iterations in 31.595s
% 31.89/32.08  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 31.89/32.08  % SZS output start Refutation
% 31.89/32.08  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 31.89/32.08  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 31.89/32.08  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 31.89/32.08  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 31.89/32.08  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 31.89/32.08  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 31.89/32.08  thf(sk_C_type, type, sk_C: $i).
% 31.89/32.08  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 31.89/32.08  thf(sk_B_type, type, sk_B: $i).
% 31.89/32.08  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 31.89/32.08  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 31.89/32.08  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 31.89/32.08  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 31.89/32.08  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 31.89/32.08                                           $i > $i).
% 31.89/32.08  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 31.89/32.08  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 31.89/32.08  thf(sk_A_type, type, sk_A: $i).
% 31.89/32.08  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 31.89/32.08  thf(t63_zfmisc_1, conjecture,
% 31.89/32.08    (![A:$i,B:$i,C:$i]:
% 31.89/32.08     ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) =>
% 31.89/32.08       ( r2_hidden @ A @ C ) ))).
% 31.89/32.08  thf(zf_stmt_0, negated_conjecture,
% 31.89/32.08    (~( ![A:$i,B:$i,C:$i]:
% 31.89/32.08        ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) =>
% 31.89/32.08          ( r2_hidden @ A @ C ) ) )),
% 31.89/32.08    inference('cnf.neg', [status(esa)], [t63_zfmisc_1])).
% 31.89/32.08  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 31.89/32.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.89/32.08  thf('1', plain,
% 31.89/32.08      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 31.89/32.08         = (k2_tarski @ sk_A @ sk_B))),
% 31.89/32.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.89/32.08  thf(t95_xboole_1, axiom,
% 31.89/32.08    (![A:$i,B:$i]:
% 31.89/32.08     ( ( k3_xboole_0 @ A @ B ) =
% 31.89/32.08       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 31.89/32.08  thf('2', plain,
% 31.89/32.08      (![X10 : $i, X11 : $i]:
% 31.89/32.08         ((k3_xboole_0 @ X10 @ X11)
% 31.89/32.08           = (k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ 
% 31.89/32.08              (k2_xboole_0 @ X10 @ X11)))),
% 31.89/32.08      inference('cnf', [status(esa)], [t95_xboole_1])).
% 31.89/32.08  thf(commutativity_k5_xboole_0, axiom,
% 31.89/32.08    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 31.89/32.08  thf('3', plain,
% 31.89/32.08      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 31.89/32.08      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 31.89/32.08  thf('4', plain,
% 31.89/32.08      (![X10 : $i, X11 : $i]:
% 31.89/32.08         ((k3_xboole_0 @ X10 @ X11)
% 31.89/32.08           = (k5_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ 
% 31.89/32.08              (k5_xboole_0 @ X10 @ X11)))),
% 31.89/32.08      inference('demod', [status(thm)], ['2', '3'])).
% 31.89/32.08  thf('5', plain,
% 31.89/32.08      (![X10 : $i, X11 : $i]:
% 31.89/32.08         ((k3_xboole_0 @ X10 @ X11)
% 31.89/32.08           = (k5_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ 
% 31.89/32.08              (k5_xboole_0 @ X10 @ X11)))),
% 31.89/32.08      inference('demod', [status(thm)], ['2', '3'])).
% 31.89/32.08  thf('6', plain,
% 31.89/32.08      (![X0 : $i, X1 : $i]:
% 31.89/32.08         ((k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 31.89/32.08           = (k5_xboole_0 @ 
% 31.89/32.08              (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)) @ 
% 31.89/32.08              (k3_xboole_0 @ X1 @ X0)))),
% 31.89/32.08      inference('sup+', [status(thm)], ['4', '5'])).
% 31.89/32.08  thf('7', plain,
% 31.89/32.08      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 31.89/32.08      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 31.89/32.08  thf('8', plain,
% 31.89/32.08      (![X0 : $i, X1 : $i]:
% 31.89/32.08         ((k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 31.89/32.08           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 31.89/32.08              (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))))),
% 31.89/32.08      inference('demod', [status(thm)], ['6', '7'])).
% 31.89/32.08  thf('9', plain,
% 31.89/32.08      (((k3_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 31.89/32.08         (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))
% 31.89/32.08         = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 31.89/32.08            (k2_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 31.89/32.08             (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))))),
% 31.89/32.08      inference('sup+', [status(thm)], ['1', '8'])).
% 31.89/32.08  thf('10', plain,
% 31.89/32.08      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 31.89/32.08      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 31.89/32.08  thf('11', plain,
% 31.89/32.08      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 31.89/32.08      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 31.89/32.08  thf('12', plain,
% 31.89/32.08      (((k3_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 31.89/32.08         (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))
% 31.89/32.08         = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 31.89/32.08            (k2_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 31.89/32.08             (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))))),
% 31.89/32.08      inference('demod', [status(thm)], ['9', '10', '11'])).
% 31.89/32.08  thf('13', plain,
% 31.89/32.08      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 31.89/32.08      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 31.89/32.08  thf(t92_xboole_1, axiom,
% 31.89/32.08    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 31.89/32.08  thf('14', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 31.89/32.08      inference('cnf', [status(esa)], [t92_xboole_1])).
% 31.89/32.08  thf(t91_xboole_1, axiom,
% 31.89/32.08    (![A:$i,B:$i,C:$i]:
% 31.89/32.08     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 31.89/32.08       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 31.89/32.08  thf('15', plain,
% 31.89/32.08      (![X6 : $i, X7 : $i, X8 : $i]:
% 31.89/32.08         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 31.89/32.08           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 31.89/32.08      inference('cnf', [status(esa)], [t91_xboole_1])).
% 31.89/32.08  thf('16', plain,
% 31.89/32.08      (![X0 : $i, X1 : $i]:
% 31.89/32.08         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 31.89/32.08           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 31.89/32.08      inference('sup+', [status(thm)], ['14', '15'])).
% 31.89/32.08  thf(idempotence_k2_xboole_0, axiom,
% 31.89/32.08    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 31.89/32.08  thf('17', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 31.89/32.08      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 31.89/32.08  thf('18', plain,
% 31.89/32.08      (![X10 : $i, X11 : $i]:
% 31.89/32.08         ((k3_xboole_0 @ X10 @ X11)
% 31.89/32.08           = (k5_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ 
% 31.89/32.08              (k5_xboole_0 @ X10 @ X11)))),
% 31.89/32.08      inference('demod', [status(thm)], ['2', '3'])).
% 31.89/32.08  thf('19', plain,
% 31.89/32.08      (![X0 : $i]:
% 31.89/32.08         ((k3_xboole_0 @ X0 @ X0)
% 31.89/32.08           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 31.89/32.08      inference('sup+', [status(thm)], ['17', '18'])).
% 31.89/32.08  thf(idempotence_k3_xboole_0, axiom,
% 31.89/32.08    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 31.89/32.08  thf('20', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 31.89/32.08      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 31.89/32.08  thf('21', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 31.89/32.08      inference('cnf', [status(esa)], [t92_xboole_1])).
% 31.89/32.08  thf('22', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 31.89/32.08      inference('demod', [status(thm)], ['19', '20', '21'])).
% 31.89/32.08  thf('23', plain,
% 31.89/32.08      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 31.89/32.08      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 31.89/32.08  thf('24', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 31.89/32.08      inference('sup+', [status(thm)], ['22', '23'])).
% 31.89/32.08  thf('25', plain,
% 31.89/32.08      (![X0 : $i, X1 : $i]:
% 31.89/32.08         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 31.89/32.08      inference('demod', [status(thm)], ['16', '24'])).
% 31.89/32.08  thf('26', plain,
% 31.89/32.08      (![X0 : $i, X1 : $i]:
% 31.89/32.08         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 31.89/32.08      inference('sup+', [status(thm)], ['13', '25'])).
% 31.89/32.08  thf('27', plain,
% 31.89/32.08      (((k2_tarski @ sk_A @ sk_B)
% 31.89/32.08         = (k5_xboole_0 @ 
% 31.89/32.08            (k2_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 31.89/32.08             (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 31.89/32.08            (k3_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 31.89/32.08             (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))))),
% 31.89/32.08      inference('sup+', [status(thm)], ['12', '26'])).
% 31.89/32.08  thf('28', plain,
% 31.89/32.08      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 31.89/32.08      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 31.89/32.08  thf('29', plain,
% 31.89/32.08      (((k2_tarski @ sk_A @ sk_B)
% 31.89/32.08         = (k5_xboole_0 @ 
% 31.89/32.08            (k3_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 31.89/32.08             (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 31.89/32.08            (k2_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 31.89/32.08             (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))))),
% 31.89/32.08      inference('demod', [status(thm)], ['27', '28'])).
% 31.89/32.08  thf('30', plain,
% 31.89/32.08      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 31.89/32.08      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 31.89/32.08  thf('31', plain,
% 31.89/32.08      (![X6 : $i, X7 : $i, X8 : $i]:
% 31.89/32.08         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 31.89/32.08           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 31.89/32.08      inference('cnf', [status(esa)], [t91_xboole_1])).
% 31.89/32.08  thf('32', plain,
% 31.89/32.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.89/32.08         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 31.89/32.08           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 31.89/32.08      inference('sup+', [status(thm)], ['30', '31'])).
% 31.89/32.08  thf('33', plain,
% 31.89/32.08      (![X0 : $i]:
% 31.89/32.08         ((k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0)
% 31.89/32.08           = (k5_xboole_0 @ 
% 31.89/32.08              (k2_xboole_0 @ 
% 31.89/32.08               (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 31.89/32.08               (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 31.89/32.08              (k5_xboole_0 @ 
% 31.89/32.08               (k3_xboole_0 @ 
% 31.89/32.08                (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 31.89/32.08                (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 31.89/32.08               X0)))),
% 31.89/32.08      inference('sup+', [status(thm)], ['29', '32'])).
% 31.89/32.08  thf('34', plain,
% 31.89/32.08      (![X6 : $i, X7 : $i, X8 : $i]:
% 31.89/32.08         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 31.89/32.08           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 31.89/32.08      inference('cnf', [status(esa)], [t91_xboole_1])).
% 31.89/32.08  thf('35', plain,
% 31.89/32.08      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 31.89/32.08      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 31.89/32.08  thf('36', plain,
% 31.89/32.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.89/32.08         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 31.89/32.08           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 31.89/32.08      inference('sup+', [status(thm)], ['34', '35'])).
% 31.89/32.08  thf('37', plain,
% 31.89/32.08      (![X0 : $i]:
% 31.89/32.08         ((k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0)
% 31.89/32.08           = (k5_xboole_0 @ 
% 31.89/32.08              (k3_xboole_0 @ 
% 31.89/32.08               (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 31.89/32.08               (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 31.89/32.08              (k5_xboole_0 @ X0 @ 
% 31.89/32.08               (k2_xboole_0 @ 
% 31.89/32.08                (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 31.89/32.08                (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))))))),
% 31.89/32.08      inference('demod', [status(thm)], ['33', '36'])).
% 31.89/32.08  thf('38', plain,
% 31.89/32.08      (![X10 : $i, X11 : $i]:
% 31.89/32.08         ((k3_xboole_0 @ X10 @ X11)
% 31.89/32.08           = (k5_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ 
% 31.89/32.08              (k5_xboole_0 @ X10 @ X11)))),
% 31.89/32.08      inference('demod', [status(thm)], ['2', '3'])).
% 31.89/32.08  thf('39', plain,
% 31.89/32.08      (![X6 : $i, X7 : $i, X8 : $i]:
% 31.89/32.08         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 31.89/32.08           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 31.89/32.08      inference('cnf', [status(esa)], [t91_xboole_1])).
% 31.89/32.08  thf('40', plain,
% 31.89/32.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.89/32.08         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 31.89/32.08           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 31.89/32.08              (k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)))),
% 31.89/32.08      inference('sup+', [status(thm)], ['38', '39'])).
% 31.89/32.08  thf('41', plain,
% 31.89/32.08      (![X6 : $i, X7 : $i, X8 : $i]:
% 31.89/32.08         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 31.89/32.08           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 31.89/32.08      inference('cnf', [status(esa)], [t91_xboole_1])).
% 31.89/32.08  thf('42', plain,
% 31.89/32.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.89/32.08         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 31.89/32.08           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 31.89/32.08              (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X2))))),
% 31.89/32.08      inference('demod', [status(thm)], ['40', '41'])).
% 31.89/32.08  thf('43', plain,
% 31.89/32.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.89/32.08         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 31.89/32.08           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 31.89/32.08      inference('sup+', [status(thm)], ['34', '35'])).
% 31.89/32.08  thf('44', plain,
% 31.89/32.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.89/32.08         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 31.89/32.08           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 31.89/32.08      inference('sup+', [status(thm)], ['30', '31'])).
% 31.89/32.08  thf('45', plain,
% 31.89/32.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.89/32.08         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 31.89/32.08           = (k5_xboole_0 @ X1 @ 
% 31.89/32.08              (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))))),
% 31.89/32.08      inference('demod', [status(thm)], ['42', '43', '44'])).
% 31.89/32.08  thf('46', plain,
% 31.89/32.08      (((k5_xboole_0 @ 
% 31.89/32.08         (k3_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 31.89/32.08          (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 31.89/32.08         (k3_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 31.89/32.08          (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))))
% 31.89/32.08         = (k5_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 31.89/32.08            (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 31.89/32.08             (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))))),
% 31.89/32.08      inference('sup+', [status(thm)], ['37', '45'])).
% 31.89/32.08  thf('47', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 31.89/32.08      inference('cnf', [status(esa)], [t92_xboole_1])).
% 31.89/32.08  thf('48', plain,
% 31.89/32.08      (![X0 : $i, X1 : $i]:
% 31.89/32.08         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 31.89/32.08      inference('sup+', [status(thm)], ['13', '25'])).
% 31.89/32.08  thf('49', plain,
% 31.89/32.08      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 31.89/32.08      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 31.89/32.08  thf('50', plain,
% 31.89/32.08      (((k1_xboole_0)
% 31.89/32.08         = (k5_xboole_0 @ sk_C @ 
% 31.89/32.08            (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 31.89/32.08      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 31.89/32.08  thf('51', plain,
% 31.89/32.08      (![X0 : $i, X1 : $i]:
% 31.89/32.08         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 31.89/32.08      inference('demod', [status(thm)], ['16', '24'])).
% 31.89/32.08  thf('52', plain,
% 31.89/32.08      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 31.89/32.08         = (k5_xboole_0 @ sk_C @ k1_xboole_0))),
% 31.89/32.08      inference('sup+', [status(thm)], ['50', '51'])).
% 31.89/32.08  thf('53', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 31.89/32.08      inference('demod', [status(thm)], ['19', '20', '21'])).
% 31.89/32.08  thf('54', plain,
% 31.89/32.08      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (sk_C))),
% 31.89/32.08      inference('demod', [status(thm)], ['52', '53'])).
% 31.89/32.08  thf(t73_enumset1, axiom,
% 31.89/32.08    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 31.89/32.08     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 31.89/32.08       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 31.89/32.08  thf('55', plain,
% 31.89/32.08      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 31.89/32.08         ((k4_enumset1 @ X40 @ X40 @ X41 @ X42 @ X43 @ X44)
% 31.89/32.08           = (k3_enumset1 @ X40 @ X41 @ X42 @ X43 @ X44))),
% 31.89/32.08      inference('cnf', [status(esa)], [t73_enumset1])).
% 31.89/32.08  thf(t75_enumset1, axiom,
% 31.89/32.08    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 31.89/32.08     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 31.89/32.08       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 31.89/32.08  thf('56', plain,
% 31.89/32.08      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 31.89/32.08         ((k6_enumset1 @ X51 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57)
% 31.89/32.08           = (k5_enumset1 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57))),
% 31.89/32.08      inference('cnf', [status(esa)], [t75_enumset1])).
% 31.89/32.08  thf(t74_enumset1, axiom,
% 31.89/32.08    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 31.89/32.08     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 31.89/32.08       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 31.89/32.08  thf('57', plain,
% 31.89/32.08      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 31.89/32.08         ((k5_enumset1 @ X45 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50)
% 31.89/32.08           = (k4_enumset1 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50))),
% 31.89/32.08      inference('cnf', [status(esa)], [t74_enumset1])).
% 31.89/32.08  thf('58', plain,
% 31.89/32.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 31.89/32.08         ((k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 31.89/32.08           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 31.89/32.08      inference('sup+', [status(thm)], ['56', '57'])).
% 31.89/32.08  thf(t69_enumset1, axiom,
% 31.89/32.08    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 31.89/32.08  thf('59', plain,
% 31.89/32.08      (![X30 : $i]: ((k2_tarski @ X30 @ X30) = (k1_tarski @ X30))),
% 31.89/32.08      inference('cnf', [status(esa)], [t69_enumset1])).
% 31.89/32.08  thf(t67_enumset1, axiom,
% 31.89/32.08    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 31.89/32.08     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 31.89/32.08       ( k2_xboole_0 @
% 31.89/32.08         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ))).
% 31.89/32.08  thf('60', plain,
% 31.89/32.08      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, 
% 31.89/32.08         X29 : $i]:
% 31.89/32.08         ((k6_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29)
% 31.89/32.08           = (k2_xboole_0 @ 
% 31.89/32.08              (k4_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27) @ 
% 31.89/32.08              (k2_tarski @ X28 @ X29)))),
% 31.89/32.08      inference('cnf', [status(esa)], [t67_enumset1])).
% 31.89/32.08  thf('61', plain,
% 31.89/32.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 31.89/32.08         ((k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 31.89/32.08           = (k2_xboole_0 @ (k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 31.89/32.08              (k1_tarski @ X0)))),
% 31.89/32.08      inference('sup+', [status(thm)], ['59', '60'])).
% 31.89/32.08  thf(t61_enumset1, axiom,
% 31.89/32.08    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 31.89/32.08     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 31.89/32.08       ( k2_xboole_0 @
% 31.89/32.08         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ))).
% 31.89/32.08  thf('62', plain,
% 31.89/32.08      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 31.89/32.08         ((k5_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21)
% 31.89/32.08           = (k2_xboole_0 @ 
% 31.89/32.08              (k4_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20) @ 
% 31.89/32.08              (k1_tarski @ X21)))),
% 31.89/32.08      inference('cnf', [status(esa)], [t61_enumset1])).
% 31.89/32.08  thf('63', plain,
% 31.89/32.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 31.89/32.08         ((k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 31.89/32.08           = (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 31.89/32.08      inference('demod', [status(thm)], ['61', '62'])).
% 31.89/32.08  thf('64', plain,
% 31.89/32.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 31.89/32.08         ((k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 31.89/32.08           = (k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 31.89/32.08      inference('sup+', [status(thm)], ['58', '63'])).
% 31.89/32.08  thf('65', plain,
% 31.89/32.08      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 31.89/32.08         ((k5_enumset1 @ X45 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50)
% 31.89/32.08           = (k4_enumset1 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50))),
% 31.89/32.08      inference('cnf', [status(esa)], [t74_enumset1])).
% 31.89/32.08  thf('66', plain,
% 31.89/32.08      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 31.89/32.08         ((k4_enumset1 @ X40 @ X40 @ X41 @ X42 @ X43 @ X44)
% 31.89/32.08           = (k3_enumset1 @ X40 @ X41 @ X42 @ X43 @ X44))),
% 31.89/32.08      inference('cnf', [status(esa)], [t73_enumset1])).
% 31.89/32.08  thf('67', plain,
% 31.89/32.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 31.89/32.08         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 31.89/32.08           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 31.89/32.08      inference('sup+', [status(thm)], ['65', '66'])).
% 31.89/32.08  thf('68', plain,
% 31.89/32.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 31.89/32.08         ((k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 31.89/32.08           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 31.89/32.08      inference('demod', [status(thm)], ['64', '67'])).
% 31.89/32.08  thf('69', plain,
% 31.89/32.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 31.89/32.08         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0)
% 31.89/32.09           = (k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0))),
% 31.89/32.09      inference('sup+', [status(thm)], ['55', '68'])).
% 31.89/32.09  thf(t72_enumset1, axiom,
% 31.89/32.09    (![A:$i,B:$i,C:$i,D:$i]:
% 31.89/32.09     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 31.89/32.09  thf('70', plain,
% 31.89/32.09      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 31.89/32.09         ((k3_enumset1 @ X36 @ X36 @ X37 @ X38 @ X39)
% 31.89/32.09           = (k2_enumset1 @ X36 @ X37 @ X38 @ X39))),
% 31.89/32.09      inference('cnf', [status(esa)], [t72_enumset1])).
% 31.89/32.09  thf('71', plain,
% 31.89/32.09      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 31.89/32.09         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0)
% 31.89/32.09           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 31.89/32.09      inference('demod', [status(thm)], ['69', '70'])).
% 31.89/32.09  thf('72', plain,
% 31.89/32.09      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 31.89/32.09         ((k3_enumset1 @ X36 @ X36 @ X37 @ X38 @ X39)
% 31.89/32.09           = (k2_enumset1 @ X36 @ X37 @ X38 @ X39))),
% 31.89/32.09      inference('cnf', [status(esa)], [t72_enumset1])).
% 31.89/32.09  thf('73', plain,
% 31.89/32.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.89/32.09         ((k2_enumset1 @ X2 @ X2 @ X1 @ X0) = (k2_enumset1 @ X2 @ X1 @ X0 @ X0))),
% 31.89/32.09      inference('sup+', [status(thm)], ['71', '72'])).
% 31.89/32.09  thf(t71_enumset1, axiom,
% 31.89/32.09    (![A:$i,B:$i,C:$i]:
% 31.89/32.09     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 31.89/32.09  thf('74', plain,
% 31.89/32.09      (![X33 : $i, X34 : $i, X35 : $i]:
% 31.89/32.09         ((k2_enumset1 @ X33 @ X33 @ X34 @ X35)
% 31.89/32.09           = (k1_enumset1 @ X33 @ X34 @ X35))),
% 31.89/32.09      inference('cnf', [status(esa)], [t71_enumset1])).
% 31.89/32.09  thf(t100_enumset1, axiom,
% 31.89/32.09    (![A:$i,B:$i,C:$i]:
% 31.89/32.09     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ B @ C @ A ) ))).
% 31.89/32.09  thf('75', plain,
% 31.89/32.09      (![X12 : $i, X13 : $i, X14 : $i]:
% 31.89/32.09         ((k1_enumset1 @ X14 @ X12 @ X13) = (k1_enumset1 @ X12 @ X13 @ X14))),
% 31.89/32.09      inference('cnf', [status(esa)], [t100_enumset1])).
% 31.89/32.09  thf(t70_enumset1, axiom,
% 31.89/32.09    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 31.89/32.09  thf('76', plain,
% 31.89/32.09      (![X31 : $i, X32 : $i]:
% 31.89/32.09         ((k1_enumset1 @ X31 @ X31 @ X32) = (k2_tarski @ X31 @ X32))),
% 31.89/32.09      inference('cnf', [status(esa)], [t70_enumset1])).
% 31.89/32.09  thf(l51_zfmisc_1, axiom,
% 31.89/32.09    (![A:$i,B:$i]:
% 31.89/32.09     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 31.89/32.09  thf('77', plain,
% 31.89/32.09      (![X58 : $i, X59 : $i]:
% 31.89/32.09         ((k3_tarski @ (k2_tarski @ X58 @ X59)) = (k2_xboole_0 @ X58 @ X59))),
% 31.89/32.09      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 31.89/32.09  thf('78', plain,
% 31.89/32.09      (![X0 : $i, X1 : $i]:
% 31.89/32.09         ((k3_tarski @ (k1_enumset1 @ X1 @ X1 @ X0)) = (k2_xboole_0 @ X1 @ X0))),
% 31.89/32.09      inference('sup+', [status(thm)], ['76', '77'])).
% 31.89/32.09  thf('79', plain,
% 31.89/32.09      (![X0 : $i, X1 : $i]:
% 31.89/32.09         ((k3_tarski @ (k1_enumset1 @ X1 @ X0 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 31.89/32.09      inference('sup+', [status(thm)], ['75', '78'])).
% 31.89/32.09  thf('80', plain,
% 31.89/32.09      (![X0 : $i, X1 : $i]:
% 31.89/32.09         ((k3_tarski @ (k2_enumset1 @ X1 @ X1 @ X0 @ X0))
% 31.89/32.09           = (k2_xboole_0 @ X0 @ X1))),
% 31.89/32.09      inference('sup+', [status(thm)], ['74', '79'])).
% 31.89/32.09  thf('81', plain,
% 31.89/32.09      (![X0 : $i, X1 : $i]:
% 31.89/32.09         ((k3_tarski @ (k2_enumset1 @ X1 @ X1 @ X1 @ X0))
% 31.89/32.09           = (k2_xboole_0 @ X0 @ X1))),
% 31.89/32.09      inference('sup+', [status(thm)], ['73', '80'])).
% 31.89/32.09  thf('82', plain,
% 31.89/32.09      (![X33 : $i, X34 : $i, X35 : $i]:
% 31.89/32.09         ((k2_enumset1 @ X33 @ X33 @ X34 @ X35)
% 31.89/32.09           = (k1_enumset1 @ X33 @ X34 @ X35))),
% 31.89/32.09      inference('cnf', [status(esa)], [t71_enumset1])).
% 31.89/32.09  thf('83', plain,
% 31.89/32.09      (![X0 : $i, X1 : $i]:
% 31.89/32.09         ((k3_tarski @ (k1_enumset1 @ X1 @ X1 @ X0)) = (k2_xboole_0 @ X1 @ X0))),
% 31.89/32.09      inference('sup+', [status(thm)], ['76', '77'])).
% 31.89/32.09  thf('84', plain,
% 31.89/32.09      (![X0 : $i, X1 : $i]:
% 31.89/32.09         ((k3_tarski @ (k2_enumset1 @ X1 @ X1 @ X1 @ X0))
% 31.89/32.09           = (k2_xboole_0 @ X1 @ X0))),
% 31.89/32.09      inference('sup+', [status(thm)], ['82', '83'])).
% 31.89/32.09  thf('85', plain,
% 31.89/32.09      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 31.89/32.09      inference('sup+', [status(thm)], ['81', '84'])).
% 31.89/32.09  thf('86', plain,
% 31.89/32.09      (((k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) = (sk_C))),
% 31.89/32.09      inference('demod', [status(thm)], ['54', '85'])).
% 31.89/32.09  thf('87', plain,
% 31.89/32.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.89/32.09         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 31.89/32.09           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 31.89/32.09      inference('sup+', [status(thm)], ['34', '35'])).
% 31.89/32.09  thf('88', plain,
% 31.89/32.09      (![X10 : $i, X11 : $i]:
% 31.89/32.09         ((k3_xboole_0 @ X10 @ X11)
% 31.89/32.09           = (k5_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ 
% 31.89/32.09              (k5_xboole_0 @ X10 @ X11)))),
% 31.89/32.09      inference('demod', [status(thm)], ['2', '3'])).
% 31.89/32.09  thf('89', plain,
% 31.89/32.09      (![X0 : $i, X1 : $i]:
% 31.89/32.09         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 31.89/32.09      inference('sup+', [status(thm)], ['13', '25'])).
% 31.89/32.09  thf('90', plain,
% 31.89/32.09      (![X0 : $i, X1 : $i]:
% 31.89/32.09         ((k2_xboole_0 @ X1 @ X0)
% 31.89/32.09           = (k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 31.89/32.09      inference('sup+', [status(thm)], ['88', '89'])).
% 31.89/32.09  thf('91', plain,
% 31.89/32.09      (![X6 : $i, X7 : $i, X8 : $i]:
% 31.89/32.09         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 31.89/32.09           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 31.89/32.09      inference('cnf', [status(esa)], [t91_xboole_1])).
% 31.89/32.09  thf('92', plain,
% 31.89/32.09      (![X0 : $i, X1 : $i]:
% 31.89/32.09         ((k2_xboole_0 @ X1 @ X0)
% 31.89/32.09           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))))),
% 31.89/32.09      inference('demod', [status(thm)], ['90', '91'])).
% 31.89/32.09  thf('93', plain,
% 31.89/32.09      (((k2_tarski @ sk_A @ sk_B)
% 31.89/32.09         = (k5_xboole_0 @ 
% 31.89/32.09            (k3_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 31.89/32.09             (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 31.89/32.09            (k2_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 31.89/32.09             (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))))),
% 31.89/32.09      inference('demod', [status(thm)], ['27', '28'])).
% 31.89/32.09  thf('94', plain,
% 31.89/32.09      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (sk_C))),
% 31.89/32.09      inference('demod', [status(thm)], ['52', '53'])).
% 31.89/32.09  thf('95', plain,
% 31.89/32.09      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (sk_C))),
% 31.89/32.09      inference('demod', [status(thm)], ['52', '53'])).
% 31.89/32.09  thf('96', plain,
% 31.89/32.09      (((k2_tarski @ sk_A @ sk_B)
% 31.89/32.09         = (k5_xboole_0 @ 
% 31.89/32.09            (k3_xboole_0 @ sk_C @ 
% 31.89/32.09             (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 31.89/32.09            (k2_xboole_0 @ sk_C @ 
% 31.89/32.09             (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))))),
% 31.89/32.09      inference('demod', [status(thm)], ['93', '94', '95'])).
% 31.89/32.09  thf('97', plain,
% 31.89/32.09      (![X6 : $i, X7 : $i, X8 : $i]:
% 31.89/32.09         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 31.89/32.09           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 31.89/32.09      inference('cnf', [status(esa)], [t91_xboole_1])).
% 31.89/32.09  thf('98', plain,
% 31.89/32.09      (![X0 : $i]:
% 31.89/32.09         ((k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0)
% 31.89/32.09           = (k5_xboole_0 @ 
% 31.89/32.09              (k3_xboole_0 @ sk_C @ 
% 31.89/32.09               (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 31.89/32.09              (k5_xboole_0 @ 
% 31.89/32.09               (k2_xboole_0 @ sk_C @ 
% 31.89/32.09                (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 31.89/32.09               X0)))),
% 31.89/32.09      inference('sup+', [status(thm)], ['96', '97'])).
% 31.89/32.09  thf('99', plain,
% 31.89/32.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.89/32.09         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 31.89/32.09           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 31.89/32.09      inference('sup+', [status(thm)], ['34', '35'])).
% 31.89/32.09  thf('100', plain,
% 31.89/32.09      (![X0 : $i, X1 : $i]:
% 31.89/32.09         ((k5_xboole_0 @ 
% 31.89/32.09           (k5_xboole_0 @ 
% 31.89/32.09            (k2_xboole_0 @ sk_C @ 
% 31.89/32.09             (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 31.89/32.09            X0) @ 
% 31.89/32.09           (k5_xboole_0 @ X1 @ 
% 31.89/32.09            (k3_xboole_0 @ sk_C @ 
% 31.89/32.09             (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))))
% 31.89/32.09           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0)))),
% 31.89/32.09      inference('sup+', [status(thm)], ['98', '99'])).
% 31.89/32.09  thf('101', plain,
% 31.89/32.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.89/32.09         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 31.89/32.09           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 31.89/32.09      inference('sup+', [status(thm)], ['30', '31'])).
% 31.89/32.09  thf('102', plain,
% 31.89/32.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.89/32.09         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 31.89/32.09           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 31.89/32.09      inference('sup+', [status(thm)], ['34', '35'])).
% 31.89/32.09  thf('103', plain,
% 31.89/32.09      (![X0 : $i]:
% 31.89/32.09         ((k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0)
% 31.89/32.09           = (k5_xboole_0 @ 
% 31.89/32.09              (k3_xboole_0 @ sk_C @ 
% 31.89/32.09               (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 31.89/32.09              (k5_xboole_0 @ 
% 31.89/32.09               (k2_xboole_0 @ sk_C @ 
% 31.89/32.09                (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 31.89/32.09               X0)))),
% 31.89/32.09      inference('sup+', [status(thm)], ['96', '97'])).
% 31.89/32.09  thf('104', plain,
% 31.89/32.09      (![X0 : $i, X1 : $i]:
% 31.89/32.09         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X1))
% 31.89/32.09           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0)))),
% 31.89/32.09      inference('demod', [status(thm)], ['100', '101', '102', '103'])).
% 31.89/32.09  thf('105', plain,
% 31.89/32.09      (![X6 : $i, X7 : $i, X8 : $i]:
% 31.89/32.09         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 31.89/32.09           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 31.89/32.09      inference('cnf', [status(esa)], [t91_xboole_1])).
% 31.89/32.09  thf('106', plain,
% 31.89/32.09      (![X0 : $i, X1 : $i]:
% 31.89/32.09         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 31.89/32.09      inference('sup+', [status(thm)], ['13', '25'])).
% 31.89/32.09  thf('107', plain,
% 31.89/32.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.89/32.09         ((k5_xboole_0 @ X2 @ X1)
% 31.89/32.09           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0))))),
% 31.89/32.09      inference('sup+', [status(thm)], ['105', '106'])).
% 31.89/32.09  thf('108', plain,
% 31.89/32.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.89/32.09         ((k5_xboole_0 @ X2 @ X0)
% 31.89/32.09           = (k5_xboole_0 @ (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X1) @ 
% 31.89/32.09              (k5_xboole_0 @ X2 @ 
% 31.89/32.09               (k5_xboole_0 @ X1 @ 
% 31.89/32.09                (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0)))))),
% 31.89/32.09      inference('sup+', [status(thm)], ['104', '107'])).
% 31.89/32.09  thf('109', plain,
% 31.89/32.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.89/32.09         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 31.89/32.09           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 31.89/32.09      inference('sup+', [status(thm)], ['34', '35'])).
% 31.89/32.09  thf('110', plain,
% 31.89/32.09      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 31.89/32.09      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 31.89/32.09  thf('111', plain,
% 31.89/32.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.89/32.09         ((k5_xboole_0 @ (k5_xboole_0 @ X0 @ X2) @ X1)
% 31.89/32.09           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 31.89/32.09      inference('sup+', [status(thm)], ['109', '110'])).
% 31.89/32.09  thf('112', plain,
% 31.89/32.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.89/32.09         ((k5_xboole_0 @ (k5_xboole_0 @ X0 @ X2) @ X1)
% 31.89/32.09           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 31.89/32.09      inference('sup+', [status(thm)], ['109', '110'])).
% 31.89/32.09  thf('113', plain,
% 31.89/32.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.89/32.09         ((k5_xboole_0 @ (k5_xboole_0 @ X0 @ X2) @ X1)
% 31.89/32.09           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 31.89/32.09      inference('sup+', [status(thm)], ['109', '110'])).
% 31.89/32.09  thf('114', plain,
% 31.89/32.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.89/32.09         ((k5_xboole_0 @ (k5_xboole_0 @ X0 @ X2) @ X1)
% 31.89/32.09           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 31.89/32.09      inference('sup+', [status(thm)], ['109', '110'])).
% 31.89/32.09  thf('115', plain,
% 31.89/32.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.89/32.09         ((k5_xboole_0 @ (k5_xboole_0 @ X0 @ X2) @ X1)
% 31.89/32.09           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 31.89/32.09      inference('sup+', [status(thm)], ['109', '110'])).
% 31.89/32.09  thf('116', plain,
% 31.89/32.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.89/32.09         ((k5_xboole_0 @ (k5_xboole_0 @ X0 @ X2) @ X1)
% 31.89/32.09           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 31.89/32.09      inference('sup+', [status(thm)], ['109', '110'])).
% 31.89/32.09  thf('117', plain,
% 31.89/32.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.89/32.09         ((k5_xboole_0 @ (k5_xboole_0 @ X0 @ X2) @ X1)
% 31.89/32.09           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 31.89/32.09      inference('sup+', [status(thm)], ['109', '110'])).
% 31.89/32.09  thf('118', plain,
% 31.89/32.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.89/32.09         ((k5_xboole_0 @ (k5_xboole_0 @ X0 @ X2) @ X1)
% 31.89/32.09           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 31.89/32.09      inference('sup+', [status(thm)], ['109', '110'])).
% 31.89/32.09  thf('119', plain,
% 31.89/32.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.89/32.09         ((k5_xboole_0 @ X2 @ X1)
% 31.89/32.09           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0))))),
% 31.89/32.09      inference('sup+', [status(thm)], ['105', '106'])).
% 31.89/32.09  thf('120', plain,
% 31.89/32.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.89/32.09         ((k5_xboole_0 @ X2 @ X0)
% 31.89/32.09           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))))),
% 31.89/32.09      inference('demod', [status(thm)],
% 31.89/32.09                ['108', '111', '112', '113', '114', '115', '116', '117', 
% 31.89/32.09                 '118', '119'])).
% 31.89/32.09  thf('121', plain,
% 31.89/32.09      (![X0 : $i, X1 : $i]:
% 31.89/32.09         ((k5_xboole_0 @ X0 @ X1)
% 31.89/32.09           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 31.89/32.09      inference('sup+', [status(thm)], ['92', '120'])).
% 31.89/32.09  thf('122', plain,
% 31.89/32.09      (![X0 : $i, X1 : $i]:
% 31.89/32.09         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 31.89/32.09      inference('sup+', [status(thm)], ['13', '25'])).
% 31.89/32.09  thf('123', plain,
% 31.89/32.09      (![X0 : $i, X1 : $i]:
% 31.89/32.09         ((k3_xboole_0 @ X0 @ X1)
% 31.89/32.09           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 31.89/32.09      inference('sup+', [status(thm)], ['121', '122'])).
% 31.89/32.09  thf('124', plain,
% 31.89/32.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 31.89/32.09         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 31.89/32.09           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 31.89/32.09      inference('sup+', [status(thm)], ['34', '35'])).
% 31.89/32.09  thf('125', plain,
% 31.89/32.09      (![X0 : $i, X1 : $i]:
% 31.89/32.09         ((k3_xboole_0 @ X0 @ X1)
% 31.89/32.09           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))))),
% 31.89/32.09      inference('demod', [status(thm)], ['123', '124'])).
% 31.89/32.09  thf('126', plain,
% 31.89/32.09      (![X0 : $i, X1 : $i]:
% 31.89/32.09         ((k3_xboole_0 @ X1 @ X0)
% 31.89/32.09           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)))),
% 31.89/32.09      inference('sup+', [status(thm)], ['87', '125'])).
% 31.89/32.09  thf('127', plain,
% 31.89/32.09      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 31.89/32.09      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 31.89/32.09  thf('128', plain,
% 31.89/32.09      (![X0 : $i, X1 : $i]:
% 31.89/32.09         ((k3_xboole_0 @ X1 @ X0)
% 31.89/32.09           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))))),
% 31.89/32.09      inference('demod', [status(thm)], ['126', '127'])).
% 31.89/32.09  thf('129', plain,
% 31.89/32.09      (((k3_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 31.89/32.09         = (k5_xboole_0 @ sk_C @ 
% 31.89/32.09            (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 31.89/32.09      inference('sup+', [status(thm)], ['86', '128'])).
% 31.89/32.09  thf('130', plain,
% 31.89/32.09      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 31.89/32.09      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 31.89/32.09  thf('131', plain,
% 31.89/32.09      (![X0 : $i, X1 : $i]:
% 31.89/32.09         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 31.89/32.09      inference('demod', [status(thm)], ['16', '24'])).
% 31.89/32.09  thf('132', plain,
% 31.89/32.09      (((k3_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 31.89/32.09         = (k2_tarski @ sk_A @ sk_B))),
% 31.89/32.09      inference('demod', [status(thm)], ['129', '130', '131'])).
% 31.89/32.09  thf(t17_xboole_1, axiom,
% 31.89/32.09    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 31.89/32.09  thf('133', plain,
% 31.89/32.09      (![X4 : $i, X5 : $i]: (r1_tarski @ (k3_xboole_0 @ X4 @ X5) @ X4)),
% 31.89/32.09      inference('cnf', [status(esa)], [t17_xboole_1])).
% 31.89/32.09  thf('134', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)),
% 31.89/32.09      inference('sup+', [status(thm)], ['132', '133'])).
% 31.89/32.09  thf(t38_zfmisc_1, axiom,
% 31.89/32.09    (![A:$i,B:$i,C:$i]:
% 31.89/32.09     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 31.89/32.09       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 31.89/32.09  thf('135', plain,
% 31.89/32.09      (![X60 : $i, X61 : $i, X62 : $i]:
% 31.89/32.09         ((r2_hidden @ X60 @ X61)
% 31.89/32.09          | ~ (r1_tarski @ (k2_tarski @ X60 @ X62) @ X61))),
% 31.89/32.09      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 31.89/32.09  thf('136', plain, ((r2_hidden @ sk_A @ sk_C)),
% 31.89/32.09      inference('sup-', [status(thm)], ['134', '135'])).
% 31.89/32.09  thf('137', plain, ($false), inference('demod', [status(thm)], ['0', '136'])).
% 31.89/32.09  
% 31.89/32.09  % SZS output end Refutation
% 31.89/32.09  
% 31.89/32.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

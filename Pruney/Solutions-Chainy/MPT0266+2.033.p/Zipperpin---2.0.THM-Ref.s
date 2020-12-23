%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FM34QHKCaF

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:48 EST 2020

% Result     : Theorem 26.49s
% Output     : Refutation 26.49s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 270 expanded)
%              Number of leaves         :   38 ( 105 expanded)
%              Depth                    :   21
%              Number of atoms          : 1355 (2399 expanded)
%              Number of equality atoms :  112 ( 244 expanded)
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

thf(t102_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ C @ B @ A ) ) )).

thf('75',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k1_enumset1 @ X14 @ X13 @ X12 )
      = ( k1_enumset1 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t102_enumset1])).

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
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('89',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_C @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['86','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','24'])).

thf('93',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('94',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('95',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ),
    inference('sup+',[status(thm)],['93','94'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('96',plain,(
    ! [X60: $i,X61: $i,X62: $i] :
      ( ( r2_hidden @ X60 @ X61 )
      | ~ ( r1_tarski @ ( k2_tarski @ X60 @ X62 ) @ X61 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('97',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    $false ),
    inference(demod,[status(thm)],['0','97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FM34QHKCaF
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:59:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 26.49/26.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 26.49/26.71  % Solved by: fo/fo7.sh
% 26.49/26.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 26.49/26.71  % done 4467 iterations in 26.249s
% 26.49/26.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 26.49/26.71  % SZS output start Refutation
% 26.49/26.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 26.49/26.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 26.49/26.71  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 26.49/26.71  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 26.49/26.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 26.49/26.71  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 26.49/26.71  thf(sk_C_type, type, sk_C: $i).
% 26.49/26.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 26.49/26.71  thf(sk_B_type, type, sk_B: $i).
% 26.49/26.71  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 26.49/26.71  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 26.49/26.71  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 26.49/26.71  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 26.49/26.71  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 26.49/26.71                                           $i > $i).
% 26.49/26.71  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 26.49/26.71  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 26.49/26.71  thf(sk_A_type, type, sk_A: $i).
% 26.49/26.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 26.49/26.71  thf(t63_zfmisc_1, conjecture,
% 26.49/26.71    (![A:$i,B:$i,C:$i]:
% 26.49/26.71     ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) =>
% 26.49/26.71       ( r2_hidden @ A @ C ) ))).
% 26.49/26.71  thf(zf_stmt_0, negated_conjecture,
% 26.49/26.71    (~( ![A:$i,B:$i,C:$i]:
% 26.49/26.71        ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) =>
% 26.49/26.71          ( r2_hidden @ A @ C ) ) )),
% 26.49/26.71    inference('cnf.neg', [status(esa)], [t63_zfmisc_1])).
% 26.49/26.71  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 26.49/26.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.49/26.71  thf('1', plain,
% 26.49/26.71      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 26.49/26.71         = (k2_tarski @ sk_A @ sk_B))),
% 26.49/26.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.49/26.71  thf(t95_xboole_1, axiom,
% 26.49/26.71    (![A:$i,B:$i]:
% 26.49/26.71     ( ( k3_xboole_0 @ A @ B ) =
% 26.49/26.71       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 26.49/26.71  thf('2', plain,
% 26.49/26.71      (![X10 : $i, X11 : $i]:
% 26.49/26.71         ((k3_xboole_0 @ X10 @ X11)
% 26.49/26.71           = (k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ 
% 26.49/26.71              (k2_xboole_0 @ X10 @ X11)))),
% 26.49/26.71      inference('cnf', [status(esa)], [t95_xboole_1])).
% 26.49/26.71  thf(commutativity_k5_xboole_0, axiom,
% 26.49/26.71    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 26.49/26.71  thf('3', plain,
% 26.49/26.71      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 26.49/26.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 26.49/26.71  thf('4', plain,
% 26.49/26.71      (![X10 : $i, X11 : $i]:
% 26.49/26.71         ((k3_xboole_0 @ X10 @ X11)
% 26.49/26.71           = (k5_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ 
% 26.49/26.71              (k5_xboole_0 @ X10 @ X11)))),
% 26.49/26.71      inference('demod', [status(thm)], ['2', '3'])).
% 26.49/26.71  thf('5', plain,
% 26.49/26.71      (![X10 : $i, X11 : $i]:
% 26.49/26.71         ((k3_xboole_0 @ X10 @ X11)
% 26.49/26.71           = (k5_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ 
% 26.49/26.71              (k5_xboole_0 @ X10 @ X11)))),
% 26.49/26.71      inference('demod', [status(thm)], ['2', '3'])).
% 26.49/26.71  thf('6', plain,
% 26.49/26.71      (![X0 : $i, X1 : $i]:
% 26.49/26.71         ((k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 26.49/26.71           = (k5_xboole_0 @ 
% 26.49/26.71              (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)) @ 
% 26.49/26.71              (k3_xboole_0 @ X1 @ X0)))),
% 26.49/26.71      inference('sup+', [status(thm)], ['4', '5'])).
% 26.49/26.71  thf('7', plain,
% 26.49/26.71      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 26.49/26.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 26.49/26.71  thf('8', plain,
% 26.49/26.71      (![X0 : $i, X1 : $i]:
% 26.49/26.71         ((k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 26.49/26.71           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 26.49/26.71              (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))))),
% 26.49/26.71      inference('demod', [status(thm)], ['6', '7'])).
% 26.49/26.71  thf('9', plain,
% 26.49/26.71      (((k3_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 26.49/26.71         (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))
% 26.49/26.71         = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 26.49/26.71            (k2_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 26.49/26.71             (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))))),
% 26.49/26.71      inference('sup+', [status(thm)], ['1', '8'])).
% 26.49/26.71  thf('10', plain,
% 26.49/26.71      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 26.49/26.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 26.49/26.71  thf('11', plain,
% 26.49/26.71      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 26.49/26.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 26.49/26.71  thf('12', plain,
% 26.49/26.71      (((k3_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 26.49/26.71         (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))
% 26.49/26.71         = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 26.49/26.71            (k2_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 26.49/26.71             (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))))),
% 26.49/26.71      inference('demod', [status(thm)], ['9', '10', '11'])).
% 26.49/26.71  thf('13', plain,
% 26.49/26.71      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 26.49/26.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 26.49/26.71  thf(t92_xboole_1, axiom,
% 26.49/26.71    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 26.49/26.71  thf('14', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 26.49/26.71      inference('cnf', [status(esa)], [t92_xboole_1])).
% 26.49/26.71  thf(t91_xboole_1, axiom,
% 26.49/26.71    (![A:$i,B:$i,C:$i]:
% 26.49/26.71     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 26.49/26.71       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 26.49/26.71  thf('15', plain,
% 26.49/26.71      (![X6 : $i, X7 : $i, X8 : $i]:
% 26.49/26.71         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 26.49/26.71           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 26.49/26.71      inference('cnf', [status(esa)], [t91_xboole_1])).
% 26.49/26.71  thf('16', plain,
% 26.49/26.71      (![X0 : $i, X1 : $i]:
% 26.49/26.71         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 26.49/26.71           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 26.49/26.71      inference('sup+', [status(thm)], ['14', '15'])).
% 26.49/26.71  thf(idempotence_k2_xboole_0, axiom,
% 26.49/26.71    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 26.49/26.71  thf('17', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 26.49/26.71      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 26.49/26.71  thf('18', plain,
% 26.49/26.71      (![X10 : $i, X11 : $i]:
% 26.49/26.71         ((k3_xboole_0 @ X10 @ X11)
% 26.49/26.71           = (k5_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ 
% 26.49/26.71              (k5_xboole_0 @ X10 @ X11)))),
% 26.49/26.71      inference('demod', [status(thm)], ['2', '3'])).
% 26.49/26.71  thf('19', plain,
% 26.49/26.71      (![X0 : $i]:
% 26.49/26.71         ((k3_xboole_0 @ X0 @ X0)
% 26.49/26.71           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 26.49/26.71      inference('sup+', [status(thm)], ['17', '18'])).
% 26.49/26.71  thf(idempotence_k3_xboole_0, axiom,
% 26.49/26.71    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 26.49/26.71  thf('20', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 26.49/26.71      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 26.49/26.71  thf('21', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 26.49/26.71      inference('cnf', [status(esa)], [t92_xboole_1])).
% 26.49/26.71  thf('22', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 26.49/26.71      inference('demod', [status(thm)], ['19', '20', '21'])).
% 26.49/26.71  thf('23', plain,
% 26.49/26.71      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 26.49/26.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 26.49/26.71  thf('24', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 26.49/26.71      inference('sup+', [status(thm)], ['22', '23'])).
% 26.49/26.71  thf('25', plain,
% 26.49/26.71      (![X0 : $i, X1 : $i]:
% 26.49/26.71         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 26.49/26.71      inference('demod', [status(thm)], ['16', '24'])).
% 26.49/26.71  thf('26', plain,
% 26.49/26.71      (![X0 : $i, X1 : $i]:
% 26.49/26.71         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 26.49/26.71      inference('sup+', [status(thm)], ['13', '25'])).
% 26.49/26.71  thf('27', plain,
% 26.49/26.71      (((k2_tarski @ sk_A @ sk_B)
% 26.49/26.71         = (k5_xboole_0 @ 
% 26.49/26.71            (k2_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 26.49/26.71             (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 26.49/26.71            (k3_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 26.49/26.71             (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))))),
% 26.49/26.71      inference('sup+', [status(thm)], ['12', '26'])).
% 26.49/26.71  thf('28', plain,
% 26.49/26.71      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 26.49/26.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 26.49/26.71  thf('29', plain,
% 26.49/26.71      (((k2_tarski @ sk_A @ sk_B)
% 26.49/26.71         = (k5_xboole_0 @ 
% 26.49/26.71            (k3_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 26.49/26.71             (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 26.49/26.71            (k2_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 26.49/26.71             (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))))),
% 26.49/26.71      inference('demod', [status(thm)], ['27', '28'])).
% 26.49/26.71  thf('30', plain,
% 26.49/26.71      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 26.49/26.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 26.49/26.71  thf('31', plain,
% 26.49/26.71      (![X6 : $i, X7 : $i, X8 : $i]:
% 26.49/26.71         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 26.49/26.71           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 26.49/26.71      inference('cnf', [status(esa)], [t91_xboole_1])).
% 26.49/26.71  thf('32', plain,
% 26.49/26.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.49/26.71         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 26.49/26.71           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 26.49/26.71      inference('sup+', [status(thm)], ['30', '31'])).
% 26.49/26.71  thf('33', plain,
% 26.49/26.71      (![X0 : $i]:
% 26.49/26.71         ((k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0)
% 26.49/26.71           = (k5_xboole_0 @ 
% 26.49/26.71              (k2_xboole_0 @ 
% 26.49/26.71               (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 26.49/26.71               (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 26.49/26.71              (k5_xboole_0 @ 
% 26.49/26.71               (k3_xboole_0 @ 
% 26.49/26.71                (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 26.49/26.71                (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 26.49/26.71               X0)))),
% 26.49/26.71      inference('sup+', [status(thm)], ['29', '32'])).
% 26.49/26.71  thf('34', plain,
% 26.49/26.71      (![X6 : $i, X7 : $i, X8 : $i]:
% 26.49/26.71         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 26.49/26.71           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 26.49/26.71      inference('cnf', [status(esa)], [t91_xboole_1])).
% 26.49/26.71  thf('35', plain,
% 26.49/26.71      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 26.49/26.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 26.49/26.71  thf('36', plain,
% 26.49/26.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.49/26.71         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 26.49/26.71           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 26.49/26.71      inference('sup+', [status(thm)], ['34', '35'])).
% 26.49/26.71  thf('37', plain,
% 26.49/26.71      (![X0 : $i]:
% 26.49/26.71         ((k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0)
% 26.49/26.71           = (k5_xboole_0 @ 
% 26.49/26.71              (k3_xboole_0 @ 
% 26.49/26.71               (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 26.49/26.71               (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 26.49/26.71              (k5_xboole_0 @ X0 @ 
% 26.49/26.71               (k2_xboole_0 @ 
% 26.49/26.71                (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 26.49/26.71                (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))))))),
% 26.49/26.71      inference('demod', [status(thm)], ['33', '36'])).
% 26.49/26.71  thf('38', plain,
% 26.49/26.71      (![X10 : $i, X11 : $i]:
% 26.49/26.71         ((k3_xboole_0 @ X10 @ X11)
% 26.49/26.71           = (k5_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ 
% 26.49/26.71              (k5_xboole_0 @ X10 @ X11)))),
% 26.49/26.71      inference('demod', [status(thm)], ['2', '3'])).
% 26.49/26.71  thf('39', plain,
% 26.49/26.71      (![X6 : $i, X7 : $i, X8 : $i]:
% 26.49/26.71         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 26.49/26.71           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 26.49/26.71      inference('cnf', [status(esa)], [t91_xboole_1])).
% 26.49/26.71  thf('40', plain,
% 26.49/26.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.49/26.71         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 26.49/26.71           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 26.49/26.71              (k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)))),
% 26.49/26.71      inference('sup+', [status(thm)], ['38', '39'])).
% 26.49/26.71  thf('41', plain,
% 26.49/26.71      (![X6 : $i, X7 : $i, X8 : $i]:
% 26.49/26.71         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 26.49/26.71           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 26.49/26.71      inference('cnf', [status(esa)], [t91_xboole_1])).
% 26.49/26.71  thf('42', plain,
% 26.49/26.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.49/26.71         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 26.49/26.71           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 26.49/26.71              (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X2))))),
% 26.49/26.71      inference('demod', [status(thm)], ['40', '41'])).
% 26.49/26.71  thf('43', plain,
% 26.49/26.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.49/26.71         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 26.49/26.71           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 26.49/26.71      inference('sup+', [status(thm)], ['34', '35'])).
% 26.49/26.71  thf('44', plain,
% 26.49/26.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.49/26.71         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 26.49/26.71           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 26.49/26.71      inference('sup+', [status(thm)], ['30', '31'])).
% 26.49/26.71  thf('45', plain,
% 26.49/26.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.49/26.71         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 26.49/26.71           = (k5_xboole_0 @ X1 @ 
% 26.49/26.71              (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))))),
% 26.49/26.71      inference('demod', [status(thm)], ['42', '43', '44'])).
% 26.49/26.71  thf('46', plain,
% 26.49/26.71      (((k5_xboole_0 @ 
% 26.49/26.71         (k3_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 26.49/26.71          (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 26.49/26.71         (k3_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 26.49/26.71          (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))))
% 26.49/26.71         = (k5_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 26.49/26.71            (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 26.49/26.71             (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))))),
% 26.49/26.71      inference('sup+', [status(thm)], ['37', '45'])).
% 26.49/26.71  thf('47', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 26.49/26.71      inference('cnf', [status(esa)], [t92_xboole_1])).
% 26.49/26.71  thf('48', plain,
% 26.49/26.71      (![X0 : $i, X1 : $i]:
% 26.49/26.71         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 26.49/26.71      inference('sup+', [status(thm)], ['13', '25'])).
% 26.49/26.71  thf('49', plain,
% 26.49/26.71      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 26.49/26.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 26.49/26.71  thf('50', plain,
% 26.49/26.71      (((k1_xboole_0)
% 26.49/26.71         = (k5_xboole_0 @ sk_C @ 
% 26.49/26.71            (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 26.49/26.71      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 26.49/26.71  thf('51', plain,
% 26.49/26.71      (![X0 : $i, X1 : $i]:
% 26.49/26.71         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 26.49/26.71      inference('demod', [status(thm)], ['16', '24'])).
% 26.49/26.71  thf('52', plain,
% 26.49/26.71      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 26.49/26.71         = (k5_xboole_0 @ sk_C @ k1_xboole_0))),
% 26.49/26.71      inference('sup+', [status(thm)], ['50', '51'])).
% 26.49/26.71  thf('53', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 26.49/26.71      inference('demod', [status(thm)], ['19', '20', '21'])).
% 26.49/26.71  thf('54', plain,
% 26.49/26.71      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (sk_C))),
% 26.49/26.71      inference('demod', [status(thm)], ['52', '53'])).
% 26.49/26.71  thf(t73_enumset1, axiom,
% 26.49/26.71    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 26.49/26.71     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 26.49/26.71       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 26.49/26.71  thf('55', plain,
% 26.49/26.71      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 26.49/26.71         ((k4_enumset1 @ X40 @ X40 @ X41 @ X42 @ X43 @ X44)
% 26.49/26.71           = (k3_enumset1 @ X40 @ X41 @ X42 @ X43 @ X44))),
% 26.49/26.71      inference('cnf', [status(esa)], [t73_enumset1])).
% 26.49/26.71  thf(t75_enumset1, axiom,
% 26.49/26.71    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 26.49/26.71     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 26.49/26.71       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 26.49/26.71  thf('56', plain,
% 26.49/26.71      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 26.49/26.71         ((k6_enumset1 @ X51 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57)
% 26.49/26.71           = (k5_enumset1 @ X51 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57))),
% 26.49/26.71      inference('cnf', [status(esa)], [t75_enumset1])).
% 26.49/26.71  thf(t74_enumset1, axiom,
% 26.49/26.71    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 26.49/26.71     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 26.49/26.71       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 26.49/26.71  thf('57', plain,
% 26.49/26.71      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 26.49/26.71         ((k5_enumset1 @ X45 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50)
% 26.49/26.71           = (k4_enumset1 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50))),
% 26.49/26.71      inference('cnf', [status(esa)], [t74_enumset1])).
% 26.49/26.71  thf('58', plain,
% 26.49/26.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 26.49/26.71         ((k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 26.49/26.71           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 26.49/26.71      inference('sup+', [status(thm)], ['56', '57'])).
% 26.49/26.71  thf(t69_enumset1, axiom,
% 26.49/26.71    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 26.49/26.71  thf('59', plain,
% 26.49/26.71      (![X30 : $i]: ((k2_tarski @ X30 @ X30) = (k1_tarski @ X30))),
% 26.49/26.71      inference('cnf', [status(esa)], [t69_enumset1])).
% 26.49/26.71  thf(t67_enumset1, axiom,
% 26.49/26.71    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 26.49/26.71     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 26.49/26.71       ( k2_xboole_0 @
% 26.49/26.71         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ))).
% 26.49/26.71  thf('60', plain,
% 26.49/26.71      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, 
% 26.49/26.71         X29 : $i]:
% 26.49/26.71         ((k6_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29)
% 26.49/26.71           = (k2_xboole_0 @ 
% 26.49/26.71              (k4_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27) @ 
% 26.49/26.71              (k2_tarski @ X28 @ X29)))),
% 26.49/26.71      inference('cnf', [status(esa)], [t67_enumset1])).
% 26.49/26.71  thf('61', plain,
% 26.49/26.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 26.49/26.71         ((k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 26.49/26.71           = (k2_xboole_0 @ (k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 26.49/26.71              (k1_tarski @ X0)))),
% 26.49/26.71      inference('sup+', [status(thm)], ['59', '60'])).
% 26.49/26.71  thf(t61_enumset1, axiom,
% 26.49/26.71    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 26.49/26.71     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 26.49/26.71       ( k2_xboole_0 @
% 26.49/26.71         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ))).
% 26.49/26.71  thf('62', plain,
% 26.49/26.71      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 26.49/26.71         ((k5_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21)
% 26.49/26.71           = (k2_xboole_0 @ 
% 26.49/26.71              (k4_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20) @ 
% 26.49/26.71              (k1_tarski @ X21)))),
% 26.49/26.71      inference('cnf', [status(esa)], [t61_enumset1])).
% 26.49/26.71  thf('63', plain,
% 26.49/26.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 26.49/26.71         ((k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 26.49/26.71           = (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 26.49/26.71      inference('demod', [status(thm)], ['61', '62'])).
% 26.49/26.71  thf('64', plain,
% 26.49/26.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 26.49/26.71         ((k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 26.49/26.71           = (k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 26.49/26.71      inference('sup+', [status(thm)], ['58', '63'])).
% 26.49/26.71  thf('65', plain,
% 26.49/26.71      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 26.49/26.71         ((k5_enumset1 @ X45 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50)
% 26.49/26.71           = (k4_enumset1 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50))),
% 26.49/26.71      inference('cnf', [status(esa)], [t74_enumset1])).
% 26.49/26.71  thf('66', plain,
% 26.49/26.71      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 26.49/26.71         ((k4_enumset1 @ X40 @ X40 @ X41 @ X42 @ X43 @ X44)
% 26.49/26.71           = (k3_enumset1 @ X40 @ X41 @ X42 @ X43 @ X44))),
% 26.49/26.71      inference('cnf', [status(esa)], [t73_enumset1])).
% 26.49/26.71  thf('67', plain,
% 26.49/26.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 26.49/26.71         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 26.49/26.71           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 26.49/26.71      inference('sup+', [status(thm)], ['65', '66'])).
% 26.49/26.71  thf('68', plain,
% 26.49/26.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 26.49/26.71         ((k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 26.49/26.71           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 26.49/26.71      inference('demod', [status(thm)], ['64', '67'])).
% 26.49/26.71  thf('69', plain,
% 26.49/26.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 26.49/26.71         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0)
% 26.49/26.71           = (k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0))),
% 26.49/26.71      inference('sup+', [status(thm)], ['55', '68'])).
% 26.49/26.71  thf(t72_enumset1, axiom,
% 26.49/26.71    (![A:$i,B:$i,C:$i,D:$i]:
% 26.49/26.71     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 26.49/26.71  thf('70', plain,
% 26.49/26.71      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 26.49/26.71         ((k3_enumset1 @ X36 @ X36 @ X37 @ X38 @ X39)
% 26.49/26.71           = (k2_enumset1 @ X36 @ X37 @ X38 @ X39))),
% 26.49/26.71      inference('cnf', [status(esa)], [t72_enumset1])).
% 26.49/26.71  thf('71', plain,
% 26.49/26.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 26.49/26.71         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0)
% 26.49/26.71           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 26.49/26.71      inference('demod', [status(thm)], ['69', '70'])).
% 26.49/26.71  thf('72', plain,
% 26.49/26.71      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 26.49/26.71         ((k3_enumset1 @ X36 @ X36 @ X37 @ X38 @ X39)
% 26.49/26.71           = (k2_enumset1 @ X36 @ X37 @ X38 @ X39))),
% 26.49/26.71      inference('cnf', [status(esa)], [t72_enumset1])).
% 26.49/26.71  thf('73', plain,
% 26.49/26.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.49/26.71         ((k2_enumset1 @ X2 @ X2 @ X1 @ X0) = (k2_enumset1 @ X2 @ X1 @ X0 @ X0))),
% 26.49/26.71      inference('sup+', [status(thm)], ['71', '72'])).
% 26.49/26.71  thf(t71_enumset1, axiom,
% 26.49/26.71    (![A:$i,B:$i,C:$i]:
% 26.49/26.71     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 26.49/26.71  thf('74', plain,
% 26.49/26.71      (![X33 : $i, X34 : $i, X35 : $i]:
% 26.49/26.71         ((k2_enumset1 @ X33 @ X33 @ X34 @ X35)
% 26.49/26.71           = (k1_enumset1 @ X33 @ X34 @ X35))),
% 26.49/26.71      inference('cnf', [status(esa)], [t71_enumset1])).
% 26.49/26.71  thf(t102_enumset1, axiom,
% 26.49/26.71    (![A:$i,B:$i,C:$i]:
% 26.49/26.71     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ C @ B @ A ) ))).
% 26.49/26.71  thf('75', plain,
% 26.49/26.71      (![X12 : $i, X13 : $i, X14 : $i]:
% 26.49/26.71         ((k1_enumset1 @ X14 @ X13 @ X12) = (k1_enumset1 @ X12 @ X13 @ X14))),
% 26.49/26.71      inference('cnf', [status(esa)], [t102_enumset1])).
% 26.49/26.71  thf(t70_enumset1, axiom,
% 26.49/26.71    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 26.49/26.71  thf('76', plain,
% 26.49/26.71      (![X31 : $i, X32 : $i]:
% 26.49/26.71         ((k1_enumset1 @ X31 @ X31 @ X32) = (k2_tarski @ X31 @ X32))),
% 26.49/26.71      inference('cnf', [status(esa)], [t70_enumset1])).
% 26.49/26.71  thf(l51_zfmisc_1, axiom,
% 26.49/26.71    (![A:$i,B:$i]:
% 26.49/26.71     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 26.49/26.71  thf('77', plain,
% 26.49/26.71      (![X58 : $i, X59 : $i]:
% 26.49/26.71         ((k3_tarski @ (k2_tarski @ X58 @ X59)) = (k2_xboole_0 @ X58 @ X59))),
% 26.49/26.71      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 26.49/26.71  thf('78', plain,
% 26.49/26.71      (![X0 : $i, X1 : $i]:
% 26.49/26.71         ((k3_tarski @ (k1_enumset1 @ X1 @ X1 @ X0)) = (k2_xboole_0 @ X1 @ X0))),
% 26.49/26.71      inference('sup+', [status(thm)], ['76', '77'])).
% 26.49/26.71  thf('79', plain,
% 26.49/26.71      (![X0 : $i, X1 : $i]:
% 26.49/26.71         ((k3_tarski @ (k1_enumset1 @ X1 @ X0 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 26.49/26.71      inference('sup+', [status(thm)], ['75', '78'])).
% 26.49/26.71  thf('80', plain,
% 26.49/26.71      (![X0 : $i, X1 : $i]:
% 26.49/26.71         ((k3_tarski @ (k2_enumset1 @ X1 @ X1 @ X0 @ X0))
% 26.49/26.71           = (k2_xboole_0 @ X0 @ X1))),
% 26.49/26.71      inference('sup+', [status(thm)], ['74', '79'])).
% 26.49/26.71  thf('81', plain,
% 26.49/26.71      (![X0 : $i, X1 : $i]:
% 26.49/26.71         ((k3_tarski @ (k2_enumset1 @ X1 @ X1 @ X1 @ X0))
% 26.49/26.71           = (k2_xboole_0 @ X0 @ X1))),
% 26.49/26.71      inference('sup+', [status(thm)], ['73', '80'])).
% 26.49/26.71  thf('82', plain,
% 26.49/26.71      (![X33 : $i, X34 : $i, X35 : $i]:
% 26.49/26.71         ((k2_enumset1 @ X33 @ X33 @ X34 @ X35)
% 26.49/26.71           = (k1_enumset1 @ X33 @ X34 @ X35))),
% 26.49/26.71      inference('cnf', [status(esa)], [t71_enumset1])).
% 26.49/26.71  thf('83', plain,
% 26.49/26.71      (![X0 : $i, X1 : $i]:
% 26.49/26.71         ((k3_tarski @ (k1_enumset1 @ X1 @ X1 @ X0)) = (k2_xboole_0 @ X1 @ X0))),
% 26.49/26.71      inference('sup+', [status(thm)], ['76', '77'])).
% 26.49/26.71  thf('84', plain,
% 26.49/26.71      (![X0 : $i, X1 : $i]:
% 26.49/26.71         ((k3_tarski @ (k2_enumset1 @ X1 @ X1 @ X1 @ X0))
% 26.49/26.71           = (k2_xboole_0 @ X1 @ X0))),
% 26.49/26.71      inference('sup+', [status(thm)], ['82', '83'])).
% 26.49/26.71  thf('85', plain,
% 26.49/26.71      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 26.49/26.71      inference('sup+', [status(thm)], ['81', '84'])).
% 26.49/26.71  thf('86', plain,
% 26.49/26.71      (((k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) = (sk_C))),
% 26.49/26.71      inference('demod', [status(thm)], ['54', '85'])).
% 26.49/26.71  thf('87', plain,
% 26.49/26.71      (![X10 : $i, X11 : $i]:
% 26.49/26.71         ((k3_xboole_0 @ X10 @ X11)
% 26.49/26.71           = (k5_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ 
% 26.49/26.71              (k5_xboole_0 @ X10 @ X11)))),
% 26.49/26.71      inference('demod', [status(thm)], ['2', '3'])).
% 26.49/26.71  thf('88', plain,
% 26.49/26.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.49/26.71         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 26.49/26.71           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 26.49/26.71      inference('sup+', [status(thm)], ['34', '35'])).
% 26.49/26.71  thf('89', plain,
% 26.49/26.71      (![X10 : $i, X11 : $i]:
% 26.49/26.71         ((k3_xboole_0 @ X10 @ X11)
% 26.49/26.71           = (k5_xboole_0 @ X10 @ 
% 26.49/26.71              (k5_xboole_0 @ X11 @ (k2_xboole_0 @ X10 @ X11))))),
% 26.49/26.71      inference('demod', [status(thm)], ['87', '88'])).
% 26.49/26.71  thf('90', plain,
% 26.49/26.71      (((k3_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 26.49/26.71         = (k5_xboole_0 @ sk_C @ 
% 26.49/26.71            (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 26.49/26.71      inference('sup+', [status(thm)], ['86', '89'])).
% 26.49/26.71  thf('91', plain,
% 26.49/26.71      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 26.49/26.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 26.49/26.71  thf('92', plain,
% 26.49/26.71      (![X0 : $i, X1 : $i]:
% 26.49/26.71         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 26.49/26.71      inference('demod', [status(thm)], ['16', '24'])).
% 26.49/26.71  thf('93', plain,
% 26.49/26.71      (((k3_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 26.49/26.71         = (k2_tarski @ sk_A @ sk_B))),
% 26.49/26.71      inference('demod', [status(thm)], ['90', '91', '92'])).
% 26.49/26.71  thf(t17_xboole_1, axiom,
% 26.49/26.71    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 26.49/26.71  thf('94', plain,
% 26.49/26.71      (![X4 : $i, X5 : $i]: (r1_tarski @ (k3_xboole_0 @ X4 @ X5) @ X4)),
% 26.49/26.71      inference('cnf', [status(esa)], [t17_xboole_1])).
% 26.49/26.71  thf('95', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)),
% 26.49/26.71      inference('sup+', [status(thm)], ['93', '94'])).
% 26.49/26.71  thf(t38_zfmisc_1, axiom,
% 26.49/26.71    (![A:$i,B:$i,C:$i]:
% 26.49/26.71     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 26.49/26.71       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 26.49/26.71  thf('96', plain,
% 26.49/26.71      (![X60 : $i, X61 : $i, X62 : $i]:
% 26.49/26.71         ((r2_hidden @ X60 @ X61)
% 26.49/26.71          | ~ (r1_tarski @ (k2_tarski @ X60 @ X62) @ X61))),
% 26.49/26.71      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 26.49/26.71  thf('97', plain, ((r2_hidden @ sk_A @ sk_C)),
% 26.49/26.71      inference('sup-', [status(thm)], ['95', '96'])).
% 26.49/26.71  thf('98', plain, ($false), inference('demod', [status(thm)], ['0', '97'])).
% 26.49/26.71  
% 26.49/26.71  % SZS output end Refutation
% 26.49/26.71  
% 26.49/26.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

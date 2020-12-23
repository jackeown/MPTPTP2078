%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8E3kPFUYsk

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:48 EST 2020

% Result     : Theorem 21.58s
% Output     : Refutation 21.58s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 782 expanded)
%              Number of leaves         :   38 ( 283 expanded)
%              Depth                    :   20
%              Number of atoms          : 1953 (7751 expanded)
%              Number of equality atoms :  151 ( 756 expanded)
%              Maximal formula depth    :   18 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

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
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('6',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('7',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('20',plain,
    ( ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('22',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['20','25'])).

thf('27',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ X0 )
      = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k5_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('33',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ X0 )
      = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k5_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) ) )
      = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) ) @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('42',plain,
    ( ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('44',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('46',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = ( k5_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k5_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X1 ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','40','41','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X1 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ X0 ) @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['28','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('54',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['52','55'])).

thf(t125_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ D @ C @ B @ A ) ) )).

thf('57',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k2_enumset1 @ X15 @ X14 @ X13 @ X12 )
      = ( k2_enumset1 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t125_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('58',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k2_enumset1 @ X34 @ X34 @ X35 @ X36 )
      = ( k1_enumset1 @ X34 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k2_enumset1 @ X34 @ X34 @ X35 @ X36 )
      = ( k1_enumset1 @ X34 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('62',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( k3_enumset1 @ X37 @ X37 @ X38 @ X39 @ X40 )
      = ( k2_enumset1 @ X37 @ X38 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('63',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k2_enumset1 @ X34 @ X34 @ X35 @ X36 )
      = ( k1_enumset1 @ X34 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('65',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i,X56: $i,X57: $i,X58: $i] :
      ( ( k6_enumset1 @ X52 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 @ X58 )
      = ( k5_enumset1 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('66',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( k5_enumset1 @ X46 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 )
      = ( k4_enumset1 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('68',plain,(
    ! [X31: $i] :
      ( ( k2_tarski @ X31 @ X31 )
      = ( k1_tarski @ X31 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t67_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ) )).

thf('69',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( k6_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 ) @ ( k2_tarski @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t67_enumset1])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf(t61_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ) )).

thf('71',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( k5_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 ) @ ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t61_enumset1])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['67','72'])).

thf('74',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( k5_enumset1 @ X46 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 )
      = ( k4_enumset1 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('75',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( k4_enumset1 @ X41 @ X41 @ X42 @ X43 @ X44 @ X45 )
      = ( k3_enumset1 @ X41 @ X42 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['73','76'])).

thf('78',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( k4_enumset1 @ X41 @ X41 @ X42 @ X43 @ X44 @ X45 )
      = ( k3_enumset1 @ X41 @ X42 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('83',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_enumset1 @ X32 @ X32 @ X33 )
      = ( k2_tarski @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('84',plain,(
    ! [X59: $i,X60: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X59 @ X60 ) )
      = ( k2_xboole_0 @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k1_enumset1 @ X1 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['82','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k1_enumset1 @ X1 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['61','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k1_enumset1 @ X1 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['82','85'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['56','89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k5_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['10','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('94',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X2 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('98',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X2 ) @ X1 )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('110',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('111',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X2 ) @ X1 )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['114','115','116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X1 ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','40','41','48'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 )
      = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_tarski @ sk_A @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['118','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X2 ) @ X1 )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('126',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['124','125','126','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('132',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['92','93','96','103','106','107','108','109','130','131'])).

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
    ! [X61: $i,X62: $i,X63: $i] :
      ( ( r2_hidden @ X61 @ X62 )
      | ~ ( r1_tarski @ ( k2_tarski @ X61 @ X63 ) @ X62 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('136',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    $false ),
    inference(demod,[status(thm)],['0','136'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.14/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8E3kPFUYsk
% 0.16/0.37  % Computer   : n023.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 11:35:06 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 21.58/21.78  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 21.58/21.78  % Solved by: fo/fo7.sh
% 21.58/21.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 21.58/21.78  % done 4011 iterations in 21.299s
% 21.58/21.78  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 21.58/21.78  % SZS output start Refutation
% 21.58/21.78  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 21.58/21.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 21.58/21.78  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 21.58/21.78  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 21.58/21.78  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 21.58/21.78  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 21.58/21.78  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 21.58/21.78  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 21.58/21.78  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 21.58/21.78  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 21.58/21.78  thf(sk_A_type, type, sk_A: $i).
% 21.58/21.78  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 21.58/21.78  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 21.58/21.78  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 21.58/21.78                                           $i > $i).
% 21.58/21.78  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 21.58/21.78  thf(sk_C_type, type, sk_C: $i).
% 21.58/21.78  thf(sk_B_type, type, sk_B: $i).
% 21.58/21.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 21.58/21.78  thf(t63_zfmisc_1, conjecture,
% 21.58/21.78    (![A:$i,B:$i,C:$i]:
% 21.58/21.78     ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) =>
% 21.58/21.78       ( r2_hidden @ A @ C ) ))).
% 21.58/21.78  thf(zf_stmt_0, negated_conjecture,
% 21.58/21.78    (~( ![A:$i,B:$i,C:$i]:
% 21.58/21.78        ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) =>
% 21.58/21.78          ( r2_hidden @ A @ C ) ) )),
% 21.58/21.78    inference('cnf.neg', [status(esa)], [t63_zfmisc_1])).
% 21.58/21.78  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 21.58/21.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.58/21.78  thf(idempotence_k2_xboole_0, axiom,
% 21.58/21.78    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 21.58/21.78  thf('1', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 21.58/21.78      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 21.58/21.78  thf(t95_xboole_1, axiom,
% 21.58/21.78    (![A:$i,B:$i]:
% 21.58/21.78     ( ( k3_xboole_0 @ A @ B ) =
% 21.58/21.78       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 21.58/21.78  thf('2', plain,
% 21.58/21.78      (![X10 : $i, X11 : $i]:
% 21.58/21.78         ((k3_xboole_0 @ X10 @ X11)
% 21.58/21.78           = (k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ 
% 21.58/21.78              (k2_xboole_0 @ X10 @ X11)))),
% 21.58/21.78      inference('cnf', [status(esa)], [t95_xboole_1])).
% 21.58/21.78  thf(commutativity_k5_xboole_0, axiom,
% 21.58/21.78    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 21.58/21.78  thf('3', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 21.58/21.78      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 21.58/21.78  thf('4', plain,
% 21.58/21.78      (![X10 : $i, X11 : $i]:
% 21.58/21.78         ((k3_xboole_0 @ X10 @ X11)
% 21.58/21.78           = (k5_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ 
% 21.58/21.78              (k5_xboole_0 @ X10 @ X11)))),
% 21.58/21.78      inference('demod', [status(thm)], ['2', '3'])).
% 21.58/21.78  thf('5', plain,
% 21.58/21.78      (![X0 : $i]:
% 21.58/21.78         ((k3_xboole_0 @ X0 @ X0)
% 21.58/21.78           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 21.58/21.78      inference('sup+', [status(thm)], ['1', '4'])).
% 21.58/21.78  thf(idempotence_k3_xboole_0, axiom,
% 21.58/21.78    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 21.58/21.78  thf('6', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 21.58/21.78      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 21.58/21.78  thf(t92_xboole_1, axiom,
% 21.58/21.78    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 21.58/21.78  thf('7', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 21.58/21.78      inference('cnf', [status(esa)], [t92_xboole_1])).
% 21.58/21.78  thf('8', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 21.58/21.78      inference('demod', [status(thm)], ['5', '6', '7'])).
% 21.58/21.78  thf('9', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 21.58/21.78      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 21.58/21.78  thf('10', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 21.58/21.78      inference('sup+', [status(thm)], ['8', '9'])).
% 21.58/21.78  thf('11', plain,
% 21.58/21.78      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 21.58/21.78         = (k2_tarski @ sk_A @ sk_B))),
% 21.58/21.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.58/21.78  thf('12', plain,
% 21.58/21.78      (![X10 : $i, X11 : $i]:
% 21.58/21.78         ((k3_xboole_0 @ X10 @ X11)
% 21.58/21.78           = (k5_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ 
% 21.58/21.78              (k5_xboole_0 @ X10 @ X11)))),
% 21.58/21.78      inference('demod', [status(thm)], ['2', '3'])).
% 21.58/21.78  thf('13', plain,
% 21.58/21.78      (![X10 : $i, X11 : $i]:
% 21.58/21.78         ((k3_xboole_0 @ X10 @ X11)
% 21.58/21.78           = (k5_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ 
% 21.58/21.78              (k5_xboole_0 @ X10 @ X11)))),
% 21.58/21.78      inference('demod', [status(thm)], ['2', '3'])).
% 21.58/21.78  thf('14', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]:
% 21.58/21.78         ((k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 21.58/21.78           = (k5_xboole_0 @ 
% 21.58/21.78              (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)) @ 
% 21.58/21.78              (k3_xboole_0 @ X1 @ X0)))),
% 21.58/21.78      inference('sup+', [status(thm)], ['12', '13'])).
% 21.58/21.78  thf('15', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 21.58/21.78      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 21.58/21.78  thf('16', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]:
% 21.58/21.78         ((k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 21.58/21.78           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 21.58/21.78              (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))))),
% 21.58/21.78      inference('demod', [status(thm)], ['14', '15'])).
% 21.58/21.78  thf('17', plain,
% 21.58/21.78      (((k3_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 21.58/21.78         (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))
% 21.58/21.78         = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 21.58/21.78            (k2_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 21.58/21.78             (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))))),
% 21.58/21.78      inference('sup+', [status(thm)], ['11', '16'])).
% 21.58/21.78  thf('18', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 21.58/21.78      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 21.58/21.78  thf('19', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 21.58/21.78      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 21.58/21.78  thf('20', plain,
% 21.58/21.78      (((k3_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 21.58/21.78         (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))
% 21.58/21.78         = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 21.58/21.78            (k2_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 21.58/21.78             (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))))),
% 21.58/21.78      inference('demod', [status(thm)], ['17', '18', '19'])).
% 21.58/21.78  thf('21', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 21.58/21.78      inference('cnf', [status(esa)], [t92_xboole_1])).
% 21.58/21.78  thf(t91_xboole_1, axiom,
% 21.58/21.78    (![A:$i,B:$i,C:$i]:
% 21.58/21.78     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 21.58/21.78       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 21.58/21.78  thf('22', plain,
% 21.58/21.78      (![X6 : $i, X7 : $i, X8 : $i]:
% 21.58/21.78         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 21.58/21.78           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 21.58/21.78      inference('cnf', [status(esa)], [t91_xboole_1])).
% 21.58/21.78  thf('23', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]:
% 21.58/21.78         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 21.58/21.78           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 21.58/21.78      inference('sup+', [status(thm)], ['21', '22'])).
% 21.58/21.78  thf('24', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 21.58/21.78      inference('sup+', [status(thm)], ['8', '9'])).
% 21.58/21.78  thf('25', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]:
% 21.58/21.78         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 21.58/21.78      inference('demod', [status(thm)], ['23', '24'])).
% 21.58/21.78  thf('26', plain,
% 21.58/21.78      (((k2_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 21.58/21.78         (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))
% 21.58/21.78         = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 21.58/21.78            (k3_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 21.58/21.78             (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))))),
% 21.58/21.78      inference('sup+', [status(thm)], ['20', '25'])).
% 21.58/21.78  thf('27', plain,
% 21.58/21.78      (![X6 : $i, X7 : $i, X8 : $i]:
% 21.58/21.78         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 21.58/21.78           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 21.58/21.78      inference('cnf', [status(esa)], [t91_xboole_1])).
% 21.58/21.78  thf('28', plain,
% 21.58/21.78      (![X0 : $i]:
% 21.58/21.78         ((k5_xboole_0 @ 
% 21.58/21.78           (k2_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 21.58/21.78            (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 21.58/21.78           X0)
% 21.58/21.78           = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 21.58/21.78              (k5_xboole_0 @ 
% 21.58/21.78               (k3_xboole_0 @ 
% 21.58/21.78                (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 21.58/21.78                (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 21.58/21.78               X0)))),
% 21.58/21.78      inference('sup+', [status(thm)], ['26', '27'])).
% 21.58/21.78  thf('29', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 21.58/21.78      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 21.58/21.78  thf('30', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]:
% 21.58/21.78         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 21.58/21.78      inference('demod', [status(thm)], ['23', '24'])).
% 21.58/21.78  thf('31', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]:
% 21.58/21.78         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 21.58/21.78      inference('sup+', [status(thm)], ['29', '30'])).
% 21.58/21.78  thf('32', plain,
% 21.58/21.78      (((k3_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 21.58/21.78         (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))
% 21.58/21.78         = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 21.58/21.78            (k2_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 21.58/21.78             (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))))),
% 21.58/21.78      inference('demod', [status(thm)], ['17', '18', '19'])).
% 21.58/21.78  thf('33', plain,
% 21.58/21.78      (![X6 : $i, X7 : $i, X8 : $i]:
% 21.58/21.78         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 21.58/21.78           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 21.58/21.78      inference('cnf', [status(esa)], [t91_xboole_1])).
% 21.58/21.78  thf('34', plain,
% 21.58/21.78      (![X0 : $i]:
% 21.58/21.78         ((k5_xboole_0 @ 
% 21.58/21.78           (k3_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 21.58/21.78            (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 21.58/21.78           X0)
% 21.58/21.78           = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 21.58/21.78              (k5_xboole_0 @ 
% 21.58/21.78               (k2_xboole_0 @ 
% 21.58/21.78                (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 21.58/21.78                (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 21.58/21.78               X0)))),
% 21.58/21.78      inference('sup+', [status(thm)], ['32', '33'])).
% 21.58/21.78  thf('35', plain,
% 21.58/21.78      (![X0 : $i]:
% 21.58/21.78         ((k5_xboole_0 @ 
% 21.58/21.78           (k3_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 21.58/21.78            (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 21.58/21.78           (k5_xboole_0 @ X0 @ 
% 21.58/21.78            (k2_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 21.58/21.78             (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))))
% 21.58/21.78           = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0))),
% 21.58/21.78      inference('sup+', [status(thm)], ['31', '34'])).
% 21.58/21.78  thf('36', plain,
% 21.58/21.78      (![X6 : $i, X7 : $i, X8 : $i]:
% 21.58/21.78         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 21.58/21.78           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 21.58/21.78      inference('cnf', [status(esa)], [t91_xboole_1])).
% 21.58/21.78  thf('37', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 21.58/21.78      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 21.58/21.78  thf('38', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.58/21.78         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 21.58/21.78           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 21.58/21.78      inference('sup+', [status(thm)], ['36', '37'])).
% 21.58/21.78  thf('39', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]:
% 21.58/21.78         ((k5_xboole_0 @ 
% 21.58/21.78           (k5_xboole_0 @ X0 @ 
% 21.58/21.78            (k2_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 21.58/21.78             (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))) @ 
% 21.58/21.78           (k5_xboole_0 @ X1 @ 
% 21.58/21.78            (k3_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 21.58/21.78             (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))))
% 21.58/21.78           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0)))),
% 21.58/21.78      inference('sup+', [status(thm)], ['35', '38'])).
% 21.58/21.78  thf('40', plain,
% 21.58/21.78      (![X6 : $i, X7 : $i, X8 : $i]:
% 21.58/21.78         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 21.58/21.78           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 21.58/21.78      inference('cnf', [status(esa)], [t91_xboole_1])).
% 21.58/21.78  thf('41', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.58/21.78         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 21.58/21.78           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 21.58/21.78      inference('sup+', [status(thm)], ['36', '37'])).
% 21.58/21.78  thf('42', plain,
% 21.58/21.78      (((k3_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 21.58/21.78         (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))
% 21.58/21.78         = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 21.58/21.78            (k2_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 21.58/21.78             (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))))),
% 21.58/21.78      inference('demod', [status(thm)], ['17', '18', '19'])).
% 21.58/21.78  thf('43', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]:
% 21.58/21.78         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 21.58/21.78      inference('sup+', [status(thm)], ['29', '30'])).
% 21.58/21.78  thf('44', plain,
% 21.58/21.78      (((k2_tarski @ sk_A @ sk_B)
% 21.58/21.78         = (k5_xboole_0 @ 
% 21.58/21.78            (k2_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 21.58/21.78             (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 21.58/21.78            (k3_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 21.58/21.78             (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))))),
% 21.58/21.78      inference('sup+', [status(thm)], ['42', '43'])).
% 21.58/21.78  thf('45', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 21.58/21.78      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 21.58/21.78  thf('46', plain,
% 21.58/21.78      (((k2_tarski @ sk_A @ sk_B)
% 21.58/21.78         = (k5_xboole_0 @ 
% 21.58/21.78            (k3_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 21.58/21.78             (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 21.58/21.78            (k2_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 21.58/21.78             (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))))),
% 21.58/21.78      inference('demod', [status(thm)], ['44', '45'])).
% 21.58/21.78  thf('47', plain,
% 21.58/21.78      (![X6 : $i, X7 : $i, X8 : $i]:
% 21.58/21.78         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 21.58/21.78           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 21.58/21.78      inference('cnf', [status(esa)], [t91_xboole_1])).
% 21.58/21.78  thf('48', plain,
% 21.58/21.78      (![X0 : $i]:
% 21.58/21.78         ((k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0)
% 21.58/21.78           = (k5_xboole_0 @ 
% 21.58/21.78              (k3_xboole_0 @ 
% 21.58/21.78               (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 21.58/21.78               (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 21.58/21.78              (k5_xboole_0 @ 
% 21.58/21.78               (k2_xboole_0 @ 
% 21.58/21.78                (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 21.58/21.78                (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 21.58/21.78               X0)))),
% 21.58/21.78      inference('sup+', [status(thm)], ['46', '47'])).
% 21.58/21.78  thf('49', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]:
% 21.58/21.78         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X1))
% 21.58/21.78           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0)))),
% 21.58/21.78      inference('demod', [status(thm)], ['39', '40', '41', '48'])).
% 21.58/21.78  thf('50', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]:
% 21.58/21.78         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 21.58/21.78      inference('demod', [status(thm)], ['23', '24'])).
% 21.58/21.78  thf('51', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]:
% 21.58/21.78         ((k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X1)
% 21.58/21.78           = (k5_xboole_0 @ X0 @ 
% 21.58/21.78              (k5_xboole_0 @ X1 @ 
% 21.58/21.78               (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0))))),
% 21.58/21.78      inference('sup+', [status(thm)], ['49', '50'])).
% 21.58/21.78  thf('52', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]:
% 21.58/21.78         ((k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X1)
% 21.58/21.78           = (k5_xboole_0 @ 
% 21.58/21.78              (k5_xboole_0 @ 
% 21.58/21.78               (k3_xboole_0 @ 
% 21.58/21.78                (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 21.58/21.78                (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 21.58/21.78               X0) @ 
% 21.58/21.78              (k5_xboole_0 @ X1 @ 
% 21.58/21.78               (k5_xboole_0 @ 
% 21.58/21.78                (k2_xboole_0 @ 
% 21.58/21.78                 (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 21.58/21.78                 (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 21.58/21.78                X0))))),
% 21.58/21.78      inference('sup+', [status(thm)], ['28', '51'])).
% 21.58/21.78  thf('53', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 21.58/21.78      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 21.58/21.78  thf('54', plain,
% 21.58/21.78      (![X6 : $i, X7 : $i, X8 : $i]:
% 21.58/21.78         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 21.58/21.78           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 21.58/21.78      inference('cnf', [status(esa)], [t91_xboole_1])).
% 21.58/21.78  thf('55', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.58/21.78         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 21.58/21.78           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 21.58/21.78      inference('sup+', [status(thm)], ['53', '54'])).
% 21.58/21.78  thf('56', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]:
% 21.58/21.78         ((k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X1)
% 21.58/21.78           = (k5_xboole_0 @ X0 @ 
% 21.58/21.78              (k5_xboole_0 @ 
% 21.58/21.78               (k3_xboole_0 @ 
% 21.58/21.78                (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 21.58/21.78                (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 21.58/21.78               (k5_xboole_0 @ X1 @ 
% 21.58/21.78                (k5_xboole_0 @ 
% 21.58/21.78                 (k2_xboole_0 @ 
% 21.58/21.78                  (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 21.58/21.78                  (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 21.58/21.78                 X0)))))),
% 21.58/21.78      inference('demod', [status(thm)], ['52', '55'])).
% 21.58/21.78  thf(t125_enumset1, axiom,
% 21.58/21.78    (![A:$i,B:$i,C:$i,D:$i]:
% 21.58/21.78     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ D @ C @ B @ A ) ))).
% 21.58/21.78  thf('57', plain,
% 21.58/21.78      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 21.58/21.78         ((k2_enumset1 @ X15 @ X14 @ X13 @ X12)
% 21.58/21.78           = (k2_enumset1 @ X12 @ X13 @ X14 @ X15))),
% 21.58/21.78      inference('cnf', [status(esa)], [t125_enumset1])).
% 21.58/21.78  thf(t71_enumset1, axiom,
% 21.58/21.78    (![A:$i,B:$i,C:$i]:
% 21.58/21.78     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 21.58/21.78  thf('58', plain,
% 21.58/21.78      (![X34 : $i, X35 : $i, X36 : $i]:
% 21.58/21.78         ((k2_enumset1 @ X34 @ X34 @ X35 @ X36)
% 21.58/21.78           = (k1_enumset1 @ X34 @ X35 @ X36))),
% 21.58/21.78      inference('cnf', [status(esa)], [t71_enumset1])).
% 21.58/21.78  thf('59', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.58/21.78         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 21.58/21.78      inference('sup+', [status(thm)], ['57', '58'])).
% 21.58/21.78  thf('60', plain,
% 21.58/21.78      (![X34 : $i, X35 : $i, X36 : $i]:
% 21.58/21.78         ((k2_enumset1 @ X34 @ X34 @ X35 @ X36)
% 21.58/21.78           = (k1_enumset1 @ X34 @ X35 @ X36))),
% 21.58/21.78      inference('cnf', [status(esa)], [t71_enumset1])).
% 21.58/21.78  thf('61', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]:
% 21.58/21.78         ((k1_enumset1 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X1))),
% 21.58/21.78      inference('sup+', [status(thm)], ['59', '60'])).
% 21.58/21.78  thf(t72_enumset1, axiom,
% 21.58/21.78    (![A:$i,B:$i,C:$i,D:$i]:
% 21.58/21.78     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 21.58/21.78  thf('62', plain,
% 21.58/21.78      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 21.58/21.78         ((k3_enumset1 @ X37 @ X37 @ X38 @ X39 @ X40)
% 21.58/21.78           = (k2_enumset1 @ X37 @ X38 @ X39 @ X40))),
% 21.58/21.78      inference('cnf', [status(esa)], [t72_enumset1])).
% 21.58/21.78  thf('63', plain,
% 21.58/21.78      (![X34 : $i, X35 : $i, X36 : $i]:
% 21.58/21.78         ((k2_enumset1 @ X34 @ X34 @ X35 @ X36)
% 21.58/21.78           = (k1_enumset1 @ X34 @ X35 @ X36))),
% 21.58/21.78      inference('cnf', [status(esa)], [t71_enumset1])).
% 21.58/21.78  thf('64', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.58/21.78         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 21.58/21.78      inference('sup+', [status(thm)], ['62', '63'])).
% 21.58/21.78  thf(t75_enumset1, axiom,
% 21.58/21.78    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 21.58/21.78     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 21.58/21.78       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 21.58/21.78  thf('65', plain,
% 21.58/21.78      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i, X57 : $i, X58 : $i]:
% 21.58/21.78         ((k6_enumset1 @ X52 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 @ X58)
% 21.58/21.78           = (k5_enumset1 @ X52 @ X53 @ X54 @ X55 @ X56 @ X57 @ X58))),
% 21.58/21.78      inference('cnf', [status(esa)], [t75_enumset1])).
% 21.58/21.78  thf(t74_enumset1, axiom,
% 21.58/21.78    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 21.58/21.78     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 21.58/21.78       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 21.58/21.78  thf('66', plain,
% 21.58/21.78      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 21.58/21.78         ((k5_enumset1 @ X46 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51)
% 21.58/21.78           = (k4_enumset1 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51))),
% 21.58/21.78      inference('cnf', [status(esa)], [t74_enumset1])).
% 21.58/21.78  thf('67', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 21.58/21.78         ((k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 21.58/21.78           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 21.58/21.78      inference('sup+', [status(thm)], ['65', '66'])).
% 21.58/21.78  thf(t69_enumset1, axiom,
% 21.58/21.78    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 21.58/21.78  thf('68', plain,
% 21.58/21.78      (![X31 : $i]: ((k2_tarski @ X31 @ X31) = (k1_tarski @ X31))),
% 21.58/21.78      inference('cnf', [status(esa)], [t69_enumset1])).
% 21.58/21.78  thf(t67_enumset1, axiom,
% 21.58/21.78    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 21.58/21.78     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 21.58/21.78       ( k2_xboole_0 @
% 21.58/21.78         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ))).
% 21.58/21.78  thf('69', plain,
% 21.58/21.78      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, 
% 21.58/21.78         X30 : $i]:
% 21.58/21.78         ((k6_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30)
% 21.58/21.78           = (k2_xboole_0 @ 
% 21.58/21.78              (k4_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28) @ 
% 21.58/21.78              (k2_tarski @ X29 @ X30)))),
% 21.58/21.78      inference('cnf', [status(esa)], [t67_enumset1])).
% 21.58/21.78  thf('70', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 21.58/21.78         ((k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 21.58/21.78           = (k2_xboole_0 @ (k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 21.58/21.78              (k1_tarski @ X0)))),
% 21.58/21.78      inference('sup+', [status(thm)], ['68', '69'])).
% 21.58/21.78  thf(t61_enumset1, axiom,
% 21.58/21.78    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 21.58/21.78     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 21.58/21.78       ( k2_xboole_0 @
% 21.58/21.78         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ))).
% 21.58/21.78  thf('71', plain,
% 21.58/21.78      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 21.58/21.78         ((k5_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22)
% 21.58/21.78           = (k2_xboole_0 @ 
% 21.58/21.78              (k4_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21) @ 
% 21.58/21.78              (k1_tarski @ X22)))),
% 21.58/21.78      inference('cnf', [status(esa)], [t61_enumset1])).
% 21.58/21.78  thf('72', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 21.58/21.78         ((k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 21.58/21.78           = (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 21.58/21.78      inference('demod', [status(thm)], ['70', '71'])).
% 21.58/21.78  thf('73', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 21.58/21.78         ((k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 21.58/21.78           = (k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 21.58/21.78      inference('sup+', [status(thm)], ['67', '72'])).
% 21.58/21.78  thf('74', plain,
% 21.58/21.78      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 21.58/21.78         ((k5_enumset1 @ X46 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51)
% 21.58/21.78           = (k4_enumset1 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51))),
% 21.58/21.78      inference('cnf', [status(esa)], [t74_enumset1])).
% 21.58/21.78  thf(t73_enumset1, axiom,
% 21.58/21.78    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 21.58/21.78     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 21.58/21.78       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 21.58/21.78  thf('75', plain,
% 21.58/21.78      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 21.58/21.78         ((k4_enumset1 @ X41 @ X41 @ X42 @ X43 @ X44 @ X45)
% 21.58/21.78           = (k3_enumset1 @ X41 @ X42 @ X43 @ X44 @ X45))),
% 21.58/21.78      inference('cnf', [status(esa)], [t73_enumset1])).
% 21.58/21.78  thf('76', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 21.58/21.78         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 21.58/21.78           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 21.58/21.78      inference('sup+', [status(thm)], ['74', '75'])).
% 21.58/21.78  thf('77', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 21.58/21.78         ((k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 21.58/21.78           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 21.58/21.78      inference('demod', [status(thm)], ['73', '76'])).
% 21.58/21.78  thf('78', plain,
% 21.58/21.78      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 21.58/21.78         ((k4_enumset1 @ X41 @ X41 @ X42 @ X43 @ X44 @ X45)
% 21.58/21.78           = (k3_enumset1 @ X41 @ X42 @ X43 @ X44 @ X45))),
% 21.58/21.78      inference('cnf', [status(esa)], [t73_enumset1])).
% 21.58/21.78  thf('79', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 21.58/21.78         ((k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0)
% 21.58/21.78           = (k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0))),
% 21.58/21.78      inference('sup+', [status(thm)], ['77', '78'])).
% 21.58/21.78  thf('80', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]:
% 21.58/21.78         ((k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X0))),
% 21.58/21.78      inference('sup+', [status(thm)], ['64', '79'])).
% 21.58/21.78  thf('81', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.58/21.78         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 21.58/21.78      inference('sup+', [status(thm)], ['62', '63'])).
% 21.58/21.78  thf('82', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]:
% 21.58/21.78         ((k1_enumset1 @ X1 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X0))),
% 21.58/21.78      inference('demod', [status(thm)], ['80', '81'])).
% 21.58/21.78  thf(t70_enumset1, axiom,
% 21.58/21.78    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 21.58/21.78  thf('83', plain,
% 21.58/21.78      (![X32 : $i, X33 : $i]:
% 21.58/21.78         ((k1_enumset1 @ X32 @ X32 @ X33) = (k2_tarski @ X32 @ X33))),
% 21.58/21.78      inference('cnf', [status(esa)], [t70_enumset1])).
% 21.58/21.78  thf(l51_zfmisc_1, axiom,
% 21.58/21.78    (![A:$i,B:$i]:
% 21.58/21.78     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 21.58/21.78  thf('84', plain,
% 21.58/21.78      (![X59 : $i, X60 : $i]:
% 21.58/21.78         ((k3_tarski @ (k2_tarski @ X59 @ X60)) = (k2_xboole_0 @ X59 @ X60))),
% 21.58/21.78      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 21.58/21.78  thf('85', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]:
% 21.58/21.78         ((k3_tarski @ (k1_enumset1 @ X1 @ X1 @ X0)) = (k2_xboole_0 @ X1 @ X0))),
% 21.58/21.78      inference('sup+', [status(thm)], ['83', '84'])).
% 21.58/21.78  thf('86', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]:
% 21.58/21.78         ((k3_tarski @ (k1_enumset1 @ X1 @ X0 @ X0)) = (k2_xboole_0 @ X1 @ X0))),
% 21.58/21.78      inference('sup+', [status(thm)], ['82', '85'])).
% 21.58/21.78  thf('87', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]:
% 21.58/21.78         ((k3_tarski @ (k1_enumset1 @ X1 @ X0 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 21.58/21.78      inference('sup+', [status(thm)], ['61', '86'])).
% 21.58/21.78  thf('88', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]:
% 21.58/21.78         ((k3_tarski @ (k1_enumset1 @ X1 @ X0 @ X0)) = (k2_xboole_0 @ X1 @ X0))),
% 21.58/21.78      inference('sup+', [status(thm)], ['82', '85'])).
% 21.58/21.78  thf('89', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 21.58/21.78      inference('sup+', [status(thm)], ['87', '88'])).
% 21.58/21.78  thf('90', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 21.58/21.78      inference('sup+', [status(thm)], ['87', '88'])).
% 21.58/21.78  thf('91', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]:
% 21.58/21.78         ((k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X1)
% 21.58/21.78           = (k5_xboole_0 @ X0 @ 
% 21.58/21.78              (k5_xboole_0 @ 
% 21.58/21.78               (k3_xboole_0 @ 
% 21.58/21.78                (k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) @ 
% 21.58/21.78                (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 21.58/21.78               (k5_xboole_0 @ X1 @ 
% 21.58/21.78                (k5_xboole_0 @ 
% 21.58/21.78                 (k2_xboole_0 @ 
% 21.58/21.78                  (k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) @ 
% 21.58/21.78                  (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 21.58/21.78                 X0)))))),
% 21.58/21.78      inference('demod', [status(thm)], ['56', '89', '90'])).
% 21.58/21.78  thf('92', plain,
% 21.58/21.78      (![X0 : $i]:
% 21.58/21.78         ((k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0)
% 21.58/21.78           = (k5_xboole_0 @ X0 @ 
% 21.58/21.78              (k5_xboole_0 @ 
% 21.58/21.78               (k3_xboole_0 @ 
% 21.58/21.78                (k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) @ 
% 21.58/21.78                (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 21.58/21.78               (k5_xboole_0 @ 
% 21.58/21.78                (k2_xboole_0 @ 
% 21.58/21.78                 (k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) @ 
% 21.58/21.78                 (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 21.58/21.78                X0))))),
% 21.58/21.78      inference('sup+', [status(thm)], ['10', '91'])).
% 21.58/21.78  thf('93', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 21.58/21.78      inference('demod', [status(thm)], ['5', '6', '7'])).
% 21.58/21.78  thf('94', plain,
% 21.58/21.78      (![X6 : $i, X7 : $i, X8 : $i]:
% 21.58/21.78         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 21.58/21.78           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 21.58/21.78      inference('cnf', [status(esa)], [t91_xboole_1])).
% 21.58/21.78  thf('95', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]:
% 21.58/21.78         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 21.58/21.78      inference('sup+', [status(thm)], ['29', '30'])).
% 21.58/21.78  thf('96', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.58/21.78         ((k5_xboole_0 @ X2 @ X1)
% 21.58/21.78           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0))))),
% 21.58/21.78      inference('sup+', [status(thm)], ['94', '95'])).
% 21.58/21.78  thf('97', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 21.58/21.78      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 21.58/21.78  thf('98', plain,
% 21.58/21.78      (![X10 : $i, X11 : $i]:
% 21.58/21.78         ((k3_xboole_0 @ X10 @ X11)
% 21.58/21.78           = (k5_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ 
% 21.58/21.78              (k5_xboole_0 @ X10 @ X11)))),
% 21.58/21.78      inference('demod', [status(thm)], ['2', '3'])).
% 21.58/21.78  thf('99', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]:
% 21.58/21.78         ((k3_xboole_0 @ X0 @ X1)
% 21.58/21.78           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 21.58/21.78      inference('sup+', [status(thm)], ['97', '98'])).
% 21.58/21.78  thf('100', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]:
% 21.58/21.78         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 21.58/21.78      inference('demod', [status(thm)], ['23', '24'])).
% 21.58/21.78  thf('101', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]:
% 21.58/21.78         ((k5_xboole_0 @ X0 @ X1)
% 21.58/21.78           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 21.58/21.78      inference('sup+', [status(thm)], ['99', '100'])).
% 21.58/21.78  thf('102', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 21.58/21.78      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 21.58/21.78  thf('103', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]:
% 21.58/21.78         ((k5_xboole_0 @ X0 @ X1)
% 21.58/21.78           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 21.58/21.78      inference('demod', [status(thm)], ['101', '102'])).
% 21.58/21.78  thf('104', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.58/21.78         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 21.58/21.78           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 21.58/21.78      inference('sup+', [status(thm)], ['36', '37'])).
% 21.58/21.78  thf('105', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 21.58/21.78      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 21.58/21.78  thf('106', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.58/21.78         ((k5_xboole_0 @ (k5_xboole_0 @ X0 @ X2) @ X1)
% 21.58/21.78           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 21.58/21.78      inference('sup+', [status(thm)], ['104', '105'])).
% 21.58/21.78  thf('107', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 21.58/21.78      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 21.58/21.78  thf('108', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.58/21.78         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 21.58/21.78           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 21.58/21.78      inference('sup+', [status(thm)], ['36', '37'])).
% 21.58/21.78  thf('109', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 21.58/21.78      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 21.58/21.78  thf('110', plain,
% 21.58/21.78      (![X10 : $i, X11 : $i]:
% 21.58/21.78         ((k3_xboole_0 @ X10 @ X11)
% 21.58/21.78           = (k5_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ 
% 21.58/21.78              (k5_xboole_0 @ X10 @ X11)))),
% 21.58/21.78      inference('demod', [status(thm)], ['2', '3'])).
% 21.58/21.78  thf('111', plain,
% 21.58/21.78      (![X6 : $i, X7 : $i, X8 : $i]:
% 21.58/21.78         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 21.58/21.78           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 21.58/21.78      inference('cnf', [status(esa)], [t91_xboole_1])).
% 21.58/21.78  thf('112', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.58/21.78         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 21.58/21.78           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 21.58/21.78              (k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)))),
% 21.58/21.78      inference('sup+', [status(thm)], ['110', '111'])).
% 21.58/21.78  thf('113', plain,
% 21.58/21.78      (![X6 : $i, X7 : $i, X8 : $i]:
% 21.58/21.78         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 21.58/21.78           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 21.58/21.78      inference('cnf', [status(esa)], [t91_xboole_1])).
% 21.58/21.78  thf('114', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.58/21.78         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 21.58/21.78           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 21.58/21.78              (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X2))))),
% 21.58/21.78      inference('demod', [status(thm)], ['112', '113'])).
% 21.58/21.78  thf('115', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.58/21.78         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 21.58/21.78           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 21.58/21.78      inference('sup+', [status(thm)], ['36', '37'])).
% 21.58/21.78  thf('116', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.58/21.78         ((k5_xboole_0 @ (k5_xboole_0 @ X0 @ X2) @ X1)
% 21.58/21.78           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 21.58/21.78      inference('sup+', [status(thm)], ['104', '105'])).
% 21.58/21.78  thf('117', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 21.58/21.78      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 21.58/21.78  thf('118', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.58/21.78         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 21.58/21.78           = (k5_xboole_0 @ X1 @ 
% 21.58/21.78              (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))))),
% 21.58/21.78      inference('demod', [status(thm)], ['114', '115', '116', '117'])).
% 21.58/21.78  thf('119', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]:
% 21.58/21.78         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 21.58/21.78      inference('demod', [status(thm)], ['23', '24'])).
% 21.58/21.78  thf('120', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]:
% 21.58/21.78         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X1))
% 21.58/21.78           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0)))),
% 21.58/21.78      inference('demod', [status(thm)], ['39', '40', '41', '48'])).
% 21.58/21.78  thf('121', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]:
% 21.58/21.78         ((k5_xboole_0 @ X1 @ X0)
% 21.58/21.78           = (k5_xboole_0 @ (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0) @ 
% 21.58/21.78              (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X1)))),
% 21.58/21.78      inference('sup+', [status(thm)], ['119', '120'])).
% 21.58/21.78  thf('122', plain,
% 21.58/21.78      (![X6 : $i, X7 : $i, X8 : $i]:
% 21.58/21.78         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 21.58/21.78           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 21.58/21.78      inference('cnf', [status(esa)], [t91_xboole_1])).
% 21.58/21.78  thf('123', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]:
% 21.58/21.78         ((k5_xboole_0 @ X1 @ X0)
% 21.58/21.78           = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 21.58/21.78              (k5_xboole_0 @ X0 @ 
% 21.58/21.78               (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X1))))),
% 21.58/21.78      inference('demod', [status(thm)], ['121', '122'])).
% 21.58/21.78  thf('124', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]:
% 21.58/21.78         ((k5_xboole_0 @ (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) @ X1)
% 21.58/21.78           = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 21.58/21.78              (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 21.58/21.78               (k2_tarski @ sk_A @ sk_B))))),
% 21.58/21.78      inference('sup+', [status(thm)], ['118', '123'])).
% 21.58/21.78  thf('125', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.58/21.78         ((k5_xboole_0 @ (k5_xboole_0 @ X0 @ X2) @ X1)
% 21.58/21.78           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 21.58/21.78      inference('sup+', [status(thm)], ['104', '105'])).
% 21.58/21.78  thf('126', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.58/21.78         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 21.58/21.78           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 21.58/21.78      inference('sup+', [status(thm)], ['36', '37'])).
% 21.58/21.78  thf('127', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]:
% 21.58/21.78         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 21.58/21.78      inference('sup+', [status(thm)], ['29', '30'])).
% 21.58/21.78  thf('128', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]:
% 21.58/21.78         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))
% 21.58/21.78           = (k3_xboole_0 @ X1 @ X0))),
% 21.58/21.78      inference('demod', [status(thm)], ['124', '125', '126', '127'])).
% 21.58/21.78  thf('129', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]:
% 21.58/21.78         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 21.58/21.78      inference('demod', [status(thm)], ['23', '24'])).
% 21.58/21.78  thf('130', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]:
% 21.58/21.78         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 21.58/21.78           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 21.58/21.78      inference('sup+', [status(thm)], ['128', '129'])).
% 21.58/21.78  thf('131', plain,
% 21.58/21.78      (![X0 : $i, X1 : $i]:
% 21.58/21.78         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 21.58/21.78      inference('demod', [status(thm)], ['23', '24'])).
% 21.58/21.78  thf('132', plain,
% 21.58/21.78      (((k2_tarski @ sk_A @ sk_B)
% 21.58/21.78         = (k3_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 21.58/21.78      inference('demod', [status(thm)],
% 21.58/21.78                ['92', '93', '96', '103', '106', '107', '108', '109', '130', 
% 21.58/21.78                 '131'])).
% 21.58/21.78  thf(t17_xboole_1, axiom,
% 21.58/21.78    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 21.58/21.78  thf('133', plain,
% 21.58/21.78      (![X4 : $i, X5 : $i]: (r1_tarski @ (k3_xboole_0 @ X4 @ X5) @ X4)),
% 21.58/21.78      inference('cnf', [status(esa)], [t17_xboole_1])).
% 21.58/21.78  thf('134', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)),
% 21.58/21.78      inference('sup+', [status(thm)], ['132', '133'])).
% 21.58/21.78  thf(t38_zfmisc_1, axiom,
% 21.58/21.78    (![A:$i,B:$i,C:$i]:
% 21.58/21.78     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 21.58/21.78       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 21.58/21.78  thf('135', plain,
% 21.58/21.78      (![X61 : $i, X62 : $i, X63 : $i]:
% 21.58/21.78         ((r2_hidden @ X61 @ X62)
% 21.58/21.78          | ~ (r1_tarski @ (k2_tarski @ X61 @ X63) @ X62))),
% 21.58/21.78      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 21.58/21.78  thf('136', plain, ((r2_hidden @ sk_A @ sk_C)),
% 21.58/21.78      inference('sup-', [status(thm)], ['134', '135'])).
% 21.58/21.78  thf('137', plain, ($false), inference('demod', [status(thm)], ['0', '136'])).
% 21.58/21.78  
% 21.58/21.78  % SZS output end Refutation
% 21.58/21.78  
% 21.58/21.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

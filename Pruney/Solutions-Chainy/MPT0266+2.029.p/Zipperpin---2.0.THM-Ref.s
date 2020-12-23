%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Fwx24ReWmh

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:47 EST 2020

% Result     : Theorem 1.15s
% Output     : Refutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :  171 (1969 expanded)
%              Number of leaves         :   30 ( 698 expanded)
%              Depth                    :   36
%              Number of atoms          : 1676 (17448 expanded)
%              Number of equality atoms :  149 (1947 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

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
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('6',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('8',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('15',plain,
    ( ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('17',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('20',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('21',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('23',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('24',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','28'])).

thf('30',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['15','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('32',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = ( k5_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k5_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k5_xboole_0 @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ) )
    = ( k5_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['5','34'])).

thf('36',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('37',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('38',plain,
    ( ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k5_xboole_0 @ sk_C @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','27'])).

thf('40',plain,
    ( ( k5_xboole_0 @ sk_C @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('42',plain,
    ( ( k5_xboole_0 @ sk_C @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ) )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','28'])).

thf('44',plain,
    ( sk_C
    = ( k5_xboole_0 @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ) @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','27'])).

thf('48',plain,
    ( sk_C
    = ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['44','45','46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','27'])).

thf('50',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('51',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('59',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['54','57','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('63',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = ( k5_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('64',plain,
    ( sk_C
    = ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['44','45','46','47'])).

thf('65',plain,
    ( sk_C
    = ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['44','45','46','47'])).

thf('66',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = ( k5_xboole_0 @ ( k3_xboole_0 @ sk_C @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k2_xboole_0 @ sk_C @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ sk_C @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k5_xboole_0 @ ( k2_xboole_0 @ sk_C @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ sk_C @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k5_xboole_0 @ ( k5_xboole_0 @ ( k2_xboole_0 @ sk_C @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ sk_C @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k5_xboole_0 @ ( k2_xboole_0 @ sk_C @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('73',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['70','71','72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','27'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k2_tarski @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ ( k2_tarski @ sk_A @ sk_B ) ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['62','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X1 ) ) @ ( k2_tarski @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['61','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['70','71','72','73'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','28'])).

thf('85',plain,(
    ! [X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X1 ) ) )
      = ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X1 ) ) ),
    inference(demod,[status(thm)],['80','81','82','83','84'])).

thf('86',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['49','85'])).

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('87',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k2_enumset1 @ X12 @ X13 @ X14 @ X15 )
      = ( k2_xboole_0 @ ( k2_tarski @ X12 @ X13 ) @ ( k2_tarski @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('88',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k2_enumset1 @ X12 @ X13 @ X14 @ X15 )
      = ( k2_xboole_0 @ ( k2_tarski @ X12 @ X13 ) @ ( k2_tarski @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('89',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('91',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_enumset1 @ X24 @ X24 @ X25 )
      = ( k2_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X0 )
      = ( k2_enumset1 @ X1 @ X0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf(t125_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ D @ C @ B @ A ) ) )).

thf('93',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k2_enumset1 @ X19 @ X18 @ X17 @ X16 )
      = ( k2_enumset1 @ X16 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t125_enumset1])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X0 @ X1 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_enumset1 @ X24 @ X24 @ X25 )
      = ( k2_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('96',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('97',plain,
    ( ( k2_tarski @ sk_B @ sk_A )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['86','87','94','95','96'])).

thf('98',plain,
    ( sk_C
    = ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ sk_C ) ),
    inference(demod,[status(thm)],['48','97'])).

thf('99',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k2_enumset1 @ X19 @ X18 @ X17 @ X16 )
      = ( k2_enumset1 @ X16 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t125_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('100',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k2_enumset1 @ X26 @ X26 @ X27 @ X28 )
      = ( k1_enumset1 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k2_enumset1 @ X26 @ X26 @ X27 @ X28 )
      = ( k1_enumset1 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('104',plain,(
    ! [X23: $i] :
      ( ( k2_tarski @ X23 @ X23 )
      = ( k1_tarski @ X23 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('105',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k2_enumset1 @ X12 @ X13 @ X14 @ X15 )
      = ( k2_xboole_0 @ ( k2_tarski @ X12 @ X13 ) @ ( k2_tarski @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf(t43_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ) )).

thf('107',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X20 @ X21 @ X22 )
      = ( k2_xboole_0 @ ( k2_tarski @ X20 @ X21 ) @ ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k2_enumset1 @ X26 @ X26 @ X27 @ X28 )
      = ( k1_enumset1 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_enumset1 @ X24 @ X24 @ X25 )
      = ( k2_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['103','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('115',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_enumset1 @ X24 @ X24 @ X25 )
      = ( k2_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('116',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X51 @ X52 ) )
      = ( k2_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k1_enumset1 @ X1 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['114','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['113','118'])).

thf('120',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X51 @ X52 ) )
      = ( k2_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,
    ( sk_C
    = ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','121'])).

thf('123',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','27'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_B @ sk_A ) )
    = ( k5_xboole_0 @ ( k3_xboole_0 @ sk_C @ ( k2_tarski @ sk_B @ sk_A ) ) @ sk_C ) ),
    inference('sup+',[status(thm)],['122','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('130',plain,
    ( ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_B @ sk_A ) )
    = ( k5_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_C @ ( k2_tarski @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','27'])).

thf('132',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k2_tarski @ sk_B @ sk_A ) )
    = ( k5_xboole_0 @ sk_C @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','27'])).

thf('134',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k2_tarski @ sk_B @ sk_A ) )
    = ( k2_tarski @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['132','133'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('135',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('136',plain,(
    r1_tarski @ ( k2_tarski @ sk_B @ sk_A ) @ sk_C ),
    inference('sup+',[status(thm)],['134','135'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('137',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( r2_hidden @ X55 @ X54 )
      | ~ ( r1_tarski @ ( k2_tarski @ X53 @ X55 ) @ X54 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('138',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    $false ),
    inference(demod,[status(thm)],['0','138'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Fwx24ReWmh
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:41:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.15/1.35  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.15/1.35  % Solved by: fo/fo7.sh
% 1.15/1.35  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.15/1.35  % done 1164 iterations in 0.886s
% 1.15/1.35  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.15/1.35  % SZS output start Refutation
% 1.15/1.35  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.15/1.35  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.15/1.35  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.15/1.35  thf(sk_C_type, type, sk_C: $i).
% 1.15/1.35  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.15/1.35  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 1.15/1.35  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.15/1.35  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.15/1.35  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.15/1.35  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.15/1.35  thf(sk_A_type, type, sk_A: $i).
% 1.15/1.35  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.15/1.35  thf(sk_B_type, type, sk_B: $i).
% 1.15/1.35  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.15/1.35  thf(t63_zfmisc_1, conjecture,
% 1.15/1.35    (![A:$i,B:$i,C:$i]:
% 1.15/1.35     ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) =>
% 1.15/1.35       ( r2_hidden @ A @ C ) ))).
% 1.15/1.35  thf(zf_stmt_0, negated_conjecture,
% 1.15/1.35    (~( ![A:$i,B:$i,C:$i]:
% 1.15/1.35        ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) =>
% 1.15/1.35          ( r2_hidden @ A @ C ) ) )),
% 1.15/1.35    inference('cnf.neg', [status(esa)], [t63_zfmisc_1])).
% 1.15/1.35  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf(commutativity_k5_xboole_0, axiom,
% 1.15/1.35    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 1.15/1.35  thf('1', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.15/1.35      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.15/1.35  thf(t95_xboole_1, axiom,
% 1.15/1.35    (![A:$i,B:$i]:
% 1.15/1.35     ( ( k3_xboole_0 @ A @ B ) =
% 1.15/1.35       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 1.15/1.35  thf('2', plain,
% 1.15/1.35      (![X10 : $i, X11 : $i]:
% 1.15/1.35         ((k3_xboole_0 @ X10 @ X11)
% 1.15/1.35           = (k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ 
% 1.15/1.35              (k2_xboole_0 @ X10 @ X11)))),
% 1.15/1.35      inference('cnf', [status(esa)], [t95_xboole_1])).
% 1.15/1.35  thf('3', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.15/1.35      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.15/1.35  thf('4', plain,
% 1.15/1.35      (![X10 : $i, X11 : $i]:
% 1.15/1.35         ((k3_xboole_0 @ X10 @ X11)
% 1.15/1.35           = (k5_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ 
% 1.15/1.35              (k5_xboole_0 @ X10 @ X11)))),
% 1.15/1.35      inference('demod', [status(thm)], ['2', '3'])).
% 1.15/1.35  thf('5', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((k3_xboole_0 @ X0 @ X1)
% 1.15/1.35           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 1.15/1.35      inference('sup+', [status(thm)], ['1', '4'])).
% 1.15/1.35  thf('6', plain,
% 1.15/1.35      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 1.15/1.35         = (k2_tarski @ sk_A @ sk_B))),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('7', plain,
% 1.15/1.35      (![X10 : $i, X11 : $i]:
% 1.15/1.35         ((k3_xboole_0 @ X10 @ X11)
% 1.15/1.35           = (k5_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ 
% 1.15/1.35              (k5_xboole_0 @ X10 @ X11)))),
% 1.15/1.35      inference('demod', [status(thm)], ['2', '3'])).
% 1.15/1.35  thf('8', plain,
% 1.15/1.35      (![X10 : $i, X11 : $i]:
% 1.15/1.35         ((k3_xboole_0 @ X10 @ X11)
% 1.15/1.35           = (k5_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ 
% 1.15/1.35              (k5_xboole_0 @ X10 @ X11)))),
% 1.15/1.35      inference('demod', [status(thm)], ['2', '3'])).
% 1.15/1.35  thf('9', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 1.15/1.35           = (k5_xboole_0 @ 
% 1.15/1.35              (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)) @ 
% 1.15/1.35              (k3_xboole_0 @ X1 @ X0)))),
% 1.15/1.35      inference('sup+', [status(thm)], ['7', '8'])).
% 1.15/1.35  thf('10', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.15/1.35      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.15/1.35  thf('11', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 1.15/1.35           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 1.15/1.35              (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))))),
% 1.15/1.35      inference('demod', [status(thm)], ['9', '10'])).
% 1.15/1.35  thf('12', plain,
% 1.15/1.35      (((k3_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 1.15/1.35         (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))
% 1.15/1.35         = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 1.15/1.35            (k2_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 1.15/1.35             (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))))),
% 1.15/1.35      inference('sup+', [status(thm)], ['6', '11'])).
% 1.15/1.35  thf('13', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.15/1.35      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.15/1.35  thf('14', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.15/1.35      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.15/1.35  thf('15', plain,
% 1.15/1.35      (((k3_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 1.15/1.35         (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))
% 1.15/1.35         = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 1.15/1.35            (k2_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 1.15/1.35             (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))))),
% 1.15/1.35      inference('demod', [status(thm)], ['12', '13', '14'])).
% 1.15/1.35  thf('16', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.15/1.35      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.15/1.35  thf(t92_xboole_1, axiom,
% 1.15/1.35    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.15/1.35  thf('17', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 1.15/1.35      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.15/1.35  thf(t91_xboole_1, axiom,
% 1.15/1.35    (![A:$i,B:$i,C:$i]:
% 1.15/1.35     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.15/1.35       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.15/1.35  thf('18', plain,
% 1.15/1.35      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.15/1.35         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 1.15/1.35           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 1.15/1.35      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.15/1.35  thf('19', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.15/1.35           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.15/1.35      inference('sup+', [status(thm)], ['17', '18'])).
% 1.15/1.35  thf(idempotence_k2_xboole_0, axiom,
% 1.15/1.35    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 1.15/1.35  thf('20', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 1.15/1.35      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 1.15/1.35  thf('21', plain,
% 1.15/1.35      (![X10 : $i, X11 : $i]:
% 1.15/1.35         ((k3_xboole_0 @ X10 @ X11)
% 1.15/1.35           = (k5_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ 
% 1.15/1.35              (k5_xboole_0 @ X10 @ X11)))),
% 1.15/1.35      inference('demod', [status(thm)], ['2', '3'])).
% 1.15/1.35  thf('22', plain,
% 1.15/1.35      (![X0 : $i]:
% 1.15/1.35         ((k3_xboole_0 @ X0 @ X0)
% 1.15/1.35           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 1.15/1.35      inference('sup+', [status(thm)], ['20', '21'])).
% 1.15/1.35  thf(idempotence_k3_xboole_0, axiom,
% 1.15/1.35    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.15/1.35  thf('23', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 1.15/1.35      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.15/1.35  thf('24', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 1.15/1.35      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.15/1.35  thf('25', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.15/1.35      inference('demod', [status(thm)], ['22', '23', '24'])).
% 1.15/1.35  thf('26', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.15/1.35      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.15/1.35  thf('27', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.15/1.35      inference('sup+', [status(thm)], ['25', '26'])).
% 1.15/1.35  thf('28', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.15/1.35      inference('demod', [status(thm)], ['19', '27'])).
% 1.15/1.35  thf('29', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.15/1.35      inference('sup+', [status(thm)], ['16', '28'])).
% 1.15/1.35  thf('30', plain,
% 1.15/1.35      (((k2_tarski @ sk_A @ sk_B)
% 1.15/1.35         = (k5_xboole_0 @ 
% 1.15/1.35            (k2_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 1.15/1.35             (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 1.15/1.35            (k3_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 1.15/1.35             (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))))),
% 1.15/1.35      inference('sup+', [status(thm)], ['15', '29'])).
% 1.15/1.35  thf('31', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.15/1.35      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.15/1.35  thf('32', plain,
% 1.15/1.35      (((k2_tarski @ sk_A @ sk_B)
% 1.15/1.35         = (k5_xboole_0 @ 
% 1.15/1.35            (k3_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 1.15/1.35             (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 1.15/1.35            (k2_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 1.15/1.35             (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))))),
% 1.15/1.35      inference('demod', [status(thm)], ['30', '31'])).
% 1.15/1.35  thf('33', plain,
% 1.15/1.35      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.15/1.35         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 1.15/1.35           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 1.15/1.35      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.15/1.35  thf('34', plain,
% 1.15/1.35      (![X0 : $i]:
% 1.15/1.35         ((k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0)
% 1.15/1.35           = (k5_xboole_0 @ 
% 1.15/1.35              (k3_xboole_0 @ 
% 1.15/1.35               (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 1.15/1.35               (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 1.15/1.35              (k5_xboole_0 @ 
% 1.15/1.35               (k2_xboole_0 @ 
% 1.15/1.35                (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 1.15/1.35                (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 1.15/1.35               X0)))),
% 1.15/1.35      inference('sup+', [status(thm)], ['32', '33'])).
% 1.15/1.35  thf('35', plain,
% 1.15/1.35      (((k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 1.15/1.35         (k5_xboole_0 @ (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) @ 
% 1.15/1.35          (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))
% 1.15/1.35         = (k5_xboole_0 @ 
% 1.15/1.35            (k3_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 1.15/1.35             (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 1.15/1.35            (k3_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 1.15/1.35             (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))))),
% 1.15/1.35      inference('sup+', [status(thm)], ['5', '34'])).
% 1.15/1.35  thf('36', plain,
% 1.15/1.35      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.15/1.35         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 1.15/1.35           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 1.15/1.35      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.15/1.35  thf('37', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 1.15/1.35      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.15/1.35  thf('38', plain,
% 1.15/1.35      (((k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 1.15/1.35         (k5_xboole_0 @ sk_C @ 
% 1.15/1.35          (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 1.15/1.35           (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))))
% 1.15/1.35         = (k1_xboole_0))),
% 1.15/1.35      inference('demod', [status(thm)], ['35', '36', '37'])).
% 1.15/1.35  thf('39', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.15/1.35      inference('demod', [status(thm)], ['19', '27'])).
% 1.15/1.35  thf('40', plain,
% 1.15/1.35      (((k5_xboole_0 @ sk_C @ 
% 1.15/1.35         (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 1.15/1.35          (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))
% 1.15/1.35         = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0))),
% 1.15/1.35      inference('sup+', [status(thm)], ['38', '39'])).
% 1.15/1.35  thf('41', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.15/1.35      inference('demod', [status(thm)], ['22', '23', '24'])).
% 1.15/1.35  thf('42', plain,
% 1.15/1.35      (((k5_xboole_0 @ sk_C @ 
% 1.15/1.35         (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 1.15/1.35          (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))
% 1.15/1.35         = (k2_tarski @ sk_A @ sk_B))),
% 1.15/1.35      inference('demod', [status(thm)], ['40', '41'])).
% 1.15/1.35  thf('43', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.15/1.35      inference('sup+', [status(thm)], ['16', '28'])).
% 1.15/1.35  thf('44', plain,
% 1.15/1.35      (((sk_C)
% 1.15/1.35         = (k5_xboole_0 @ 
% 1.15/1.35            (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 1.15/1.35             (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)) @ 
% 1.15/1.35            (k2_tarski @ sk_A @ sk_B)))),
% 1.15/1.35      inference('sup+', [status(thm)], ['42', '43'])).
% 1.15/1.35  thf('45', plain,
% 1.15/1.35      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.15/1.35         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 1.15/1.35           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 1.15/1.35      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.15/1.35  thf('46', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.15/1.35      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.15/1.35  thf('47', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.15/1.35      inference('demod', [status(thm)], ['19', '27'])).
% 1.15/1.35  thf('48', plain,
% 1.15/1.35      (((sk_C) = (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 1.15/1.35      inference('demod', [status(thm)], ['44', '45', '46', '47'])).
% 1.15/1.35  thf('49', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.15/1.35      inference('demod', [status(thm)], ['19', '27'])).
% 1.15/1.35  thf('50', plain,
% 1.15/1.35      (![X10 : $i, X11 : $i]:
% 1.15/1.35         ((k3_xboole_0 @ X10 @ X11)
% 1.15/1.35           = (k5_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ 
% 1.15/1.35              (k5_xboole_0 @ X10 @ X11)))),
% 1.15/1.35      inference('demod', [status(thm)], ['2', '3'])).
% 1.15/1.35  thf('51', plain,
% 1.15/1.35      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.15/1.35         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 1.15/1.35           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 1.15/1.35      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.15/1.35  thf('52', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.35         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 1.15/1.35           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 1.15/1.35              (k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)))),
% 1.15/1.35      inference('sup+', [status(thm)], ['50', '51'])).
% 1.15/1.35  thf('53', plain,
% 1.15/1.35      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.15/1.35         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 1.15/1.35           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 1.15/1.35      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.15/1.35  thf('54', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.35         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 1.15/1.35           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 1.15/1.35              (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X2))))),
% 1.15/1.35      inference('demod', [status(thm)], ['52', '53'])).
% 1.15/1.35  thf('55', plain,
% 1.15/1.35      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.15/1.35         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 1.15/1.35           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 1.15/1.35      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.15/1.35  thf('56', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.15/1.35      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.15/1.35  thf('57', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.35         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 1.15/1.35           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.15/1.35      inference('sup+', [status(thm)], ['55', '56'])).
% 1.15/1.35  thf('58', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.15/1.35      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.15/1.35  thf('59', plain,
% 1.15/1.35      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.15/1.35         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 1.15/1.35           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 1.15/1.35      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.15/1.35  thf('60', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.35         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 1.15/1.35           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 1.15/1.35      inference('sup+', [status(thm)], ['58', '59'])).
% 1.15/1.35  thf('61', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.35         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 1.15/1.35           = (k5_xboole_0 @ X1 @ 
% 1.15/1.35              (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))))),
% 1.15/1.35      inference('demod', [status(thm)], ['54', '57', '60'])).
% 1.15/1.35  thf('62', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.15/1.35      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.15/1.35  thf('63', plain,
% 1.15/1.35      (((k2_tarski @ sk_A @ sk_B)
% 1.15/1.35         = (k5_xboole_0 @ 
% 1.15/1.35            (k3_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 1.15/1.35             (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 1.15/1.35            (k2_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 1.15/1.35             (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))))),
% 1.15/1.35      inference('demod', [status(thm)], ['30', '31'])).
% 1.15/1.35  thf('64', plain,
% 1.15/1.35      (((sk_C) = (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 1.15/1.35      inference('demod', [status(thm)], ['44', '45', '46', '47'])).
% 1.15/1.35  thf('65', plain,
% 1.15/1.35      (((sk_C) = (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 1.15/1.35      inference('demod', [status(thm)], ['44', '45', '46', '47'])).
% 1.15/1.35  thf('66', plain,
% 1.15/1.35      (((k2_tarski @ sk_A @ sk_B)
% 1.15/1.35         = (k5_xboole_0 @ 
% 1.15/1.35            (k3_xboole_0 @ sk_C @ 
% 1.15/1.35             (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 1.15/1.35            (k2_xboole_0 @ sk_C @ 
% 1.15/1.35             (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))))),
% 1.15/1.35      inference('demod', [status(thm)], ['63', '64', '65'])).
% 1.15/1.35  thf('67', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.35         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 1.15/1.35           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.15/1.35      inference('sup+', [status(thm)], ['55', '56'])).
% 1.15/1.35  thf('68', plain,
% 1.15/1.35      (![X0 : $i]:
% 1.15/1.35         ((k5_xboole_0 @ X0 @ (k2_tarski @ sk_A @ sk_B))
% 1.15/1.35           = (k5_xboole_0 @ 
% 1.15/1.35              (k3_xboole_0 @ sk_C @ 
% 1.15/1.35               (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 1.15/1.35              (k5_xboole_0 @ 
% 1.15/1.35               (k2_xboole_0 @ sk_C @ 
% 1.15/1.35                (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 1.15/1.35               X0)))),
% 1.15/1.35      inference('sup+', [status(thm)], ['66', '67'])).
% 1.15/1.35  thf('69', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.35         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 1.15/1.35           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.15/1.35      inference('sup+', [status(thm)], ['55', '56'])).
% 1.15/1.35  thf('70', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k2_tarski @ sk_A @ sk_B)))
% 1.15/1.35           = (k5_xboole_0 @ 
% 1.15/1.35              (k3_xboole_0 @ sk_C @ 
% 1.15/1.35               (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 1.15/1.35              (k5_xboole_0 @ 
% 1.15/1.35               (k5_xboole_0 @ 
% 1.15/1.35                (k2_xboole_0 @ sk_C @ 
% 1.15/1.35                 (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 1.15/1.35                X0) @ 
% 1.15/1.35               X1)))),
% 1.15/1.35      inference('sup+', [status(thm)], ['68', '69'])).
% 1.15/1.35  thf('71', plain,
% 1.15/1.35      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.15/1.35         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 1.15/1.35           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 1.15/1.35      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.15/1.35  thf('72', plain,
% 1.15/1.35      (![X0 : $i]:
% 1.15/1.35         ((k5_xboole_0 @ X0 @ (k2_tarski @ sk_A @ sk_B))
% 1.15/1.35           = (k5_xboole_0 @ 
% 1.15/1.35              (k3_xboole_0 @ sk_C @ 
% 1.15/1.35               (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 1.15/1.35              (k5_xboole_0 @ 
% 1.15/1.35               (k2_xboole_0 @ sk_C @ 
% 1.15/1.35                (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 1.15/1.35               X0)))),
% 1.15/1.35      inference('sup+', [status(thm)], ['66', '67'])).
% 1.15/1.35  thf('73', plain,
% 1.15/1.35      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.15/1.35         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 1.15/1.35           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 1.15/1.35      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.15/1.35  thf('74', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k2_tarski @ sk_A @ sk_B)))
% 1.15/1.35           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k2_tarski @ sk_A @ sk_B))))),
% 1.15/1.35      inference('demod', [status(thm)], ['70', '71', '72', '73'])).
% 1.15/1.35  thf('75', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.15/1.35      inference('demod', [status(thm)], ['19', '27'])).
% 1.15/1.35  thf('76', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((k5_xboole_0 @ X1 @ (k2_tarski @ sk_A @ sk_B))
% 1.15/1.35           = (k5_xboole_0 @ X0 @ 
% 1.15/1.35              (k5_xboole_0 @ X1 @ 
% 1.15/1.35               (k5_xboole_0 @ X0 @ (k2_tarski @ sk_A @ sk_B)))))),
% 1.15/1.35      inference('sup+', [status(thm)], ['74', '75'])).
% 1.15/1.35  thf('77', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((k5_xboole_0 @ X0 @ (k2_tarski @ sk_A @ sk_B))
% 1.15/1.35           = (k5_xboole_0 @ X1 @ 
% 1.15/1.35              (k5_xboole_0 @ (k5_xboole_0 @ X1 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 1.15/1.35               X0)))),
% 1.15/1.35      inference('sup+', [status(thm)], ['62', '76'])).
% 1.15/1.35  thf('78', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.35         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 1.15/1.35           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 1.15/1.35      inference('sup+', [status(thm)], ['58', '59'])).
% 1.15/1.35  thf('79', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((k5_xboole_0 @ X0 @ (k2_tarski @ sk_A @ sk_B))
% 1.15/1.35           = (k5_xboole_0 @ X1 @ 
% 1.15/1.35              (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 1.15/1.35               (k5_xboole_0 @ X1 @ X0))))),
% 1.15/1.35      inference('demod', [status(thm)], ['77', '78'])).
% 1.15/1.35  thf('80', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((k5_xboole_0 @ 
% 1.15/1.35           (k5_xboole_0 @ X1 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X1)) @ 
% 1.15/1.35           (k2_tarski @ sk_A @ sk_B))
% 1.15/1.35           = (k5_xboole_0 @ X0 @ 
% 1.15/1.35              (k5_xboole_0 @ (k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X1) @ 
% 1.15/1.35               X0)))),
% 1.15/1.35      inference('sup+', [status(thm)], ['61', '79'])).
% 1.15/1.35  thf('81', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.35         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 1.15/1.35           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 1.15/1.35      inference('sup+', [status(thm)], ['58', '59'])).
% 1.15/1.35  thf('82', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k2_tarski @ sk_A @ sk_B)))
% 1.15/1.35           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k2_tarski @ sk_A @ sk_B))))),
% 1.15/1.35      inference('demod', [status(thm)], ['70', '71', '72', '73'])).
% 1.15/1.35  thf('83', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.15/1.35      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.15/1.35  thf('84', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.15/1.35      inference('sup+', [status(thm)], ['16', '28'])).
% 1.15/1.35  thf('85', plain,
% 1.15/1.35      (![X1 : $i]:
% 1.15/1.35         ((k5_xboole_0 @ X1 @ 
% 1.15/1.35           (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 1.15/1.35            (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X1)))
% 1.15/1.35           = (k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X1))),
% 1.15/1.35      inference('demod', [status(thm)], ['80', '81', '82', '83', '84'])).
% 1.15/1.35  thf('86', plain,
% 1.15/1.35      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_A @ sk_B))
% 1.15/1.35         = (k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_A @ sk_B)))),
% 1.15/1.35      inference('sup+', [status(thm)], ['49', '85'])).
% 1.15/1.35  thf(l53_enumset1, axiom,
% 1.15/1.35    (![A:$i,B:$i,C:$i,D:$i]:
% 1.15/1.35     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 1.15/1.35       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 1.15/1.35  thf('87', plain,
% 1.15/1.35      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 1.15/1.35         ((k2_enumset1 @ X12 @ X13 @ X14 @ X15)
% 1.15/1.35           = (k2_xboole_0 @ (k2_tarski @ X12 @ X13) @ (k2_tarski @ X14 @ X15)))),
% 1.15/1.35      inference('cnf', [status(esa)], [l53_enumset1])).
% 1.15/1.35  thf('88', plain,
% 1.15/1.35      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 1.15/1.35         ((k2_enumset1 @ X12 @ X13 @ X14 @ X15)
% 1.15/1.35           = (k2_xboole_0 @ (k2_tarski @ X12 @ X13) @ (k2_tarski @ X14 @ X15)))),
% 1.15/1.35      inference('cnf', [status(esa)], [l53_enumset1])).
% 1.15/1.35  thf('89', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 1.15/1.35      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 1.15/1.35  thf('90', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((k2_enumset1 @ X1 @ X0 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 1.15/1.35      inference('sup+', [status(thm)], ['88', '89'])).
% 1.15/1.35  thf(t70_enumset1, axiom,
% 1.15/1.35    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.15/1.35  thf('91', plain,
% 1.15/1.35      (![X24 : $i, X25 : $i]:
% 1.15/1.35         ((k1_enumset1 @ X24 @ X24 @ X25) = (k2_tarski @ X24 @ X25))),
% 1.15/1.35      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.15/1.35  thf('92', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((k1_enumset1 @ X1 @ X1 @ X0) = (k2_enumset1 @ X1 @ X0 @ X1 @ X0))),
% 1.15/1.35      inference('sup+', [status(thm)], ['90', '91'])).
% 1.15/1.35  thf(t125_enumset1, axiom,
% 1.15/1.35    (![A:$i,B:$i,C:$i,D:$i]:
% 1.15/1.35     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ D @ C @ B @ A ) ))).
% 1.15/1.35  thf('93', plain,
% 1.15/1.35      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 1.15/1.35         ((k2_enumset1 @ X19 @ X18 @ X17 @ X16)
% 1.15/1.35           = (k2_enumset1 @ X16 @ X17 @ X18 @ X19))),
% 1.15/1.35      inference('cnf', [status(esa)], [t125_enumset1])).
% 1.15/1.35  thf('94', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((k2_enumset1 @ X0 @ X1 @ X0 @ X1) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 1.15/1.35      inference('sup+', [status(thm)], ['92', '93'])).
% 1.15/1.35  thf('95', plain,
% 1.15/1.35      (![X24 : $i, X25 : $i]:
% 1.15/1.35         ((k1_enumset1 @ X24 @ X24 @ X25) = (k2_tarski @ X24 @ X25))),
% 1.15/1.35      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.15/1.35  thf('96', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 1.15/1.35      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.15/1.35  thf('97', plain, (((k2_tarski @ sk_B @ sk_A) = (k2_tarski @ sk_A @ sk_B))),
% 1.15/1.35      inference('demod', [status(thm)], ['86', '87', '94', '95', '96'])).
% 1.15/1.35  thf('98', plain,
% 1.15/1.35      (((sk_C) = (k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ sk_C))),
% 1.15/1.35      inference('demod', [status(thm)], ['48', '97'])).
% 1.15/1.35  thf('99', plain,
% 1.15/1.35      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 1.15/1.35         ((k2_enumset1 @ X19 @ X18 @ X17 @ X16)
% 1.15/1.35           = (k2_enumset1 @ X16 @ X17 @ X18 @ X19))),
% 1.15/1.35      inference('cnf', [status(esa)], [t125_enumset1])).
% 1.15/1.35  thf(t71_enumset1, axiom,
% 1.15/1.35    (![A:$i,B:$i,C:$i]:
% 1.15/1.35     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 1.15/1.35  thf('100', plain,
% 1.15/1.35      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.15/1.35         ((k2_enumset1 @ X26 @ X26 @ X27 @ X28)
% 1.15/1.35           = (k1_enumset1 @ X26 @ X27 @ X28))),
% 1.15/1.35      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.15/1.35  thf('101', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.35         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 1.15/1.35      inference('sup+', [status(thm)], ['99', '100'])).
% 1.15/1.35  thf('102', plain,
% 1.15/1.35      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.15/1.35         ((k2_enumset1 @ X26 @ X26 @ X27 @ X28)
% 1.15/1.35           = (k1_enumset1 @ X26 @ X27 @ X28))),
% 1.15/1.35      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.15/1.35  thf('103', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((k1_enumset1 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X1))),
% 1.15/1.35      inference('sup+', [status(thm)], ['101', '102'])).
% 1.15/1.35  thf(t69_enumset1, axiom,
% 1.15/1.35    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.15/1.35  thf('104', plain,
% 1.15/1.35      (![X23 : $i]: ((k2_tarski @ X23 @ X23) = (k1_tarski @ X23))),
% 1.15/1.35      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.15/1.35  thf('105', plain,
% 1.15/1.35      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 1.15/1.35         ((k2_enumset1 @ X12 @ X13 @ X14 @ X15)
% 1.15/1.35           = (k2_xboole_0 @ (k2_tarski @ X12 @ X13) @ (k2_tarski @ X14 @ X15)))),
% 1.15/1.35      inference('cnf', [status(esa)], [l53_enumset1])).
% 1.15/1.35  thf('106', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.35         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0)
% 1.15/1.35           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)))),
% 1.15/1.35      inference('sup+', [status(thm)], ['104', '105'])).
% 1.15/1.35  thf(t43_enumset1, axiom,
% 1.15/1.35    (![A:$i,B:$i,C:$i]:
% 1.15/1.35     ( ( k1_enumset1 @ A @ B @ C ) =
% 1.15/1.35       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ))).
% 1.15/1.35  thf('107', plain,
% 1.15/1.35      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.15/1.35         ((k1_enumset1 @ X20 @ X21 @ X22)
% 1.15/1.35           = (k2_xboole_0 @ (k2_tarski @ X20 @ X21) @ (k1_tarski @ X22)))),
% 1.15/1.35      inference('cnf', [status(esa)], [t43_enumset1])).
% 1.15/1.35  thf('108', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.35         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 1.15/1.35      inference('demod', [status(thm)], ['106', '107'])).
% 1.15/1.35  thf('109', plain,
% 1.15/1.35      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.15/1.35         ((k2_enumset1 @ X26 @ X26 @ X27 @ X28)
% 1.15/1.35           = (k1_enumset1 @ X26 @ X27 @ X28))),
% 1.15/1.35      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.15/1.35  thf('110', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((k1_enumset1 @ X1 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X0))),
% 1.15/1.35      inference('sup+', [status(thm)], ['108', '109'])).
% 1.15/1.35  thf('111', plain,
% 1.15/1.35      (![X24 : $i, X25 : $i]:
% 1.15/1.35         ((k1_enumset1 @ X24 @ X24 @ X25) = (k2_tarski @ X24 @ X25))),
% 1.15/1.35      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.15/1.35  thf('112', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 1.15/1.35      inference('sup+', [status(thm)], ['110', '111'])).
% 1.15/1.35  thf('113', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X0 @ X1))),
% 1.15/1.35      inference('sup+', [status(thm)], ['103', '112'])).
% 1.15/1.35  thf('114', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((k1_enumset1 @ X1 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X0))),
% 1.15/1.35      inference('sup+', [status(thm)], ['108', '109'])).
% 1.15/1.35  thf('115', plain,
% 1.15/1.35      (![X24 : $i, X25 : $i]:
% 1.15/1.35         ((k1_enumset1 @ X24 @ X24 @ X25) = (k2_tarski @ X24 @ X25))),
% 1.15/1.35      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.15/1.35  thf(l51_zfmisc_1, axiom,
% 1.15/1.35    (![A:$i,B:$i]:
% 1.15/1.35     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.15/1.35  thf('116', plain,
% 1.15/1.35      (![X51 : $i, X52 : $i]:
% 1.15/1.35         ((k3_tarski @ (k2_tarski @ X51 @ X52)) = (k2_xboole_0 @ X51 @ X52))),
% 1.15/1.35      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.15/1.35  thf('117', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((k3_tarski @ (k1_enumset1 @ X1 @ X1 @ X0)) = (k2_xboole_0 @ X1 @ X0))),
% 1.15/1.35      inference('sup+', [status(thm)], ['115', '116'])).
% 1.15/1.35  thf('118', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((k3_tarski @ (k1_enumset1 @ X1 @ X0 @ X0)) = (k2_xboole_0 @ X1 @ X0))),
% 1.15/1.35      inference('sup+', [status(thm)], ['114', '117'])).
% 1.15/1.35  thf('119', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 1.15/1.35      inference('sup+', [status(thm)], ['113', '118'])).
% 1.15/1.35  thf('120', plain,
% 1.15/1.35      (![X51 : $i, X52 : $i]:
% 1.15/1.35         ((k3_tarski @ (k2_tarski @ X51 @ X52)) = (k2_xboole_0 @ X51 @ X52))),
% 1.15/1.35      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.15/1.35  thf('121', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.15/1.35      inference('sup+', [status(thm)], ['119', '120'])).
% 1.15/1.35  thf('122', plain,
% 1.15/1.35      (((sk_C) = (k2_xboole_0 @ sk_C @ (k2_tarski @ sk_B @ sk_A)))),
% 1.15/1.35      inference('demod', [status(thm)], ['98', '121'])).
% 1.15/1.35  thf('123', plain,
% 1.15/1.35      (![X10 : $i, X11 : $i]:
% 1.15/1.35         ((k3_xboole_0 @ X10 @ X11)
% 1.15/1.35           = (k5_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ 
% 1.15/1.35              (k5_xboole_0 @ X10 @ X11)))),
% 1.15/1.35      inference('demod', [status(thm)], ['2', '3'])).
% 1.15/1.35  thf('124', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.15/1.35      inference('demod', [status(thm)], ['19', '27'])).
% 1.15/1.35  thf('125', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((k5_xboole_0 @ X1 @ X0)
% 1.15/1.35           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 1.15/1.35      inference('sup+', [status(thm)], ['123', '124'])).
% 1.15/1.35  thf('126', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.15/1.35      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.15/1.35  thf('127', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((k5_xboole_0 @ X1 @ X0)
% 1.15/1.35           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 1.15/1.35      inference('demod', [status(thm)], ['125', '126'])).
% 1.15/1.35  thf('128', plain,
% 1.15/1.35      (((k5_xboole_0 @ sk_C @ (k2_tarski @ sk_B @ sk_A))
% 1.15/1.35         = (k5_xboole_0 @ (k3_xboole_0 @ sk_C @ (k2_tarski @ sk_B @ sk_A)) @ 
% 1.15/1.35            sk_C))),
% 1.15/1.35      inference('sup+', [status(thm)], ['122', '127'])).
% 1.15/1.35  thf('129', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.15/1.35      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.15/1.35  thf('130', plain,
% 1.15/1.35      (((k5_xboole_0 @ sk_C @ (k2_tarski @ sk_B @ sk_A))
% 1.15/1.35         = (k5_xboole_0 @ sk_C @ 
% 1.15/1.35            (k3_xboole_0 @ sk_C @ (k2_tarski @ sk_B @ sk_A))))),
% 1.15/1.35      inference('demod', [status(thm)], ['128', '129'])).
% 1.15/1.35  thf('131', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.15/1.35      inference('demod', [status(thm)], ['19', '27'])).
% 1.15/1.35  thf('132', plain,
% 1.15/1.35      (((k3_xboole_0 @ sk_C @ (k2_tarski @ sk_B @ sk_A))
% 1.15/1.35         = (k5_xboole_0 @ sk_C @ 
% 1.15/1.35            (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_B @ sk_A))))),
% 1.15/1.35      inference('sup+', [status(thm)], ['130', '131'])).
% 1.15/1.35  thf('133', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.15/1.35      inference('demod', [status(thm)], ['19', '27'])).
% 1.15/1.35  thf('134', plain,
% 1.15/1.35      (((k3_xboole_0 @ sk_C @ (k2_tarski @ sk_B @ sk_A))
% 1.15/1.35         = (k2_tarski @ sk_B @ sk_A))),
% 1.15/1.35      inference('demod', [status(thm)], ['132', '133'])).
% 1.15/1.35  thf(t17_xboole_1, axiom,
% 1.15/1.35    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.15/1.35  thf('135', plain,
% 1.15/1.35      (![X4 : $i, X5 : $i]: (r1_tarski @ (k3_xboole_0 @ X4 @ X5) @ X4)),
% 1.15/1.35      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.15/1.35  thf('136', plain, ((r1_tarski @ (k2_tarski @ sk_B @ sk_A) @ sk_C)),
% 1.15/1.35      inference('sup+', [status(thm)], ['134', '135'])).
% 1.15/1.35  thf(t38_zfmisc_1, axiom,
% 1.15/1.35    (![A:$i,B:$i,C:$i]:
% 1.15/1.35     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 1.15/1.35       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 1.15/1.35  thf('137', plain,
% 1.15/1.35      (![X53 : $i, X54 : $i, X55 : $i]:
% 1.15/1.35         ((r2_hidden @ X55 @ X54)
% 1.15/1.35          | ~ (r1_tarski @ (k2_tarski @ X53 @ X55) @ X54))),
% 1.15/1.35      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 1.15/1.35  thf('138', plain, ((r2_hidden @ sk_A @ sk_C)),
% 1.15/1.35      inference('sup-', [status(thm)], ['136', '137'])).
% 1.15/1.35  thf('139', plain, ($false), inference('demod', [status(thm)], ['0', '138'])).
% 1.15/1.35  
% 1.15/1.35  % SZS output end Refutation
% 1.15/1.35  
% 1.15/1.36  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

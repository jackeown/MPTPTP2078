%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jX5bsv7LYR

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:48 EST 2020

% Result     : Theorem 44.11s
% Output     : Refutation 44.11s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 297 expanded)
%              Number of leaves         :   39 ( 114 expanded)
%              Depth                    :   18
%              Number of atoms          : 1382 (2794 expanded)
%              Number of equality atoms :  117 ( 271 expanded)
%              Maximal formula depth    :   18 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

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

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('5',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('8',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('10',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('11',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['4','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','15'])).

thf('17',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('19',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('26',plain,
    ( ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ X0 )
      = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k5_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) ) )
      = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','28'])).

thf('30',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('31',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('39',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['34','37','40'])).

thf('42',plain,
    ( ( k5_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) )
    = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['29','41'])).

thf('43',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','15'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('46',plain,
    ( k1_xboole_0
    = ( k5_xboole_0 @ sk_C @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['4','14'])).

thf('48',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = ( k5_xboole_0 @ sk_C @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('50',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['48','49'])).

thf(t107_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ D @ C @ B ) ) )).

thf('51',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k2_enumset1 @ X12 @ X15 @ X14 @ X13 )
      = ( k2_enumset1 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t107_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('52',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( k2_enumset1 @ X38 @ X38 @ X39 @ X40 )
      = ( k1_enumset1 @ X38 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf(t108_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ B @ A @ C @ D ) ) )).

thf('54',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k2_enumset1 @ X17 @ X16 @ X18 @ X19 )
      = ( k2_enumset1 @ X16 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t108_enumset1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('56',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( k3_enumset1 @ X41 @ X41 @ X42 @ X43 @ X44 )
      = ( k2_enumset1 @ X41 @ X42 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X2 @ X1 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('58',plain,(
    ! [X56: $i,X57: $i,X58: $i,X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ( k6_enumset1 @ X56 @ X56 @ X57 @ X58 @ X59 @ X60 @ X61 @ X62 )
      = ( k5_enumset1 @ X56 @ X57 @ X58 @ X59 @ X60 @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('59',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( k5_enumset1 @ X50 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 )
      = ( k4_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('61',plain,(
    ! [X35: $i] :
      ( ( k2_tarski @ X35 @ X35 )
      = ( k1_tarski @ X35 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t67_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ) )).

thf('62',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( k6_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 ) @ ( k2_tarski @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t67_enumset1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf(t61_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ) )).

thf('64',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k5_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 ) @ ( k1_tarski @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t61_enumset1])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','65'])).

thf('67',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( k5_enumset1 @ X50 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 )
      = ( k4_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('68',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( k4_enumset1 @ X45 @ X45 @ X46 @ X47 @ X48 @ X49 )
      = ( k3_enumset1 @ X45 @ X46 @ X47 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( k4_enumset1 @ X45 @ X45 @ X46 @ X47 @ X48 @ X49 )
      = ( k3_enumset1 @ X45 @ X46 @ X47 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X0 @ X1 @ X1 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['57','72'])).

thf('74',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( k3_enumset1 @ X41 @ X41 @ X42 @ X43 @ X44 )
      = ( k2_enumset1 @ X41 @ X42 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('75',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( k2_enumset1 @ X38 @ X38 @ X39 @ X40 )
      = ( k1_enumset1 @ X38 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X1 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['73','76'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('78',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_enumset1 @ X36 @ X36 @ X37 )
      = ( k2_tarski @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('79',plain,(
    ! [X63: $i,X64: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X63 @ X64 ) )
      = ( k2_xboole_0 @ X63 @ X64 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k1_enumset1 @ X1 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['77','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k1_enumset1 @ X1 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['81','88'])).

thf('90',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['50','89'])).

thf('91',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('93',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_C @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['90','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['4','14'])).

thf('97',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('98',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('99',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ),
    inference('sup+',[status(thm)],['97','98'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('100',plain,(
    ! [X65: $i,X66: $i,X67: $i] :
      ( ( r2_hidden @ X65 @ X66 )
      | ~ ( r1_tarski @ ( k2_tarski @ X65 @ X67 ) @ X66 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('101',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    $false ),
    inference(demod,[status(thm)],['0','101'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jX5bsv7LYR
% 0.13/0.35  % Computer   : n012.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:10:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 44.11/44.32  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 44.11/44.32  % Solved by: fo/fo7.sh
% 44.11/44.32  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 44.11/44.32  % done 5721 iterations in 43.872s
% 44.11/44.32  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 44.11/44.32  % SZS output start Refutation
% 44.11/44.32  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 44.11/44.32  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 44.11/44.32  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 44.11/44.32  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 44.11/44.32  thf(sk_B_type, type, sk_B: $i).
% 44.11/44.32  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 44.11/44.32  thf(sk_C_type, type, sk_C: $i).
% 44.11/44.32  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 44.11/44.32  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 44.11/44.32  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 44.11/44.32  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 44.11/44.32  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 44.11/44.32  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 44.11/44.32  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 44.11/44.32  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 44.11/44.32  thf(sk_A_type, type, sk_A: $i).
% 44.11/44.32  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 44.11/44.32                                           $i > $i).
% 44.11/44.32  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 44.11/44.32  thf(t63_zfmisc_1, conjecture,
% 44.11/44.32    (![A:$i,B:$i,C:$i]:
% 44.11/44.32     ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) =>
% 44.11/44.32       ( r2_hidden @ A @ C ) ))).
% 44.11/44.32  thf(zf_stmt_0, negated_conjecture,
% 44.11/44.32    (~( ![A:$i,B:$i,C:$i]:
% 44.11/44.32        ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) =>
% 44.11/44.32          ( r2_hidden @ A @ C ) ) )),
% 44.11/44.32    inference('cnf.neg', [status(esa)], [t63_zfmisc_1])).
% 44.11/44.32  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 44.11/44.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.11/44.32  thf(commutativity_k5_xboole_0, axiom,
% 44.11/44.32    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 44.11/44.32  thf('1', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 44.11/44.32      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 44.11/44.32  thf(t92_xboole_1, axiom,
% 44.11/44.32    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 44.11/44.32  thf('2', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 44.11/44.32      inference('cnf', [status(esa)], [t92_xboole_1])).
% 44.11/44.32  thf(t91_xboole_1, axiom,
% 44.11/44.32    (![A:$i,B:$i,C:$i]:
% 44.11/44.32     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 44.11/44.32       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 44.11/44.32  thf('3', plain,
% 44.11/44.32      (![X6 : $i, X7 : $i, X8 : $i]:
% 44.11/44.32         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 44.11/44.32           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 44.11/44.32      inference('cnf', [status(esa)], [t91_xboole_1])).
% 44.11/44.32  thf('4', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i]:
% 44.11/44.32         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 44.11/44.32           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 44.11/44.32      inference('sup+', [status(thm)], ['2', '3'])).
% 44.11/44.32  thf(idempotence_k2_xboole_0, axiom,
% 44.11/44.32    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 44.11/44.32  thf('5', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 44.11/44.32      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 44.11/44.32  thf(t95_xboole_1, axiom,
% 44.11/44.32    (![A:$i,B:$i]:
% 44.11/44.32     ( ( k3_xboole_0 @ A @ B ) =
% 44.11/44.32       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 44.11/44.32  thf('6', plain,
% 44.11/44.32      (![X10 : $i, X11 : $i]:
% 44.11/44.32         ((k3_xboole_0 @ X10 @ X11)
% 44.11/44.32           = (k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ 
% 44.11/44.32              (k2_xboole_0 @ X10 @ X11)))),
% 44.11/44.32      inference('cnf', [status(esa)], [t95_xboole_1])).
% 44.11/44.32  thf('7', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 44.11/44.32      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 44.11/44.32  thf('8', plain,
% 44.11/44.32      (![X10 : $i, X11 : $i]:
% 44.11/44.32         ((k3_xboole_0 @ X10 @ X11)
% 44.11/44.32           = (k5_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ 
% 44.11/44.32              (k5_xboole_0 @ X10 @ X11)))),
% 44.11/44.32      inference('demod', [status(thm)], ['6', '7'])).
% 44.11/44.32  thf('9', plain,
% 44.11/44.32      (![X0 : $i]:
% 44.11/44.32         ((k3_xboole_0 @ X0 @ X0)
% 44.11/44.32           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 44.11/44.32      inference('sup+', [status(thm)], ['5', '8'])).
% 44.11/44.32  thf(idempotence_k3_xboole_0, axiom,
% 44.11/44.32    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 44.11/44.32  thf('10', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 44.11/44.32      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 44.11/44.32  thf('11', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 44.11/44.32      inference('cnf', [status(esa)], [t92_xboole_1])).
% 44.11/44.32  thf('12', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 44.11/44.32      inference('demod', [status(thm)], ['9', '10', '11'])).
% 44.11/44.32  thf('13', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 44.11/44.32      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 44.11/44.32  thf('14', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 44.11/44.32      inference('sup+', [status(thm)], ['12', '13'])).
% 44.11/44.32  thf('15', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i]:
% 44.11/44.32         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 44.11/44.32      inference('demod', [status(thm)], ['4', '14'])).
% 44.11/44.32  thf('16', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i]:
% 44.11/44.32         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 44.11/44.32      inference('sup+', [status(thm)], ['1', '15'])).
% 44.11/44.32  thf('17', plain,
% 44.11/44.32      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 44.11/44.32         = (k2_tarski @ sk_A @ sk_B))),
% 44.11/44.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.11/44.32  thf('18', plain,
% 44.11/44.32      (![X10 : $i, X11 : $i]:
% 44.11/44.32         ((k3_xboole_0 @ X10 @ X11)
% 44.11/44.32           = (k5_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ 
% 44.11/44.32              (k5_xboole_0 @ X10 @ X11)))),
% 44.11/44.32      inference('demod', [status(thm)], ['6', '7'])).
% 44.11/44.32  thf('19', plain,
% 44.11/44.32      (![X10 : $i, X11 : $i]:
% 44.11/44.32         ((k3_xboole_0 @ X10 @ X11)
% 44.11/44.32           = (k5_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ 
% 44.11/44.32              (k5_xboole_0 @ X10 @ X11)))),
% 44.11/44.32      inference('demod', [status(thm)], ['6', '7'])).
% 44.11/44.32  thf('20', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i]:
% 44.11/44.32         ((k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 44.11/44.32           = (k5_xboole_0 @ 
% 44.11/44.32              (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)) @ 
% 44.11/44.32              (k3_xboole_0 @ X1 @ X0)))),
% 44.11/44.32      inference('sup+', [status(thm)], ['18', '19'])).
% 44.11/44.32  thf('21', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 44.11/44.32      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 44.11/44.32  thf('22', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i]:
% 44.11/44.32         ((k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 44.11/44.32           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 44.11/44.32              (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))))),
% 44.11/44.32      inference('demod', [status(thm)], ['20', '21'])).
% 44.11/44.32  thf('23', plain,
% 44.11/44.32      (((k3_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 44.11/44.32         (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))
% 44.11/44.32         = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 44.11/44.32            (k2_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 44.11/44.32             (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))))),
% 44.11/44.32      inference('sup+', [status(thm)], ['17', '22'])).
% 44.11/44.32  thf('24', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 44.11/44.32      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 44.11/44.32  thf('25', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 44.11/44.32      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 44.11/44.32  thf('26', plain,
% 44.11/44.32      (((k3_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 44.11/44.32         (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))
% 44.11/44.32         = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 44.11/44.32            (k2_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 44.11/44.32             (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))))),
% 44.11/44.32      inference('demod', [status(thm)], ['23', '24', '25'])).
% 44.11/44.32  thf('27', plain,
% 44.11/44.32      (![X6 : $i, X7 : $i, X8 : $i]:
% 44.11/44.32         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 44.11/44.32           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 44.11/44.32      inference('cnf', [status(esa)], [t91_xboole_1])).
% 44.11/44.32  thf('28', plain,
% 44.11/44.32      (![X0 : $i]:
% 44.11/44.32         ((k5_xboole_0 @ 
% 44.11/44.32           (k3_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 44.11/44.32            (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 44.11/44.32           X0)
% 44.11/44.32           = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 44.11/44.32              (k5_xboole_0 @ 
% 44.11/44.32               (k2_xboole_0 @ 
% 44.11/44.32                (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 44.11/44.32                (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 44.11/44.32               X0)))),
% 44.11/44.32      inference('sup+', [status(thm)], ['26', '27'])).
% 44.11/44.32  thf('29', plain,
% 44.11/44.32      (![X0 : $i]:
% 44.11/44.32         ((k5_xboole_0 @ 
% 44.11/44.32           (k3_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 44.11/44.32            (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 44.11/44.32           (k5_xboole_0 @ X0 @ 
% 44.11/44.32            (k2_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 44.11/44.32             (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))))
% 44.11/44.32           = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0))),
% 44.11/44.32      inference('sup+', [status(thm)], ['16', '28'])).
% 44.11/44.32  thf('30', plain,
% 44.11/44.32      (![X10 : $i, X11 : $i]:
% 44.11/44.32         ((k3_xboole_0 @ X10 @ X11)
% 44.11/44.32           = (k5_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ 
% 44.11/44.32              (k5_xboole_0 @ X10 @ X11)))),
% 44.11/44.32      inference('demod', [status(thm)], ['6', '7'])).
% 44.11/44.32  thf('31', plain,
% 44.11/44.32      (![X6 : $i, X7 : $i, X8 : $i]:
% 44.11/44.32         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 44.11/44.32           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 44.11/44.32      inference('cnf', [status(esa)], [t91_xboole_1])).
% 44.11/44.32  thf('32', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.11/44.32         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 44.11/44.32           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 44.11/44.32              (k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)))),
% 44.11/44.32      inference('sup+', [status(thm)], ['30', '31'])).
% 44.11/44.32  thf('33', plain,
% 44.11/44.32      (![X6 : $i, X7 : $i, X8 : $i]:
% 44.11/44.32         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 44.11/44.32           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 44.11/44.32      inference('cnf', [status(esa)], [t91_xboole_1])).
% 44.11/44.32  thf('34', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.11/44.32         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 44.11/44.32           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 44.11/44.32              (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X2))))),
% 44.11/44.32      inference('demod', [status(thm)], ['32', '33'])).
% 44.11/44.32  thf('35', plain,
% 44.11/44.32      (![X6 : $i, X7 : $i, X8 : $i]:
% 44.11/44.32         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 44.11/44.32           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 44.11/44.32      inference('cnf', [status(esa)], [t91_xboole_1])).
% 44.11/44.32  thf('36', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 44.11/44.32      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 44.11/44.32  thf('37', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.11/44.32         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 44.11/44.32           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 44.11/44.32      inference('sup+', [status(thm)], ['35', '36'])).
% 44.11/44.32  thf('38', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 44.11/44.32      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 44.11/44.32  thf('39', plain,
% 44.11/44.32      (![X6 : $i, X7 : $i, X8 : $i]:
% 44.11/44.32         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 44.11/44.32           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 44.11/44.32      inference('cnf', [status(esa)], [t91_xboole_1])).
% 44.11/44.32  thf('40', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.11/44.32         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 44.11/44.32           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 44.11/44.32      inference('sup+', [status(thm)], ['38', '39'])).
% 44.11/44.32  thf('41', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.11/44.32         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 44.11/44.32           = (k5_xboole_0 @ X1 @ 
% 44.11/44.32              (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))))),
% 44.11/44.32      inference('demod', [status(thm)], ['34', '37', '40'])).
% 44.11/44.32  thf('42', plain,
% 44.11/44.32      (((k5_xboole_0 @ 
% 44.11/44.32         (k3_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 44.11/44.32          (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))) @ 
% 44.11/44.32         (k3_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 44.11/44.32          (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))))
% 44.11/44.32         = (k5_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 44.11/44.32            (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 44.11/44.32             (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))))),
% 44.11/44.32      inference('sup+', [status(thm)], ['29', '41'])).
% 44.11/44.32  thf('43', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 44.11/44.32      inference('cnf', [status(esa)], [t92_xboole_1])).
% 44.11/44.32  thf('44', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i]:
% 44.11/44.32         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 44.11/44.32      inference('sup+', [status(thm)], ['1', '15'])).
% 44.11/44.32  thf('45', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 44.11/44.32      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 44.11/44.32  thf('46', plain,
% 44.11/44.32      (((k1_xboole_0)
% 44.11/44.32         = (k5_xboole_0 @ sk_C @ 
% 44.11/44.32            (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 44.11/44.32      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 44.11/44.32  thf('47', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i]:
% 44.11/44.32         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 44.11/44.32      inference('demod', [status(thm)], ['4', '14'])).
% 44.11/44.32  thf('48', plain,
% 44.11/44.32      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 44.11/44.32         = (k5_xboole_0 @ sk_C @ k1_xboole_0))),
% 44.11/44.32      inference('sup+', [status(thm)], ['46', '47'])).
% 44.11/44.32  thf('49', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 44.11/44.32      inference('demod', [status(thm)], ['9', '10', '11'])).
% 44.11/44.32  thf('50', plain,
% 44.11/44.32      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (sk_C))),
% 44.11/44.32      inference('demod', [status(thm)], ['48', '49'])).
% 44.11/44.32  thf(t107_enumset1, axiom,
% 44.11/44.32    (![A:$i,B:$i,C:$i,D:$i]:
% 44.11/44.32     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ D @ C @ B ) ))).
% 44.11/44.32  thf('51', plain,
% 44.11/44.32      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 44.11/44.32         ((k2_enumset1 @ X12 @ X15 @ X14 @ X13)
% 44.11/44.32           = (k2_enumset1 @ X12 @ X13 @ X14 @ X15))),
% 44.11/44.32      inference('cnf', [status(esa)], [t107_enumset1])).
% 44.11/44.32  thf(t71_enumset1, axiom,
% 44.11/44.32    (![A:$i,B:$i,C:$i]:
% 44.11/44.32     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 44.11/44.32  thf('52', plain,
% 44.11/44.32      (![X38 : $i, X39 : $i, X40 : $i]:
% 44.11/44.32         ((k2_enumset1 @ X38 @ X38 @ X39 @ X40)
% 44.11/44.32           = (k1_enumset1 @ X38 @ X39 @ X40))),
% 44.11/44.32      inference('cnf', [status(esa)], [t71_enumset1])).
% 44.11/44.32  thf('53', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.11/44.32         ((k2_enumset1 @ X0 @ X2 @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 44.11/44.32      inference('sup+', [status(thm)], ['51', '52'])).
% 44.11/44.32  thf(t108_enumset1, axiom,
% 44.11/44.32    (![A:$i,B:$i,C:$i,D:$i]:
% 44.11/44.32     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ A @ C @ D ) ))).
% 44.11/44.32  thf('54', plain,
% 44.11/44.32      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 44.11/44.32         ((k2_enumset1 @ X17 @ X16 @ X18 @ X19)
% 44.11/44.32           = (k2_enumset1 @ X16 @ X17 @ X18 @ X19))),
% 44.11/44.32      inference('cnf', [status(esa)], [t108_enumset1])).
% 44.11/44.32  thf('55', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.11/44.32         ((k2_enumset1 @ X0 @ X2 @ X1 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 44.11/44.32      inference('sup+', [status(thm)], ['53', '54'])).
% 44.11/44.32  thf(t72_enumset1, axiom,
% 44.11/44.32    (![A:$i,B:$i,C:$i,D:$i]:
% 44.11/44.32     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 44.11/44.32  thf('56', plain,
% 44.11/44.32      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 44.11/44.32         ((k3_enumset1 @ X41 @ X41 @ X42 @ X43 @ X44)
% 44.11/44.32           = (k2_enumset1 @ X41 @ X42 @ X43 @ X44))),
% 44.11/44.32      inference('cnf', [status(esa)], [t72_enumset1])).
% 44.11/44.32  thf('57', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.11/44.32         ((k3_enumset1 @ X0 @ X0 @ X2 @ X1 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 44.11/44.32      inference('sup+', [status(thm)], ['55', '56'])).
% 44.11/44.32  thf(t75_enumset1, axiom,
% 44.11/44.32    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 44.11/44.32     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 44.11/44.32       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 44.11/44.32  thf('58', plain,
% 44.11/44.32      (![X56 : $i, X57 : $i, X58 : $i, X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 44.11/44.32         ((k6_enumset1 @ X56 @ X56 @ X57 @ X58 @ X59 @ X60 @ X61 @ X62)
% 44.11/44.32           = (k5_enumset1 @ X56 @ X57 @ X58 @ X59 @ X60 @ X61 @ X62))),
% 44.11/44.32      inference('cnf', [status(esa)], [t75_enumset1])).
% 44.11/44.32  thf(t74_enumset1, axiom,
% 44.11/44.32    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 44.11/44.32     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 44.11/44.32       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 44.11/44.32  thf('59', plain,
% 44.11/44.32      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 44.11/44.32         ((k5_enumset1 @ X50 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55)
% 44.11/44.32           = (k4_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55))),
% 44.11/44.32      inference('cnf', [status(esa)], [t74_enumset1])).
% 44.11/44.32  thf('60', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 44.11/44.32         ((k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 44.11/44.32           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 44.11/44.32      inference('sup+', [status(thm)], ['58', '59'])).
% 44.11/44.32  thf(t69_enumset1, axiom,
% 44.11/44.32    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 44.11/44.32  thf('61', plain,
% 44.11/44.32      (![X35 : $i]: ((k2_tarski @ X35 @ X35) = (k1_tarski @ X35))),
% 44.11/44.32      inference('cnf', [status(esa)], [t69_enumset1])).
% 44.11/44.32  thf(t67_enumset1, axiom,
% 44.11/44.32    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 44.11/44.32     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 44.11/44.32       ( k2_xboole_0 @
% 44.11/44.32         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ))).
% 44.11/44.32  thf('62', plain,
% 44.11/44.32      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, 
% 44.11/44.32         X34 : $i]:
% 44.11/44.32         ((k6_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34)
% 44.11/44.32           = (k2_xboole_0 @ 
% 44.11/44.32              (k4_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32) @ 
% 44.11/44.32              (k2_tarski @ X33 @ X34)))),
% 44.11/44.32      inference('cnf', [status(esa)], [t67_enumset1])).
% 44.11/44.32  thf('63', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 44.11/44.32         ((k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 44.11/44.32           = (k2_xboole_0 @ (k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 44.11/44.32              (k1_tarski @ X0)))),
% 44.11/44.32      inference('sup+', [status(thm)], ['61', '62'])).
% 44.11/44.32  thf(t61_enumset1, axiom,
% 44.11/44.32    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 44.11/44.32     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 44.11/44.32       ( k2_xboole_0 @
% 44.11/44.32         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ))).
% 44.11/44.32  thf('64', plain,
% 44.11/44.32      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 44.11/44.32         ((k5_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26)
% 44.11/44.32           = (k2_xboole_0 @ 
% 44.11/44.32              (k4_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25) @ 
% 44.11/44.32              (k1_tarski @ X26)))),
% 44.11/44.32      inference('cnf', [status(esa)], [t61_enumset1])).
% 44.11/44.32  thf('65', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 44.11/44.32         ((k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 44.11/44.32           = (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 44.11/44.32      inference('demod', [status(thm)], ['63', '64'])).
% 44.11/44.32  thf('66', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 44.11/44.32         ((k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 44.11/44.32           = (k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 44.11/44.32      inference('sup+', [status(thm)], ['60', '65'])).
% 44.11/44.32  thf('67', plain,
% 44.11/44.32      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 44.11/44.32         ((k5_enumset1 @ X50 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55)
% 44.11/44.32           = (k4_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54 @ X55))),
% 44.11/44.32      inference('cnf', [status(esa)], [t74_enumset1])).
% 44.11/44.32  thf(t73_enumset1, axiom,
% 44.11/44.32    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 44.11/44.32     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 44.11/44.32       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 44.11/44.32  thf('68', plain,
% 44.11/44.32      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 44.11/44.32         ((k4_enumset1 @ X45 @ X45 @ X46 @ X47 @ X48 @ X49)
% 44.11/44.32           = (k3_enumset1 @ X45 @ X46 @ X47 @ X48 @ X49))),
% 44.11/44.32      inference('cnf', [status(esa)], [t73_enumset1])).
% 44.11/44.32  thf('69', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 44.11/44.32         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 44.11/44.32           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 44.11/44.32      inference('sup+', [status(thm)], ['67', '68'])).
% 44.11/44.32  thf('70', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 44.11/44.32         ((k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 44.11/44.32           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 44.11/44.32      inference('demod', [status(thm)], ['66', '69'])).
% 44.11/44.32  thf('71', plain,
% 44.11/44.32      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 44.11/44.32         ((k4_enumset1 @ X45 @ X45 @ X46 @ X47 @ X48 @ X49)
% 44.11/44.32           = (k3_enumset1 @ X45 @ X46 @ X47 @ X48 @ X49))),
% 44.11/44.32      inference('cnf', [status(esa)], [t73_enumset1])).
% 44.11/44.32  thf('72', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 44.11/44.32         ((k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0)
% 44.11/44.32           = (k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0))),
% 44.11/44.32      inference('sup+', [status(thm)], ['70', '71'])).
% 44.11/44.32  thf('73', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i]:
% 44.11/44.32         ((k3_enumset1 @ X0 @ X0 @ X0 @ X1 @ X1) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 44.11/44.32      inference('sup+', [status(thm)], ['57', '72'])).
% 44.11/44.32  thf('74', plain,
% 44.11/44.32      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 44.11/44.32         ((k3_enumset1 @ X41 @ X41 @ X42 @ X43 @ X44)
% 44.11/44.32           = (k2_enumset1 @ X41 @ X42 @ X43 @ X44))),
% 44.11/44.32      inference('cnf', [status(esa)], [t72_enumset1])).
% 44.11/44.32  thf('75', plain,
% 44.11/44.32      (![X38 : $i, X39 : $i, X40 : $i]:
% 44.11/44.32         ((k2_enumset1 @ X38 @ X38 @ X39 @ X40)
% 44.11/44.32           = (k1_enumset1 @ X38 @ X39 @ X40))),
% 44.11/44.32      inference('cnf', [status(esa)], [t71_enumset1])).
% 44.11/44.32  thf('76', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.11/44.32         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 44.11/44.32      inference('sup+', [status(thm)], ['74', '75'])).
% 44.11/44.32  thf('77', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i]:
% 44.11/44.32         ((k1_enumset1 @ X0 @ X1 @ X1) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 44.11/44.32      inference('demod', [status(thm)], ['73', '76'])).
% 44.11/44.32  thf(t70_enumset1, axiom,
% 44.11/44.32    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 44.11/44.32  thf('78', plain,
% 44.11/44.32      (![X36 : $i, X37 : $i]:
% 44.11/44.32         ((k1_enumset1 @ X36 @ X36 @ X37) = (k2_tarski @ X36 @ X37))),
% 44.11/44.32      inference('cnf', [status(esa)], [t70_enumset1])).
% 44.11/44.32  thf(l51_zfmisc_1, axiom,
% 44.11/44.32    (![A:$i,B:$i]:
% 44.11/44.32     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 44.11/44.32  thf('79', plain,
% 44.11/44.32      (![X63 : $i, X64 : $i]:
% 44.11/44.32         ((k3_tarski @ (k2_tarski @ X63 @ X64)) = (k2_xboole_0 @ X63 @ X64))),
% 44.11/44.32      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 44.11/44.32  thf('80', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i]:
% 44.11/44.32         ((k3_tarski @ (k1_enumset1 @ X1 @ X1 @ X0)) = (k2_xboole_0 @ X1 @ X0))),
% 44.11/44.32      inference('sup+', [status(thm)], ['78', '79'])).
% 44.11/44.32  thf('81', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i]:
% 44.11/44.32         ((k3_tarski @ (k1_enumset1 @ X1 @ X0 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 44.11/44.32      inference('sup+', [status(thm)], ['77', '80'])).
% 44.11/44.32  thf('82', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.11/44.32         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 44.11/44.32      inference('sup+', [status(thm)], ['74', '75'])).
% 44.11/44.32  thf('83', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 44.11/44.32         ((k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0)
% 44.11/44.32           = (k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0))),
% 44.11/44.32      inference('sup+', [status(thm)], ['70', '71'])).
% 44.11/44.32  thf('84', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i]:
% 44.11/44.32         ((k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X0))),
% 44.11/44.32      inference('sup+', [status(thm)], ['82', '83'])).
% 44.11/44.32  thf('85', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.11/44.32         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 44.11/44.32      inference('sup+', [status(thm)], ['74', '75'])).
% 44.11/44.32  thf('86', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i]:
% 44.11/44.32         ((k1_enumset1 @ X1 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X0))),
% 44.11/44.32      inference('demod', [status(thm)], ['84', '85'])).
% 44.11/44.32  thf('87', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i]:
% 44.11/44.32         ((k3_tarski @ (k1_enumset1 @ X1 @ X1 @ X0)) = (k2_xboole_0 @ X1 @ X0))),
% 44.11/44.32      inference('sup+', [status(thm)], ['78', '79'])).
% 44.11/44.32  thf('88', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i]:
% 44.11/44.32         ((k3_tarski @ (k1_enumset1 @ X1 @ X0 @ X0)) = (k2_xboole_0 @ X1 @ X0))),
% 44.11/44.32      inference('sup+', [status(thm)], ['86', '87'])).
% 44.11/44.32  thf('89', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 44.11/44.32      inference('sup+', [status(thm)], ['81', '88'])).
% 44.11/44.32  thf('90', plain,
% 44.11/44.32      (((k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) = (sk_C))),
% 44.11/44.32      inference('demod', [status(thm)], ['50', '89'])).
% 44.11/44.32  thf('91', plain,
% 44.11/44.32      (![X10 : $i, X11 : $i]:
% 44.11/44.32         ((k3_xboole_0 @ X10 @ X11)
% 44.11/44.32           = (k5_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ 
% 44.11/44.32              (k5_xboole_0 @ X10 @ X11)))),
% 44.11/44.32      inference('demod', [status(thm)], ['6', '7'])).
% 44.11/44.32  thf('92', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.11/44.32         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 44.11/44.32           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 44.11/44.32      inference('sup+', [status(thm)], ['35', '36'])).
% 44.11/44.32  thf('93', plain,
% 44.11/44.32      (![X10 : $i, X11 : $i]:
% 44.11/44.32         ((k3_xboole_0 @ X10 @ X11)
% 44.11/44.32           = (k5_xboole_0 @ X10 @ 
% 44.11/44.32              (k5_xboole_0 @ X11 @ (k2_xboole_0 @ X10 @ X11))))),
% 44.11/44.32      inference('demod', [status(thm)], ['91', '92'])).
% 44.11/44.32  thf('94', plain,
% 44.11/44.32      (((k3_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 44.11/44.32         = (k5_xboole_0 @ sk_C @ 
% 44.11/44.32            (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 44.11/44.32      inference('sup+', [status(thm)], ['90', '93'])).
% 44.11/44.32  thf('95', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 44.11/44.32      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 44.11/44.32  thf('96', plain,
% 44.11/44.32      (![X0 : $i, X1 : $i]:
% 44.11/44.32         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 44.11/44.32      inference('demod', [status(thm)], ['4', '14'])).
% 44.11/44.32  thf('97', plain,
% 44.11/44.32      (((k3_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 44.11/44.32         = (k2_tarski @ sk_A @ sk_B))),
% 44.11/44.32      inference('demod', [status(thm)], ['94', '95', '96'])).
% 44.11/44.32  thf(t17_xboole_1, axiom,
% 44.11/44.32    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 44.11/44.32  thf('98', plain,
% 44.11/44.32      (![X4 : $i, X5 : $i]: (r1_tarski @ (k3_xboole_0 @ X4 @ X5) @ X4)),
% 44.11/44.32      inference('cnf', [status(esa)], [t17_xboole_1])).
% 44.11/44.32  thf('99', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)),
% 44.11/44.32      inference('sup+', [status(thm)], ['97', '98'])).
% 44.11/44.32  thf(t38_zfmisc_1, axiom,
% 44.11/44.32    (![A:$i,B:$i,C:$i]:
% 44.11/44.32     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 44.11/44.32       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 44.11/44.32  thf('100', plain,
% 44.11/44.32      (![X65 : $i, X66 : $i, X67 : $i]:
% 44.11/44.32         ((r2_hidden @ X65 @ X66)
% 44.11/44.32          | ~ (r1_tarski @ (k2_tarski @ X65 @ X67) @ X66))),
% 44.11/44.32      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 44.11/44.32  thf('101', plain, ((r2_hidden @ sk_A @ sk_C)),
% 44.11/44.32      inference('sup-', [status(thm)], ['99', '100'])).
% 44.11/44.32  thf('102', plain, ($false), inference('demod', [status(thm)], ['0', '101'])).
% 44.11/44.32  
% 44.11/44.32  % SZS output end Refutation
% 44.11/44.32  
% 44.11/44.33  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

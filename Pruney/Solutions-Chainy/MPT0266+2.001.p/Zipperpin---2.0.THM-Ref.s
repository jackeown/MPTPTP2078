%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.t6dS5M2f8O

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:44 EST 2020

% Result     : Theorem 0.62s
% Output     : Refutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 368 expanded)
%              Number of leaves         :   29 ( 137 expanded)
%              Depth                    :   21
%              Number of atoms          : 1214 (3135 expanded)
%              Number of equality atoms :  102 ( 342 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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
    ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_tarski @ X15 @ X14 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('3',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_tarski @ X15 @ X14 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ sk_C_1 )
    = ( k2_tarski @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X12 @ X13 ) @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X12 @ X13 ) @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k5_xboole_0 @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k5_xboole_0 @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k5_xboole_0 @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('16',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k5_xboole_0 @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['11','14','17'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('19',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('20',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k5_xboole_0 @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('22',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('23',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X12 @ X13 ) @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('25',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('26',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','29'])).

thf('31',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ sk_C_1 )
    = ( k2_tarski @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf('32',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X12 @ X13 ) @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('33',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X12 @ X13 ) @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ sk_C_1 ) @ ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ sk_C_1 ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ sk_C_1 ) @ ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ sk_C_1 ) ) ) ),
    inference('sup+',[status(thm)],['31','36'])).

thf('38',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_tarski @ X15 @ X14 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('39',plain,(
    ! [X57: $i,X58: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X57 @ X58 ) )
      = ( k2_xboole_0 @ X57 @ X58 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X57: $i,X58: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X57 @ X58 ) )
      = ( k2_xboole_0 @ X57 @ X58 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('46',plain,
    ( ( k3_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) @ ( k5_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) @ ( k5_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['37','42','43','44','45'])).

thf('47',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k5_xboole_0 @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) @ ( k5_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) ) @ X0 )
      = ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k5_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) @ ( k5_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) @ ( k5_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) ) @ ( k5_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) @ ( k5_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) ) @ X0 ) )
      = ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) @ ( k5_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) ) @ ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) @ ( k5_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) ) ) )
      = ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k5_xboole_0 @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) @ ( k5_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) ) @ ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) @ ( k5_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) ) ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('56',plain,
    ( ( k3_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) @ ( k5_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) @ ( k5_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['37','42','43','44','45'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','29'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k2_tarski @ sk_B @ sk_A )
    = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) @ ( k5_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) @ ( k5_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k5_xboole_0 @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ X0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) @ ( k5_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) ) @ ( k5_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) @ ( k5_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ X1 ) )
      = ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['53','54','55','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','29'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_tarski @ sk_B @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['18','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','29'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k5_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ sk_C_1 ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k2_tarski @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('73',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('74',plain,
    ( ( k5_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','29'])).

thf('76',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) )
    = ( k5_xboole_0 @ sk_C_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('78',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) )
    = sk_C_1 ),
    inference(demod,[status(thm)],['76','77'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('79',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_enumset1 @ X28 @ X28 @ X29 )
      = ( k2_tarski @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('80',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X24 )
      | ( r2_hidden @ X21 @ X25 )
      | ( X25
       != ( k1_enumset1 @ X24 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('81',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ X21 @ ( k1_enumset1 @ X24 @ X23 @ X22 ) )
      | ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X24 ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['79','81'])).

thf('83',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X17 != X18 )
      | ~ ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('84',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ~ ( zip_tseitin_0 @ X18 @ X18 @ X19 @ X16 ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['82','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['79','81'])).

thf('87',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X17 != X16 )
      | ~ ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('88',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ~ ( zip_tseitin_0 @ X16 @ X18 @ X19 @ X16 ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['86','88'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('90',plain,(
    ! [X55: $i,X56: $i] :
      ( ( r1_tarski @ X55 @ ( k3_tarski @ X56 ) )
      | ~ ( r2_hidden @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('94',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['85','95'])).

thf('97',plain,(
    r2_hidden @ sk_A @ sk_C_1 ),
    inference('sup+',[status(thm)],['78','96'])).

thf('98',plain,(
    $false ),
    inference(demod,[status(thm)],['0','97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.t6dS5M2f8O
% 0.14/0.38  % Computer   : n004.cluster.edu
% 0.14/0.38  % Model      : x86_64 x86_64
% 0.14/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.38  % Memory     : 8042.1875MB
% 0.14/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.38  % CPULimit   : 60
% 0.14/0.38  % DateTime   : Tue Dec  1 18:05:39 EST 2020
% 0.14/0.38  % CPUTime    : 
% 0.14/0.38  % Running portfolio for 600 s
% 0.14/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.39  % Running in FO mode
% 0.62/0.82  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.62/0.82  % Solved by: fo/fo7.sh
% 0.62/0.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.62/0.82  % done 382 iterations in 0.331s
% 0.62/0.82  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.62/0.82  % SZS output start Refutation
% 0.62/0.82  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.62/0.82  thf(sk_B_type, type, sk_B: $i).
% 0.62/0.82  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.62/0.82  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.62/0.82  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.62/0.82  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.62/0.82  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.62/0.82  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.62/0.82  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.62/0.82  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.62/0.82  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.62/0.82  thf(sk_A_type, type, sk_A: $i).
% 0.62/0.82  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.62/0.82  thf(t63_zfmisc_1, conjecture,
% 0.62/0.82    (![A:$i,B:$i,C:$i]:
% 0.62/0.82     ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) =>
% 0.62/0.82       ( r2_hidden @ A @ C ) ))).
% 0.62/0.82  thf(zf_stmt_0, negated_conjecture,
% 0.62/0.82    (~( ![A:$i,B:$i,C:$i]:
% 0.62/0.82        ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) =>
% 0.62/0.82          ( r2_hidden @ A @ C ) ) )),
% 0.62/0.82    inference('cnf.neg', [status(esa)], [t63_zfmisc_1])).
% 0.62/0.82  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C_1)),
% 0.62/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.82  thf('1', plain,
% 0.62/0.82      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.62/0.82         = (k2_tarski @ sk_A @ sk_B))),
% 0.62/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.82  thf(commutativity_k2_tarski, axiom,
% 0.62/0.82    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.62/0.82  thf('2', plain,
% 0.62/0.82      (![X14 : $i, X15 : $i]:
% 0.62/0.82         ((k2_tarski @ X15 @ X14) = (k2_tarski @ X14 @ X15))),
% 0.62/0.82      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.62/0.82  thf('3', plain,
% 0.62/0.82      (![X14 : $i, X15 : $i]:
% 0.62/0.82         ((k2_tarski @ X15 @ X14) = (k2_tarski @ X14 @ X15))),
% 0.62/0.82      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.62/0.82  thf('4', plain,
% 0.62/0.82      (((k3_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ sk_C_1)
% 0.62/0.82         = (k2_tarski @ sk_B @ sk_A))),
% 0.62/0.82      inference('demod', [status(thm)], ['1', '2', '3'])).
% 0.62/0.82  thf(t95_xboole_1, axiom,
% 0.62/0.82    (![A:$i,B:$i]:
% 0.62/0.82     ( ( k3_xboole_0 @ A @ B ) =
% 0.62/0.82       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.62/0.82  thf('5', plain,
% 0.62/0.82      (![X12 : $i, X13 : $i]:
% 0.62/0.82         ((k3_xboole_0 @ X12 @ X13)
% 0.62/0.82           = (k5_xboole_0 @ (k5_xboole_0 @ X12 @ X13) @ 
% 0.62/0.82              (k2_xboole_0 @ X12 @ X13)))),
% 0.62/0.82      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.62/0.82  thf(commutativity_k5_xboole_0, axiom,
% 0.62/0.82    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.62/0.82  thf('6', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.62/0.82      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.62/0.82  thf('7', plain,
% 0.62/0.82      (![X12 : $i, X13 : $i]:
% 0.62/0.82         ((k3_xboole_0 @ X12 @ X13)
% 0.62/0.82           = (k5_xboole_0 @ (k2_xboole_0 @ X12 @ X13) @ 
% 0.62/0.82              (k5_xboole_0 @ X12 @ X13)))),
% 0.62/0.82      inference('demod', [status(thm)], ['5', '6'])).
% 0.62/0.82  thf(t91_xboole_1, axiom,
% 0.62/0.82    (![A:$i,B:$i,C:$i]:
% 0.62/0.82     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.62/0.82       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.62/0.82  thf('8', plain,
% 0.62/0.82      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.62/0.82         ((k5_xboole_0 @ (k5_xboole_0 @ X8 @ X9) @ X10)
% 0.62/0.82           = (k5_xboole_0 @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 0.62/0.82      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.62/0.82  thf('9', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.82         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.62/0.82           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 0.62/0.82              (k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)))),
% 0.62/0.82      inference('sup+', [status(thm)], ['7', '8'])).
% 0.62/0.82  thf('10', plain,
% 0.62/0.82      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.62/0.82         ((k5_xboole_0 @ (k5_xboole_0 @ X8 @ X9) @ X10)
% 0.62/0.82           = (k5_xboole_0 @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 0.62/0.82      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.62/0.82  thf('11', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.82         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.62/0.82           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 0.62/0.82              (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X2))))),
% 0.62/0.82      inference('demod', [status(thm)], ['9', '10'])).
% 0.62/0.82  thf('12', plain,
% 0.62/0.82      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.62/0.82         ((k5_xboole_0 @ (k5_xboole_0 @ X8 @ X9) @ X10)
% 0.62/0.82           = (k5_xboole_0 @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 0.62/0.82      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.62/0.82  thf('13', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.62/0.82      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.62/0.82  thf('14', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.82         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.62/0.82           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.62/0.82      inference('sup+', [status(thm)], ['12', '13'])).
% 0.62/0.82  thf('15', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.62/0.82      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.62/0.82  thf('16', plain,
% 0.62/0.82      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.62/0.82         ((k5_xboole_0 @ (k5_xboole_0 @ X8 @ X9) @ X10)
% 0.62/0.82           = (k5_xboole_0 @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 0.62/0.82      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.62/0.82  thf('17', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.82         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 0.62/0.82           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 0.62/0.82      inference('sup+', [status(thm)], ['15', '16'])).
% 0.62/0.82  thf('18', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.82         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.62/0.82           = (k5_xboole_0 @ X1 @ 
% 0.62/0.82              (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))))),
% 0.62/0.82      inference('demod', [status(thm)], ['11', '14', '17'])).
% 0.62/0.82  thf(t92_xboole_1, axiom,
% 0.62/0.82    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.62/0.82  thf('19', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ X11) = (k1_xboole_0))),
% 0.62/0.82      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.62/0.82  thf('20', plain,
% 0.62/0.82      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.62/0.82         ((k5_xboole_0 @ (k5_xboole_0 @ X8 @ X9) @ X10)
% 0.62/0.82           = (k5_xboole_0 @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 0.62/0.82      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.62/0.82  thf('21', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]:
% 0.62/0.82         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.62/0.82           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.62/0.82      inference('sup+', [status(thm)], ['19', '20'])).
% 0.62/0.82  thf(idempotence_k2_xboole_0, axiom,
% 0.62/0.82    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.62/0.82  thf('22', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ X6) = (X6))),
% 0.62/0.82      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.62/0.82  thf('23', plain,
% 0.62/0.82      (![X12 : $i, X13 : $i]:
% 0.62/0.82         ((k3_xboole_0 @ X12 @ X13)
% 0.62/0.82           = (k5_xboole_0 @ (k2_xboole_0 @ X12 @ X13) @ 
% 0.62/0.82              (k5_xboole_0 @ X12 @ X13)))),
% 0.62/0.82      inference('demod', [status(thm)], ['5', '6'])).
% 0.62/0.82  thf('24', plain,
% 0.62/0.82      (![X0 : $i]:
% 0.62/0.82         ((k3_xboole_0 @ X0 @ X0)
% 0.62/0.82           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.62/0.82      inference('sup+', [status(thm)], ['22', '23'])).
% 0.62/0.82  thf(idempotence_k3_xboole_0, axiom,
% 0.62/0.82    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.62/0.82  thf('25', plain, (![X7 : $i]: ((k3_xboole_0 @ X7 @ X7) = (X7))),
% 0.62/0.82      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.62/0.82  thf('26', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ X11) = (k1_xboole_0))),
% 0.62/0.82      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.62/0.82  thf('27', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.62/0.82      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.62/0.82  thf('28', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.62/0.82      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.62/0.82  thf('29', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.62/0.82      inference('sup+', [status(thm)], ['27', '28'])).
% 0.62/0.82  thf('30', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]:
% 0.62/0.82         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.62/0.82      inference('demod', [status(thm)], ['21', '29'])).
% 0.62/0.82  thf('31', plain,
% 0.62/0.82      (((k3_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ sk_C_1)
% 0.62/0.82         = (k2_tarski @ sk_B @ sk_A))),
% 0.62/0.82      inference('demod', [status(thm)], ['1', '2', '3'])).
% 0.62/0.82  thf('32', plain,
% 0.62/0.82      (![X12 : $i, X13 : $i]:
% 0.62/0.82         ((k3_xboole_0 @ X12 @ X13)
% 0.62/0.82           = (k5_xboole_0 @ (k2_xboole_0 @ X12 @ X13) @ 
% 0.62/0.82              (k5_xboole_0 @ X12 @ X13)))),
% 0.62/0.82      inference('demod', [status(thm)], ['5', '6'])).
% 0.62/0.82  thf('33', plain,
% 0.62/0.82      (![X12 : $i, X13 : $i]:
% 0.62/0.82         ((k3_xboole_0 @ X12 @ X13)
% 0.62/0.82           = (k5_xboole_0 @ (k2_xboole_0 @ X12 @ X13) @ 
% 0.62/0.82              (k5_xboole_0 @ X12 @ X13)))),
% 0.62/0.82      inference('demod', [status(thm)], ['5', '6'])).
% 0.62/0.82  thf('34', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]:
% 0.62/0.82         ((k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.62/0.82           = (k5_xboole_0 @ 
% 0.62/0.82              (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)) @ 
% 0.62/0.82              (k3_xboole_0 @ X1 @ X0)))),
% 0.62/0.82      inference('sup+', [status(thm)], ['32', '33'])).
% 0.62/0.82  thf('35', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.62/0.82      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.62/0.82  thf('36', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]:
% 0.62/0.82         ((k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.62/0.82           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.62/0.82              (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))))),
% 0.62/0.82      inference('demod', [status(thm)], ['34', '35'])).
% 0.62/0.82  thf('37', plain,
% 0.62/0.82      (((k3_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ sk_C_1) @ 
% 0.62/0.82         (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ sk_C_1))
% 0.62/0.82         = (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ 
% 0.62/0.82            (k2_xboole_0 @ 
% 0.62/0.82             (k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ sk_C_1) @ 
% 0.62/0.82             (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ sk_C_1))))),
% 0.62/0.82      inference('sup+', [status(thm)], ['31', '36'])).
% 0.62/0.82  thf('38', plain,
% 0.62/0.82      (![X14 : $i, X15 : $i]:
% 0.62/0.82         ((k2_tarski @ X15 @ X14) = (k2_tarski @ X14 @ X15))),
% 0.62/0.82      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.62/0.82  thf(l51_zfmisc_1, axiom,
% 0.62/0.82    (![A:$i,B:$i]:
% 0.62/0.82     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.62/0.82  thf('39', plain,
% 0.62/0.82      (![X57 : $i, X58 : $i]:
% 0.62/0.82         ((k3_tarski @ (k2_tarski @ X57 @ X58)) = (k2_xboole_0 @ X57 @ X58))),
% 0.62/0.82      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.62/0.82  thf('40', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]:
% 0.62/0.82         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.62/0.82      inference('sup+', [status(thm)], ['38', '39'])).
% 0.62/0.82  thf('41', plain,
% 0.62/0.82      (![X57 : $i, X58 : $i]:
% 0.62/0.82         ((k3_tarski @ (k2_tarski @ X57 @ X58)) = (k2_xboole_0 @ X57 @ X58))),
% 0.62/0.82      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.62/0.82  thf('42', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.62/0.82      inference('sup+', [status(thm)], ['40', '41'])).
% 0.62/0.82  thf('43', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.62/0.82      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.62/0.82  thf('44', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.62/0.82      inference('sup+', [status(thm)], ['40', '41'])).
% 0.62/0.82  thf('45', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.62/0.82      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.62/0.82  thf('46', plain,
% 0.62/0.82      (((k3_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A)) @ 
% 0.62/0.82         (k5_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A)))
% 0.62/0.82         = (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ 
% 0.62/0.82            (k2_xboole_0 @ 
% 0.62/0.82             (k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A)) @ 
% 0.62/0.82             (k5_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A)))))),
% 0.62/0.82      inference('demod', [status(thm)], ['37', '42', '43', '44', '45'])).
% 0.62/0.82  thf('47', plain,
% 0.62/0.82      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.62/0.82         ((k5_xboole_0 @ (k5_xboole_0 @ X8 @ X9) @ X10)
% 0.62/0.82           = (k5_xboole_0 @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 0.62/0.82      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.62/0.82  thf('48', plain,
% 0.62/0.82      (![X0 : $i]:
% 0.62/0.82         ((k5_xboole_0 @ 
% 0.62/0.82           (k3_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A)) @ 
% 0.62/0.82            (k5_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A))) @ 
% 0.62/0.82           X0)
% 0.62/0.82           = (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ 
% 0.62/0.82              (k5_xboole_0 @ 
% 0.62/0.82               (k2_xboole_0 @ 
% 0.62/0.82                (k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A)) @ 
% 0.62/0.82                (k5_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A))) @ 
% 0.62/0.82               X0)))),
% 0.62/0.82      inference('sup+', [status(thm)], ['46', '47'])).
% 0.62/0.82  thf('49', plain,
% 0.62/0.82      (![X0 : $i]:
% 0.62/0.82         ((k5_xboole_0 @ 
% 0.62/0.82           (k3_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A)) @ 
% 0.62/0.82            (k5_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A))) @ 
% 0.62/0.82           (k5_xboole_0 @ 
% 0.62/0.82            (k2_xboole_0 @ 
% 0.62/0.82             (k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A)) @ 
% 0.62/0.82             (k5_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A))) @ 
% 0.62/0.82            X0))
% 0.62/0.82           = (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ X0))),
% 0.62/0.82      inference('sup+', [status(thm)], ['30', '48'])).
% 0.62/0.82  thf('50', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.82         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.62/0.82           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.62/0.82      inference('sup+', [status(thm)], ['12', '13'])).
% 0.62/0.82  thf('51', plain,
% 0.62/0.82      (![X0 : $i]:
% 0.62/0.82         ((k5_xboole_0 @ 
% 0.62/0.82           (k2_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A)) @ 
% 0.62/0.82            (k5_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A))) @ 
% 0.62/0.82           (k5_xboole_0 @ X0 @ 
% 0.62/0.82            (k3_xboole_0 @ 
% 0.62/0.82             (k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A)) @ 
% 0.62/0.82             (k5_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A)))))
% 0.62/0.82           = (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ X0))),
% 0.62/0.82      inference('demod', [status(thm)], ['49', '50'])).
% 0.62/0.82  thf('52', plain,
% 0.62/0.82      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.62/0.82         ((k5_xboole_0 @ (k5_xboole_0 @ X8 @ X9) @ X10)
% 0.62/0.82           = (k5_xboole_0 @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 0.62/0.82      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.62/0.82  thf('53', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]:
% 0.62/0.82         ((k5_xboole_0 @ (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ X0) @ X1)
% 0.62/0.82           = (k5_xboole_0 @ 
% 0.62/0.82              (k2_xboole_0 @ 
% 0.62/0.82               (k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A)) @ 
% 0.62/0.82               (k5_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A))) @ 
% 0.62/0.82              (k5_xboole_0 @ 
% 0.62/0.82               (k5_xboole_0 @ X0 @ 
% 0.62/0.82                (k3_xboole_0 @ 
% 0.62/0.82                 (k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A)) @ 
% 0.62/0.82                 (k5_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A)))) @ 
% 0.62/0.82               X1)))),
% 0.62/0.82      inference('sup+', [status(thm)], ['51', '52'])).
% 0.62/0.82  thf('54', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.82         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 0.62/0.82           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 0.62/0.82      inference('sup+', [status(thm)], ['15', '16'])).
% 0.62/0.82  thf('55', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.82         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 0.62/0.82           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 0.62/0.82      inference('sup+', [status(thm)], ['15', '16'])).
% 0.62/0.82  thf('56', plain,
% 0.62/0.82      (((k3_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A)) @ 
% 0.62/0.82         (k5_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A)))
% 0.62/0.82         = (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ 
% 0.62/0.82            (k2_xboole_0 @ 
% 0.62/0.82             (k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A)) @ 
% 0.62/0.82             (k5_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A)))))),
% 0.62/0.82      inference('demod', [status(thm)], ['37', '42', '43', '44', '45'])).
% 0.62/0.82  thf('57', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.62/0.82      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.62/0.82  thf('58', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]:
% 0.62/0.82         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.62/0.82      inference('demod', [status(thm)], ['21', '29'])).
% 0.62/0.82  thf('59', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]:
% 0.62/0.82         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.62/0.82      inference('sup+', [status(thm)], ['57', '58'])).
% 0.62/0.82  thf('60', plain,
% 0.62/0.82      (((k2_tarski @ sk_B @ sk_A)
% 0.62/0.82         = (k5_xboole_0 @ 
% 0.62/0.82            (k2_xboole_0 @ 
% 0.62/0.82             (k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A)) @ 
% 0.62/0.82             (k5_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A))) @ 
% 0.62/0.82            (k3_xboole_0 @ 
% 0.62/0.82             (k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A)) @ 
% 0.62/0.82             (k5_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A)))))),
% 0.62/0.82      inference('sup+', [status(thm)], ['56', '59'])).
% 0.62/0.82  thf('61', plain,
% 0.62/0.82      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.62/0.82         ((k5_xboole_0 @ (k5_xboole_0 @ X8 @ X9) @ X10)
% 0.62/0.82           = (k5_xboole_0 @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 0.62/0.82      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.62/0.82  thf('62', plain,
% 0.62/0.82      (![X0 : $i]:
% 0.62/0.82         ((k5_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ X0)
% 0.62/0.82           = (k5_xboole_0 @ 
% 0.62/0.82              (k2_xboole_0 @ 
% 0.62/0.82               (k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A)) @ 
% 0.62/0.82               (k5_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A))) @ 
% 0.62/0.82              (k5_xboole_0 @ 
% 0.62/0.82               (k3_xboole_0 @ 
% 0.62/0.82                (k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A)) @ 
% 0.62/0.82                (k5_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A))) @ 
% 0.62/0.82               X0)))),
% 0.62/0.82      inference('sup+', [status(thm)], ['60', '61'])).
% 0.62/0.82  thf('63', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]:
% 0.62/0.82         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ X1))
% 0.62/0.82           = (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k5_xboole_0 @ X0 @ X1)))),
% 0.62/0.82      inference('demod', [status(thm)], ['53', '54', '55', '62'])).
% 0.62/0.82  thf('64', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]:
% 0.62/0.82         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.62/0.82      inference('demod', [status(thm)], ['21', '29'])).
% 0.62/0.82  thf('65', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]:
% 0.62/0.82         ((k5_xboole_0 @ X1 @ X0)
% 0.62/0.82           = (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ 
% 0.62/0.82              (k5_xboole_0 @ X1 @ 
% 0.62/0.82               (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ X0))))),
% 0.62/0.82      inference('sup+', [status(thm)], ['63', '64'])).
% 0.62/0.82  thf('66', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]:
% 0.62/0.82         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))
% 0.62/0.82           = (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ 
% 0.62/0.82              (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.62/0.82               (k2_tarski @ sk_B @ sk_A))))),
% 0.62/0.82      inference('sup+', [status(thm)], ['18', '65'])).
% 0.62/0.82  thf('67', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]:
% 0.62/0.82         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.62/0.82      inference('sup+', [status(thm)], ['57', '58'])).
% 0.62/0.82  thf('68', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]:
% 0.62/0.82         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))
% 0.62/0.82           = (k3_xboole_0 @ X1 @ X0))),
% 0.62/0.82      inference('demod', [status(thm)], ['66', '67'])).
% 0.62/0.82  thf('69', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]:
% 0.62/0.82         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.62/0.82      inference('demod', [status(thm)], ['21', '29'])).
% 0.62/0.82  thf('70', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]:
% 0.62/0.82         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.62/0.82           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.62/0.82      inference('sup+', [status(thm)], ['68', '69'])).
% 0.62/0.82  thf('71', plain,
% 0.62/0.82      (((k5_xboole_0 @ sk_C_1 @ 
% 0.62/0.82         (k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ sk_C_1))
% 0.62/0.82         = (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_B @ sk_A)))),
% 0.62/0.82      inference('sup+', [status(thm)], ['4', '70'])).
% 0.62/0.82  thf('72', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.62/0.82      inference('sup+', [status(thm)], ['40', '41'])).
% 0.62/0.82  thf('73', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ X11) = (k1_xboole_0))),
% 0.62/0.82      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.62/0.82  thf('74', plain,
% 0.62/0.82      (((k5_xboole_0 @ sk_C_1 @ 
% 0.62/0.82         (k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A))) = (k1_xboole_0))),
% 0.62/0.82      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.62/0.82  thf('75', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]:
% 0.62/0.82         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.62/0.82      inference('demod', [status(thm)], ['21', '29'])).
% 0.62/0.82  thf('76', plain,
% 0.62/0.82      (((k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A))
% 0.62/0.82         = (k5_xboole_0 @ sk_C_1 @ k1_xboole_0))),
% 0.62/0.82      inference('sup+', [status(thm)], ['74', '75'])).
% 0.62/0.82  thf('77', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.62/0.82      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.62/0.82  thf('78', plain,
% 0.62/0.82      (((k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A)) = (sk_C_1))),
% 0.62/0.82      inference('demod', [status(thm)], ['76', '77'])).
% 0.62/0.82  thf(t70_enumset1, axiom,
% 0.62/0.82    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.62/0.82  thf('79', plain,
% 0.62/0.82      (![X28 : $i, X29 : $i]:
% 0.62/0.82         ((k1_enumset1 @ X28 @ X28 @ X29) = (k2_tarski @ X28 @ X29))),
% 0.62/0.82      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.62/0.82  thf(d1_enumset1, axiom,
% 0.62/0.82    (![A:$i,B:$i,C:$i,D:$i]:
% 0.62/0.82     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.62/0.82       ( ![E:$i]:
% 0.62/0.82         ( ( r2_hidden @ E @ D ) <=>
% 0.62/0.82           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.62/0.82  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.62/0.82  thf(zf_stmt_2, axiom,
% 0.62/0.82    (![E:$i,C:$i,B:$i,A:$i]:
% 0.62/0.82     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.62/0.82       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.62/0.82  thf(zf_stmt_3, axiom,
% 0.62/0.82    (![A:$i,B:$i,C:$i,D:$i]:
% 0.62/0.82     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.62/0.82       ( ![E:$i]:
% 0.62/0.82         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.62/0.82  thf('80', plain,
% 0.62/0.82      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.62/0.82         ((zip_tseitin_0 @ X21 @ X22 @ X23 @ X24)
% 0.62/0.82          | (r2_hidden @ X21 @ X25)
% 0.62/0.82          | ((X25) != (k1_enumset1 @ X24 @ X23 @ X22)))),
% 0.62/0.82      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.62/0.82  thf('81', plain,
% 0.62/0.82      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.62/0.82         ((r2_hidden @ X21 @ (k1_enumset1 @ X24 @ X23 @ X22))
% 0.62/0.82          | (zip_tseitin_0 @ X21 @ X22 @ X23 @ X24))),
% 0.62/0.82      inference('simplify', [status(thm)], ['80'])).
% 0.62/0.82  thf('82', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.82         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.62/0.82          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.62/0.82      inference('sup+', [status(thm)], ['79', '81'])).
% 0.62/0.82  thf('83', plain,
% 0.62/0.82      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.62/0.82         (((X17) != (X18)) | ~ (zip_tseitin_0 @ X17 @ X18 @ X19 @ X16))),
% 0.62/0.82      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.62/0.82  thf('84', plain,
% 0.62/0.82      (![X16 : $i, X18 : $i, X19 : $i]:
% 0.62/0.82         ~ (zip_tseitin_0 @ X18 @ X18 @ X19 @ X16)),
% 0.62/0.82      inference('simplify', [status(thm)], ['83'])).
% 0.62/0.82  thf('85', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 0.62/0.82      inference('sup-', [status(thm)], ['82', '84'])).
% 0.62/0.82  thf('86', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.82         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.62/0.82          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.62/0.82      inference('sup+', [status(thm)], ['79', '81'])).
% 0.62/0.82  thf('87', plain,
% 0.62/0.82      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.62/0.82         (((X17) != (X16)) | ~ (zip_tseitin_0 @ X17 @ X18 @ X19 @ X16))),
% 0.62/0.82      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.62/0.82  thf('88', plain,
% 0.62/0.82      (![X16 : $i, X18 : $i, X19 : $i]:
% 0.62/0.82         ~ (zip_tseitin_0 @ X16 @ X18 @ X19 @ X16)),
% 0.62/0.82      inference('simplify', [status(thm)], ['87'])).
% 0.62/0.82  thf('89', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.62/0.82      inference('sup-', [status(thm)], ['86', '88'])).
% 0.62/0.82  thf(l49_zfmisc_1, axiom,
% 0.62/0.82    (![A:$i,B:$i]:
% 0.62/0.82     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.62/0.82  thf('90', plain,
% 0.62/0.82      (![X55 : $i, X56 : $i]:
% 0.62/0.82         ((r1_tarski @ X55 @ (k3_tarski @ X56)) | ~ (r2_hidden @ X55 @ X56))),
% 0.62/0.82      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.62/0.82  thf('91', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]:
% 0.62/0.82         (r1_tarski @ X1 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 0.62/0.82      inference('sup-', [status(thm)], ['89', '90'])).
% 0.62/0.82  thf('92', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]:
% 0.62/0.82         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.62/0.82      inference('sup+', [status(thm)], ['38', '39'])).
% 0.62/0.82  thf('93', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ X1))),
% 0.62/0.82      inference('demod', [status(thm)], ['91', '92'])).
% 0.62/0.82  thf(d3_tarski, axiom,
% 0.62/0.82    (![A:$i,B:$i]:
% 0.62/0.82     ( ( r1_tarski @ A @ B ) <=>
% 0.62/0.82       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.62/0.82  thf('94', plain,
% 0.62/0.82      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.62/0.82         (~ (r2_hidden @ X2 @ X3)
% 0.62/0.82          | (r2_hidden @ X2 @ X4)
% 0.62/0.82          | ~ (r1_tarski @ X3 @ X4))),
% 0.62/0.82      inference('cnf', [status(esa)], [d3_tarski])).
% 0.62/0.82  thf('95', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.82         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X0))),
% 0.62/0.82      inference('sup-', [status(thm)], ['93', '94'])).
% 0.62/0.82  thf('96', plain,
% 0.62/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.82         (r2_hidden @ X0 @ (k2_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)))),
% 0.62/0.82      inference('sup-', [status(thm)], ['85', '95'])).
% 0.62/0.82  thf('97', plain, ((r2_hidden @ sk_A @ sk_C_1)),
% 0.62/0.82      inference('sup+', [status(thm)], ['78', '96'])).
% 0.62/0.82  thf('98', plain, ($false), inference('demod', [status(thm)], ['0', '97'])).
% 0.62/0.82  
% 0.62/0.82  % SZS output end Refutation
% 0.62/0.82  
% 0.62/0.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

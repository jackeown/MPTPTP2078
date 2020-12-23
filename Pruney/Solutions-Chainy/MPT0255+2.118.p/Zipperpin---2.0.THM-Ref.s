%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VXLXff866e

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:10 EST 2020

% Result     : Theorem 1.92s
% Output     : Refutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :  162 (1642 expanded)
%              Number of leaves         :   36 ( 566 expanded)
%              Depth                    :   23
%              Number of atoms          : 1268 (14016 expanded)
%              Number of equality atoms :  154 (1670 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('0',plain,(
    ! [X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('3',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ X14 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('10',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('11',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('13',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('14',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ X14 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t50_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t50_zfmisc_1])).

thf('16',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('18',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k5_xboole_0 @ sk_C @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('20',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('22',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('23',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ X0 )
      = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k5_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k5_xboole_0 @ ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ sk_C )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('29',plain,
    ( ( k5_xboole_0 @ ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ sk_C )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ ( k5_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k5_xboole_0 @ k1_xboole_0 @ sk_C ) )
    = ( k5_xboole_0 @ ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('34',plain,
    ( ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k5_xboole_0 @ k1_xboole_0 @ sk_C ) )
    = ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ X14 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('36',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k5_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ k1_xboole_0 @ sk_C ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('40',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('41',plain,
    ( ( k5_xboole_0 @ k1_xboole_0 @ sk_C )
    = ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('46',plain,(
    ! [X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( sk_C
    = ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['41','47'])).

thf('49',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('50',plain,(
    ! [X70: $i,X71: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X70 ) @ ( k1_tarski @ X71 ) )
        = ( k1_tarski @ X70 ) )
      | ( X70 = X71 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('51',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
        = ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['50','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
        = ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['50','59'])).

thf('62',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('63',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ X14 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) )
      | ( X1 = X0 ) ) ),
    inference('sup+',[status(thm)],['61','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) )
      | ( X1 = X0 )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['60','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(condensation,[status(thm)],['73'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('75',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_enumset1 @ X36 @ X36 @ X37 )
      = ( k2_tarski @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('76',plain,(
    ! [X35: $i] :
      ( ( k2_tarski @ X35 @ X35 )
      = ( k1_tarski @ X35 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('78',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( k3_enumset1 @ X41 @ X41 @ X42 @ X43 @ X44 )
      = ( k2_enumset1 @ X41 @ X42 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t55_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ) )).

thf('79',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k4_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 ) @ ( k1_tarski @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t55_enumset1])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('81',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( k4_enumset1 @ X45 @ X45 @ X46 @ X47 @ X48 @ X49 )
      = ( k3_enumset1 @ X45 @ X46 @ X47 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('82',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( k3_enumset1 @ X41 @ X41 @ X42 @ X43 @ X44 )
      = ( k2_enumset1 @ X41 @ X42 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('84',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( k2_enumset1 @ X38 @ X38 @ X39 @ X40 )
      = ( k1_enumset1 @ X38 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_enumset1 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X2 @ X2 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['80','85'])).

thf('87',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( k2_enumset1 @ X38 @ X38 @ X39 @ X40 )
      = ( k1_enumset1 @ X38 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k1_enumset1 @ X0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['77','88'])).

thf('90',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_enumset1 @ X36 @ X36 @ X37 )
      = ( k2_tarski @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['74','91','92'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('94',plain,(
    ! [X67: $i,X68: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X67 @ X68 ) )
      = ( k2_xboole_0 @ X67 @ X68 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X67: $i,X68: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X67 @ X68 ) )
      = ( k2_xboole_0 @ X67 @ X68 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','97'])).

thf('99',plain,
    ( sk_C
    = ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['41','47'])).

thf('100',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('101',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_C )
    = ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('103',plain,
    ( sk_C
    = ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup+',[status(thm)],['98','103'])).

thf('105',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup+',[status(thm)],['98','103'])).

thf('106',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('107',plain,
    ( k1_xboole_0
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['48','104','105','106'])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('108',plain,(
    ! [X63: $i,X65: $i,X66: $i] :
      ( ( r1_tarski @ X65 @ ( k2_tarski @ X63 @ X66 ) )
      | ( X65
       != ( k1_tarski @ X63 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('109',plain,(
    ! [X63: $i,X66: $i] :
      ( r1_tarski @ ( k1_tarski @ X63 ) @ ( k2_tarski @ X63 @ X66 ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('110',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ sk_A ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['107','111'])).

thf('113',plain,(
    ! [X35: $i] :
      ( ( k2_tarski @ X35 @ X35 )
      = ( k1_tarski @ X35 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('114',plain,(
    ! [X63: $i,X65: $i,X66: $i] :
      ( ( r1_tarski @ X65 @ ( k2_tarski @ X63 @ X66 ) )
      | ( X65 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('115',plain,(
    ! [X63: $i,X66: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k2_tarski @ X63 @ X66 ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['113','115'])).

thf('117',plain,
    ( k1_xboole_0
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['48','104','105','106'])).

thf('118',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['112','116','117'])).

thf('119',plain,(
    ! [X69: $i,X70: $i] :
      ( ( X70 != X69 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X70 ) @ ( k1_tarski @ X69 ) )
       != ( k1_tarski @ X70 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('120',plain,(
    ! [X69: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X69 ) @ ( k1_tarski @ X69 ) )
     != ( k1_tarski @ X69 ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('122',plain,(
    ! [X69: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X69 ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['118','122'])).

thf('124',plain,(
    $false ),
    inference(simplify,[status(thm)],['123'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VXLXff866e
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:00:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.92/2.11  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.92/2.11  % Solved by: fo/fo7.sh
% 1.92/2.11  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.92/2.11  % done 1831 iterations in 1.660s
% 1.92/2.11  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.92/2.11  % SZS output start Refutation
% 1.92/2.11  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.92/2.11  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.92/2.11  thf(sk_C_type, type, sk_C: $i).
% 1.92/2.11  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.92/2.11  thf(sk_A_type, type, sk_A: $i).
% 1.92/2.11  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.92/2.11  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.92/2.11  thf(sk_B_type, type, sk_B: $i).
% 1.92/2.11  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.92/2.11  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 1.92/2.11  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 1.92/2.11  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.92/2.11  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 1.92/2.11  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.92/2.11  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.92/2.11  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.92/2.11  thf(idempotence_k3_xboole_0, axiom,
% 1.92/2.11    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.92/2.11  thf('0', plain, (![X1 : $i]: ((k3_xboole_0 @ X1 @ X1) = (X1))),
% 1.92/2.11      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.92/2.11  thf(t100_xboole_1, axiom,
% 1.92/2.11    (![A:$i,B:$i]:
% 1.92/2.11     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.92/2.11  thf('1', plain,
% 1.92/2.11      (![X5 : $i, X6 : $i]:
% 1.92/2.11         ((k4_xboole_0 @ X5 @ X6)
% 1.92/2.11           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.92/2.11      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.92/2.11  thf('2', plain,
% 1.92/2.11      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.92/2.11      inference('sup+', [status(thm)], ['0', '1'])).
% 1.92/2.11  thf(t92_xboole_1, axiom,
% 1.92/2.11    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.92/2.11  thf('3', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ X14) = (k1_xboole_0))),
% 1.92/2.11      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.92/2.11  thf('4', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.92/2.11      inference('sup+', [status(thm)], ['2', '3'])).
% 1.92/2.11  thf(t39_xboole_1, axiom,
% 1.92/2.11    (![A:$i,B:$i]:
% 1.92/2.11     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.92/2.11  thf('5', plain,
% 1.92/2.11      (![X8 : $i, X9 : $i]:
% 1.92/2.11         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 1.92/2.11           = (k2_xboole_0 @ X8 @ X9))),
% 1.92/2.11      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.92/2.11  thf('6', plain,
% 1.92/2.11      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 1.92/2.11      inference('sup+', [status(thm)], ['4', '5'])).
% 1.92/2.11  thf(idempotence_k2_xboole_0, axiom,
% 1.92/2.11    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 1.92/2.11  thf('7', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 1.92/2.11      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 1.92/2.11  thf('8', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.92/2.11      inference('demod', [status(thm)], ['6', '7'])).
% 1.92/2.11  thf(t95_xboole_1, axiom,
% 1.92/2.11    (![A:$i,B:$i]:
% 1.92/2.11     ( ( k3_xboole_0 @ A @ B ) =
% 1.92/2.11       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 1.92/2.11  thf('9', plain,
% 1.92/2.11      (![X15 : $i, X16 : $i]:
% 1.92/2.11         ((k3_xboole_0 @ X15 @ X16)
% 1.92/2.11           = (k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ 
% 1.92/2.11              (k2_xboole_0 @ X15 @ X16)))),
% 1.92/2.11      inference('cnf', [status(esa)], [t95_xboole_1])).
% 1.92/2.11  thf(t91_xboole_1, axiom,
% 1.92/2.11    (![A:$i,B:$i,C:$i]:
% 1.92/2.11     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.92/2.11       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.92/2.11  thf('10', plain,
% 1.92/2.11      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.92/2.11         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 1.92/2.11           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 1.92/2.11      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.92/2.11  thf('11', plain,
% 1.92/2.11      (![X15 : $i, X16 : $i]:
% 1.92/2.11         ((k3_xboole_0 @ X15 @ X16)
% 1.92/2.11           = (k5_xboole_0 @ X15 @ 
% 1.92/2.11              (k5_xboole_0 @ X16 @ (k2_xboole_0 @ X15 @ X16))))),
% 1.92/2.11      inference('demod', [status(thm)], ['9', '10'])).
% 1.92/2.11  thf('12', plain,
% 1.92/2.11      (![X0 : $i]:
% 1.92/2.11         ((k3_xboole_0 @ X0 @ k1_xboole_0)
% 1.92/2.11           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ X0)))),
% 1.92/2.11      inference('sup+', [status(thm)], ['8', '11'])).
% 1.92/2.11  thf(t2_boole, axiom,
% 1.92/2.11    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.92/2.11  thf('13', plain,
% 1.92/2.11      (![X7 : $i]: ((k3_xboole_0 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 1.92/2.11      inference('cnf', [status(esa)], [t2_boole])).
% 1.92/2.11  thf('14', plain,
% 1.92/2.11      (![X0 : $i]:
% 1.92/2.11         ((k1_xboole_0) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ X0)))),
% 1.92/2.11      inference('demod', [status(thm)], ['12', '13'])).
% 1.92/2.11  thf('15', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ X14) = (k1_xboole_0))),
% 1.92/2.11      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.92/2.11  thf(t50_zfmisc_1, conjecture,
% 1.92/2.11    (![A:$i,B:$i,C:$i]:
% 1.92/2.11     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 1.92/2.11  thf(zf_stmt_0, negated_conjecture,
% 1.92/2.11    (~( ![A:$i,B:$i,C:$i]:
% 1.92/2.11        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) )),
% 1.92/2.11    inference('cnf.neg', [status(esa)], [t50_zfmisc_1])).
% 1.92/2.11  thf('16', plain,
% 1.92/2.11      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))),
% 1.92/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.11  thf('17', plain,
% 1.92/2.11      (![X15 : $i, X16 : $i]:
% 1.92/2.11         ((k3_xboole_0 @ X15 @ X16)
% 1.92/2.11           = (k5_xboole_0 @ X15 @ 
% 1.92/2.11              (k5_xboole_0 @ X16 @ (k2_xboole_0 @ X15 @ X16))))),
% 1.92/2.11      inference('demod', [status(thm)], ['9', '10'])).
% 1.92/2.11  thf('18', plain,
% 1.92/2.11      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 1.92/2.11         = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 1.92/2.11            (k5_xboole_0 @ sk_C @ k1_xboole_0)))),
% 1.92/2.11      inference('sup+', [status(thm)], ['16', '17'])).
% 1.92/2.11  thf('19', plain,
% 1.92/2.11      (![X7 : $i]: ((k3_xboole_0 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 1.92/2.11      inference('cnf', [status(esa)], [t2_boole])).
% 1.92/2.11  thf('20', plain,
% 1.92/2.11      (![X5 : $i, X6 : $i]:
% 1.92/2.11         ((k4_xboole_0 @ X5 @ X6)
% 1.92/2.11           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.92/2.11      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.92/2.11  thf('21', plain,
% 1.92/2.11      (![X0 : $i]:
% 1.92/2.11         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.92/2.11      inference('sup+', [status(thm)], ['19', '20'])).
% 1.92/2.11  thf(t3_boole, axiom,
% 1.92/2.11    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.92/2.11  thf('22', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 1.92/2.11      inference('cnf', [status(esa)], [t3_boole])).
% 1.92/2.11  thf('23', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.92/2.11      inference('demod', [status(thm)], ['21', '22'])).
% 1.92/2.11  thf('24', plain,
% 1.92/2.11      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 1.92/2.11         = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 1.92/2.11      inference('demod', [status(thm)], ['18', '23'])).
% 1.92/2.11  thf('25', plain,
% 1.92/2.11      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.92/2.11         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 1.92/2.11           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 1.92/2.11      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.92/2.11  thf('26', plain,
% 1.92/2.11      (![X0 : $i]:
% 1.92/2.11         ((k5_xboole_0 @ (k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ X0)
% 1.92/2.11           = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 1.92/2.11              (k5_xboole_0 @ sk_C @ X0)))),
% 1.92/2.11      inference('sup+', [status(thm)], ['24', '25'])).
% 1.92/2.11  thf('27', plain,
% 1.92/2.11      (((k5_xboole_0 @ (k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ sk_C)
% 1.92/2.11         = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0))),
% 1.92/2.11      inference('sup+', [status(thm)], ['15', '26'])).
% 1.92/2.11  thf('28', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.92/2.11      inference('demod', [status(thm)], ['21', '22'])).
% 1.92/2.11  thf('29', plain,
% 1.92/2.11      (((k5_xboole_0 @ (k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ sk_C)
% 1.92/2.11         = (k2_tarski @ sk_A @ sk_B))),
% 1.92/2.11      inference('demod', [status(thm)], ['27', '28'])).
% 1.92/2.11  thf('30', plain,
% 1.92/2.11      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.92/2.11         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 1.92/2.11           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 1.92/2.11      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.92/2.11  thf('31', plain,
% 1.92/2.11      (![X0 : $i]:
% 1.92/2.11         ((k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0)
% 1.92/2.11           = (k5_xboole_0 @ (k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 1.92/2.11              (k5_xboole_0 @ sk_C @ X0)))),
% 1.92/2.11      inference('sup+', [status(thm)], ['29', '30'])).
% 1.92/2.11  thf('32', plain,
% 1.92/2.11      (((k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 1.92/2.11         (k5_xboole_0 @ k1_xboole_0 @ sk_C))
% 1.92/2.11         = (k5_xboole_0 @ (k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 1.92/2.11            k1_xboole_0))),
% 1.92/2.11      inference('sup+', [status(thm)], ['14', '31'])).
% 1.92/2.11  thf('33', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.92/2.11      inference('demod', [status(thm)], ['21', '22'])).
% 1.92/2.11  thf('34', plain,
% 1.92/2.11      (((k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 1.92/2.11         (k5_xboole_0 @ k1_xboole_0 @ sk_C))
% 1.92/2.11         = (k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 1.92/2.11      inference('demod', [status(thm)], ['32', '33'])).
% 1.92/2.11  thf('35', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ X14) = (k1_xboole_0))),
% 1.92/2.11      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.92/2.11  thf('36', plain,
% 1.92/2.11      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.92/2.11         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 1.92/2.11           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 1.92/2.11      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.92/2.11  thf('37', plain,
% 1.92/2.11      (![X0 : $i, X1 : $i]:
% 1.92/2.11         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.92/2.11           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.92/2.11      inference('sup+', [status(thm)], ['35', '36'])).
% 1.92/2.11  thf('38', plain,
% 1.92/2.11      (((k5_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ k1_xboole_0 @ sk_C))
% 1.92/2.11         = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 1.92/2.11            (k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 1.92/2.11      inference('sup+', [status(thm)], ['34', '37'])).
% 1.92/2.11  thf('39', plain,
% 1.92/2.11      (![X0 : $i, X1 : $i]:
% 1.92/2.11         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.92/2.11           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.92/2.11      inference('sup+', [status(thm)], ['35', '36'])).
% 1.92/2.11  thf('40', plain,
% 1.92/2.11      (![X5 : $i, X6 : $i]:
% 1.92/2.11         ((k4_xboole_0 @ X5 @ X6)
% 1.92/2.11           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.92/2.11      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.92/2.11  thf('41', plain,
% 1.92/2.11      (((k5_xboole_0 @ k1_xboole_0 @ sk_C)
% 1.92/2.11         = (k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 1.92/2.11      inference('demod', [status(thm)], ['38', '39', '40'])).
% 1.92/2.11  thf('42', plain,
% 1.92/2.11      (![X15 : $i, X16 : $i]:
% 1.92/2.11         ((k3_xboole_0 @ X15 @ X16)
% 1.92/2.11           = (k5_xboole_0 @ X15 @ 
% 1.92/2.11              (k5_xboole_0 @ X16 @ (k2_xboole_0 @ X15 @ X16))))),
% 1.92/2.11      inference('demod', [status(thm)], ['9', '10'])).
% 1.92/2.11  thf('43', plain,
% 1.92/2.11      (![X0 : $i, X1 : $i]:
% 1.92/2.11         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.92/2.11           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.92/2.11      inference('sup+', [status(thm)], ['35', '36'])).
% 1.92/2.11  thf('44', plain,
% 1.92/2.11      (![X0 : $i]:
% 1.92/2.11         ((k5_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X0))
% 1.92/2.11           = (k3_xboole_0 @ X0 @ X0))),
% 1.92/2.11      inference('sup+', [status(thm)], ['42', '43'])).
% 1.92/2.11  thf('45', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 1.92/2.11      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 1.92/2.11  thf('46', plain, (![X1 : $i]: ((k3_xboole_0 @ X1 @ X1) = (X1))),
% 1.92/2.11      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.92/2.11  thf('47', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.92/2.11      inference('demod', [status(thm)], ['44', '45', '46'])).
% 1.92/2.11  thf('48', plain,
% 1.92/2.11      (((sk_C) = (k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 1.92/2.11      inference('demod', [status(thm)], ['41', '47'])).
% 1.92/2.11  thf('49', plain,
% 1.92/2.11      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))),
% 1.92/2.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.11  thf(t20_zfmisc_1, axiom,
% 1.92/2.11    (![A:$i,B:$i]:
% 1.92/2.11     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 1.92/2.11         ( k1_tarski @ A ) ) <=>
% 1.92/2.11       ( ( A ) != ( B ) ) ))).
% 1.92/2.11  thf('50', plain,
% 1.92/2.11      (![X70 : $i, X71 : $i]:
% 1.92/2.11         (((k4_xboole_0 @ (k1_tarski @ X70) @ (k1_tarski @ X71))
% 1.92/2.11            = (k1_tarski @ X70))
% 1.92/2.11          | ((X70) = (X71)))),
% 1.92/2.11      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 1.92/2.11  thf('51', plain,
% 1.92/2.11      (![X15 : $i, X16 : $i]:
% 1.92/2.11         ((k3_xboole_0 @ X15 @ X16)
% 1.92/2.11           = (k5_xboole_0 @ X15 @ 
% 1.92/2.11              (k5_xboole_0 @ X16 @ (k2_xboole_0 @ X15 @ X16))))),
% 1.92/2.11      inference('demod', [status(thm)], ['9', '10'])).
% 1.92/2.11  thf('52', plain,
% 1.92/2.11      (![X0 : $i, X1 : $i]:
% 1.92/2.11         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.92/2.11           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.92/2.11      inference('sup+', [status(thm)], ['35', '36'])).
% 1.92/2.11  thf('53', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.92/2.11      inference('demod', [status(thm)], ['44', '45', '46'])).
% 1.92/2.11  thf('54', plain,
% 1.92/2.11      (![X0 : $i, X1 : $i]:
% 1.92/2.11         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.92/2.11      inference('demod', [status(thm)], ['52', '53'])).
% 1.92/2.11  thf('55', plain,
% 1.92/2.11      (![X0 : $i, X1 : $i]:
% 1.92/2.11         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.92/2.11           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.92/2.11      inference('sup+', [status(thm)], ['51', '54'])).
% 1.92/2.11  thf('56', plain,
% 1.92/2.11      (![X5 : $i, X6 : $i]:
% 1.92/2.11         ((k4_xboole_0 @ X5 @ X6)
% 1.92/2.11           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.92/2.11      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.92/2.11  thf('57', plain,
% 1.92/2.11      (![X0 : $i, X1 : $i]:
% 1.92/2.11         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.92/2.11           = (k4_xboole_0 @ X1 @ X0))),
% 1.92/2.11      inference('demod', [status(thm)], ['55', '56'])).
% 1.92/2.11  thf('58', plain,
% 1.92/2.11      (![X0 : $i, X1 : $i]:
% 1.92/2.11         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.92/2.11      inference('demod', [status(thm)], ['52', '53'])).
% 1.92/2.11  thf('59', plain,
% 1.92/2.11      (![X0 : $i, X1 : $i]:
% 1.92/2.11         ((k2_xboole_0 @ X1 @ X0)
% 1.92/2.11           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.92/2.11      inference('sup+', [status(thm)], ['57', '58'])).
% 1.92/2.11  thf('60', plain,
% 1.92/2.11      (![X0 : $i, X1 : $i]:
% 1.92/2.11         (((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 1.92/2.11            = (k5_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))
% 1.92/2.11          | ((X0) = (X1)))),
% 1.92/2.11      inference('sup+', [status(thm)], ['50', '59'])).
% 1.92/2.11  thf('61', plain,
% 1.92/2.11      (![X0 : $i, X1 : $i]:
% 1.92/2.11         (((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 1.92/2.11            = (k5_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))
% 1.92/2.11          | ((X0) = (X1)))),
% 1.92/2.11      inference('sup+', [status(thm)], ['50', '59'])).
% 1.92/2.11  thf('62', plain,
% 1.92/2.11      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.92/2.11         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 1.92/2.11           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 1.92/2.11      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.92/2.11  thf('63', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ X14) = (k1_xboole_0))),
% 1.92/2.11      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.92/2.11  thf('64', plain,
% 1.92/2.11      (![X0 : $i, X1 : $i]:
% 1.92/2.11         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 1.92/2.11           = (k1_xboole_0))),
% 1.92/2.11      inference('sup+', [status(thm)], ['62', '63'])).
% 1.92/2.11  thf('65', plain,
% 1.92/2.11      (![X0 : $i, X1 : $i]:
% 1.92/2.11         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.92/2.11      inference('demod', [status(thm)], ['52', '53'])).
% 1.92/2.11  thf('66', plain,
% 1.92/2.11      (![X0 : $i, X1 : $i]:
% 1.92/2.11         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 1.92/2.11           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 1.92/2.11      inference('sup+', [status(thm)], ['64', '65'])).
% 1.92/2.11  thf('67', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.92/2.11      inference('demod', [status(thm)], ['21', '22'])).
% 1.92/2.11  thf('68', plain,
% 1.92/2.11      (![X0 : $i, X1 : $i]:
% 1.92/2.11         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 1.92/2.11      inference('demod', [status(thm)], ['66', '67'])).
% 1.92/2.11  thf('69', plain,
% 1.92/2.11      (![X0 : $i, X1 : $i]:
% 1.92/2.11         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.92/2.11      inference('demod', [status(thm)], ['52', '53'])).
% 1.92/2.11  thf('70', plain,
% 1.92/2.11      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 1.92/2.11      inference('sup+', [status(thm)], ['68', '69'])).
% 1.92/2.11  thf('71', plain,
% 1.92/2.11      (![X0 : $i, X1 : $i]:
% 1.92/2.11         (((k5_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 1.92/2.11            = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))
% 1.92/2.11          | ((X1) = (X0)))),
% 1.92/2.11      inference('sup+', [status(thm)], ['61', '70'])).
% 1.92/2.11  thf('72', plain,
% 1.92/2.11      (![X0 : $i, X1 : $i]:
% 1.92/2.11         (((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 1.92/2.11            = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))
% 1.92/2.11          | ((X1) = (X0))
% 1.92/2.11          | ((X0) = (X1)))),
% 1.92/2.11      inference('sup+', [status(thm)], ['60', '71'])).
% 1.92/2.11  thf('73', plain,
% 1.92/2.11      (![X0 : $i, X1 : $i]:
% 1.92/2.11         (((X1) = (X0))
% 1.92/2.11          | ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 1.92/2.11              = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))))),
% 1.92/2.11      inference('simplify', [status(thm)], ['72'])).
% 1.92/2.11  thf('74', plain,
% 1.92/2.11      (![X0 : $i, X1 : $i]:
% 1.92/2.11         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 1.92/2.11           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 1.92/2.11      inference('condensation', [status(thm)], ['73'])).
% 1.92/2.11  thf(t70_enumset1, axiom,
% 1.92/2.11    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.92/2.11  thf('75', plain,
% 1.92/2.11      (![X36 : $i, X37 : $i]:
% 1.92/2.11         ((k1_enumset1 @ X36 @ X36 @ X37) = (k2_tarski @ X36 @ X37))),
% 1.92/2.11      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.92/2.11  thf(t69_enumset1, axiom,
% 1.92/2.11    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.92/2.11  thf('76', plain,
% 1.92/2.11      (![X35 : $i]: ((k2_tarski @ X35 @ X35) = (k1_tarski @ X35))),
% 1.92/2.11      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.92/2.11  thf('77', plain,
% 1.92/2.11      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 1.92/2.11      inference('sup+', [status(thm)], ['75', '76'])).
% 1.92/2.11  thf(t72_enumset1, axiom,
% 1.92/2.11    (![A:$i,B:$i,C:$i,D:$i]:
% 1.92/2.11     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 1.92/2.11  thf('78', plain,
% 1.92/2.11      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 1.92/2.11         ((k3_enumset1 @ X41 @ X41 @ X42 @ X43 @ X44)
% 1.92/2.11           = (k2_enumset1 @ X41 @ X42 @ X43 @ X44))),
% 1.92/2.11      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.92/2.11  thf(t55_enumset1, axiom,
% 1.92/2.11    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.92/2.11     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 1.92/2.11       ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ))).
% 1.92/2.11  thf('79', plain,
% 1.92/2.11      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.92/2.11         ((k4_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26)
% 1.92/2.11           = (k2_xboole_0 @ (k3_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25) @ 
% 1.92/2.11              (k1_tarski @ X26)))),
% 1.92/2.11      inference('cnf', [status(esa)], [t55_enumset1])).
% 1.92/2.11  thf('80', plain,
% 1.92/2.11      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.92/2.11         ((k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4)
% 1.92/2.11           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 1.92/2.11              (k1_tarski @ X4)))),
% 1.92/2.11      inference('sup+', [status(thm)], ['78', '79'])).
% 1.92/2.11  thf(t73_enumset1, axiom,
% 1.92/2.11    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.92/2.11     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 1.92/2.11       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 1.92/2.11  thf('81', plain,
% 1.92/2.11      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 1.92/2.11         ((k4_enumset1 @ X45 @ X45 @ X46 @ X47 @ X48 @ X49)
% 1.92/2.11           = (k3_enumset1 @ X45 @ X46 @ X47 @ X48 @ X49))),
% 1.92/2.11      inference('cnf', [status(esa)], [t73_enumset1])).
% 1.92/2.11  thf('82', plain,
% 1.92/2.11      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 1.92/2.11         ((k3_enumset1 @ X41 @ X41 @ X42 @ X43 @ X44)
% 1.92/2.11           = (k2_enumset1 @ X41 @ X42 @ X43 @ X44))),
% 1.92/2.11      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.92/2.11  thf('83', plain,
% 1.92/2.11      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.92/2.11         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 1.92/2.11           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 1.92/2.11      inference('sup+', [status(thm)], ['81', '82'])).
% 1.92/2.11  thf(t71_enumset1, axiom,
% 1.92/2.11    (![A:$i,B:$i,C:$i]:
% 1.92/2.11     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 1.92/2.11  thf('84', plain,
% 1.92/2.11      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.92/2.11         ((k2_enumset1 @ X38 @ X38 @ X39 @ X40)
% 1.92/2.11           = (k1_enumset1 @ X38 @ X39 @ X40))),
% 1.92/2.11      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.92/2.11  thf('85', plain,
% 1.92/2.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.92/2.11         ((k4_enumset1 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0)
% 1.92/2.11           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 1.92/2.11      inference('sup+', [status(thm)], ['83', '84'])).
% 1.92/2.11  thf('86', plain,
% 1.92/2.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.92/2.11         ((k2_xboole_0 @ (k2_enumset1 @ X2 @ X2 @ X2 @ X1) @ (k1_tarski @ X0))
% 1.92/2.11           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 1.92/2.11      inference('sup+', [status(thm)], ['80', '85'])).
% 1.92/2.11  thf('87', plain,
% 1.92/2.11      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.92/2.11         ((k2_enumset1 @ X38 @ X38 @ X39 @ X40)
% 1.92/2.11           = (k1_enumset1 @ X38 @ X39 @ X40))),
% 1.92/2.11      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.92/2.11  thf('88', plain,
% 1.92/2.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.92/2.11         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X2 @ X1) @ (k1_tarski @ X0))
% 1.92/2.11           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 1.92/2.11      inference('demod', [status(thm)], ['86', '87'])).
% 1.92/2.11  thf('89', plain,
% 1.92/2.11      (![X0 : $i, X1 : $i]:
% 1.92/2.11         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 1.92/2.11           = (k1_enumset1 @ X0 @ X0 @ X1))),
% 1.92/2.11      inference('sup+', [status(thm)], ['77', '88'])).
% 1.92/2.11  thf('90', plain,
% 1.92/2.11      (![X36 : $i, X37 : $i]:
% 1.92/2.11         ((k1_enumset1 @ X36 @ X36 @ X37) = (k2_tarski @ X36 @ X37))),
% 1.92/2.11      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.92/2.11  thf('91', plain,
% 1.92/2.11      (![X0 : $i, X1 : $i]:
% 1.92/2.11         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 1.92/2.11           = (k2_tarski @ X1 @ X0))),
% 1.92/2.11      inference('sup+', [status(thm)], ['89', '90'])).
% 1.92/2.11  thf('92', plain,
% 1.92/2.11      (![X0 : $i, X1 : $i]:
% 1.92/2.11         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 1.92/2.11           = (k2_tarski @ X1 @ X0))),
% 1.92/2.11      inference('sup+', [status(thm)], ['89', '90'])).
% 1.92/2.11  thf('93', plain,
% 1.92/2.11      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 1.92/2.11      inference('demod', [status(thm)], ['74', '91', '92'])).
% 1.92/2.11  thf(l51_zfmisc_1, axiom,
% 1.92/2.11    (![A:$i,B:$i]:
% 1.92/2.11     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.92/2.11  thf('94', plain,
% 1.92/2.11      (![X67 : $i, X68 : $i]:
% 1.92/2.11         ((k3_tarski @ (k2_tarski @ X67 @ X68)) = (k2_xboole_0 @ X67 @ X68))),
% 1.92/2.11      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.92/2.11  thf('95', plain,
% 1.92/2.11      (![X0 : $i, X1 : $i]:
% 1.92/2.11         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 1.92/2.11      inference('sup+', [status(thm)], ['93', '94'])).
% 1.92/2.11  thf('96', plain,
% 1.92/2.11      (![X67 : $i, X68 : $i]:
% 1.92/2.11         ((k3_tarski @ (k2_tarski @ X67 @ X68)) = (k2_xboole_0 @ X67 @ X68))),
% 1.92/2.11      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.92/2.11  thf('97', plain,
% 1.92/2.11      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.92/2.11      inference('sup+', [status(thm)], ['95', '96'])).
% 1.92/2.11  thf('98', plain,
% 1.92/2.11      (((k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) = (k1_xboole_0))),
% 1.92/2.11      inference('demod', [status(thm)], ['49', '97'])).
% 1.92/2.11  thf('99', plain,
% 1.92/2.11      (((sk_C) = (k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 1.92/2.11      inference('demod', [status(thm)], ['41', '47'])).
% 1.92/2.11  thf('100', plain,
% 1.92/2.11      (![X8 : $i, X9 : $i]:
% 1.92/2.11         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 1.92/2.11           = (k2_xboole_0 @ X8 @ X9))),
% 1.92/2.11      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.92/2.11  thf('101', plain,
% 1.92/2.11      (((k2_xboole_0 @ sk_C @ sk_C)
% 1.92/2.11         = (k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 1.92/2.11      inference('sup+', [status(thm)], ['99', '100'])).
% 1.92/2.11  thf('102', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 1.92/2.11      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 1.92/2.11  thf('103', plain,
% 1.92/2.11      (((sk_C) = (k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 1.92/2.11      inference('demod', [status(thm)], ['101', '102'])).
% 1.92/2.11  thf('104', plain, (((sk_C) = (k1_xboole_0))),
% 1.92/2.11      inference('sup+', [status(thm)], ['98', '103'])).
% 1.92/2.11  thf('105', plain, (((sk_C) = (k1_xboole_0))),
% 1.92/2.11      inference('sup+', [status(thm)], ['98', '103'])).
% 1.92/2.11  thf('106', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 1.92/2.11      inference('cnf', [status(esa)], [t3_boole])).
% 1.92/2.11  thf('107', plain, (((k1_xboole_0) = (k2_tarski @ sk_A @ sk_B))),
% 1.92/2.11      inference('demod', [status(thm)], ['48', '104', '105', '106'])).
% 1.92/2.11  thf(l45_zfmisc_1, axiom,
% 1.92/2.11    (![A:$i,B:$i,C:$i]:
% 1.92/2.11     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 1.92/2.11       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 1.92/2.11            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 1.92/2.11  thf('108', plain,
% 1.92/2.11      (![X63 : $i, X65 : $i, X66 : $i]:
% 1.92/2.11         ((r1_tarski @ X65 @ (k2_tarski @ X63 @ X66))
% 1.92/2.11          | ((X65) != (k1_tarski @ X63)))),
% 1.92/2.11      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 1.92/2.11  thf('109', plain,
% 1.92/2.11      (![X63 : $i, X66 : $i]:
% 1.92/2.11         (r1_tarski @ (k1_tarski @ X63) @ (k2_tarski @ X63 @ X66))),
% 1.92/2.11      inference('simplify', [status(thm)], ['108'])).
% 1.92/2.11  thf(d10_xboole_0, axiom,
% 1.92/2.11    (![A:$i,B:$i]:
% 1.92/2.11     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.92/2.11  thf('110', plain,
% 1.92/2.11      (![X2 : $i, X4 : $i]:
% 1.92/2.11         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 1.92/2.11      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.92/2.11  thf('111', plain,
% 1.92/2.11      (![X0 : $i, X1 : $i]:
% 1.92/2.11         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 1.92/2.11          | ((k2_tarski @ X1 @ X0) = (k1_tarski @ X1)))),
% 1.92/2.11      inference('sup-', [status(thm)], ['109', '110'])).
% 1.92/2.11  thf('112', plain,
% 1.92/2.11      ((~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ sk_A))
% 1.92/2.11        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_A)))),
% 1.92/2.11      inference('sup-', [status(thm)], ['107', '111'])).
% 1.92/2.11  thf('113', plain,
% 1.92/2.11      (![X35 : $i]: ((k2_tarski @ X35 @ X35) = (k1_tarski @ X35))),
% 1.92/2.11      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.92/2.11  thf('114', plain,
% 1.92/2.11      (![X63 : $i, X65 : $i, X66 : $i]:
% 1.92/2.11         ((r1_tarski @ X65 @ (k2_tarski @ X63 @ X66))
% 1.92/2.11          | ((X65) != (k1_xboole_0)))),
% 1.92/2.11      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 1.92/2.11  thf('115', plain,
% 1.92/2.11      (![X63 : $i, X66 : $i]:
% 1.92/2.11         (r1_tarski @ k1_xboole_0 @ (k2_tarski @ X63 @ X66))),
% 1.92/2.11      inference('simplify', [status(thm)], ['114'])).
% 1.92/2.11  thf('116', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0))),
% 1.92/2.11      inference('sup+', [status(thm)], ['113', '115'])).
% 1.92/2.11  thf('117', plain, (((k1_xboole_0) = (k2_tarski @ sk_A @ sk_B))),
% 1.92/2.11      inference('demod', [status(thm)], ['48', '104', '105', '106'])).
% 1.92/2.11  thf('118', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 1.92/2.11      inference('demod', [status(thm)], ['112', '116', '117'])).
% 1.92/2.11  thf('119', plain,
% 1.92/2.11      (![X69 : $i, X70 : $i]:
% 1.92/2.11         (((X70) != (X69))
% 1.92/2.11          | ((k4_xboole_0 @ (k1_tarski @ X70) @ (k1_tarski @ X69))
% 1.92/2.11              != (k1_tarski @ X70)))),
% 1.92/2.11      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 1.92/2.11  thf('120', plain,
% 1.92/2.11      (![X69 : $i]:
% 1.92/2.11         ((k4_xboole_0 @ (k1_tarski @ X69) @ (k1_tarski @ X69))
% 1.92/2.11           != (k1_tarski @ X69))),
% 1.92/2.11      inference('simplify', [status(thm)], ['119'])).
% 1.92/2.11  thf('121', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.92/2.11      inference('sup+', [status(thm)], ['2', '3'])).
% 1.92/2.11  thf('122', plain, (![X69 : $i]: ((k1_xboole_0) != (k1_tarski @ X69))),
% 1.92/2.11      inference('demod', [status(thm)], ['120', '121'])).
% 1.92/2.11  thf('123', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 1.92/2.11      inference('sup-', [status(thm)], ['118', '122'])).
% 1.92/2.11  thf('124', plain, ($false), inference('simplify', [status(thm)], ['123'])).
% 1.92/2.11  
% 1.92/2.11  % SZS output end Refutation
% 1.92/2.11  
% 1.92/2.12  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

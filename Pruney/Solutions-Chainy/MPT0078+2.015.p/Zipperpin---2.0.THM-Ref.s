%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.i3gM5vsacR

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:54 EST 2020

% Result     : Theorem 2.01s
% Output     : Refutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 344 expanded)
%              Number of leaves         :   18 ( 121 expanded)
%              Depth                    :   15
%              Number of atoms          :  883 (2696 expanded)
%              Number of equality atoms :  111 ( 352 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t71_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( ( k2_xboole_0 @ A @ B )
          = ( k2_xboole_0 @ C @ B ) )
        & ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ C @ B ) )
     => ( A = C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( ( k2_xboole_0 @ A @ B )
            = ( k2_xboole_0 @ C @ B ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ C @ B ) )
       => ( A = C ) ) ),
    inference('cnf.neg',[status(esa)],[t71_xboole_1])).

thf('0',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('2',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('4',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_A ),
    inference('sup+',[status(thm)],['2','3'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('6',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['4','7'])).

thf('9',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_C )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_C )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['8','15'])).

thf('17',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['4','7'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('18',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('21',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['16','17','22'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('25',plain,
    ( ( k2_xboole_0 @ sk_C @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('28',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['4','7'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('30',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ sk_B )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ sk_B )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ sk_B )
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('37',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ k1_xboole_0 @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_C @ sk_A ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('41',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf('42',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ ( k4_xboole_0 @ sk_C @ sk_A ) )
      = ( k4_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_C @ sk_A ) )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['28','43'])).

thf('45',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['4','7'])).

thf('46',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_C @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('49',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['47','54'])).

thf('56',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_C @ sk_A ) )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_A ) @ sk_A ) @ ( k4_xboole_0 @ sk_C @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['46','55'])).

thf('57',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_C @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['44','45'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('59',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('60',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C ) @ ( k4_xboole_0 @ sk_C @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['56','57','58','59'])).

thf('61',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('62',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_C )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('69',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    r1_xboole_0 @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('72',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('74',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_B ) )
    = sk_C ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('76',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_B )
    = sk_C ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['69','76'])).

thf('78',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('80',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('81',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ k1_xboole_0 @ X1 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['79','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('85',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('88',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['83','92','93','94','95'])).

thf('97',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['60','77','78','96'])).

thf('98',plain,(
    sk_C = sk_A ),
    inference(demod,[status(thm)],['25','26','27','97'])).

thf('99',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['98','99'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.i3gM5vsacR
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:28:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 2.01/2.23  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.01/2.23  % Solved by: fo/fo7.sh
% 2.01/2.23  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.01/2.23  % done 1948 iterations in 1.763s
% 2.01/2.23  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.01/2.23  % SZS output start Refutation
% 2.01/2.23  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.01/2.23  thf(sk_B_type, type, sk_B: $i).
% 2.01/2.23  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.01/2.23  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.01/2.23  thf(sk_C_type, type, sk_C: $i).
% 2.01/2.23  thf(sk_A_type, type, sk_A: $i).
% 2.01/2.23  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.01/2.23  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.01/2.23  thf(t71_xboole_1, conjecture,
% 2.01/2.23    (![A:$i,B:$i,C:$i]:
% 2.01/2.23     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ B ) ) & 
% 2.01/2.23         ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ C @ B ) ) =>
% 2.01/2.23       ( ( A ) = ( C ) ) ))).
% 2.01/2.23  thf(zf_stmt_0, negated_conjecture,
% 2.01/2.23    (~( ![A:$i,B:$i,C:$i]:
% 2.01/2.23        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ B ) ) & 
% 2.01/2.23            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ C @ B ) ) =>
% 2.01/2.23          ( ( A ) = ( C ) ) ) )),
% 2.01/2.23    inference('cnf.neg', [status(esa)], [t71_xboole_1])).
% 2.01/2.23  thf('0', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 2.01/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.01/2.23  thf(d7_xboole_0, axiom,
% 2.01/2.23    (![A:$i,B:$i]:
% 2.01/2.23     ( ( r1_xboole_0 @ A @ B ) <=>
% 2.01/2.23       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 2.01/2.23  thf('1', plain,
% 2.01/2.23      (![X2 : $i, X3 : $i]:
% 2.01/2.23         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 2.01/2.23      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.01/2.23  thf('2', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 2.01/2.23      inference('sup-', [status(thm)], ['0', '1'])).
% 2.01/2.23  thf(t51_xboole_1, axiom,
% 2.01/2.23    (![A:$i,B:$i]:
% 2.01/2.23     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 2.01/2.23       ( A ) ))).
% 2.01/2.23  thf('3', plain,
% 2.01/2.23      (![X15 : $i, X16 : $i]:
% 2.01/2.23         ((k2_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ (k4_xboole_0 @ X15 @ X16))
% 2.01/2.23           = (X15))),
% 2.01/2.23      inference('cnf', [status(esa)], [t51_xboole_1])).
% 2.01/2.23  thf('4', plain,
% 2.01/2.23      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_A))),
% 2.01/2.23      inference('sup+', [status(thm)], ['2', '3'])).
% 2.01/2.23  thf(commutativity_k2_xboole_0, axiom,
% 2.01/2.23    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 2.01/2.23  thf('5', plain,
% 2.01/2.23      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.01/2.23      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.01/2.23  thf(t1_boole, axiom,
% 2.01/2.23    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.01/2.23  thf('6', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 2.01/2.23      inference('cnf', [status(esa)], [t1_boole])).
% 2.01/2.23  thf('7', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.01/2.23      inference('sup+', [status(thm)], ['5', '6'])).
% 2.01/2.23  thf('8', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 2.01/2.23      inference('demod', [status(thm)], ['4', '7'])).
% 2.01/2.23  thf('9', plain,
% 2.01/2.23      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ sk_B))),
% 2.01/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.01/2.23  thf('10', plain,
% 2.01/2.23      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.01/2.23      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.01/2.23  thf(t41_xboole_1, axiom,
% 2.01/2.23    (![A:$i,B:$i,C:$i]:
% 2.01/2.23     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 2.01/2.23       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 2.01/2.23  thf('11', plain,
% 2.01/2.23      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.01/2.23         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 2.01/2.23           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 2.01/2.23      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.01/2.23  thf('12', plain,
% 2.01/2.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.01/2.23         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 2.01/2.23           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.01/2.23      inference('sup+', [status(thm)], ['10', '11'])).
% 2.01/2.23  thf('13', plain,
% 2.01/2.23      (![X0 : $i]:
% 2.01/2.23         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_C)
% 2.01/2.23           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ sk_A @ sk_B)))),
% 2.01/2.23      inference('sup+', [status(thm)], ['9', '12'])).
% 2.01/2.23  thf('14', plain,
% 2.01/2.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.01/2.23         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 2.01/2.23           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.01/2.23      inference('sup+', [status(thm)], ['10', '11'])).
% 2.01/2.23  thf('15', plain,
% 2.01/2.23      (![X0 : $i]:
% 2.01/2.23         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_C)
% 2.01/2.23           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A))),
% 2.01/2.23      inference('demod', [status(thm)], ['13', '14'])).
% 2.01/2.23  thf('16', plain,
% 2.01/2.23      (((k4_xboole_0 @ sk_A @ sk_C)
% 2.01/2.23         = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_A))),
% 2.01/2.23      inference('sup+', [status(thm)], ['8', '15'])).
% 2.01/2.23  thf('17', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 2.01/2.23      inference('demod', [status(thm)], ['4', '7'])).
% 2.01/2.23  thf(t3_boole, axiom,
% 2.01/2.23    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.01/2.23  thf('18', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 2.01/2.23      inference('cnf', [status(esa)], [t3_boole])).
% 2.01/2.23  thf(t48_xboole_1, axiom,
% 2.01/2.23    (![A:$i,B:$i]:
% 2.01/2.23     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.01/2.23  thf('19', plain,
% 2.01/2.23      (![X13 : $i, X14 : $i]:
% 2.01/2.23         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 2.01/2.23           = (k3_xboole_0 @ X13 @ X14))),
% 2.01/2.23      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.01/2.23  thf('20', plain,
% 2.01/2.23      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 2.01/2.23      inference('sup+', [status(thm)], ['18', '19'])).
% 2.01/2.23  thf(t2_boole, axiom,
% 2.01/2.23    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 2.01/2.23  thf('21', plain,
% 2.01/2.23      (![X6 : $i]: ((k3_xboole_0 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 2.01/2.23      inference('cnf', [status(esa)], [t2_boole])).
% 2.01/2.23  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.01/2.23      inference('demod', [status(thm)], ['20', '21'])).
% 2.01/2.23  thf('23', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 2.01/2.23      inference('demod', [status(thm)], ['16', '17', '22'])).
% 2.01/2.23  thf(t39_xboole_1, axiom,
% 2.01/2.23    (![A:$i,B:$i]:
% 2.01/2.23     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 2.01/2.23  thf('24', plain,
% 2.01/2.23      (![X7 : $i, X8 : $i]:
% 2.01/2.23         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 2.01/2.23           = (k2_xboole_0 @ X7 @ X8))),
% 2.01/2.23      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.01/2.23  thf('25', plain,
% 2.01/2.23      (((k2_xboole_0 @ sk_C @ k1_xboole_0) = (k2_xboole_0 @ sk_C @ sk_A))),
% 2.01/2.23      inference('sup+', [status(thm)], ['23', '24'])).
% 2.01/2.23  thf('26', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 2.01/2.23      inference('cnf', [status(esa)], [t1_boole])).
% 2.01/2.23  thf('27', plain,
% 2.01/2.23      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.01/2.23      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.01/2.23  thf('28', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 2.01/2.23      inference('demod', [status(thm)], ['4', '7'])).
% 2.01/2.23  thf('29', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.01/2.23      inference('demod', [status(thm)], ['20', '21'])).
% 2.01/2.23  thf('30', plain,
% 2.01/2.23      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ sk_B))),
% 2.01/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.01/2.23  thf('31', plain,
% 2.01/2.23      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.01/2.23         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 2.01/2.23           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 2.01/2.23      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.01/2.23  thf('32', plain,
% 2.01/2.23      (![X0 : $i]:
% 2.01/2.23         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ sk_B)
% 2.01/2.23           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ sk_A @ sk_B)))),
% 2.01/2.23      inference('sup+', [status(thm)], ['30', '31'])).
% 2.01/2.23  thf('33', plain,
% 2.01/2.23      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.01/2.23         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 2.01/2.23           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 2.01/2.23      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.01/2.23  thf('34', plain,
% 2.01/2.23      (![X0 : $i]:
% 2.01/2.23         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ sk_B)
% 2.01/2.23           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_A) @ sk_B))),
% 2.01/2.23      inference('demod', [status(thm)], ['32', '33'])).
% 2.01/2.23  thf('35', plain,
% 2.01/2.23      (((k4_xboole_0 @ k1_xboole_0 @ sk_B)
% 2.01/2.23         = (k4_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_A) @ sk_B))),
% 2.01/2.23      inference('sup+', [status(thm)], ['29', '34'])).
% 2.01/2.23  thf('36', plain,
% 2.01/2.23      (![X7 : $i, X8 : $i]:
% 2.01/2.23         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 2.01/2.23           = (k2_xboole_0 @ X7 @ X8))),
% 2.01/2.23      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.01/2.23  thf('37', plain,
% 2.01/2.23      (((k2_xboole_0 @ sk_B @ (k4_xboole_0 @ k1_xboole_0 @ sk_B))
% 2.01/2.23         = (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_C @ sk_A)))),
% 2.01/2.23      inference('sup+', [status(thm)], ['35', '36'])).
% 2.01/2.23  thf('38', plain,
% 2.01/2.23      (![X7 : $i, X8 : $i]:
% 2.01/2.23         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 2.01/2.23           = (k2_xboole_0 @ X7 @ X8))),
% 2.01/2.23      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.01/2.23  thf('39', plain,
% 2.01/2.23      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.01/2.23      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.01/2.23  thf('40', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.01/2.23      inference('sup+', [status(thm)], ['5', '6'])).
% 2.01/2.23  thf('41', plain,
% 2.01/2.23      (((sk_B) = (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_C @ sk_A)))),
% 2.01/2.23      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 2.01/2.23  thf('42', plain,
% 2.01/2.23      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.01/2.23         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 2.01/2.23           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 2.01/2.23      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.01/2.23  thf('43', plain,
% 2.01/2.23      (![X0 : $i]:
% 2.01/2.23         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ 
% 2.01/2.23           (k4_xboole_0 @ sk_C @ sk_A)) = (k4_xboole_0 @ X0 @ sk_B))),
% 2.01/2.23      inference('sup+', [status(thm)], ['41', '42'])).
% 2.01/2.23  thf('44', plain,
% 2.01/2.23      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_C @ sk_A))
% 2.01/2.23         = (k4_xboole_0 @ sk_A @ sk_B))),
% 2.01/2.23      inference('sup+', [status(thm)], ['28', '43'])).
% 2.01/2.23  thf('45', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 2.01/2.23      inference('demod', [status(thm)], ['4', '7'])).
% 2.01/2.23  thf('46', plain,
% 2.01/2.23      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_C @ sk_A)) = (sk_A))),
% 2.01/2.23      inference('demod', [status(thm)], ['44', '45'])).
% 2.01/2.23  thf('47', plain,
% 2.01/2.23      (![X7 : $i, X8 : $i]:
% 2.01/2.23         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 2.01/2.23           = (k2_xboole_0 @ X7 @ X8))),
% 2.01/2.23      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.01/2.23  thf('48', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.01/2.23      inference('demod', [status(thm)], ['20', '21'])).
% 2.01/2.23  thf('49', plain,
% 2.01/2.23      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.01/2.23         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 2.01/2.23           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 2.01/2.23      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.01/2.23  thf('50', plain,
% 2.01/2.23      (![X0 : $i, X1 : $i]:
% 2.01/2.23         ((k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 2.01/2.23           = (k1_xboole_0))),
% 2.01/2.23      inference('sup+', [status(thm)], ['48', '49'])).
% 2.01/2.23  thf('51', plain,
% 2.01/2.23      (![X7 : $i, X8 : $i]:
% 2.01/2.23         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 2.01/2.23           = (k2_xboole_0 @ X7 @ X8))),
% 2.01/2.23      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.01/2.23  thf('52', plain,
% 2.01/2.23      (![X0 : $i, X1 : $i]:
% 2.01/2.23         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 2.01/2.23           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)))),
% 2.01/2.23      inference('sup+', [status(thm)], ['50', '51'])).
% 2.01/2.23  thf('53', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 2.01/2.23      inference('cnf', [status(esa)], [t1_boole])).
% 2.01/2.23  thf('54', plain,
% 2.01/2.23      (![X0 : $i, X1 : $i]:
% 2.01/2.23         ((X1)
% 2.01/2.23           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)))),
% 2.01/2.23      inference('demod', [status(thm)], ['52', '53'])).
% 2.01/2.23  thf('55', plain,
% 2.01/2.23      (![X0 : $i, X1 : $i]:
% 2.01/2.23         ((k4_xboole_0 @ X0 @ X1)
% 2.01/2.23           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 2.01/2.23              (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)))),
% 2.01/2.23      inference('sup+', [status(thm)], ['47', '54'])).
% 2.01/2.23  thf('56', plain,
% 2.01/2.23      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_C @ sk_A))
% 2.01/2.23         = (k2_xboole_0 @ sk_A @ 
% 2.01/2.23            (k4_xboole_0 @ 
% 2.01/2.23             (k2_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_A) @ sk_A) @ 
% 2.01/2.23             (k4_xboole_0 @ sk_C @ sk_A))))),
% 2.01/2.23      inference('sup+', [status(thm)], ['46', '55'])).
% 2.01/2.23  thf('57', plain,
% 2.01/2.23      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_C @ sk_A)) = (sk_A))),
% 2.01/2.23      inference('demod', [status(thm)], ['44', '45'])).
% 2.01/2.23  thf('58', plain,
% 2.01/2.23      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.01/2.23      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.01/2.23  thf('59', plain,
% 2.01/2.23      (![X7 : $i, X8 : $i]:
% 2.01/2.23         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 2.01/2.23           = (k2_xboole_0 @ X7 @ X8))),
% 2.01/2.23      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.01/2.23  thf('60', plain,
% 2.01/2.23      (((sk_A)
% 2.01/2.23         = (k2_xboole_0 @ sk_A @ 
% 2.01/2.23            (k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C) @ 
% 2.01/2.23             (k4_xboole_0 @ sk_C @ sk_A))))),
% 2.01/2.23      inference('demod', [status(thm)], ['56', '57', '58', '59'])).
% 2.01/2.23  thf('61', plain,
% 2.01/2.23      (![X7 : $i, X8 : $i]:
% 2.01/2.23         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 2.01/2.23           = (k2_xboole_0 @ X7 @ X8))),
% 2.01/2.23      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.01/2.23  thf('62', plain,
% 2.01/2.23      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.01/2.23         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 2.01/2.23           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 2.01/2.23      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.01/2.23  thf('63', plain,
% 2.01/2.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.01/2.23         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k4_xboole_0 @ X0 @ X1))
% 2.01/2.23           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.01/2.23      inference('sup+', [status(thm)], ['61', '62'])).
% 2.01/2.23  thf('64', plain,
% 2.01/2.23      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.01/2.23         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 2.01/2.23           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 2.01/2.23      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.01/2.23  thf('65', plain,
% 2.01/2.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.01/2.23         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k4_xboole_0 @ X0 @ X1))
% 2.01/2.23           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 2.01/2.23      inference('demod', [status(thm)], ['63', '64'])).
% 2.01/2.23  thf('66', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.01/2.23      inference('demod', [status(thm)], ['20', '21'])).
% 2.01/2.23  thf('67', plain,
% 2.01/2.23      (![X0 : $i, X1 : $i]:
% 2.01/2.23         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 2.01/2.23      inference('sup+', [status(thm)], ['65', '66'])).
% 2.01/2.23  thf('68', plain,
% 2.01/2.23      (![X0 : $i]:
% 2.01/2.23         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_C)
% 2.01/2.23           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A))),
% 2.01/2.23      inference('demod', [status(thm)], ['13', '14'])).
% 2.01/2.23  thf('69', plain,
% 2.01/2.23      (((k1_xboole_0) = (k4_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_B) @ sk_A))),
% 2.01/2.23      inference('sup+', [status(thm)], ['67', '68'])).
% 2.01/2.23  thf('70', plain, ((r1_xboole_0 @ sk_C @ sk_B)),
% 2.01/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.01/2.23  thf('71', plain,
% 2.01/2.23      (![X2 : $i, X3 : $i]:
% 2.01/2.23         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 2.01/2.23      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.01/2.23  thf('72', plain, (((k3_xboole_0 @ sk_C @ sk_B) = (k1_xboole_0))),
% 2.01/2.23      inference('sup-', [status(thm)], ['70', '71'])).
% 2.01/2.23  thf('73', plain,
% 2.01/2.23      (![X15 : $i, X16 : $i]:
% 2.01/2.23         ((k2_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ (k4_xboole_0 @ X15 @ X16))
% 2.01/2.23           = (X15))),
% 2.01/2.23      inference('cnf', [status(esa)], [t51_xboole_1])).
% 2.01/2.23  thf('74', plain,
% 2.01/2.23      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_B)) = (sk_C))),
% 2.01/2.23      inference('sup+', [status(thm)], ['72', '73'])).
% 2.01/2.23  thf('75', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.01/2.23      inference('sup+', [status(thm)], ['5', '6'])).
% 2.01/2.23  thf('76', plain, (((k4_xboole_0 @ sk_C @ sk_B) = (sk_C))),
% 2.01/2.23      inference('demod', [status(thm)], ['74', '75'])).
% 2.01/2.23  thf('77', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_C @ sk_A))),
% 2.01/2.23      inference('demod', [status(thm)], ['69', '76'])).
% 2.01/2.23  thf('78', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 2.01/2.23      inference('cnf', [status(esa)], [t3_boole])).
% 2.01/2.23  thf('79', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.01/2.23      inference('demod', [status(thm)], ['20', '21'])).
% 2.01/2.23  thf('80', plain,
% 2.01/2.23      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.01/2.23         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 2.01/2.23           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 2.01/2.23      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.01/2.23  thf('81', plain,
% 2.01/2.23      (![X7 : $i, X8 : $i]:
% 2.01/2.23         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 2.01/2.23           = (k2_xboole_0 @ X7 @ X8))),
% 2.01/2.23      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.01/2.23  thf('82', plain,
% 2.01/2.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.01/2.23         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 2.01/2.23           (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 2.01/2.23           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 2.01/2.23      inference('sup+', [status(thm)], ['80', '81'])).
% 2.01/2.23  thf('83', plain,
% 2.01/2.23      (![X0 : $i, X1 : $i]:
% 2.01/2.23         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ 
% 2.01/2.23           (k4_xboole_0 @ k1_xboole_0 @ X1))
% 2.01/2.23           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 2.01/2.23      inference('sup+', [status(thm)], ['79', '82'])).
% 2.01/2.23  thf('84', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.01/2.23      inference('demod', [status(thm)], ['20', '21'])).
% 2.01/2.23  thf('85', plain,
% 2.01/2.23      (![X7 : $i, X8 : $i]:
% 2.01/2.23         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 2.01/2.23           = (k2_xboole_0 @ X7 @ X8))),
% 2.01/2.23      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.01/2.23  thf('86', plain,
% 2.01/2.23      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 2.01/2.23      inference('sup+', [status(thm)], ['84', '85'])).
% 2.01/2.23  thf('87', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 2.01/2.23      inference('cnf', [status(esa)], [t1_boole])).
% 2.01/2.23  thf('88', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 2.01/2.23      inference('demod', [status(thm)], ['86', '87'])).
% 2.01/2.23  thf('89', plain,
% 2.01/2.23      (![X0 : $i, X1 : $i]:
% 2.01/2.23         ((k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 2.01/2.23           = (k1_xboole_0))),
% 2.01/2.23      inference('sup+', [status(thm)], ['48', '49'])).
% 2.01/2.23  thf('90', plain,
% 2.01/2.23      (![X0 : $i]:
% 2.01/2.23         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0) = (k1_xboole_0))),
% 2.01/2.23      inference('sup+', [status(thm)], ['88', '89'])).
% 2.01/2.23  thf('91', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.01/2.23      inference('demod', [status(thm)], ['20', '21'])).
% 2.01/2.23  thf('92', plain,
% 2.01/2.23      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 2.01/2.23      inference('demod', [status(thm)], ['90', '91'])).
% 2.01/2.23  thf('93', plain,
% 2.01/2.23      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.01/2.23      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.01/2.23  thf('94', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.01/2.23      inference('sup+', [status(thm)], ['5', '6'])).
% 2.01/2.23  thf('95', plain,
% 2.01/2.23      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.01/2.23      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.01/2.23  thf('96', plain,
% 2.01/2.23      (![X0 : $i, X1 : $i]:
% 2.01/2.23         ((k2_xboole_0 @ X0 @ X1)
% 2.01/2.23           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 2.01/2.23      inference('demod', [status(thm)], ['83', '92', '93', '94', '95'])).
% 2.01/2.23  thf('97', plain, (((sk_A) = (k2_xboole_0 @ sk_A @ sk_C))),
% 2.01/2.23      inference('demod', [status(thm)], ['60', '77', '78', '96'])).
% 2.01/2.23  thf('98', plain, (((sk_C) = (sk_A))),
% 2.01/2.23      inference('demod', [status(thm)], ['25', '26', '27', '97'])).
% 2.01/2.23  thf('99', plain, (((sk_A) != (sk_C))),
% 2.01/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.01/2.23  thf('100', plain, ($false),
% 2.01/2.23      inference('simplify_reflect-', [status(thm)], ['98', '99'])).
% 2.01/2.23  
% 2.01/2.23  % SZS output end Refutation
% 2.01/2.23  
% 2.01/2.24  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

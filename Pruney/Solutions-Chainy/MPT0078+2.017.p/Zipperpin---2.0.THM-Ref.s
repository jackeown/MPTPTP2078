%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.El9VxX51yP

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:54 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 333 expanded)
%              Number of leaves         :   17 ( 116 expanded)
%              Depth                    :   25
%              Number of atoms          :  767 (2575 expanded)
%              Number of equality atoms :   99 ( 334 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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

thf('0',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('2',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ k1_xboole_0 ) @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('12',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['1','16'])).

thf('18',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['0','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['1','16'])).

thf('20',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('24',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('25',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['18','19','28'])).

thf('30',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('31',plain,
    ( ( k2_xboole_0 @ sk_C @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('36',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('38',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','46'])).

thf('48',plain,
    ( sk_C
    = ( k3_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['36','47'])).

thf('49',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('50',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_C )
    = ( k4_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('52',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('54',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_C @ sk_A ) ) ),
    inference('sup+',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('58',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    r1_xboole_0 @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('61',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('63',plain,
    ( ( k4_xboole_0 @ sk_C @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_C @ k1_xboole_0 ) @ X0 )
      = ( k4_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k4_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_C @ X0 )
      = ( k4_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k4_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_C @ sk_A ) )
    = ( k4_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['58','69'])).

thf('71',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('72',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k4_xboole_0 @ sk_C @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('75',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('76',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_C @ sk_A ) )
    = sk_C ),
    inference(demod,[status(thm)],['70','73','76'])).

thf('78',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('79',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_C )
    = ( k4_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_C @ sk_A ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('81',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('82',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('84',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('86',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    sk_C = sk_A ),
    inference(demod,[status(thm)],['31','34','35','86'])).

thf('88',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['87','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.El9VxX51yP
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:50:48 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.52/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.52/0.68  % Solved by: fo/fo7.sh
% 0.52/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.68  % done 553 iterations in 0.260s
% 0.52/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.52/0.68  % SZS output start Refutation
% 0.52/0.68  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.52/0.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.52/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.68  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.52/0.68  thf(sk_C_type, type, sk_C: $i).
% 0.52/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.68  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.52/0.68  thf(t71_xboole_1, conjecture,
% 0.52/0.68    (![A:$i,B:$i,C:$i]:
% 0.52/0.68     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ B ) ) & 
% 0.52/0.68         ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.52/0.68       ( ( A ) = ( C ) ) ))).
% 0.52/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.68    (~( ![A:$i,B:$i,C:$i]:
% 0.52/0.68        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ B ) ) & 
% 0.52/0.68            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.52/0.68          ( ( A ) = ( C ) ) ) )),
% 0.52/0.68    inference('cnf.neg', [status(esa)], [t71_xboole_1])).
% 0.52/0.68  thf('0', plain,
% 0.52/0.68      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ sk_B))),
% 0.52/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.68  thf(commutativity_k2_xboole_0, axiom,
% 0.52/0.68    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.52/0.68  thf('1', plain,
% 0.52/0.68      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.52/0.68      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.52/0.68  thf('2', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.52/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.68  thf(d7_xboole_0, axiom,
% 0.52/0.68    (![A:$i,B:$i]:
% 0.52/0.68     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.52/0.68       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.52/0.68  thf('3', plain,
% 0.52/0.68      (![X2 : $i, X3 : $i]:
% 0.52/0.68         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.52/0.68      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.52/0.68  thf('4', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.52/0.68      inference('sup-', [status(thm)], ['2', '3'])).
% 0.52/0.68  thf(t47_xboole_1, axiom,
% 0.52/0.68    (![A:$i,B:$i]:
% 0.52/0.68     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.52/0.68  thf('5', plain,
% 0.52/0.68      (![X11 : $i, X12 : $i]:
% 0.52/0.68         ((k4_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12))
% 0.52/0.68           = (k4_xboole_0 @ X11 @ X12))),
% 0.52/0.68      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.52/0.68  thf('6', plain,
% 0.52/0.68      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.52/0.68      inference('sup+', [status(thm)], ['4', '5'])).
% 0.52/0.68  thf(t41_xboole_1, axiom,
% 0.52/0.68    (![A:$i,B:$i,C:$i]:
% 0.52/0.68     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.52/0.68       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.52/0.68  thf('7', plain,
% 0.52/0.68      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.52/0.68         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 0.52/0.68           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 0.52/0.68      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.52/0.68  thf('8', plain,
% 0.52/0.68      (![X0 : $i]:
% 0.52/0.68         ((k4_xboole_0 @ (k4_xboole_0 @ sk_A @ k1_xboole_0) @ X0)
% 0.52/0.68           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.52/0.68      inference('sup+', [status(thm)], ['6', '7'])).
% 0.52/0.68  thf('9', plain,
% 0.52/0.68      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.52/0.68         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 0.52/0.68           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 0.52/0.68      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.52/0.68  thf('10', plain,
% 0.52/0.68      (![X0 : $i]:
% 0.52/0.68         ((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ k1_xboole_0 @ X0))
% 0.52/0.68           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.52/0.68      inference('demod', [status(thm)], ['8', '9'])).
% 0.52/0.68  thf(t2_boole, axiom,
% 0.52/0.68    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.52/0.68  thf('11', plain,
% 0.52/0.68      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.68      inference('cnf', [status(esa)], [t2_boole])).
% 0.52/0.68  thf(t51_xboole_1, axiom,
% 0.52/0.68    (![A:$i,B:$i]:
% 0.52/0.68     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.52/0.68       ( A ) ))).
% 0.52/0.68  thf('12', plain,
% 0.52/0.68      (![X15 : $i, X16 : $i]:
% 0.52/0.68         ((k2_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ (k4_xboole_0 @ X15 @ X16))
% 0.52/0.68           = (X15))),
% 0.52/0.68      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.52/0.68  thf('13', plain,
% 0.52/0.68      (![X0 : $i]:
% 0.52/0.68         ((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 0.52/0.68      inference('sup+', [status(thm)], ['11', '12'])).
% 0.52/0.68  thf(t39_xboole_1, axiom,
% 0.52/0.68    (![A:$i,B:$i]:
% 0.52/0.68     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.52/0.68  thf('14', plain,
% 0.52/0.68      (![X6 : $i, X7 : $i]:
% 0.52/0.68         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.52/0.68           = (k2_xboole_0 @ X6 @ X7))),
% 0.52/0.68      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.52/0.68  thf('15', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.52/0.68      inference('demod', [status(thm)], ['13', '14'])).
% 0.52/0.68  thf('16', plain,
% 0.52/0.68      (![X0 : $i]:
% 0.52/0.68         ((k4_xboole_0 @ sk_A @ X0)
% 0.52/0.68           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.52/0.68      inference('demod', [status(thm)], ['10', '15'])).
% 0.52/0.68  thf('17', plain,
% 0.52/0.68      (![X0 : $i]:
% 0.52/0.68         ((k4_xboole_0 @ sk_A @ X0)
% 0.52/0.68           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_B)))),
% 0.52/0.68      inference('sup+', [status(thm)], ['1', '16'])).
% 0.52/0.68  thf('18', plain,
% 0.52/0.68      (((k4_xboole_0 @ sk_A @ sk_C)
% 0.52/0.68         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_A @ sk_B)))),
% 0.52/0.68      inference('sup+', [status(thm)], ['0', '17'])).
% 0.52/0.68  thf('19', plain,
% 0.52/0.68      (![X0 : $i]:
% 0.52/0.68         ((k4_xboole_0 @ sk_A @ X0)
% 0.52/0.68           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_B)))),
% 0.52/0.68      inference('sup+', [status(thm)], ['1', '16'])).
% 0.52/0.68  thf('20', plain,
% 0.52/0.68      (![X6 : $i, X7 : $i]:
% 0.52/0.68         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.52/0.68           = (k2_xboole_0 @ X6 @ X7))),
% 0.52/0.68      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.52/0.68  thf('21', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.52/0.68      inference('demod', [status(thm)], ['13', '14'])).
% 0.52/0.68  thf('22', plain,
% 0.52/0.68      (![X0 : $i]:
% 0.52/0.68         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.52/0.68      inference('sup+', [status(thm)], ['20', '21'])).
% 0.52/0.68  thf('23', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.52/0.68      inference('demod', [status(thm)], ['13', '14'])).
% 0.52/0.68  thf('24', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.52/0.68      inference('demod', [status(thm)], ['22', '23'])).
% 0.52/0.68  thf(t48_xboole_1, axiom,
% 0.52/0.68    (![A:$i,B:$i]:
% 0.52/0.68     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.52/0.68  thf('25', plain,
% 0.52/0.68      (![X13 : $i, X14 : $i]:
% 0.52/0.68         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.52/0.68           = (k3_xboole_0 @ X13 @ X14))),
% 0.52/0.68      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.52/0.68  thf('26', plain,
% 0.52/0.68      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.52/0.68      inference('sup+', [status(thm)], ['24', '25'])).
% 0.52/0.68  thf('27', plain,
% 0.52/0.68      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.68      inference('cnf', [status(esa)], [t2_boole])).
% 0.52/0.68  thf('28', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.52/0.68      inference('demod', [status(thm)], ['26', '27'])).
% 0.52/0.68  thf('29', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.52/0.68      inference('demod', [status(thm)], ['18', '19', '28'])).
% 0.52/0.68  thf('30', plain,
% 0.52/0.68      (![X6 : $i, X7 : $i]:
% 0.52/0.68         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.52/0.68           = (k2_xboole_0 @ X6 @ X7))),
% 0.52/0.68      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.52/0.68  thf('31', plain,
% 0.52/0.68      (((k2_xboole_0 @ sk_C @ k1_xboole_0) = (k2_xboole_0 @ sk_C @ sk_A))),
% 0.52/0.68      inference('sup+', [status(thm)], ['29', '30'])).
% 0.52/0.68  thf('32', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.52/0.68      inference('demod', [status(thm)], ['13', '14'])).
% 0.52/0.68  thf('33', plain,
% 0.52/0.68      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.52/0.68      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.52/0.68  thf('34', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.52/0.68      inference('sup+', [status(thm)], ['32', '33'])).
% 0.52/0.68  thf('35', plain,
% 0.52/0.68      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.52/0.68      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.52/0.68  thf('36', plain,
% 0.52/0.68      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ sk_B))),
% 0.52/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.68  thf('37', plain,
% 0.52/0.68      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.52/0.68      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.52/0.68  thf('38', plain,
% 0.52/0.68      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.52/0.68         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 0.52/0.68           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 0.52/0.68      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.52/0.68  thf('39', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.52/0.68      inference('demod', [status(thm)], ['26', '27'])).
% 0.52/0.68  thf('40', plain,
% 0.52/0.68      (![X0 : $i, X1 : $i]:
% 0.52/0.68         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 0.52/0.68           = (k1_xboole_0))),
% 0.52/0.68      inference('sup+', [status(thm)], ['38', '39'])).
% 0.52/0.68  thf('41', plain,
% 0.52/0.68      (![X6 : $i, X7 : $i]:
% 0.52/0.68         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.52/0.68           = (k2_xboole_0 @ X6 @ X7))),
% 0.52/0.68      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.52/0.68  thf('42', plain,
% 0.52/0.68      (![X0 : $i, X1 : $i]:
% 0.52/0.68         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.52/0.68      inference('demod', [status(thm)], ['40', '41'])).
% 0.52/0.68  thf('43', plain,
% 0.52/0.68      (![X13 : $i, X14 : $i]:
% 0.52/0.68         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.52/0.68           = (k3_xboole_0 @ X13 @ X14))),
% 0.52/0.68      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.52/0.68  thf('44', plain,
% 0.52/0.68      (![X0 : $i, X1 : $i]:
% 0.52/0.68         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.52/0.68           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.52/0.68      inference('sup+', [status(thm)], ['42', '43'])).
% 0.52/0.68  thf('45', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.52/0.68      inference('demod', [status(thm)], ['22', '23'])).
% 0.52/0.68  thf('46', plain,
% 0.52/0.68      (![X0 : $i, X1 : $i]:
% 0.52/0.68         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.52/0.68      inference('demod', [status(thm)], ['44', '45'])).
% 0.52/0.68  thf('47', plain,
% 0.52/0.68      (![X0 : $i, X1 : $i]:
% 0.52/0.68         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.52/0.68      inference('sup+', [status(thm)], ['37', '46'])).
% 0.52/0.68  thf('48', plain,
% 0.52/0.68      (((sk_C) = (k3_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_A @ sk_B)))),
% 0.52/0.68      inference('sup+', [status(thm)], ['36', '47'])).
% 0.52/0.68  thf('49', plain,
% 0.52/0.68      (![X11 : $i, X12 : $i]:
% 0.52/0.68         ((k4_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12))
% 0.52/0.68           = (k4_xboole_0 @ X11 @ X12))),
% 0.52/0.68      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.52/0.68  thf('50', plain,
% 0.52/0.68      (((k4_xboole_0 @ sk_C @ sk_C)
% 0.52/0.68         = (k4_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_A @ sk_B)))),
% 0.52/0.68      inference('sup+', [status(thm)], ['48', '49'])).
% 0.52/0.68  thf('51', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.52/0.68      inference('demod', [status(thm)], ['26', '27'])).
% 0.52/0.68  thf('52', plain,
% 0.52/0.68      (((k1_xboole_0) = (k4_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_A @ sk_B)))),
% 0.52/0.68      inference('demod', [status(thm)], ['50', '51'])).
% 0.52/0.68  thf('53', plain,
% 0.52/0.68      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.52/0.68         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 0.52/0.68           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 0.52/0.68      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.52/0.68  thf('54', plain,
% 0.52/0.68      (![X6 : $i, X7 : $i]:
% 0.52/0.68         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.52/0.68           = (k2_xboole_0 @ X6 @ X7))),
% 0.52/0.68      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.52/0.68  thf('55', plain,
% 0.52/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.68         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.52/0.68           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 0.52/0.68      inference('sup+', [status(thm)], ['53', '54'])).
% 0.52/0.68  thf('56', plain,
% 0.52/0.68      (((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 0.52/0.68         = (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_C @ sk_A)))),
% 0.52/0.68      inference('sup+', [status(thm)], ['52', '55'])).
% 0.52/0.68  thf('57', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.52/0.68      inference('sup+', [status(thm)], ['32', '33'])).
% 0.52/0.68  thf('58', plain,
% 0.52/0.68      (((sk_B) = (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_C @ sk_A)))),
% 0.52/0.68      inference('demod', [status(thm)], ['56', '57'])).
% 0.52/0.68  thf('59', plain, ((r1_xboole_0 @ sk_C @ sk_B)),
% 0.52/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.68  thf('60', plain,
% 0.52/0.68      (![X2 : $i, X3 : $i]:
% 0.52/0.68         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.52/0.68      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.52/0.68  thf('61', plain, (((k3_xboole_0 @ sk_C @ sk_B) = (k1_xboole_0))),
% 0.52/0.68      inference('sup-', [status(thm)], ['59', '60'])).
% 0.52/0.68  thf('62', plain,
% 0.52/0.68      (![X11 : $i, X12 : $i]:
% 0.52/0.68         ((k4_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12))
% 0.52/0.68           = (k4_xboole_0 @ X11 @ X12))),
% 0.52/0.68      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.52/0.68  thf('63', plain,
% 0.52/0.68      (((k4_xboole_0 @ sk_C @ k1_xboole_0) = (k4_xboole_0 @ sk_C @ sk_B))),
% 0.52/0.68      inference('sup+', [status(thm)], ['61', '62'])).
% 0.52/0.68  thf('64', plain,
% 0.52/0.68      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.52/0.68         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 0.52/0.68           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 0.52/0.68      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.52/0.68  thf('65', plain,
% 0.52/0.68      (![X0 : $i]:
% 0.52/0.68         ((k4_xboole_0 @ (k4_xboole_0 @ sk_C @ k1_xboole_0) @ X0)
% 0.52/0.68           = (k4_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.52/0.68      inference('sup+', [status(thm)], ['63', '64'])).
% 0.52/0.68  thf('66', plain,
% 0.52/0.68      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.52/0.68         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 0.52/0.68           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 0.52/0.68      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.52/0.68  thf('67', plain,
% 0.52/0.68      (![X0 : $i]:
% 0.52/0.68         ((k4_xboole_0 @ sk_C @ (k2_xboole_0 @ k1_xboole_0 @ X0))
% 0.52/0.68           = (k4_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.52/0.68      inference('demod', [status(thm)], ['65', '66'])).
% 0.52/0.68  thf('68', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.52/0.68      inference('demod', [status(thm)], ['13', '14'])).
% 0.52/0.68  thf('69', plain,
% 0.52/0.68      (![X0 : $i]:
% 0.52/0.68         ((k4_xboole_0 @ sk_C @ X0)
% 0.52/0.68           = (k4_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.52/0.68      inference('demod', [status(thm)], ['67', '68'])).
% 0.52/0.68  thf('70', plain,
% 0.52/0.68      (((k4_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_C @ sk_A))
% 0.52/0.68         = (k4_xboole_0 @ sk_C @ sk_B))),
% 0.52/0.68      inference('sup+', [status(thm)], ['58', '69'])).
% 0.52/0.68  thf('71', plain,
% 0.52/0.68      (![X11 : $i, X12 : $i]:
% 0.52/0.68         ((k4_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12))
% 0.52/0.68           = (k4_xboole_0 @ X11 @ X12))),
% 0.52/0.68      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.52/0.68  thf('72', plain,
% 0.52/0.68      (![X13 : $i, X14 : $i]:
% 0.52/0.68         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.52/0.68           = (k3_xboole_0 @ X13 @ X14))),
% 0.52/0.68      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.52/0.68  thf('73', plain,
% 0.52/0.68      (![X0 : $i, X1 : $i]:
% 0.52/0.68         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.52/0.68           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.52/0.68      inference('sup+', [status(thm)], ['71', '72'])).
% 0.52/0.68  thf('74', plain,
% 0.52/0.68      (((k4_xboole_0 @ sk_C @ k1_xboole_0) = (k4_xboole_0 @ sk_C @ sk_B))),
% 0.52/0.68      inference('sup+', [status(thm)], ['61', '62'])).
% 0.52/0.68  thf('75', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.52/0.68      inference('demod', [status(thm)], ['22', '23'])).
% 0.52/0.68  thf('76', plain, (((sk_C) = (k4_xboole_0 @ sk_C @ sk_B))),
% 0.52/0.68      inference('demod', [status(thm)], ['74', '75'])).
% 0.52/0.68  thf('77', plain,
% 0.52/0.68      (((k3_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_C @ sk_A)) = (sk_C))),
% 0.52/0.68      inference('demod', [status(thm)], ['70', '73', '76'])).
% 0.52/0.68  thf('78', plain,
% 0.52/0.68      (![X11 : $i, X12 : $i]:
% 0.52/0.68         ((k4_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12))
% 0.52/0.68           = (k4_xboole_0 @ X11 @ X12))),
% 0.52/0.68      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.52/0.68  thf('79', plain,
% 0.52/0.68      (((k4_xboole_0 @ sk_C @ sk_C)
% 0.52/0.68         = (k4_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_C @ sk_A)))),
% 0.52/0.68      inference('sup+', [status(thm)], ['77', '78'])).
% 0.52/0.68  thf('80', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.52/0.68      inference('demod', [status(thm)], ['26', '27'])).
% 0.52/0.68  thf('81', plain,
% 0.52/0.68      (![X11 : $i, X12 : $i]:
% 0.52/0.68         ((k4_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12))
% 0.52/0.68           = (k4_xboole_0 @ X11 @ X12))),
% 0.52/0.68      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.52/0.68  thf('82', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_C @ sk_A))),
% 0.52/0.68      inference('demod', [status(thm)], ['79', '80', '81'])).
% 0.52/0.68  thf('83', plain,
% 0.52/0.68      (![X6 : $i, X7 : $i]:
% 0.52/0.68         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.52/0.68           = (k2_xboole_0 @ X6 @ X7))),
% 0.52/0.68      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.52/0.68  thf('84', plain,
% 0.52/0.68      (((k2_xboole_0 @ sk_A @ k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_C))),
% 0.52/0.68      inference('sup+', [status(thm)], ['82', '83'])).
% 0.52/0.68  thf('85', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.52/0.68      inference('sup+', [status(thm)], ['32', '33'])).
% 0.52/0.68  thf('86', plain, (((sk_A) = (k2_xboole_0 @ sk_A @ sk_C))),
% 0.52/0.68      inference('demod', [status(thm)], ['84', '85'])).
% 0.52/0.68  thf('87', plain, (((sk_C) = (sk_A))),
% 0.52/0.68      inference('demod', [status(thm)], ['31', '34', '35', '86'])).
% 0.52/0.68  thf('88', plain, (((sk_A) != (sk_C))),
% 0.52/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.68  thf('89', plain, ($false),
% 0.52/0.68      inference('simplify_reflect-', [status(thm)], ['87', '88'])).
% 0.52/0.68  
% 0.52/0.68  % SZS output end Refutation
% 0.52/0.68  
% 0.52/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

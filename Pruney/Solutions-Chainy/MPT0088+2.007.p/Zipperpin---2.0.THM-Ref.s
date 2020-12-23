%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.roIoZVxqe2

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:35 EST 2020

% Result     : Theorem 0.89s
% Output     : Refutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 124 expanded)
%              Number of leaves         :   18 (  46 expanded)
%              Depth                    :   13
%              Number of atoms          :  593 ( 961 expanded)
%              Number of equality atoms :   61 ( 104 expanded)
%              Maximal formula depth    :   10 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t81_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
       => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t81_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('3',plain,(
    r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('7',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('9',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('10',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ) ),
    inference('sup+',[status(thm)],['2','11'])).

thf('13',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['1','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('15',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('17',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('20',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('26',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('30',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('36',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['34','41'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('43',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('44',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('45',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X2 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','54'])).

thf('56',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['15','57'])).

thf('59',plain,(
    $false ),
    inference(demod,[status(thm)],['0','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.roIoZVxqe2
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:15:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.89/1.12  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.89/1.12  % Solved by: fo/fo7.sh
% 0.89/1.12  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.89/1.12  % done 1102 iterations in 0.668s
% 0.89/1.12  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.89/1.12  % SZS output start Refutation
% 0.89/1.12  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.89/1.12  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.89/1.12  thf(sk_C_type, type, sk_C: $i).
% 0.89/1.12  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.89/1.12  thf(sk_B_type, type, sk_B: $i).
% 0.89/1.12  thf(sk_A_type, type, sk_A: $i).
% 0.89/1.12  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.89/1.12  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.89/1.12  thf(t81_xboole_1, conjecture,
% 0.89/1.12    (![A:$i,B:$i,C:$i]:
% 0.89/1.12     ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.89/1.12       ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.89/1.12  thf(zf_stmt_0, negated_conjecture,
% 0.89/1.12    (~( ![A:$i,B:$i,C:$i]:
% 0.89/1.12        ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.89/1.12          ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )),
% 0.89/1.12    inference('cnf.neg', [status(esa)], [t81_xboole_1])).
% 0.89/1.12  thf('0', plain, (~ (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.12  thf(t39_xboole_1, axiom,
% 0.89/1.12    (![A:$i,B:$i]:
% 0.89/1.12     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.89/1.12  thf('1', plain,
% 0.89/1.12      (![X6 : $i, X7 : $i]:
% 0.89/1.12         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.89/1.12           = (k2_xboole_0 @ X6 @ X7))),
% 0.89/1.12      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.89/1.12  thf(commutativity_k2_xboole_0, axiom,
% 0.89/1.12    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.89/1.12  thf('2', plain,
% 0.89/1.12      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.89/1.12      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.89/1.12  thf('3', plain, ((r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.12  thf(d7_xboole_0, axiom,
% 0.89/1.12    (![A:$i,B:$i]:
% 0.89/1.12     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.89/1.12       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.89/1.12  thf('4', plain,
% 0.89/1.12      (![X2 : $i, X3 : $i]:
% 0.89/1.12         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.89/1.12      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.89/1.12  thf('5', plain,
% 0.89/1.12      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 0.89/1.12      inference('sup-', [status(thm)], ['3', '4'])).
% 0.89/1.12  thf(t47_xboole_1, axiom,
% 0.89/1.12    (![A:$i,B:$i]:
% 0.89/1.12     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.89/1.12  thf('6', plain,
% 0.89/1.12      (![X12 : $i, X13 : $i]:
% 0.89/1.12         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 0.89/1.12           = (k4_xboole_0 @ X12 @ X13))),
% 0.89/1.12      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.89/1.12  thf('7', plain,
% 0.89/1.12      (((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 0.89/1.12         = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.89/1.12      inference('sup+', [status(thm)], ['5', '6'])).
% 0.89/1.12  thf(t3_boole, axiom,
% 0.89/1.12    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.89/1.12  thf('8', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.89/1.12      inference('cnf', [status(esa)], [t3_boole])).
% 0.89/1.12  thf('9', plain,
% 0.89/1.12      (((sk_A) = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.89/1.12      inference('demod', [status(thm)], ['7', '8'])).
% 0.89/1.12  thf(t41_xboole_1, axiom,
% 0.89/1.12    (![A:$i,B:$i,C:$i]:
% 0.89/1.12     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.89/1.12       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.89/1.12  thf('10', plain,
% 0.89/1.12      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.89/1.12         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.89/1.12           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.89/1.12      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.89/1.12  thf('11', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         ((k4_xboole_0 @ sk_A @ X0)
% 0.89/1.12           = (k4_xboole_0 @ sk_A @ 
% 0.89/1.12              (k2_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ X0)))),
% 0.89/1.12      inference('sup+', [status(thm)], ['9', '10'])).
% 0.89/1.12  thf('12', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         ((k4_xboole_0 @ sk_A @ X0)
% 0.89/1.12           = (k4_xboole_0 @ sk_A @ 
% 0.89/1.12              (k2_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C))))),
% 0.89/1.12      inference('sup+', [status(thm)], ['2', '11'])).
% 0.89/1.12  thf('13', plain,
% 0.89/1.12      (((k4_xboole_0 @ sk_A @ sk_C)
% 0.89/1.12         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B)))),
% 0.89/1.12      inference('sup+', [status(thm)], ['1', '12'])).
% 0.89/1.12  thf('14', plain,
% 0.89/1.12      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.89/1.12      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.89/1.12  thf('15', plain,
% 0.89/1.12      (((k4_xboole_0 @ sk_A @ sk_C)
% 0.89/1.12         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.89/1.12      inference('demod', [status(thm)], ['13', '14'])).
% 0.89/1.12  thf('16', plain,
% 0.89/1.12      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.89/1.12         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.89/1.12           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.89/1.12      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.89/1.12  thf('17', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.89/1.12      inference('cnf', [status(esa)], [t3_boole])).
% 0.89/1.12  thf(t48_xboole_1, axiom,
% 0.89/1.12    (![A:$i,B:$i]:
% 0.89/1.12     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.89/1.12  thf('18', plain,
% 0.89/1.12      (![X14 : $i, X15 : $i]:
% 0.89/1.12         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.89/1.12           = (k3_xboole_0 @ X14 @ X15))),
% 0.89/1.12      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.89/1.12  thf('19', plain,
% 0.89/1.12      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.89/1.12      inference('sup+', [status(thm)], ['17', '18'])).
% 0.89/1.12  thf(t2_boole, axiom,
% 0.89/1.12    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.89/1.12  thf('20', plain,
% 0.89/1.12      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.89/1.12      inference('cnf', [status(esa)], [t2_boole])).
% 0.89/1.12  thf('21', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.89/1.12      inference('demod', [status(thm)], ['19', '20'])).
% 0.89/1.12  thf('22', plain,
% 0.89/1.12      (![X0 : $i, X1 : $i]:
% 0.89/1.12         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 0.89/1.12           = (k1_xboole_0))),
% 0.89/1.12      inference('sup+', [status(thm)], ['16', '21'])).
% 0.89/1.12  thf('23', plain,
% 0.89/1.12      (![X6 : $i, X7 : $i]:
% 0.89/1.12         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.89/1.12           = (k2_xboole_0 @ X6 @ X7))),
% 0.89/1.12      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.89/1.12  thf('24', plain,
% 0.89/1.12      (![X0 : $i, X1 : $i]:
% 0.89/1.12         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.89/1.12      inference('demod', [status(thm)], ['22', '23'])).
% 0.89/1.12  thf('25', plain,
% 0.89/1.12      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.89/1.12         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.89/1.12           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.89/1.12      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.89/1.12  thf('26', plain,
% 0.89/1.12      (![X6 : $i, X7 : $i]:
% 0.89/1.12         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.89/1.12           = (k2_xboole_0 @ X6 @ X7))),
% 0.89/1.12      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.89/1.12  thf('27', plain,
% 0.89/1.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.12         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.89/1.12           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 0.89/1.12      inference('sup+', [status(thm)], ['25', '26'])).
% 0.89/1.12  thf('28', plain,
% 0.89/1.12      (![X0 : $i, X1 : $i]:
% 0.89/1.12         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 0.89/1.12           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.89/1.12      inference('sup+', [status(thm)], ['24', '27'])).
% 0.89/1.12  thf('29', plain,
% 0.89/1.12      (![X0 : $i, X1 : $i]:
% 0.89/1.12         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.89/1.12      inference('demod', [status(thm)], ['22', '23'])).
% 0.89/1.12  thf('30', plain,
% 0.89/1.12      (![X14 : $i, X15 : $i]:
% 0.89/1.12         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.89/1.12           = (k3_xboole_0 @ X14 @ X15))),
% 0.89/1.12      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.89/1.12  thf('31', plain,
% 0.89/1.12      (![X0 : $i, X1 : $i]:
% 0.89/1.12         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.89/1.12           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.89/1.12      inference('sup+', [status(thm)], ['29', '30'])).
% 0.89/1.12  thf('32', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.89/1.12      inference('cnf', [status(esa)], [t3_boole])).
% 0.89/1.12  thf('33', plain,
% 0.89/1.12      (![X0 : $i, X1 : $i]:
% 0.89/1.12         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.89/1.12      inference('demod', [status(thm)], ['31', '32'])).
% 0.89/1.12  thf('34', plain,
% 0.89/1.12      (![X0 : $i, X1 : $i]:
% 0.89/1.12         ((k4_xboole_0 @ X0 @ X1)
% 0.89/1.12           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 0.89/1.12              (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.89/1.12      inference('sup+', [status(thm)], ['28', '33'])).
% 0.89/1.12  thf('35', plain,
% 0.89/1.12      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.89/1.12         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.89/1.12           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.89/1.12      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.89/1.12  thf('36', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.89/1.12      inference('cnf', [status(esa)], [t3_boole])).
% 0.89/1.12  thf('37', plain,
% 0.89/1.12      (![X0 : $i, X1 : $i]:
% 0.89/1.12         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ k1_xboole_0))
% 0.89/1.12           = (k4_xboole_0 @ X1 @ X0))),
% 0.89/1.12      inference('sup+', [status(thm)], ['35', '36'])).
% 0.89/1.12  thf('38', plain,
% 0.89/1.12      (![X14 : $i, X15 : $i]:
% 0.89/1.12         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.89/1.12           = (k3_xboole_0 @ X14 @ X15))),
% 0.89/1.12      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.89/1.12  thf('39', plain,
% 0.89/1.12      (![X0 : $i, X1 : $i]:
% 0.89/1.12         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.89/1.12           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.89/1.12      inference('sup+', [status(thm)], ['37', '38'])).
% 0.89/1.12  thf('40', plain,
% 0.89/1.12      (![X14 : $i, X15 : $i]:
% 0.89/1.12         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.89/1.12           = (k3_xboole_0 @ X14 @ X15))),
% 0.89/1.12      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.89/1.12  thf('41', plain,
% 0.89/1.12      (![X0 : $i, X1 : $i]:
% 0.89/1.12         ((k3_xboole_0 @ X1 @ X0)
% 0.89/1.12           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.89/1.12      inference('demod', [status(thm)], ['39', '40'])).
% 0.89/1.12  thf('42', plain,
% 0.89/1.12      (![X0 : $i, X1 : $i]:
% 0.89/1.12         ((k4_xboole_0 @ X0 @ X1)
% 0.89/1.12           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.89/1.12      inference('demod', [status(thm)], ['34', '41'])).
% 0.89/1.12  thf(t49_xboole_1, axiom,
% 0.89/1.12    (![A:$i,B:$i,C:$i]:
% 0.89/1.12     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.89/1.12       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.89/1.12  thf('43', plain,
% 0.89/1.12      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.89/1.12         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 0.89/1.12           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18))),
% 0.89/1.12      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.89/1.12  thf('44', plain,
% 0.89/1.12      (![X14 : $i, X15 : $i]:
% 0.89/1.12         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.89/1.12           = (k3_xboole_0 @ X14 @ X15))),
% 0.89/1.12      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.89/1.12  thf('45', plain,
% 0.89/1.12      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.89/1.12         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.89/1.12           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.89/1.12      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.89/1.12  thf('46', plain,
% 0.89/1.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.12         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.89/1.12           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 0.89/1.12      inference('sup+', [status(thm)], ['44', '45'])).
% 0.89/1.12  thf('47', plain,
% 0.89/1.12      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.89/1.12         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 0.89/1.12           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18))),
% 0.89/1.12      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.89/1.12  thf('48', plain,
% 0.89/1.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.12         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X2))
% 0.89/1.12           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 0.89/1.12      inference('demod', [status(thm)], ['46', '47'])).
% 0.89/1.12  thf('49', plain,
% 0.89/1.12      (![X0 : $i, X1 : $i]:
% 0.89/1.12         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.89/1.12      inference('demod', [status(thm)], ['22', '23'])).
% 0.89/1.12  thf('50', plain,
% 0.89/1.12      (![X0 : $i, X1 : $i]:
% 0.89/1.12         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.89/1.12      inference('sup+', [status(thm)], ['48', '49'])).
% 0.89/1.12  thf('51', plain,
% 0.89/1.12      (![X2 : $i, X4 : $i]:
% 0.89/1.12         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.89/1.12      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.89/1.12  thf('52', plain,
% 0.89/1.12      (![X0 : $i, X1 : $i]:
% 0.89/1.12         (((k1_xboole_0) != (k1_xboole_0))
% 0.89/1.12          | (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.89/1.12      inference('sup-', [status(thm)], ['50', '51'])).
% 0.89/1.12  thf('53', plain,
% 0.89/1.12      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.89/1.12      inference('simplify', [status(thm)], ['52'])).
% 0.89/1.12  thf('54', plain,
% 0.89/1.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.12         (r1_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.89/1.12      inference('sup+', [status(thm)], ['43', '53'])).
% 0.89/1.12  thf('55', plain,
% 0.89/1.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.12         (r1_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.89/1.12      inference('sup+', [status(thm)], ['42', '54'])).
% 0.89/1.12  thf('56', plain,
% 0.89/1.12      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.89/1.12         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.89/1.12           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.89/1.12      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.89/1.12  thf('57', plain,
% 0.89/1.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.12         (r1_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.89/1.12      inference('demod', [status(thm)], ['55', '56'])).
% 0.89/1.12  thf('58', plain, ((r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 0.89/1.12      inference('sup+', [status(thm)], ['15', '57'])).
% 0.89/1.12  thf('59', plain, ($false), inference('demod', [status(thm)], ['0', '58'])).
% 0.89/1.12  
% 0.89/1.12  % SZS output end Refutation
% 0.89/1.12  
% 0.97/1.13  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

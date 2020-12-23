%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4q6d5f877c

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:15 EST 2020

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 152 expanded)
%              Number of leaves         :   19 (  56 expanded)
%              Depth                    :   13
%              Number of atoms          :  590 (1231 expanded)
%              Number of equality atoms :   61 ( 128 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t76_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_xboole_0 @ A @ B )
       => ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t76_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('3',plain,(
    ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

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
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k4_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('12',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('13',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('15',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('16',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('17',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['10','19'])).

thf('21',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('24',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('26',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('27',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('33',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('36',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('37',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('39',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','43'])).

thf('45',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('50',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','43'])).

thf('52',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ),
    inference('sup+',[status(thm)],['48','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X1 ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','57'])).

thf('59',plain,(
    $false ),
    inference(demod,[status(thm)],['3','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4q6d5f877c
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:11:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.74/0.94  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.74/0.94  % Solved by: fo/fo7.sh
% 0.74/0.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.74/0.94  % done 1411 iterations in 0.493s
% 0.74/0.94  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.74/0.94  % SZS output start Refutation
% 0.74/0.94  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.74/0.94  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.74/0.94  thf(sk_B_type, type, sk_B: $i).
% 0.74/0.94  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.74/0.94  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.74/0.94  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.74/0.94  thf(sk_A_type, type, sk_A: $i).
% 0.74/0.94  thf(sk_C_type, type, sk_C: $i).
% 0.74/0.94  thf(t76_xboole_1, conjecture,
% 0.74/0.94    (![A:$i,B:$i,C:$i]:
% 0.74/0.94     ( ( r1_xboole_0 @ A @ B ) =>
% 0.74/0.94       ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ))).
% 0.74/0.94  thf(zf_stmt_0, negated_conjecture,
% 0.74/0.94    (~( ![A:$i,B:$i,C:$i]:
% 0.74/0.94        ( ( r1_xboole_0 @ A @ B ) =>
% 0.74/0.94          ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ) )),
% 0.74/0.94    inference('cnf.neg', [status(esa)], [t76_xboole_1])).
% 0.74/0.94  thf('0', plain,
% 0.74/0.94      (~ (r1_xboole_0 @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 0.74/0.94          (k3_xboole_0 @ sk_C @ sk_B))),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf(commutativity_k3_xboole_0, axiom,
% 0.74/0.94    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.74/0.94  thf('1', plain,
% 0.74/0.94      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.74/0.94      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.74/0.94  thf('2', plain,
% 0.74/0.94      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.74/0.94      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.74/0.94  thf('3', plain,
% 0.74/0.94      (~ (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_C) @ 
% 0.74/0.94          (k3_xboole_0 @ sk_B @ sk_C))),
% 0.74/0.94      inference('demod', [status(thm)], ['0', '1', '2'])).
% 0.74/0.94  thf(t47_xboole_1, axiom,
% 0.74/0.94    (![A:$i,B:$i]:
% 0.74/0.94     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.74/0.94  thf('4', plain,
% 0.74/0.94      (![X14 : $i, X15 : $i]:
% 0.74/0.94         ((k4_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15))
% 0.74/0.94           = (k4_xboole_0 @ X14 @ X15))),
% 0.74/0.94      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.74/0.94  thf(t39_xboole_1, axiom,
% 0.74/0.94    (![A:$i,B:$i]:
% 0.74/0.94     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.74/0.94  thf('5', plain,
% 0.74/0.94      (![X8 : $i, X9 : $i]:
% 0.74/0.94         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 0.74/0.94           = (k2_xboole_0 @ X8 @ X9))),
% 0.74/0.94      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.74/0.94  thf('6', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i]:
% 0.74/0.94         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.74/0.94           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 0.74/0.94      inference('sup+', [status(thm)], ['4', '5'])).
% 0.74/0.94  thf(commutativity_k2_xboole_0, axiom,
% 0.74/0.94    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.74/0.94  thf('7', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.74/0.94      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.74/0.94  thf('8', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i]:
% 0.74/0.94         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.74/0.94           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.74/0.94      inference('demod', [status(thm)], ['6', '7'])).
% 0.74/0.94  thf(t51_xboole_1, axiom,
% 0.74/0.94    (![A:$i,B:$i]:
% 0.74/0.94     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.74/0.94       ( A ) ))).
% 0.74/0.94  thf('9', plain,
% 0.74/0.94      (![X18 : $i, X19 : $i]:
% 0.74/0.94         ((k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ (k4_xboole_0 @ X18 @ X19))
% 0.74/0.94           = (X18))),
% 0.74/0.94      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.74/0.94  thf('10', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i]:
% 0.74/0.94         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 0.74/0.94      inference('sup+', [status(thm)], ['8', '9'])).
% 0.74/0.94  thf('11', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf(d7_xboole_0, axiom,
% 0.74/0.94    (![A:$i,B:$i]:
% 0.74/0.94     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.74/0.94       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.74/0.94  thf('12', plain,
% 0.74/0.94      (![X4 : $i, X5 : $i]:
% 0.74/0.94         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.74/0.94      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.74/0.94  thf('13', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.74/0.94      inference('sup-', [status(thm)], ['11', '12'])).
% 0.74/0.94  thf('14', plain,
% 0.74/0.94      (![X14 : $i, X15 : $i]:
% 0.74/0.94         ((k4_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15))
% 0.74/0.94           = (k4_xboole_0 @ X14 @ X15))),
% 0.74/0.94      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.74/0.94  thf('15', plain,
% 0.74/0.94      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.74/0.94      inference('sup+', [status(thm)], ['13', '14'])).
% 0.74/0.94  thf(t3_boole, axiom,
% 0.74/0.94    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.74/0.94  thf('16', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.74/0.94      inference('cnf', [status(esa)], [t3_boole])).
% 0.74/0.94  thf('17', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.74/0.94      inference('demod', [status(thm)], ['15', '16'])).
% 0.74/0.94  thf(t41_xboole_1, axiom,
% 0.74/0.94    (![A:$i,B:$i,C:$i]:
% 0.74/0.94     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.74/0.94       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.74/0.94  thf('18', plain,
% 0.74/0.94      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.74/0.94         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 0.74/0.94           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.74/0.94      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.74/0.94  thf('19', plain,
% 0.74/0.94      (![X0 : $i]:
% 0.74/0.94         ((k4_xboole_0 @ sk_A @ X0)
% 0.74/0.94           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.74/0.94      inference('sup+', [status(thm)], ['17', '18'])).
% 0.74/0.94  thf('20', plain,
% 0.74/0.94      (![X0 : $i]:
% 0.74/0.94         ((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0))
% 0.74/0.94           = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.74/0.94      inference('sup+', [status(thm)], ['10', '19'])).
% 0.74/0.94  thf('21', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.74/0.94      inference('demod', [status(thm)], ['15', '16'])).
% 0.74/0.94  thf('22', plain,
% 0.74/0.94      (![X0 : $i]: ((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)) = (sk_A))),
% 0.74/0.94      inference('demod', [status(thm)], ['20', '21'])).
% 0.74/0.94  thf('23', plain,
% 0.74/0.94      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.74/0.94         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 0.74/0.94           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.74/0.94      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.74/0.94  thf('24', plain,
% 0.74/0.94      (![X8 : $i, X9 : $i]:
% 0.74/0.94         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 0.74/0.94           = (k2_xboole_0 @ X8 @ X9))),
% 0.74/0.94      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.74/0.94  thf('25', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.94         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.74/0.94           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 0.74/0.94      inference('sup+', [status(thm)], ['23', '24'])).
% 0.74/0.94  thf(t48_xboole_1, axiom,
% 0.74/0.94    (![A:$i,B:$i]:
% 0.74/0.94     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.74/0.94  thf('26', plain,
% 0.74/0.94      (![X16 : $i, X17 : $i]:
% 0.74/0.94         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.74/0.94           = (k3_xboole_0 @ X16 @ X17))),
% 0.74/0.94      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.74/0.94  thf('27', plain,
% 0.74/0.94      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.74/0.94         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 0.74/0.94           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.74/0.94      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.74/0.94  thf('28', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.94         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.74/0.94           = (k4_xboole_0 @ X2 @ 
% 0.74/0.94              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))))),
% 0.74/0.94      inference('sup+', [status(thm)], ['26', '27'])).
% 0.74/0.94  thf('29', plain,
% 0.74/0.94      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.74/0.94         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 0.74/0.94           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.74/0.94      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.74/0.94  thf('30', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.94         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.74/0.94           = (k4_xboole_0 @ X2 @ 
% 0.74/0.94              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 0.74/0.94      inference('demod', [status(thm)], ['28', '29'])).
% 0.74/0.94  thf('31', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i]:
% 0.74/0.94         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.74/0.94           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.74/0.94      inference('sup+', [status(thm)], ['25', '30'])).
% 0.74/0.94  thf('32', plain,
% 0.74/0.94      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.74/0.94      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.74/0.94  thf('33', plain,
% 0.74/0.94      (![X8 : $i, X9 : $i]:
% 0.74/0.94         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 0.74/0.94           = (k2_xboole_0 @ X8 @ X9))),
% 0.74/0.94      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.74/0.94  thf('34', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i]:
% 0.74/0.94         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.74/0.94           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.74/0.94      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.74/0.94  thf('35', plain,
% 0.74/0.94      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.74/0.94         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 0.74/0.94           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.74/0.94      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.74/0.94  thf('36', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.74/0.94      inference('cnf', [status(esa)], [t3_boole])).
% 0.74/0.94  thf('37', plain,
% 0.74/0.94      (![X16 : $i, X17 : $i]:
% 0.74/0.94         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.74/0.94           = (k3_xboole_0 @ X16 @ X17))),
% 0.74/0.94      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.74/0.94  thf('38', plain,
% 0.74/0.94      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.74/0.94      inference('sup+', [status(thm)], ['36', '37'])).
% 0.74/0.94  thf(t2_boole, axiom,
% 0.74/0.94    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.74/0.94  thf('39', plain,
% 0.74/0.94      (![X7 : $i]: ((k3_xboole_0 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 0.74/0.94      inference('cnf', [status(esa)], [t2_boole])).
% 0.74/0.94  thf('40', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.74/0.94      inference('demod', [status(thm)], ['38', '39'])).
% 0.74/0.94  thf('41', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i]:
% 0.74/0.94         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 0.74/0.94           = (k1_xboole_0))),
% 0.74/0.94      inference('sup+', [status(thm)], ['35', '40'])).
% 0.74/0.94  thf('42', plain,
% 0.74/0.94      (![X8 : $i, X9 : $i]:
% 0.74/0.94         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 0.74/0.94           = (k2_xboole_0 @ X8 @ X9))),
% 0.74/0.94      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.74/0.94  thf('43', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i]:
% 0.74/0.94         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.74/0.94      inference('demod', [status(thm)], ['41', '42'])).
% 0.74/0.94  thf('44', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i]:
% 0.74/0.94         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.74/0.94      inference('demod', [status(thm)], ['34', '43'])).
% 0.74/0.94  thf('45', plain,
% 0.74/0.94      (![X14 : $i, X15 : $i]:
% 0.74/0.94         ((k4_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15))
% 0.74/0.94           = (k4_xboole_0 @ X14 @ X15))),
% 0.74/0.94      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.74/0.94  thf('46', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i]:
% 0.74/0.94         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.74/0.94           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.74/0.94      inference('sup+', [status(thm)], ['44', '45'])).
% 0.74/0.94  thf('47', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.74/0.94      inference('cnf', [status(esa)], [t3_boole])).
% 0.74/0.94  thf('48', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i]:
% 0.74/0.94         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.74/0.94      inference('demod', [status(thm)], ['46', '47'])).
% 0.74/0.94  thf('49', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i]:
% 0.74/0.94         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 0.74/0.94      inference('sup+', [status(thm)], ['8', '9'])).
% 0.74/0.94  thf('50', plain,
% 0.74/0.94      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.74/0.94         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 0.74/0.94           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.74/0.94      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.74/0.94  thf('51', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i]:
% 0.74/0.94         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.74/0.94      inference('demod', [status(thm)], ['34', '43'])).
% 0.74/0.94  thf('52', plain,
% 0.74/0.94      (![X4 : $i, X6 : $i]:
% 0.74/0.94         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 0.74/0.94      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.74/0.94  thf('53', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i]:
% 0.74/0.94         (((k1_xboole_0) != (k1_xboole_0))
% 0.74/0.94          | (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.74/0.94      inference('sup-', [status(thm)], ['51', '52'])).
% 0.74/0.94  thf('54', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.74/0.94      inference('simplify', [status(thm)], ['53'])).
% 0.74/0.94  thf('55', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.94         (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.74/0.94      inference('sup+', [status(thm)], ['50', '54'])).
% 0.74/0.94  thf('56', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.94         (r1_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X2 @ X0))),
% 0.74/0.94      inference('sup+', [status(thm)], ['49', '55'])).
% 0.74/0.94  thf('57', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.94         (r1_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X0)),
% 0.74/0.94      inference('sup+', [status(thm)], ['48', '56'])).
% 0.74/0.94  thf('58', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i]:
% 0.74/0.94         (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ X1) @ (k3_xboole_0 @ sk_B @ X0))),
% 0.74/0.94      inference('sup+', [status(thm)], ['22', '57'])).
% 0.74/0.94  thf('59', plain, ($false), inference('demod', [status(thm)], ['3', '58'])).
% 0.74/0.94  
% 0.74/0.94  % SZS output end Refutation
% 0.74/0.94  
% 0.74/0.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

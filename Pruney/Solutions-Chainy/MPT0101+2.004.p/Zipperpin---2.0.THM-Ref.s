%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZLGxlltIRx

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:55 EST 2020

% Result     : Theorem 32.93s
% Output     : Refutation 32.93s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 248 expanded)
%              Number of leaves         :   20 (  91 expanded)
%              Depth                    :   17
%              Number of atoms          :  534 (1786 expanded)
%              Number of equality atoms :   65 ( 237 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t94_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ A @ B )
        = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t94_xboole_1])).

thf('0',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l97_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X6 @ X7 ) @ ( k5_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k4_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X9 @ X10 ) @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('7',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('12',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X9 @ X10 ) @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('19',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('20',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('23',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k4_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','24'])).

thf('26',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','24'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28','31'])).

thf(t93_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('33',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ ( k3_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','24'])).

thf('38',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('41',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28','31'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('46',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','44','45','46'])).

thf('48',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ ( k3_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ ( k3_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','52'])).

thf('54',plain,(
    $false ),
    inference(simplify,[status(thm)],['53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZLGxlltIRx
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:35:27 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.33  % Python version: Python 3.6.8
% 0.13/0.33  % Running in FO mode
% 32.93/33.13  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 32.93/33.13  % Solved by: fo/fo7.sh
% 32.93/33.13  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 32.93/33.13  % done 13577 iterations in 32.694s
% 32.93/33.13  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 32.93/33.13  % SZS output start Refutation
% 32.93/33.13  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 32.93/33.13  thf(sk_A_type, type, sk_A: $i).
% 32.93/33.13  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 32.93/33.13  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 32.93/33.13  thf(sk_B_type, type, sk_B: $i).
% 32.93/33.13  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 32.93/33.13  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 32.93/33.13  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 32.93/33.13  thf(t94_xboole_1, conjecture,
% 32.93/33.13    (![A:$i,B:$i]:
% 32.93/33.13     ( ( k2_xboole_0 @ A @ B ) =
% 32.93/33.13       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 32.93/33.13  thf(zf_stmt_0, negated_conjecture,
% 32.93/33.13    (~( ![A:$i,B:$i]:
% 32.93/33.13        ( ( k2_xboole_0 @ A @ B ) =
% 32.93/33.13          ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 32.93/33.13    inference('cnf.neg', [status(esa)], [t94_xboole_1])).
% 32.93/33.13  thf('0', plain,
% 32.93/33.13      (((k2_xboole_0 @ sk_A @ sk_B)
% 32.93/33.13         != (k5_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ 
% 32.93/33.13             (k3_xboole_0 @ sk_A @ sk_B)))),
% 32.93/33.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.93/33.13  thf(l97_xboole_1, axiom,
% 32.93/33.13    (![A:$i,B:$i]:
% 32.93/33.13     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 32.93/33.13  thf('1', plain,
% 32.93/33.13      (![X6 : $i, X7 : $i]:
% 32.93/33.13         (r1_xboole_0 @ (k3_xboole_0 @ X6 @ X7) @ (k5_xboole_0 @ X6 @ X7))),
% 32.93/33.13      inference('cnf', [status(esa)], [l97_xboole_1])).
% 32.93/33.13  thf(t83_xboole_1, axiom,
% 32.93/33.13    (![A:$i,B:$i]:
% 32.93/33.13     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 32.93/33.13  thf('2', plain,
% 32.93/33.13      (![X21 : $i, X22 : $i]:
% 32.93/33.13         (((k4_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_xboole_0 @ X21 @ X22))),
% 32.93/33.13      inference('cnf', [status(esa)], [t83_xboole_1])).
% 32.93/33.13  thf('3', plain,
% 32.93/33.13      (![X0 : $i, X1 : $i]:
% 32.93/33.13         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 32.93/33.13           = (k3_xboole_0 @ X1 @ X0))),
% 32.93/33.13      inference('sup-', [status(thm)], ['1', '2'])).
% 32.93/33.13  thf(t48_xboole_1, axiom,
% 32.93/33.13    (![A:$i,B:$i]:
% 32.93/33.13     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 32.93/33.13  thf('4', plain,
% 32.93/33.13      (![X14 : $i, X15 : $i]:
% 32.93/33.13         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 32.93/33.13           = (k3_xboole_0 @ X14 @ X15))),
% 32.93/33.13      inference('cnf', [status(esa)], [t48_xboole_1])).
% 32.93/33.13  thf('5', plain,
% 32.93/33.13      (![X0 : $i, X1 : $i]:
% 32.93/33.13         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 32.93/33.13           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)))),
% 32.93/33.13      inference('sup+', [status(thm)], ['3', '4'])).
% 32.93/33.13  thf(t40_xboole_1, axiom,
% 32.93/33.13    (![A:$i,B:$i]:
% 32.93/33.13     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 32.93/33.13  thf('6', plain,
% 32.93/33.13      (![X9 : $i, X10 : $i]:
% 32.93/33.13         ((k4_xboole_0 @ (k2_xboole_0 @ X9 @ X10) @ X10)
% 32.93/33.13           = (k4_xboole_0 @ X9 @ X10))),
% 32.93/33.13      inference('cnf', [status(esa)], [t40_xboole_1])).
% 32.93/33.13  thf(t3_boole, axiom,
% 32.93/33.13    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 32.93/33.13  thf('7', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 32.93/33.13      inference('cnf', [status(esa)], [t3_boole])).
% 32.93/33.13  thf('8', plain,
% 32.93/33.13      (![X0 : $i]:
% 32.93/33.13         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 32.93/33.13      inference('sup+', [status(thm)], ['6', '7'])).
% 32.93/33.13  thf('9', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 32.93/33.13      inference('cnf', [status(esa)], [t3_boole])).
% 32.93/33.13  thf('10', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 32.93/33.13      inference('sup+', [status(thm)], ['8', '9'])).
% 32.93/33.13  thf(commutativity_k2_xboole_0, axiom,
% 32.93/33.13    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 32.93/33.13  thf('11', plain,
% 32.93/33.13      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 32.93/33.13      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 32.93/33.13  thf('12', plain,
% 32.93/33.13      (![X9 : $i, X10 : $i]:
% 32.93/33.13         ((k4_xboole_0 @ (k2_xboole_0 @ X9 @ X10) @ X10)
% 32.93/33.13           = (k4_xboole_0 @ X9 @ X10))),
% 32.93/33.13      inference('cnf', [status(esa)], [t40_xboole_1])).
% 32.93/33.13  thf('13', plain,
% 32.93/33.13      (![X0 : $i, X1 : $i]:
% 32.93/33.13         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 32.93/33.13           = (k4_xboole_0 @ X0 @ X1))),
% 32.93/33.13      inference('sup+', [status(thm)], ['11', '12'])).
% 32.93/33.13  thf('14', plain,
% 32.93/33.13      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 32.93/33.13      inference('sup+', [status(thm)], ['10', '13'])).
% 32.93/33.13  thf('15', plain,
% 32.93/33.13      (![X14 : $i, X15 : $i]:
% 32.93/33.13         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 32.93/33.13           = (k3_xboole_0 @ X14 @ X15))),
% 32.93/33.13      inference('cnf', [status(esa)], [t48_xboole_1])).
% 32.93/33.13  thf('16', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 32.93/33.13      inference('cnf', [status(esa)], [t3_boole])).
% 32.93/33.13  thf(d6_xboole_0, axiom,
% 32.93/33.13    (![A:$i,B:$i]:
% 32.93/33.13     ( ( k5_xboole_0 @ A @ B ) =
% 32.93/33.13       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 32.93/33.13  thf('17', plain,
% 32.93/33.13      (![X4 : $i, X5 : $i]:
% 32.93/33.13         ((k5_xboole_0 @ X4 @ X5)
% 32.93/33.13           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 32.93/33.13      inference('cnf', [status(esa)], [d6_xboole_0])).
% 32.93/33.13  thf('18', plain,
% 32.93/33.13      (![X0 : $i]:
% 32.93/33.13         ((k5_xboole_0 @ X0 @ k1_xboole_0)
% 32.93/33.13           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 32.93/33.13      inference('sup+', [status(thm)], ['16', '17'])).
% 32.93/33.13  thf(t5_boole, axiom,
% 32.93/33.13    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 32.93/33.13  thf('19', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 32.93/33.13      inference('cnf', [status(esa)], [t5_boole])).
% 32.93/33.13  thf('20', plain,
% 32.93/33.13      (![X0 : $i]:
% 32.93/33.13         ((X0) = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 32.93/33.13      inference('demod', [status(thm)], ['18', '19'])).
% 32.93/33.13  thf('21', plain,
% 32.93/33.13      (![X0 : $i]:
% 32.93/33.13         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 32.93/33.13           = (k2_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0) @ 
% 32.93/33.13              (k3_xboole_0 @ k1_xboole_0 @ X0)))),
% 32.93/33.13      inference('sup+', [status(thm)], ['15', '20'])).
% 32.93/33.13  thf('22', plain,
% 32.93/33.13      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 32.93/33.13      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 32.93/33.13  thf(t51_xboole_1, axiom,
% 32.93/33.13    (![A:$i,B:$i]:
% 32.93/33.13     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 32.93/33.13       ( A ) ))).
% 32.93/33.13  thf('23', plain,
% 32.93/33.13      (![X16 : $i, X17 : $i]:
% 32.93/33.13         ((k2_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ (k4_xboole_0 @ X16 @ X17))
% 32.93/33.13           = (X16))),
% 32.93/33.13      inference('cnf', [status(esa)], [t51_xboole_1])).
% 32.93/33.13  thf('24', plain,
% 32.93/33.13      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 32.93/33.13      inference('demod', [status(thm)], ['21', '22', '23'])).
% 32.93/33.13  thf('25', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 32.93/33.13      inference('demod', [status(thm)], ['14', '24'])).
% 32.93/33.13  thf('26', plain,
% 32.93/33.13      (![X4 : $i, X5 : $i]:
% 32.93/33.13         ((k5_xboole_0 @ X4 @ X5)
% 32.93/33.13           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 32.93/33.13      inference('cnf', [status(esa)], [d6_xboole_0])).
% 32.93/33.13  thf('27', plain,
% 32.93/33.13      (![X0 : $i]:
% 32.93/33.13         ((k5_xboole_0 @ X0 @ X0)
% 32.93/33.13           = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ X0)))),
% 32.93/33.13      inference('sup+', [status(thm)], ['25', '26'])).
% 32.93/33.13  thf('28', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 32.93/33.13      inference('demod', [status(thm)], ['14', '24'])).
% 32.93/33.13  thf('29', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 32.93/33.13      inference('sup+', [status(thm)], ['8', '9'])).
% 32.93/33.13  thf('30', plain,
% 32.93/33.13      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 32.93/33.13      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 32.93/33.13  thf('31', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 32.93/33.13      inference('sup+', [status(thm)], ['29', '30'])).
% 32.93/33.13  thf('32', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 32.93/33.13      inference('demod', [status(thm)], ['27', '28', '31'])).
% 32.93/33.13  thf(t93_xboole_1, axiom,
% 32.93/33.13    (![A:$i,B:$i]:
% 32.93/33.13     ( ( k2_xboole_0 @ A @ B ) =
% 32.93/33.13       ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 32.93/33.13  thf('33', plain,
% 32.93/33.13      (![X24 : $i, X25 : $i]:
% 32.93/33.13         ((k2_xboole_0 @ X24 @ X25)
% 32.93/33.13           = (k2_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ 
% 32.93/33.13              (k3_xboole_0 @ X24 @ X25)))),
% 32.93/33.13      inference('cnf', [status(esa)], [t93_xboole_1])).
% 32.93/33.13  thf('34', plain,
% 32.93/33.13      (![X0 : $i]:
% 32.93/33.13         ((k2_xboole_0 @ X0 @ X0)
% 32.93/33.13           = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X0 @ X0)))),
% 32.93/33.13      inference('sup+', [status(thm)], ['32', '33'])).
% 32.93/33.13  thf('35', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 32.93/33.13      inference('sup+', [status(thm)], ['29', '30'])).
% 32.93/33.13  thf('36', plain,
% 32.93/33.13      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ X0))),
% 32.93/33.13      inference('demod', [status(thm)], ['34', '35'])).
% 32.93/33.13  thf('37', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 32.93/33.13      inference('demod', [status(thm)], ['14', '24'])).
% 32.93/33.13  thf('38', plain,
% 32.93/33.13      (![X14 : $i, X15 : $i]:
% 32.93/33.13         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 32.93/33.13           = (k3_xboole_0 @ X14 @ X15))),
% 32.93/33.13      inference('cnf', [status(esa)], [t48_xboole_1])).
% 32.93/33.13  thf('39', plain,
% 32.93/33.13      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 32.93/33.13      inference('sup+', [status(thm)], ['37', '38'])).
% 32.93/33.13  thf('40', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 32.93/33.13      inference('cnf', [status(esa)], [t3_boole])).
% 32.93/33.13  thf('41', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 32.93/33.13      inference('demod', [status(thm)], ['39', '40'])).
% 32.93/33.13  thf('42', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 32.93/33.13      inference('demod', [status(thm)], ['36', '41'])).
% 32.93/33.13  thf('43', plain,
% 32.93/33.13      (![X4 : $i, X5 : $i]:
% 32.93/33.13         ((k5_xboole_0 @ X4 @ X5)
% 32.93/33.13           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 32.93/33.13      inference('cnf', [status(esa)], [d6_xboole_0])).
% 32.93/33.13  thf('44', plain,
% 32.93/33.13      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 32.93/33.13      inference('sup+', [status(thm)], ['42', '43'])).
% 32.93/33.13  thf('45', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 32.93/33.13      inference('demod', [status(thm)], ['27', '28', '31'])).
% 32.93/33.13  thf(commutativity_k3_xboole_0, axiom,
% 32.93/33.13    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 32.93/33.13  thf('46', plain,
% 32.93/33.13      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 32.93/33.13      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 32.93/33.13  thf('47', plain,
% 32.93/33.13      (![X0 : $i, X1 : $i]:
% 32.93/33.13         ((k1_xboole_0)
% 32.93/33.13           = (k3_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 32.93/33.13      inference('demod', [status(thm)], ['5', '44', '45', '46'])).
% 32.93/33.13  thf('48', plain,
% 32.93/33.13      (![X24 : $i, X25 : $i]:
% 32.93/33.13         ((k2_xboole_0 @ X24 @ X25)
% 32.93/33.13           = (k2_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ 
% 32.93/33.13              (k3_xboole_0 @ X24 @ X25)))),
% 32.93/33.13      inference('cnf', [status(esa)], [t93_xboole_1])).
% 32.93/33.13  thf('49', plain,
% 32.93/33.13      (![X0 : $i, X1 : $i]:
% 32.93/33.13         ((k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 32.93/33.13           = (k2_xboole_0 @ 
% 32.93/33.13              (k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)) @ 
% 32.93/33.13              k1_xboole_0))),
% 32.93/33.13      inference('sup+', [status(thm)], ['47', '48'])).
% 32.93/33.13  thf('50', plain,
% 32.93/33.13      (![X24 : $i, X25 : $i]:
% 32.93/33.13         ((k2_xboole_0 @ X24 @ X25)
% 32.93/33.13           = (k2_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ 
% 32.93/33.13              (k3_xboole_0 @ X24 @ X25)))),
% 32.93/33.13      inference('cnf', [status(esa)], [t93_xboole_1])).
% 32.93/33.13  thf('51', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 32.93/33.13      inference('sup+', [status(thm)], ['8', '9'])).
% 32.93/33.13  thf('52', plain,
% 32.93/33.13      (![X0 : $i, X1 : $i]:
% 32.93/33.13         ((k2_xboole_0 @ X1 @ X0)
% 32.93/33.13           = (k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 32.93/33.13      inference('demod', [status(thm)], ['49', '50', '51'])).
% 32.93/33.13  thf('53', plain,
% 32.93/33.13      (((k2_xboole_0 @ sk_A @ sk_B) != (k2_xboole_0 @ sk_A @ sk_B))),
% 32.93/33.13      inference('demod', [status(thm)], ['0', '52'])).
% 32.93/33.13  thf('54', plain, ($false), inference('simplify', [status(thm)], ['53'])).
% 32.93/33.13  
% 32.93/33.13  % SZS output end Refutation
% 32.93/33.13  
% 32.93/33.14  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

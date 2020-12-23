%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.n7KiIAsYtd

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:18 EST 2020

% Result     : Theorem 0.96s
% Output     : Refutation 0.96s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 113 expanded)
%              Number of leaves         :   17 (  42 expanded)
%              Depth                    :   13
%              Number of atoms          :  467 ( 904 expanded)
%              Number of equality atoms :   37 (  74 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('2',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','6'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('8',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('12',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ ( k3_xboole_0 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('13',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ( r1_xboole_0 @ X17 @ X18 )
      | ~ ( r1_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ X3 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_xboole_0 @ X3 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ X3 @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_xboole_0 @ X3 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('25',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('28',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('30',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ ( k3_xboole_0 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('31',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ( r1_xboole_0 @ X17 @ X20 )
      | ~ ( r1_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ X3 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_xboole_0 @ X3 @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['23','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','35'])).

thf('37',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('39',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('41',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('43',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ X3 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_xboole_0 @ X3 @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ sk_A ) )
      | ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['0','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.n7KiIAsYtd
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:26:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.96/1.16  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.96/1.16  % Solved by: fo/fo7.sh
% 0.96/1.16  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.96/1.16  % done 2109 iterations in 0.735s
% 0.96/1.16  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.96/1.16  % SZS output start Refutation
% 0.96/1.16  thf(sk_A_type, type, sk_A: $i).
% 0.96/1.16  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.96/1.16  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.96/1.16  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.96/1.16  thf(sk_C_type, type, sk_C: $i).
% 0.96/1.16  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.96/1.16  thf(sk_B_type, type, sk_B: $i).
% 0.96/1.16  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.96/1.16  thf(t76_xboole_1, conjecture,
% 0.96/1.16    (![A:$i,B:$i,C:$i]:
% 0.96/1.16     ( ( r1_xboole_0 @ A @ B ) =>
% 0.96/1.16       ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ))).
% 0.96/1.16  thf(zf_stmt_0, negated_conjecture,
% 0.96/1.16    (~( ![A:$i,B:$i,C:$i]:
% 0.96/1.16        ( ( r1_xboole_0 @ A @ B ) =>
% 0.96/1.16          ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ) )),
% 0.96/1.16    inference('cnf.neg', [status(esa)], [t76_xboole_1])).
% 0.96/1.16  thf('0', plain,
% 0.96/1.16      (~ (r1_xboole_0 @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 0.96/1.16          (k3_xboole_0 @ sk_C @ sk_B))),
% 0.96/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.16  thf(t49_xboole_1, axiom,
% 0.96/1.16    (![A:$i,B:$i,C:$i]:
% 0.96/1.16     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.96/1.16       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.96/1.16  thf('1', plain,
% 0.96/1.16      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.96/1.16         ((k3_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X13))
% 0.96/1.16           = (k4_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13))),
% 0.96/1.16      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.96/1.16  thf(t3_boole, axiom,
% 0.96/1.16    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.96/1.16  thf('2', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.96/1.16      inference('cnf', [status(esa)], [t3_boole])).
% 0.96/1.16  thf(t48_xboole_1, axiom,
% 0.96/1.16    (![A:$i,B:$i]:
% 0.96/1.16     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.96/1.16  thf('3', plain,
% 0.96/1.16      (![X9 : $i, X10 : $i]:
% 0.96/1.16         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.96/1.16           = (k3_xboole_0 @ X9 @ X10))),
% 0.96/1.16      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.96/1.16  thf('4', plain,
% 0.96/1.16      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.96/1.16      inference('sup+', [status(thm)], ['2', '3'])).
% 0.96/1.16  thf(t2_boole, axiom,
% 0.96/1.16    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.96/1.16  thf('5', plain,
% 0.96/1.16      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.96/1.16      inference('cnf', [status(esa)], [t2_boole])).
% 0.96/1.16  thf('6', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.96/1.16      inference('demod', [status(thm)], ['4', '5'])).
% 0.96/1.16  thf('7', plain,
% 0.96/1.16      (![X0 : $i, X1 : $i]:
% 0.96/1.16         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 0.96/1.16           = (k1_xboole_0))),
% 0.96/1.16      inference('sup+', [status(thm)], ['1', '6'])).
% 0.96/1.16  thf(d7_xboole_0, axiom,
% 0.96/1.16    (![A:$i,B:$i]:
% 0.96/1.16     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.96/1.16       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.96/1.16  thf('8', plain,
% 0.96/1.16      (![X0 : $i, X2 : $i]:
% 0.96/1.16         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.96/1.16      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.96/1.16  thf('9', plain,
% 0.96/1.16      (![X0 : $i, X1 : $i]:
% 0.96/1.16         (((k1_xboole_0) != (k1_xboole_0))
% 0.96/1.16          | (r1_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.96/1.16      inference('sup-', [status(thm)], ['7', '8'])).
% 0.96/1.16  thf('10', plain,
% 0.96/1.16      (![X0 : $i, X1 : $i]:
% 0.96/1.16         (r1_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.96/1.16      inference('simplify', [status(thm)], ['9'])).
% 0.96/1.16  thf('11', plain,
% 0.96/1.16      (![X9 : $i, X10 : $i]:
% 0.96/1.16         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.96/1.16           = (k3_xboole_0 @ X9 @ X10))),
% 0.96/1.16      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.96/1.16  thf(t52_xboole_1, axiom,
% 0.96/1.16    (![A:$i,B:$i,C:$i]:
% 0.96/1.16     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.96/1.16       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.96/1.16  thf('12', plain,
% 0.96/1.16      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.96/1.16         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X16))
% 0.96/1.16           = (k2_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ 
% 0.96/1.16              (k3_xboole_0 @ X14 @ X16)))),
% 0.96/1.16      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.96/1.16  thf(t70_xboole_1, axiom,
% 0.96/1.16    (![A:$i,B:$i,C:$i]:
% 0.96/1.16     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.96/1.16            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.96/1.16       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.96/1.16            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.96/1.16  thf('13', plain,
% 0.96/1.16      (![X17 : $i, X18 : $i, X20 : $i]:
% 0.96/1.16         ((r1_xboole_0 @ X17 @ X18)
% 0.96/1.16          | ~ (r1_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X20)))),
% 0.96/1.16      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.96/1.16  thf('14', plain,
% 0.96/1.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.96/1.16         (~ (r1_xboole_0 @ X3 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 0.96/1.16          | (r1_xboole_0 @ X3 @ (k4_xboole_0 @ X2 @ X1)))),
% 0.96/1.16      inference('sup-', [status(thm)], ['12', '13'])).
% 0.96/1.16  thf('15', plain,
% 0.96/1.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.96/1.16         (~ (r1_xboole_0 @ X3 @ (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.96/1.16          | (r1_xboole_0 @ X3 @ (k4_xboole_0 @ X2 @ X1)))),
% 0.96/1.16      inference('sup-', [status(thm)], ['11', '14'])).
% 0.96/1.16  thf('16', plain,
% 0.96/1.16      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1))),
% 0.96/1.16      inference('sup-', [status(thm)], ['10', '15'])).
% 0.96/1.16  thf('17', plain,
% 0.96/1.16      (![X0 : $i, X1 : $i]:
% 0.96/1.16         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.96/1.16      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.96/1.16  thf('18', plain,
% 0.96/1.16      (![X0 : $i, X1 : $i]:
% 0.96/1.16         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.96/1.16      inference('sup-', [status(thm)], ['16', '17'])).
% 0.96/1.16  thf(t47_xboole_1, axiom,
% 0.96/1.16    (![A:$i,B:$i]:
% 0.96/1.16     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.96/1.16  thf('19', plain,
% 0.96/1.16      (![X7 : $i, X8 : $i]:
% 0.96/1.16         ((k4_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8))
% 0.96/1.16           = (k4_xboole_0 @ X7 @ X8))),
% 0.96/1.16      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.96/1.16  thf('20', plain,
% 0.96/1.16      (![X0 : $i, X1 : $i]:
% 0.96/1.16         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.96/1.16           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.96/1.16      inference('sup+', [status(thm)], ['18', '19'])).
% 0.96/1.16  thf('21', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.96/1.16      inference('cnf', [status(esa)], [t3_boole])).
% 0.96/1.16  thf('22', plain,
% 0.96/1.16      (![X0 : $i, X1 : $i]:
% 0.96/1.16         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.96/1.16      inference('demod', [status(thm)], ['20', '21'])).
% 0.96/1.16  thf('23', plain,
% 0.96/1.16      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.96/1.16         ((k3_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X13))
% 0.96/1.16           = (k4_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13))),
% 0.96/1.16      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.96/1.16  thf('24', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.96/1.16      inference('demod', [status(thm)], ['4', '5'])).
% 0.96/1.16  thf('25', plain,
% 0.96/1.16      (![X9 : $i, X10 : $i]:
% 0.96/1.16         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.96/1.16           = (k3_xboole_0 @ X9 @ X10))),
% 0.96/1.16      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.96/1.16  thf('26', plain,
% 0.96/1.16      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.96/1.16      inference('sup+', [status(thm)], ['24', '25'])).
% 0.96/1.16  thf('27', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.96/1.16      inference('cnf', [status(esa)], [t3_boole])).
% 0.96/1.16  thf('28', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.96/1.16      inference('demod', [status(thm)], ['26', '27'])).
% 0.96/1.16  thf('29', plain,
% 0.96/1.16      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1))),
% 0.96/1.16      inference('sup-', [status(thm)], ['10', '15'])).
% 0.96/1.16  thf('30', plain,
% 0.96/1.16      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.96/1.16         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X16))
% 0.96/1.16           = (k2_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ 
% 0.96/1.16              (k3_xboole_0 @ X14 @ X16)))),
% 0.96/1.16      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.96/1.16  thf('31', plain,
% 0.96/1.16      (![X17 : $i, X18 : $i, X20 : $i]:
% 0.96/1.16         ((r1_xboole_0 @ X17 @ X20)
% 0.96/1.16          | ~ (r1_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X20)))),
% 0.96/1.16      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.96/1.16  thf('32', plain,
% 0.96/1.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.96/1.16         (~ (r1_xboole_0 @ X3 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 0.96/1.16          | (r1_xboole_0 @ X3 @ (k3_xboole_0 @ X2 @ X0)))),
% 0.96/1.16      inference('sup-', [status(thm)], ['30', '31'])).
% 0.96/1.16  thf('33', plain,
% 0.96/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.96/1.16         (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X2 @ X0))),
% 0.96/1.16      inference('sup-', [status(thm)], ['29', '32'])).
% 0.96/1.16  thf('34', plain,
% 0.96/1.16      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.96/1.16      inference('sup+', [status(thm)], ['28', '33'])).
% 0.96/1.16  thf('35', plain,
% 0.96/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.96/1.16         (r1_xboole_0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0)),
% 0.96/1.16      inference('sup+', [status(thm)], ['23', '34'])).
% 0.96/1.16  thf('36', plain,
% 0.96/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.96/1.16         (r1_xboole_0 @ (k3_xboole_0 @ X2 @ X0) @ (k4_xboole_0 @ X1 @ X0))),
% 0.96/1.16      inference('sup+', [status(thm)], ['22', '35'])).
% 0.96/1.16  thf('37', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.96/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.16  thf('38', plain,
% 0.96/1.16      (![X0 : $i, X1 : $i]:
% 0.96/1.16         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.96/1.16      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.96/1.16  thf('39', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.96/1.16      inference('sup-', [status(thm)], ['37', '38'])).
% 0.96/1.16  thf('40', plain,
% 0.96/1.16      (![X7 : $i, X8 : $i]:
% 0.96/1.16         ((k4_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8))
% 0.96/1.16           = (k4_xboole_0 @ X7 @ X8))),
% 0.96/1.16      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.96/1.16  thf('41', plain,
% 0.96/1.16      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.96/1.16      inference('sup+', [status(thm)], ['39', '40'])).
% 0.96/1.16  thf('42', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.96/1.16      inference('cnf', [status(esa)], [t3_boole])).
% 0.96/1.16  thf('43', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.96/1.16      inference('demod', [status(thm)], ['41', '42'])).
% 0.96/1.16  thf('44', plain,
% 0.96/1.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.96/1.16         (~ (r1_xboole_0 @ X3 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 0.96/1.16          | (r1_xboole_0 @ X3 @ (k3_xboole_0 @ X2 @ X0)))),
% 0.96/1.16      inference('sup-', [status(thm)], ['30', '31'])).
% 0.96/1.16  thf('45', plain,
% 0.96/1.16      (![X0 : $i, X1 : $i]:
% 0.96/1.16         (~ (r1_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ sk_A))
% 0.96/1.16          | (r1_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ sk_B)))),
% 0.96/1.16      inference('sup-', [status(thm)], ['43', '44'])).
% 0.96/1.16  thf('46', plain,
% 0.96/1.16      (![X0 : $i, X1 : $i]:
% 0.96/1.16         (r1_xboole_0 @ (k3_xboole_0 @ X1 @ sk_A) @ (k3_xboole_0 @ X0 @ sk_B))),
% 0.96/1.16      inference('sup-', [status(thm)], ['36', '45'])).
% 0.96/1.16  thf('47', plain, ($false), inference('demod', [status(thm)], ['0', '46'])).
% 0.96/1.16  
% 0.96/1.16  % SZS output end Refutation
% 0.96/1.16  
% 1.00/1.17  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

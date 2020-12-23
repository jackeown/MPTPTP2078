%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yOPWbaR0t4

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:37 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 117 expanded)
%              Number of leaves         :   16 (  44 expanded)
%              Depth                    :   15
%              Number of atoms          :  474 ( 799 expanded)
%              Number of equality atoms :   39 (  71 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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

thf('1',plain,(
    r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('4',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ ( k4_xboole_0 @ X17 @ X18 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('5',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) )
    = sk_A ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('6',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('7',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ X20 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ ( k4_xboole_0 @ X17 @ X18 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['5','14'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ X20 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('19',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ ( k4_xboole_0 @ X17 @ X18 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ ( k4_xboole_0 @ X17 @ X18 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('28',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('29',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ X20 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','31'])).

thf('33',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','34'])).

thf('36',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ ( k4_xboole_0 @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('40',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('41',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('42',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ ( k4_xboole_0 @ X17 @ X18 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf('45',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) ) )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['39','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('47',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['47','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['0','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yOPWbaR0t4
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:54:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.66/1.91  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.66/1.91  % Solved by: fo/fo7.sh
% 1.66/1.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.66/1.91  % done 3098 iterations in 1.448s
% 1.66/1.91  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.66/1.91  % SZS output start Refutation
% 1.66/1.91  thf(sk_B_type, type, sk_B: $i).
% 1.66/1.91  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.66/1.91  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.66/1.91  thf(sk_C_type, type, sk_C: $i).
% 1.66/1.91  thf(sk_A_type, type, sk_A: $i).
% 1.66/1.91  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.66/1.91  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.66/1.91  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.66/1.91  thf(t81_xboole_1, conjecture,
% 1.66/1.91    (![A:$i,B:$i,C:$i]:
% 1.66/1.91     ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 1.66/1.91       ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ))).
% 1.66/1.91  thf(zf_stmt_0, negated_conjecture,
% 1.66/1.91    (~( ![A:$i,B:$i,C:$i]:
% 1.66/1.91        ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 1.66/1.91          ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )),
% 1.66/1.91    inference('cnf.neg', [status(esa)], [t81_xboole_1])).
% 1.66/1.91  thf('0', plain, (~ (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 1.66/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.91  thf('1', plain, ((r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 1.66/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.91  thf(d7_xboole_0, axiom,
% 1.66/1.91    (![A:$i,B:$i]:
% 1.66/1.91     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.66/1.91       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.66/1.91  thf('2', plain,
% 1.66/1.91      (![X0 : $i, X1 : $i]:
% 1.66/1.91         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.66/1.91      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.66/1.91  thf('3', plain,
% 1.66/1.91      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 1.66/1.91      inference('sup-', [status(thm)], ['1', '2'])).
% 1.66/1.91  thf(t51_xboole_1, axiom,
% 1.66/1.91    (![A:$i,B:$i]:
% 1.66/1.91     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 1.66/1.91       ( A ) ))).
% 1.66/1.91  thf('4', plain,
% 1.66/1.91      (![X17 : $i, X18 : $i]:
% 1.66/1.91         ((k2_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ (k4_xboole_0 @ X17 @ X18))
% 1.66/1.91           = (X17))),
% 1.66/1.91      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.66/1.91  thf('5', plain,
% 1.66/1.91      (((k2_xboole_0 @ k1_xboole_0 @ 
% 1.66/1.91         (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))) = (sk_A))),
% 1.66/1.91      inference('sup+', [status(thm)], ['3', '4'])).
% 1.66/1.91  thf(t3_boole, axiom,
% 1.66/1.91    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.66/1.91  thf('6', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 1.66/1.91      inference('cnf', [status(esa)], [t3_boole])).
% 1.66/1.91  thf(t79_xboole_1, axiom,
% 1.66/1.91    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 1.66/1.91  thf('7', plain,
% 1.66/1.91      (![X19 : $i, X20 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ X20)),
% 1.66/1.91      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.66/1.91  thf('8', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.66/1.91      inference('sup+', [status(thm)], ['6', '7'])).
% 1.66/1.91  thf('9', plain,
% 1.66/1.91      (![X0 : $i, X1 : $i]:
% 1.66/1.91         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.66/1.91      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.66/1.91  thf('10', plain,
% 1.66/1.91      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.66/1.91      inference('sup-', [status(thm)], ['8', '9'])).
% 1.66/1.91  thf('11', plain,
% 1.66/1.91      (![X17 : $i, X18 : $i]:
% 1.66/1.91         ((k2_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ (k4_xboole_0 @ X17 @ X18))
% 1.66/1.91           = (X17))),
% 1.66/1.91      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.66/1.91  thf('12', plain,
% 1.66/1.91      (![X0 : $i]:
% 1.66/1.91         ((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 1.66/1.91      inference('sup+', [status(thm)], ['10', '11'])).
% 1.66/1.91  thf('13', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 1.66/1.91      inference('cnf', [status(esa)], [t3_boole])).
% 1.66/1.91  thf('14', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.66/1.91      inference('demod', [status(thm)], ['12', '13'])).
% 1.66/1.91  thf('15', plain,
% 1.66/1.91      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 1.66/1.91      inference('demod', [status(thm)], ['5', '14'])).
% 1.66/1.91  thf(t41_xboole_1, axiom,
% 1.66/1.91    (![A:$i,B:$i,C:$i]:
% 1.66/1.91     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 1.66/1.91       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.66/1.91  thf('16', plain,
% 1.66/1.91      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.66/1.91         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 1.66/1.91           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 1.66/1.91      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.66/1.91  thf('17', plain,
% 1.66/1.91      (![X0 : $i]:
% 1.66/1.91         ((k4_xboole_0 @ sk_A @ X0)
% 1.66/1.91           = (k4_xboole_0 @ sk_A @ 
% 1.66/1.91              (k2_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ X0)))),
% 1.66/1.91      inference('sup+', [status(thm)], ['15', '16'])).
% 1.66/1.91  thf('18', plain,
% 1.66/1.91      (![X19 : $i, X20 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ X20)),
% 1.66/1.91      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.66/1.91  thf(symmetry_r1_xboole_0, axiom,
% 1.66/1.91    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.66/1.91  thf('19', plain,
% 1.66/1.91      (![X3 : $i, X4 : $i]:
% 1.66/1.91         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 1.66/1.91      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.66/1.91  thf('20', plain,
% 1.66/1.91      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 1.66/1.91      inference('sup-', [status(thm)], ['18', '19'])).
% 1.66/1.91  thf('21', plain,
% 1.66/1.91      (![X0 : $i, X1 : $i]:
% 1.66/1.91         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.66/1.91      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.66/1.91  thf('22', plain,
% 1.66/1.91      (![X0 : $i, X1 : $i]:
% 1.66/1.91         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 1.66/1.91      inference('sup-', [status(thm)], ['20', '21'])).
% 1.66/1.91  thf('23', plain,
% 1.66/1.91      (![X17 : $i, X18 : $i]:
% 1.66/1.91         ((k2_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ (k4_xboole_0 @ X17 @ X18))
% 1.66/1.91           = (X17))),
% 1.66/1.91      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.66/1.91  thf('24', plain,
% 1.66/1.91      (![X0 : $i, X1 : $i]:
% 1.66/1.91         ((k2_xboole_0 @ k1_xboole_0 @ 
% 1.66/1.91           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))) = (X0))),
% 1.66/1.91      inference('sup+', [status(thm)], ['22', '23'])).
% 1.66/1.91  thf('25', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.66/1.91      inference('demod', [status(thm)], ['12', '13'])).
% 1.66/1.91  thf('26', plain,
% 1.66/1.91      (![X0 : $i, X1 : $i]:
% 1.66/1.91         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 1.66/1.91      inference('demod', [status(thm)], ['24', '25'])).
% 1.66/1.91  thf('27', plain,
% 1.66/1.91      (![X17 : $i, X18 : $i]:
% 1.66/1.91         ((k2_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ (k4_xboole_0 @ X17 @ X18))
% 1.66/1.91           = (X17))),
% 1.66/1.91      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.66/1.91  thf('28', plain,
% 1.66/1.91      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.66/1.91         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 1.66/1.91           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 1.66/1.91      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.66/1.91  thf('29', plain,
% 1.66/1.91      (![X19 : $i, X20 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ X20)),
% 1.66/1.91      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.66/1.91  thf('30', plain,
% 1.66/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.66/1.91         (r1_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X0)),
% 1.66/1.91      inference('sup+', [status(thm)], ['28', '29'])).
% 1.66/1.91  thf('31', plain,
% 1.66/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.66/1.91         (r1_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ (k4_xboole_0 @ X0 @ X1))),
% 1.66/1.91      inference('sup+', [status(thm)], ['27', '30'])).
% 1.66/1.91  thf('32', plain,
% 1.66/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.66/1.91         (r1_xboole_0 @ X0 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1))),
% 1.66/1.91      inference('sup+', [status(thm)], ['26', '31'])).
% 1.66/1.91  thf('33', plain,
% 1.66/1.91      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.66/1.91         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 1.66/1.91           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 1.66/1.91      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.66/1.91  thf('34', plain,
% 1.66/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.66/1.91         (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1)))),
% 1.66/1.91      inference('demod', [status(thm)], ['32', '33'])).
% 1.66/1.91  thf('35', plain,
% 1.66/1.91      (![X0 : $i]:
% 1.66/1.91         (r1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ (k4_xboole_0 @ sk_A @ X0))),
% 1.66/1.91      inference('sup+', [status(thm)], ['17', '34'])).
% 1.66/1.91  thf('36', plain,
% 1.66/1.91      (![X3 : $i, X4 : $i]:
% 1.66/1.91         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 1.66/1.91      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.66/1.91  thf('37', plain,
% 1.66/1.91      (![X0 : $i]:
% 1.66/1.91         (r1_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ (k4_xboole_0 @ sk_B @ sk_C))),
% 1.66/1.91      inference('sup-', [status(thm)], ['35', '36'])).
% 1.66/1.91  thf('38', plain,
% 1.66/1.91      (![X0 : $i, X1 : $i]:
% 1.66/1.91         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.66/1.91      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.66/1.91  thf('39', plain,
% 1.66/1.91      (![X0 : $i]:
% 1.66/1.91         ((k3_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ 
% 1.66/1.91           (k4_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 1.66/1.91      inference('sup-', [status(thm)], ['37', '38'])).
% 1.66/1.91  thf(t39_xboole_1, axiom,
% 1.66/1.91    (![A:$i,B:$i]:
% 1.66/1.91     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.66/1.91  thf('40', plain,
% 1.66/1.91      (![X9 : $i, X10 : $i]:
% 1.66/1.91         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 1.66/1.91           = (k2_xboole_0 @ X9 @ X10))),
% 1.66/1.91      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.66/1.91  thf('41', plain,
% 1.66/1.91      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.66/1.91         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 1.66/1.91           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 1.66/1.91      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.66/1.91  thf('42', plain,
% 1.66/1.91      (![X17 : $i, X18 : $i]:
% 1.66/1.91         ((k2_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ (k4_xboole_0 @ X17 @ X18))
% 1.66/1.91           = (X17))),
% 1.66/1.91      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.66/1.91  thf('43', plain,
% 1.66/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.66/1.91         ((k2_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) @ 
% 1.66/1.91           (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 1.66/1.91           = (k4_xboole_0 @ X2 @ X1))),
% 1.66/1.91      inference('sup+', [status(thm)], ['41', '42'])).
% 1.66/1.91  thf('44', plain,
% 1.66/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.66/1.91         ((k2_xboole_0 @ 
% 1.66/1.91           (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k4_xboole_0 @ X0 @ X1)) @ 
% 1.66/1.91           (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 1.66/1.91           = (k4_xboole_0 @ X2 @ X1))),
% 1.66/1.91      inference('sup+', [status(thm)], ['40', '43'])).
% 1.66/1.91  thf('45', plain,
% 1.66/1.91      (((k2_xboole_0 @ k1_xboole_0 @ 
% 1.66/1.91         (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B)))
% 1.66/1.91         = (k4_xboole_0 @ sk_A @ sk_C))),
% 1.66/1.91      inference('sup+', [status(thm)], ['39', '44'])).
% 1.66/1.91  thf('46', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.66/1.91      inference('demod', [status(thm)], ['12', '13'])).
% 1.66/1.91  thf('47', plain,
% 1.66/1.91      (((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B))
% 1.66/1.91         = (k4_xboole_0 @ sk_A @ sk_C))),
% 1.66/1.91      inference('demod', [status(thm)], ['45', '46'])).
% 1.66/1.91  thf('48', plain,
% 1.66/1.91      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.66/1.91         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 1.66/1.91           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 1.66/1.91      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.66/1.91  thf('49', plain,
% 1.66/1.91      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 1.66/1.91      inference('sup-', [status(thm)], ['18', '19'])).
% 1.66/1.91  thf('50', plain,
% 1.66/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.66/1.91         (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.66/1.91      inference('sup+', [status(thm)], ['48', '49'])).
% 1.66/1.91  thf('51', plain, ((r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 1.66/1.91      inference('sup+', [status(thm)], ['47', '50'])).
% 1.66/1.91  thf('52', plain, ($false), inference('demod', [status(thm)], ['0', '51'])).
% 1.66/1.91  
% 1.66/1.91  % SZS output end Refutation
% 1.66/1.91  
% 1.75/1.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

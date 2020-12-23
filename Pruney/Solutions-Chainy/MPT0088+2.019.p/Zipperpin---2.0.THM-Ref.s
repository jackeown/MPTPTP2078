%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JZZW0XxRev

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:37 EST 2020

% Result     : Theorem 1.71s
% Output     : Refutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   67 (  84 expanded)
%              Number of leaves         :   19 (  33 expanded)
%              Depth                    :   13
%              Number of atoms          :  446 ( 578 expanded)
%              Number of equality atoms :   32 (  41 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('6',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('7',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('8',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ X22 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('15',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X19 @ X20 )
      | ( r1_xboole_0 @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','19'])).

thf('21',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ ( k4_xboole_0 @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ k1_xboole_0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('33',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('34',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X12 ) @ X13 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('36',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('38',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X19 @ X20 )
      | ( r1_xboole_0 @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','43'])).

thf('45',plain,(
    r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['28','44'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['0','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JZZW0XxRev
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:41:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.71/1.95  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.71/1.95  % Solved by: fo/fo7.sh
% 1.71/1.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.71/1.95  % done 3515 iterations in 1.487s
% 1.71/1.95  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.71/1.95  % SZS output start Refutation
% 1.71/1.95  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.71/1.95  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.71/1.95  thf(sk_C_type, type, sk_C: $i).
% 1.71/1.95  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.71/1.95  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.71/1.95  thf(sk_A_type, type, sk_A: $i).
% 1.71/1.95  thf(sk_B_type, type, sk_B: $i).
% 1.71/1.95  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.71/1.95  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.71/1.95  thf(t81_xboole_1, conjecture,
% 1.71/1.95    (![A:$i,B:$i,C:$i]:
% 1.71/1.95     ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 1.71/1.95       ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ))).
% 1.71/1.95  thf(zf_stmt_0, negated_conjecture,
% 1.71/1.95    (~( ![A:$i,B:$i,C:$i]:
% 1.71/1.95        ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 1.71/1.95          ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )),
% 1.71/1.95    inference('cnf.neg', [status(esa)], [t81_xboole_1])).
% 1.71/1.95  thf('0', plain, (~ (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 1.71/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.95  thf('1', plain, ((r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 1.71/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.71/1.95  thf(d7_xboole_0, axiom,
% 1.71/1.95    (![A:$i,B:$i]:
% 1.71/1.95     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.71/1.95       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.71/1.95  thf('2', plain,
% 1.71/1.95      (![X0 : $i, X1 : $i]:
% 1.71/1.95         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.71/1.95      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.71/1.95  thf('3', plain,
% 1.71/1.95      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 1.71/1.95      inference('sup-', [status(thm)], ['1', '2'])).
% 1.71/1.95  thf(t47_xboole_1, axiom,
% 1.71/1.95    (![A:$i,B:$i]:
% 1.71/1.95     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.71/1.95  thf('4', plain,
% 1.71/1.95      (![X14 : $i, X15 : $i]:
% 1.71/1.95         ((k4_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15))
% 1.71/1.95           = (k4_xboole_0 @ X14 @ X15))),
% 1.71/1.95      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.71/1.95  thf('5', plain,
% 1.71/1.95      (((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 1.71/1.95         = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 1.71/1.95      inference('sup+', [status(thm)], ['3', '4'])).
% 1.71/1.95  thf(t3_boole, axiom,
% 1.71/1.95    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.71/1.95  thf('6', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 1.71/1.95      inference('cnf', [status(esa)], [t3_boole])).
% 1.71/1.95  thf('7', plain,
% 1.71/1.95      (((sk_A) = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 1.71/1.95      inference('demod', [status(thm)], ['5', '6'])).
% 1.71/1.95  thf(t79_xboole_1, axiom,
% 1.71/1.95    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 1.71/1.95  thf('8', plain,
% 1.71/1.95      (![X21 : $i, X22 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ X22)),
% 1.71/1.95      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.71/1.95  thf(symmetry_r1_xboole_0, axiom,
% 1.71/1.95    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.71/1.95  thf('9', plain,
% 1.71/1.95      (![X3 : $i, X4 : $i]:
% 1.71/1.95         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 1.71/1.95      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.71/1.95  thf('10', plain,
% 1.71/1.95      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 1.71/1.95      inference('sup-', [status(thm)], ['8', '9'])).
% 1.71/1.95  thf(t46_xboole_1, axiom,
% 1.71/1.95    (![A:$i,B:$i]:
% 1.71/1.95     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 1.71/1.95  thf('11', plain,
% 1.71/1.95      (![X12 : $i, X13 : $i]:
% 1.71/1.95         ((k4_xboole_0 @ X12 @ (k2_xboole_0 @ X12 @ X13)) = (k1_xboole_0))),
% 1.71/1.95      inference('cnf', [status(esa)], [t46_xboole_1])).
% 1.71/1.95  thf(l32_xboole_1, axiom,
% 1.71/1.95    (![A:$i,B:$i]:
% 1.71/1.95     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.71/1.95  thf('12', plain,
% 1.71/1.95      (![X5 : $i, X6 : $i]:
% 1.71/1.95         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 1.71/1.95      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.71/1.95  thf('13', plain,
% 1.71/1.95      (![X0 : $i, X1 : $i]:
% 1.71/1.95         (((k1_xboole_0) != (k1_xboole_0))
% 1.71/1.95          | (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.71/1.95      inference('sup-', [status(thm)], ['11', '12'])).
% 1.71/1.95  thf('14', plain,
% 1.71/1.95      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 1.71/1.95      inference('simplify', [status(thm)], ['13'])).
% 1.71/1.95  thf(t63_xboole_1, axiom,
% 1.71/1.95    (![A:$i,B:$i,C:$i]:
% 1.71/1.95     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 1.71/1.95       ( r1_xboole_0 @ A @ C ) ))).
% 1.71/1.95  thf('15', plain,
% 1.71/1.95      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.71/1.95         (~ (r1_tarski @ X18 @ X19)
% 1.71/1.95          | ~ (r1_xboole_0 @ X19 @ X20)
% 1.71/1.95          | (r1_xboole_0 @ X18 @ X20))),
% 1.71/1.95      inference('cnf', [status(esa)], [t63_xboole_1])).
% 1.71/1.95  thf('16', plain,
% 1.71/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.71/1.95         ((r1_xboole_0 @ X1 @ X2)
% 1.71/1.95          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 1.71/1.95      inference('sup-', [status(thm)], ['14', '15'])).
% 1.71/1.95  thf('17', plain,
% 1.71/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.71/1.95         (r1_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.71/1.95      inference('sup-', [status(thm)], ['10', '16'])).
% 1.71/1.95  thf(t41_xboole_1, axiom,
% 1.71/1.95    (![A:$i,B:$i,C:$i]:
% 1.71/1.95     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 1.71/1.95       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.71/1.95  thf('18', plain,
% 1.71/1.95      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.71/1.95         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 1.71/1.95           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 1.71/1.95      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.71/1.95  thf('19', plain,
% 1.71/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.71/1.95         (r1_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 1.71/1.95      inference('demod', [status(thm)], ['17', '18'])).
% 1.71/1.95  thf('20', plain,
% 1.71/1.95      (![X0 : $i]:
% 1.71/1.95         (r1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ (k4_xboole_0 @ sk_A @ X0))),
% 1.71/1.95      inference('sup+', [status(thm)], ['7', '19'])).
% 1.71/1.95  thf('21', plain,
% 1.71/1.95      (![X3 : $i, X4 : $i]:
% 1.71/1.95         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 1.71/1.95      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.71/1.95  thf('22', plain,
% 1.71/1.95      (![X0 : $i]:
% 1.71/1.95         (r1_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ (k4_xboole_0 @ sk_B @ sk_C))),
% 1.71/1.95      inference('sup-', [status(thm)], ['20', '21'])).
% 1.71/1.95  thf('23', plain,
% 1.71/1.95      (![X0 : $i, X1 : $i]:
% 1.71/1.95         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.71/1.95      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.71/1.95  thf('24', plain,
% 1.71/1.95      (![X0 : $i]:
% 1.71/1.95         ((k3_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ 
% 1.71/1.95           (k4_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 1.71/1.95      inference('sup-', [status(thm)], ['22', '23'])).
% 1.71/1.95  thf('25', plain,
% 1.71/1.95      (![X14 : $i, X15 : $i]:
% 1.71/1.95         ((k4_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15))
% 1.71/1.95           = (k4_xboole_0 @ X14 @ X15))),
% 1.71/1.95      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.71/1.95  thf('26', plain,
% 1.71/1.95      (![X0 : $i]:
% 1.71/1.95         ((k4_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ k1_xboole_0)
% 1.71/1.95           = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ 
% 1.71/1.95              (k4_xboole_0 @ sk_B @ sk_C)))),
% 1.71/1.95      inference('sup+', [status(thm)], ['24', '25'])).
% 1.71/1.95  thf('27', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 1.71/1.95      inference('cnf', [status(esa)], [t3_boole])).
% 1.71/1.95  thf('28', plain,
% 1.71/1.95      (![X0 : $i]:
% 1.71/1.95         ((k4_xboole_0 @ sk_A @ X0)
% 1.71/1.95           = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ 
% 1.71/1.95              (k4_xboole_0 @ sk_B @ sk_C)))),
% 1.71/1.95      inference('demod', [status(thm)], ['26', '27'])).
% 1.71/1.95  thf('29', plain,
% 1.71/1.95      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.71/1.95         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 1.71/1.95           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 1.71/1.95      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.71/1.95  thf('30', plain,
% 1.71/1.95      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 1.71/1.95      inference('sup-', [status(thm)], ['8', '9'])).
% 1.71/1.95  thf('31', plain,
% 1.71/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.71/1.95         (r1_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 1.71/1.95          (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 1.71/1.95      inference('sup+', [status(thm)], ['29', '30'])).
% 1.71/1.95  thf('32', plain,
% 1.71/1.95      (![X12 : $i, X13 : $i]:
% 1.71/1.95         ((k4_xboole_0 @ X12 @ (k2_xboole_0 @ X12 @ X13)) = (k1_xboole_0))),
% 1.71/1.95      inference('cnf', [status(esa)], [t46_xboole_1])).
% 1.71/1.95  thf('33', plain,
% 1.71/1.95      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.71/1.95         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 1.71/1.95           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 1.71/1.95      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.71/1.95  thf('34', plain,
% 1.71/1.95      (![X12 : $i, X13 : $i]:
% 1.71/1.95         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X12) @ X13) = (k1_xboole_0))),
% 1.71/1.95      inference('demod', [status(thm)], ['32', '33'])).
% 1.71/1.95  thf('35', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 1.71/1.95      inference('cnf', [status(esa)], [t3_boole])).
% 1.71/1.95  thf('36', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 1.71/1.95      inference('sup+', [status(thm)], ['34', '35'])).
% 1.71/1.95  thf('37', plain,
% 1.71/1.95      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.71/1.95         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 1.71/1.95           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 1.71/1.95      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.71/1.95  thf('38', plain,
% 1.71/1.95      (![X5 : $i, X6 : $i]:
% 1.71/1.95         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 1.71/1.95      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.71/1.95  thf('39', plain,
% 1.71/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.71/1.95         (((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) != (k1_xboole_0))
% 1.71/1.95          | (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.71/1.95      inference('sup-', [status(thm)], ['37', '38'])).
% 1.71/1.95  thf('40', plain,
% 1.71/1.95      (![X0 : $i, X1 : $i]:
% 1.71/1.95         (((k1_xboole_0) != (k1_xboole_0))
% 1.71/1.95          | (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.71/1.95      inference('sup-', [status(thm)], ['36', '39'])).
% 1.71/1.95  thf('41', plain,
% 1.71/1.95      (![X0 : $i, X1 : $i]:
% 1.71/1.95         (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.71/1.95      inference('simplify', [status(thm)], ['40'])).
% 1.71/1.95  thf('42', plain,
% 1.71/1.95      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.71/1.95         (~ (r1_tarski @ X18 @ X19)
% 1.71/1.95          | ~ (r1_xboole_0 @ X19 @ X20)
% 1.71/1.95          | (r1_xboole_0 @ X18 @ X20))),
% 1.71/1.95      inference('cnf', [status(esa)], [t63_xboole_1])).
% 1.71/1.95  thf('43', plain,
% 1.71/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.71/1.95         ((r1_xboole_0 @ X1 @ X2)
% 1.71/1.95          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ X2))),
% 1.71/1.95      inference('sup-', [status(thm)], ['41', '42'])).
% 1.71/1.95  thf('44', plain,
% 1.71/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.71/1.95         (r1_xboole_0 @ X1 @ 
% 1.71/1.95          (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 1.71/1.95      inference('sup-', [status(thm)], ['31', '43'])).
% 1.71/1.95  thf('45', plain, ((r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 1.71/1.95      inference('sup+', [status(thm)], ['28', '44'])).
% 1.71/1.95  thf('46', plain, ($false), inference('demod', [status(thm)], ['0', '45'])).
% 1.71/1.95  
% 1.71/1.95  % SZS output end Refutation
% 1.71/1.95  
% 1.71/1.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

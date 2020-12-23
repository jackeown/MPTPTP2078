%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.65rWyIATY6

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:28 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 223 expanded)
%              Number of leaves         :   18 (  79 expanded)
%              Depth                    :   18
%              Number of atoms          :  391 (1491 expanded)
%              Number of equality atoms :   45 ( 132 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t59_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r2_xboole_0 @ B @ C ) )
     => ( r2_xboole_0 @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r2_xboole_0 @ B @ C ) )
       => ( r2_xboole_0 @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t59_xboole_1])).

thf('0',plain,(
    r2_xboole_0 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_xboole_0 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( r2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('3',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X6: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X8 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('8',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('11',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ sk_B )
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference('sup-',[status(thm)],['1','2'])).

thf('13',plain,(
    ! [X6: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X8 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('17',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k4_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('18',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ k1_xboole_0 ) @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_B ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('21',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('22',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['18','19','20','21'])).

thf('23',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['11','22'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('24',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X9 @ X11 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r1_tarski @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['3','25'])).

thf('27',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r2_xboole_0 @ X2 @ X4 )
      | ( X2 = X4 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('28',plain,
    ( ( sk_A = sk_C )
    | ( r2_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( r2_xboole_0 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    sk_A = sk_C ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    r2_xboole_0 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['0','30'])).

thf('32',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('33',plain,(
    sk_A = sk_C ),
    inference(clc,[status(thm)],['28','29'])).

thf('34',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('36',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('38',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf('39',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('40',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k4_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('42',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ k1_xboole_0 ) @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_A ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('45',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('46',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('47',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['36','37','46'])).

thf('48',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['11','22'])).

thf('49',plain,(
    sk_B = sk_A ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    r2_xboole_0 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['31','49'])).

thf(irreflexivity_r2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_xboole_0 @ A @ A ) )).

thf('51',plain,(
    ! [X5: $i] :
      ~ ( r2_xboole_0 @ X5 @ X5 ) ),
    inference(cnf,[status(esa)],[irreflexivity_r2_xboole_0])).

thf('52',plain,(
    $false ),
    inference('sup-',[status(thm)],['50','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.65rWyIATY6
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:52:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.44  % Solved by: fo/fo7.sh
% 0.20/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.44  % done 58 iterations in 0.020s
% 0.20/0.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.44  % SZS output start Refutation
% 0.20/0.44  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.20/0.44  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.44  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.44  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.44  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.44  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.44  thf(t59_xboole_1, conjecture,
% 0.20/0.44    (![A:$i,B:$i,C:$i]:
% 0.20/0.44     ( ( ( r1_tarski @ A @ B ) & ( r2_xboole_0 @ B @ C ) ) =>
% 0.20/0.44       ( r2_xboole_0 @ A @ C ) ))).
% 0.20/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.44    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.44        ( ( ( r1_tarski @ A @ B ) & ( r2_xboole_0 @ B @ C ) ) =>
% 0.20/0.44          ( r2_xboole_0 @ A @ C ) ) )),
% 0.20/0.44    inference('cnf.neg', [status(esa)], [t59_xboole_1])).
% 0.20/0.44  thf('0', plain, ((r2_xboole_0 @ sk_B @ sk_C)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('1', plain, ((r2_xboole_0 @ sk_B @ sk_C)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf(d8_xboole_0, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.20/0.44       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.20/0.44  thf('2', plain,
% 0.20/0.44      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ~ (r2_xboole_0 @ X2 @ X3))),
% 0.20/0.44      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.20/0.44  thf('3', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.20/0.44      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.44  thf('4', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf(l32_xboole_1, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.44  thf('5', plain,
% 0.20/0.44      (![X6 : $i, X8 : $i]:
% 0.20/0.44         (((k4_xboole_0 @ X6 @ X8) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ X8))),
% 0.20/0.44      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.44  thf('6', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.44      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.44  thf(t39_xboole_1, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.44  thf('7', plain,
% 0.20/0.44      (![X12 : $i, X13 : $i]:
% 0.20/0.44         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 0.20/0.44           = (k2_xboole_0 @ X12 @ X13))),
% 0.20/0.44      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.20/0.44  thf('8', plain,
% 0.20/0.44      (((k2_xboole_0 @ sk_B @ k1_xboole_0) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.20/0.44      inference('sup+', [status(thm)], ['6', '7'])).
% 0.20/0.44  thf(commutativity_k2_xboole_0, axiom,
% 0.20/0.44    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.20/0.44  thf('9', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.44      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.44  thf('10', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.44      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.44  thf('11', plain,
% 0.20/0.44      (((k2_xboole_0 @ k1_xboole_0 @ sk_B) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.44      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.20/0.44  thf('12', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.20/0.44      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.44  thf('13', plain,
% 0.20/0.44      (![X6 : $i, X8 : $i]:
% 0.20/0.44         (((k4_xboole_0 @ X6 @ X8) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ X8))),
% 0.20/0.44      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.44  thf('14', plain, (((k4_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))),
% 0.20/0.44      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.44  thf(t48_xboole_1, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.44  thf('15', plain,
% 0.20/0.44      (![X14 : $i, X15 : $i]:
% 0.20/0.44         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.20/0.44           = (k3_xboole_0 @ X14 @ X15))),
% 0.20/0.44      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.44  thf('16', plain,
% 0.20/0.44      (((k4_xboole_0 @ sk_B @ k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_C))),
% 0.20/0.44      inference('sup+', [status(thm)], ['14', '15'])).
% 0.20/0.44  thf(t51_xboole_1, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.20/0.44       ( A ) ))).
% 0.20/0.44  thf('17', plain,
% 0.20/0.44      (![X16 : $i, X17 : $i]:
% 0.20/0.44         ((k2_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ (k4_xboole_0 @ X16 @ X17))
% 0.20/0.44           = (X16))),
% 0.20/0.44      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.20/0.44  thf('18', plain,
% 0.20/0.44      (((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ k1_xboole_0) @ 
% 0.20/0.44         (k4_xboole_0 @ sk_B @ sk_C)) = (sk_B))),
% 0.20/0.44      inference('sup+', [status(thm)], ['16', '17'])).
% 0.20/0.44  thf('19', plain, (((k4_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))),
% 0.20/0.44      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.44  thf('20', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.44      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.44  thf('21', plain,
% 0.20/0.44      (![X12 : $i, X13 : $i]:
% 0.20/0.44         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 0.20/0.44           = (k2_xboole_0 @ X12 @ X13))),
% 0.20/0.44      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.20/0.44  thf('22', plain, (((k2_xboole_0 @ k1_xboole_0 @ sk_B) = (sk_B))),
% 0.20/0.44      inference('demod', [status(thm)], ['18', '19', '20', '21'])).
% 0.20/0.44  thf('23', plain, (((sk_B) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.44      inference('demod', [status(thm)], ['11', '22'])).
% 0.20/0.44  thf(t11_xboole_1, axiom,
% 0.20/0.44    (![A:$i,B:$i,C:$i]:
% 0.20/0.44     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.20/0.44  thf('24', plain,
% 0.20/0.44      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.44         ((r1_tarski @ X9 @ X10)
% 0.20/0.44          | ~ (r1_tarski @ (k2_xboole_0 @ X9 @ X11) @ X10))),
% 0.20/0.44      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.20/0.44  thf('25', plain,
% 0.20/0.44      (![X0 : $i]: (~ (r1_tarski @ sk_B @ X0) | (r1_tarski @ sk_A @ X0))),
% 0.20/0.44      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.44  thf('26', plain, ((r1_tarski @ sk_A @ sk_C)),
% 0.20/0.44      inference('sup-', [status(thm)], ['3', '25'])).
% 0.20/0.44  thf('27', plain,
% 0.20/0.44      (![X2 : $i, X4 : $i]:
% 0.20/0.44         ((r2_xboole_0 @ X2 @ X4) | ((X2) = (X4)) | ~ (r1_tarski @ X2 @ X4))),
% 0.20/0.44      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.20/0.44  thf('28', plain, ((((sk_A) = (sk_C)) | (r2_xboole_0 @ sk_A @ sk_C))),
% 0.20/0.44      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.44  thf('29', plain, (~ (r2_xboole_0 @ sk_A @ sk_C)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('30', plain, (((sk_A) = (sk_C))),
% 0.20/0.44      inference('clc', [status(thm)], ['28', '29'])).
% 0.20/0.44  thf('31', plain, ((r2_xboole_0 @ sk_B @ sk_A)),
% 0.20/0.44      inference('demod', [status(thm)], ['0', '30'])).
% 0.20/0.44  thf('32', plain, (((k4_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))),
% 0.20/0.44      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.44  thf('33', plain, (((sk_A) = (sk_C))),
% 0.20/0.44      inference('clc', [status(thm)], ['28', '29'])).
% 0.20/0.44  thf('34', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.20/0.44      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.44  thf('35', plain,
% 0.20/0.44      (![X12 : $i, X13 : $i]:
% 0.20/0.44         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 0.20/0.44           = (k2_xboole_0 @ X12 @ X13))),
% 0.20/0.44      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.20/0.44  thf('36', plain,
% 0.20/0.44      (((k2_xboole_0 @ sk_A @ k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.44      inference('sup+', [status(thm)], ['34', '35'])).
% 0.20/0.44  thf('37', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.44      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.44  thf('38', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.44      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.44  thf('39', plain,
% 0.20/0.44      (![X14 : $i, X15 : $i]:
% 0.20/0.44         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.20/0.44           = (k3_xboole_0 @ X14 @ X15))),
% 0.20/0.44      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.44  thf('40', plain,
% 0.20/0.44      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.44      inference('sup+', [status(thm)], ['38', '39'])).
% 0.20/0.44  thf('41', plain,
% 0.20/0.44      (![X16 : $i, X17 : $i]:
% 0.20/0.44         ((k2_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ (k4_xboole_0 @ X16 @ X17))
% 0.20/0.44           = (X16))),
% 0.20/0.44      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.20/0.44  thf('42', plain,
% 0.20/0.44      (((k2_xboole_0 @ (k4_xboole_0 @ sk_A @ k1_xboole_0) @ 
% 0.20/0.44         (k4_xboole_0 @ sk_A @ sk_B)) = (sk_A))),
% 0.20/0.44      inference('sup+', [status(thm)], ['40', '41'])).
% 0.20/0.44  thf('43', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.44      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.44  thf('44', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.44      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.44  thf('45', plain,
% 0.20/0.44      (![X12 : $i, X13 : $i]:
% 0.20/0.44         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 0.20/0.44           = (k2_xboole_0 @ X12 @ X13))),
% 0.20/0.44      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.20/0.44  thf('46', plain, (((k2_xboole_0 @ k1_xboole_0 @ sk_A) = (sk_A))),
% 0.20/0.44      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 0.20/0.44  thf('47', plain, (((sk_A) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.44      inference('demod', [status(thm)], ['36', '37', '46'])).
% 0.20/0.44  thf('48', plain, (((sk_B) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.44      inference('demod', [status(thm)], ['11', '22'])).
% 0.20/0.44  thf('49', plain, (((sk_B) = (sk_A))),
% 0.20/0.44      inference('sup+', [status(thm)], ['47', '48'])).
% 0.20/0.44  thf('50', plain, ((r2_xboole_0 @ sk_A @ sk_A)),
% 0.20/0.44      inference('demod', [status(thm)], ['31', '49'])).
% 0.20/0.44  thf(irreflexivity_r2_xboole_0, axiom,
% 0.20/0.44    (![A:$i,B:$i]: ( ~( r2_xboole_0 @ A @ A ) ))).
% 0.20/0.44  thf('51', plain, (![X5 : $i]: ~ (r2_xboole_0 @ X5 @ X5)),
% 0.20/0.44      inference('cnf', [status(esa)], [irreflexivity_r2_xboole_0])).
% 0.20/0.44  thf('52', plain, ($false), inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.44  
% 0.20/0.44  % SZS output end Refutation
% 0.20/0.44  
% 0.20/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

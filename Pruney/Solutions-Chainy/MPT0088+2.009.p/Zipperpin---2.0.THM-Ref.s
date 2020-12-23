%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CpFBmBAQqh

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:35 EST 2020

% Result     : Theorem 0.71s
% Output     : Refutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :   67 (  78 expanded)
%              Number of leaves         :   23 (  33 expanded)
%              Depth                    :   14
%              Number of atoms          :  455 ( 548 expanded)
%              Number of equality atoms :   44 (  53 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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
    ~ ( r1_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) ) ),
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

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('3',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('6',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['2','7'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf('12',plain,(
    r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('14',plain,(
    r1_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('15',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('16',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['14','17'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('19',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k4_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('20',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) @ sk_A ) )
    = ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('23',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('24',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k4_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) )
    = ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['20','21','22','27'])).

thf('29',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('30',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    = ( k3_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('32',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_1 )
    = ( k3_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('33',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ ( k3_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ X0 ) @ ( k3_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ ( k3_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) ) )
      = ( k4_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ X0 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['11','36'])).

thf('38',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('39',plain,
    ( sk_B_1
    = ( k4_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('40',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X23 @ X24 ) @ X24 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('41',plain,(
    r1_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['0','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CpFBmBAQqh
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:16:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.71/0.92  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.71/0.92  % Solved by: fo/fo7.sh
% 0.71/0.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.71/0.92  % done 1123 iterations in 0.460s
% 0.71/0.92  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.71/0.92  % SZS output start Refutation
% 0.71/0.92  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.71/0.92  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.71/0.92  thf(sk_B_type, type, sk_B: $i > $i).
% 0.71/0.92  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.71/0.92  thf(sk_A_type, type, sk_A: $i).
% 0.71/0.92  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.71/0.92  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.71/0.92  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.71/0.92  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.71/0.92  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.71/0.92  thf(t81_xboole_1, conjecture,
% 0.71/0.92    (![A:$i,B:$i,C:$i]:
% 0.71/0.92     ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.71/0.92       ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.71/0.92  thf(zf_stmt_0, negated_conjecture,
% 0.71/0.92    (~( ![A:$i,B:$i,C:$i]:
% 0.71/0.92        ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.71/0.92          ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )),
% 0.71/0.92    inference('cnf.neg', [status(esa)], [t81_xboole_1])).
% 0.71/0.92  thf('0', plain, (~ (r1_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf(commutativity_k2_xboole_0, axiom,
% 0.71/0.92    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.71/0.92  thf('1', plain,
% 0.71/0.92      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.71/0.92      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.71/0.92  thf(t41_xboole_1, axiom,
% 0.71/0.92    (![A:$i,B:$i,C:$i]:
% 0.71/0.92     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.71/0.92       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.71/0.92  thf('2', plain,
% 0.71/0.92      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.71/0.92         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 0.71/0.92           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 0.71/0.92      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.71/0.92  thf(t3_boole, axiom,
% 0.71/0.92    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.71/0.92  thf('3', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.71/0.92      inference('cnf', [status(esa)], [t3_boole])).
% 0.71/0.92  thf(t48_xboole_1, axiom,
% 0.71/0.92    (![A:$i,B:$i]:
% 0.71/0.92     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.71/0.92  thf('4', plain,
% 0.71/0.92      (![X16 : $i, X17 : $i]:
% 0.71/0.92         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.71/0.92           = (k3_xboole_0 @ X16 @ X17))),
% 0.71/0.92      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.71/0.92  thf('5', plain,
% 0.71/0.92      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.71/0.92      inference('sup+', [status(thm)], ['3', '4'])).
% 0.71/0.92  thf(t2_boole, axiom,
% 0.71/0.92    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.71/0.92  thf('6', plain,
% 0.71/0.92      (![X9 : $i]: ((k3_xboole_0 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.71/0.92      inference('cnf', [status(esa)], [t2_boole])).
% 0.71/0.92  thf('7', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.71/0.92      inference('demod', [status(thm)], ['5', '6'])).
% 0.71/0.92  thf('8', plain,
% 0.71/0.92      (![X0 : $i, X1 : $i]:
% 0.71/0.92         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 0.71/0.92           = (k1_xboole_0))),
% 0.71/0.92      inference('sup+', [status(thm)], ['2', '7'])).
% 0.71/0.92  thf(t39_xboole_1, axiom,
% 0.71/0.92    (![A:$i,B:$i]:
% 0.71/0.92     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.71/0.92  thf('9', plain,
% 0.71/0.92      (![X10 : $i, X11 : $i]:
% 0.71/0.92         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 0.71/0.92           = (k2_xboole_0 @ X10 @ X11))),
% 0.71/0.92      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.71/0.92  thf('10', plain,
% 0.71/0.92      (![X0 : $i, X1 : $i]:
% 0.71/0.92         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.71/0.92      inference('demod', [status(thm)], ['8', '9'])).
% 0.71/0.92  thf('11', plain,
% 0.71/0.92      (![X0 : $i, X1 : $i]:
% 0.71/0.92         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.71/0.92      inference('sup+', [status(thm)], ['1', '10'])).
% 0.71/0.92  thf('12', plain, ((r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf(symmetry_r1_xboole_0, axiom,
% 0.71/0.92    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.71/0.92  thf('13', plain,
% 0.71/0.92      (![X2 : $i, X3 : $i]:
% 0.71/0.92         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.71/0.92      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.71/0.92  thf('14', plain, ((r1_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ sk_C_1) @ sk_A)),
% 0.71/0.92      inference('sup-', [status(thm)], ['12', '13'])).
% 0.71/0.92  thf(t7_xboole_0, axiom,
% 0.71/0.92    (![A:$i]:
% 0.71/0.92     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.71/0.92          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.71/0.92  thf('15', plain,
% 0.71/0.92      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.71/0.92      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.71/0.92  thf(t4_xboole_0, axiom,
% 0.71/0.92    (![A:$i,B:$i]:
% 0.71/0.92     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.71/0.92            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.71/0.92       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.71/0.92            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.71/0.92  thf('16', plain,
% 0.71/0.92      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.71/0.92         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.71/0.92          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.71/0.92      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.71/0.92  thf('17', plain,
% 0.71/0.92      (![X0 : $i, X1 : $i]:
% 0.71/0.92         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.71/0.92      inference('sup-', [status(thm)], ['15', '16'])).
% 0.71/0.92  thf('18', plain,
% 0.71/0.92      (((k3_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ sk_C_1) @ sk_A) = (k1_xboole_0))),
% 0.71/0.92      inference('sup-', [status(thm)], ['14', '17'])).
% 0.71/0.92  thf(t51_xboole_1, axiom,
% 0.71/0.92    (![A:$i,B:$i]:
% 0.71/0.92     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.71/0.92       ( A ) ))).
% 0.71/0.92  thf('19', plain,
% 0.71/0.92      (![X18 : $i, X19 : $i]:
% 0.71/0.92         ((k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ (k4_xboole_0 @ X18 @ X19))
% 0.71/0.92           = (X18))),
% 0.71/0.92      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.71/0.92  thf('20', plain,
% 0.71/0.92      (((k2_xboole_0 @ k1_xboole_0 @ 
% 0.71/0.92         (k4_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ sk_C_1) @ sk_A))
% 0.71/0.92         = (k4_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.71/0.92      inference('sup+', [status(thm)], ['18', '19'])).
% 0.71/0.92  thf('21', plain,
% 0.71/0.92      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.71/0.92         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 0.71/0.92           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 0.71/0.92      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.71/0.92  thf('22', plain,
% 0.71/0.92      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.71/0.92      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.71/0.92  thf('23', plain,
% 0.71/0.92      (![X9 : $i]: ((k3_xboole_0 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.71/0.92      inference('cnf', [status(esa)], [t2_boole])).
% 0.71/0.92  thf('24', plain,
% 0.71/0.92      (![X18 : $i, X19 : $i]:
% 0.71/0.92         ((k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ (k4_xboole_0 @ X18 @ X19))
% 0.71/0.92           = (X18))),
% 0.71/0.92      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.71/0.92  thf('25', plain,
% 0.71/0.92      (![X0 : $i]:
% 0.71/0.92         ((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 0.71/0.92      inference('sup+', [status(thm)], ['23', '24'])).
% 0.71/0.92  thf('26', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.71/0.92      inference('cnf', [status(esa)], [t3_boole])).
% 0.71/0.92  thf('27', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.71/0.92      inference('demod', [status(thm)], ['25', '26'])).
% 0.71/0.92  thf('28', plain,
% 0.71/0.92      (((k4_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ sk_A @ sk_C_1))
% 0.71/0.92         = (k4_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.71/0.92      inference('demod', [status(thm)], ['20', '21', '22', '27'])).
% 0.71/0.92  thf('29', plain,
% 0.71/0.92      (![X16 : $i, X17 : $i]:
% 0.71/0.92         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.71/0.92           = (k3_xboole_0 @ X16 @ X17))),
% 0.71/0.92      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.71/0.92  thf('30', plain,
% 0.71/0.92      (((k4_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ sk_B_1 @ sk_C_1))
% 0.71/0.92         = (k3_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ sk_A @ sk_C_1)))),
% 0.71/0.92      inference('sup+', [status(thm)], ['28', '29'])).
% 0.71/0.92  thf('31', plain,
% 0.71/0.92      (![X16 : $i, X17 : $i]:
% 0.71/0.92         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.71/0.92           = (k3_xboole_0 @ X16 @ X17))),
% 0.71/0.92      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.71/0.92  thf('32', plain,
% 0.71/0.92      (((k3_xboole_0 @ sk_B_1 @ sk_C_1)
% 0.71/0.92         = (k3_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ sk_A @ sk_C_1)))),
% 0.71/0.92      inference('demod', [status(thm)], ['30', '31'])).
% 0.71/0.92  thf(t52_xboole_1, axiom,
% 0.71/0.92    (![A:$i,B:$i,C:$i]:
% 0.71/0.92     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.71/0.92       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.71/0.92  thf('33', plain,
% 0.71/0.92      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.71/0.92         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X22))
% 0.71/0.92           = (k2_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ 
% 0.71/0.92              (k3_xboole_0 @ X20 @ X22)))),
% 0.71/0.92      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.71/0.92  thf('34', plain,
% 0.71/0.92      (![X0 : $i]:
% 0.71/0.92         ((k4_xboole_0 @ sk_B_1 @ 
% 0.71/0.92           (k4_xboole_0 @ X0 @ (k2_xboole_0 @ sk_A @ sk_C_1)))
% 0.71/0.92           = (k2_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ X0) @ 
% 0.71/0.92              (k3_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 0.71/0.92      inference('sup+', [status(thm)], ['32', '33'])).
% 0.71/0.92  thf('35', plain,
% 0.71/0.92      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.71/0.92         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X22))
% 0.71/0.92           = (k2_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ 
% 0.71/0.92              (k3_xboole_0 @ X20 @ X22)))),
% 0.71/0.92      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.71/0.92  thf('36', plain,
% 0.71/0.92      (![X0 : $i]:
% 0.71/0.92         ((k4_xboole_0 @ sk_B_1 @ 
% 0.71/0.92           (k4_xboole_0 @ X0 @ (k2_xboole_0 @ sk_A @ sk_C_1)))
% 0.71/0.92           = (k4_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ X0 @ sk_C_1)))),
% 0.71/0.92      inference('demod', [status(thm)], ['34', '35'])).
% 0.71/0.92  thf('37', plain,
% 0.71/0.92      (((k4_xboole_0 @ sk_B_1 @ k1_xboole_0)
% 0.71/0.92         = (k4_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ sk_A @ sk_C_1)))),
% 0.71/0.92      inference('sup+', [status(thm)], ['11', '36'])).
% 0.71/0.92  thf('38', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.71/0.92      inference('cnf', [status(esa)], [t3_boole])).
% 0.71/0.92  thf('39', plain,
% 0.71/0.92      (((sk_B_1) = (k4_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ sk_A @ sk_C_1)))),
% 0.71/0.92      inference('demod', [status(thm)], ['37', '38'])).
% 0.71/0.92  thf(t79_xboole_1, axiom,
% 0.71/0.92    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.71/0.92  thf('40', plain,
% 0.71/0.92      (![X23 : $i, X24 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X23 @ X24) @ X24)),
% 0.71/0.92      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.71/0.92  thf('41', plain, ((r1_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.71/0.92      inference('sup+', [status(thm)], ['39', '40'])).
% 0.71/0.92  thf('42', plain, ($false), inference('demod', [status(thm)], ['0', '41'])).
% 0.71/0.92  
% 0.71/0.92  % SZS output end Refutation
% 0.71/0.92  
% 0.71/0.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

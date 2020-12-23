%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fUAaYifM5N

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:38 EST 2020

% Result     : Theorem 2.82s
% Output     : Refutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   52 (  66 expanded)
%              Number of leaves         :   16 (  27 expanded)
%              Depth                    :   12
%              Number of atoms          :  348 ( 460 expanded)
%              Number of equality atoms :   29 (  36 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('3',plain,(
    r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('5',plain,
    ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('7',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ k1_xboole_0 )
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('9',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C )
    = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('11',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C )
    = ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('13',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('14',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('15',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

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

thf('19',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['13','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['12','23'])).

thf('25',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['11','26'])).

thf('28',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('29',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['0','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fUAaYifM5N
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:25:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.82/3.00  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.82/3.00  % Solved by: fo/fo7.sh
% 2.82/3.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.82/3.00  % done 3765 iterations in 2.536s
% 2.82/3.00  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.82/3.00  % SZS output start Refutation
% 2.82/3.00  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.82/3.00  thf(sk_B_type, type, sk_B: $i).
% 2.82/3.00  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.82/3.00  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.82/3.00  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.82/3.00  thf(sk_C_type, type, sk_C: $i).
% 2.82/3.00  thf(sk_A_type, type, sk_A: $i).
% 2.82/3.00  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.82/3.00  thf(t81_xboole_1, conjecture,
% 2.82/3.00    (![A:$i,B:$i,C:$i]:
% 2.82/3.00     ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 2.82/3.00       ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ))).
% 2.82/3.00  thf(zf_stmt_0, negated_conjecture,
% 2.82/3.00    (~( ![A:$i,B:$i,C:$i]:
% 2.82/3.00        ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 2.82/3.00          ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )),
% 2.82/3.00    inference('cnf.neg', [status(esa)], [t81_xboole_1])).
% 2.82/3.00  thf('0', plain, (~ (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 2.82/3.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.00  thf('1', plain, ((r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 2.82/3.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.82/3.00  thf(symmetry_r1_xboole_0, axiom,
% 2.82/3.00    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 2.82/3.00  thf('2', plain,
% 2.82/3.00      (![X3 : $i, X4 : $i]:
% 2.82/3.00         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 2.82/3.00      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.82/3.00  thf('3', plain, ((r1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 2.82/3.00      inference('sup-', [status(thm)], ['1', '2'])).
% 2.82/3.00  thf(d7_xboole_0, axiom,
% 2.82/3.00    (![A:$i,B:$i]:
% 2.82/3.00     ( ( r1_xboole_0 @ A @ B ) <=>
% 2.82/3.00       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 2.82/3.00  thf('4', plain,
% 2.82/3.00      (![X0 : $i, X1 : $i]:
% 2.82/3.00         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 2.82/3.00      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.82/3.00  thf('5', plain,
% 2.82/3.00      (((k3_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ sk_A) = (k1_xboole_0))),
% 2.82/3.00      inference('sup-', [status(thm)], ['3', '4'])).
% 2.82/3.00  thf(t47_xboole_1, axiom,
% 2.82/3.00    (![A:$i,B:$i]:
% 2.82/3.00     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 2.82/3.00  thf('6', plain,
% 2.82/3.00      (![X11 : $i, X12 : $i]:
% 2.82/3.00         ((k4_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12))
% 2.82/3.00           = (k4_xboole_0 @ X11 @ X12))),
% 2.82/3.00      inference('cnf', [status(esa)], [t47_xboole_1])).
% 2.82/3.00  thf('7', plain,
% 2.82/3.00      (((k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ k1_xboole_0)
% 2.82/3.00         = (k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ sk_A))),
% 2.82/3.00      inference('sup+', [status(thm)], ['5', '6'])).
% 2.82/3.00  thf(t3_boole, axiom,
% 2.82/3.00    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.82/3.00  thf('8', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 2.82/3.00      inference('cnf', [status(esa)], [t3_boole])).
% 2.82/3.00  thf('9', plain,
% 2.82/3.00      (((k4_xboole_0 @ sk_B @ sk_C)
% 2.82/3.00         = (k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ sk_A))),
% 2.82/3.00      inference('demod', [status(thm)], ['7', '8'])).
% 2.82/3.00  thf(t41_xboole_1, axiom,
% 2.82/3.00    (![A:$i,B:$i,C:$i]:
% 2.82/3.00     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 2.82/3.00       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 2.82/3.00  thf('10', plain,
% 2.82/3.00      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.82/3.00         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 2.82/3.00           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 2.82/3.00      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.82/3.00  thf('11', plain,
% 2.82/3.00      (((k4_xboole_0 @ sk_B @ sk_C)
% 2.82/3.00         = (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C @ sk_A)))),
% 2.82/3.00      inference('demod', [status(thm)], ['9', '10'])).
% 2.82/3.00  thf(t39_xboole_1, axiom,
% 2.82/3.00    (![A:$i,B:$i]:
% 2.82/3.00     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 2.82/3.00  thf('12', plain,
% 2.82/3.00      (![X5 : $i, X6 : $i]:
% 2.82/3.00         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 2.82/3.00           = (k2_xboole_0 @ X5 @ X6))),
% 2.82/3.00      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.82/3.00  thf('13', plain,
% 2.82/3.00      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.82/3.00         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 2.82/3.00           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 2.82/3.00      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.82/3.00  thf(t79_xboole_1, axiom,
% 2.82/3.00    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 2.82/3.00  thf('14', plain,
% 2.82/3.00      (![X15 : $i, X16 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X16)),
% 2.82/3.00      inference('cnf', [status(esa)], [t79_xboole_1])).
% 2.82/3.00  thf('15', plain,
% 2.82/3.00      (![X3 : $i, X4 : $i]:
% 2.82/3.00         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 2.82/3.00      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.82/3.00  thf('16', plain,
% 2.82/3.00      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 2.82/3.00      inference('sup-', [status(thm)], ['14', '15'])).
% 2.82/3.00  thf('17', plain,
% 2.82/3.00      (![X0 : $i, X1 : $i]:
% 2.82/3.00         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 2.82/3.00      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.82/3.00  thf('18', plain,
% 2.82/3.00      (![X0 : $i, X1 : $i]:
% 2.82/3.00         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 2.82/3.00      inference('sup-', [status(thm)], ['16', '17'])).
% 2.82/3.00  thf('19', plain,
% 2.82/3.00      (![X11 : $i, X12 : $i]:
% 2.82/3.00         ((k4_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12))
% 2.82/3.00           = (k4_xboole_0 @ X11 @ X12))),
% 2.82/3.00      inference('cnf', [status(esa)], [t47_xboole_1])).
% 2.82/3.00  thf('20', plain,
% 2.82/3.00      (![X0 : $i, X1 : $i]:
% 2.82/3.00         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 2.82/3.00           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.82/3.00      inference('sup+', [status(thm)], ['18', '19'])).
% 2.82/3.00  thf('21', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 2.82/3.00      inference('cnf', [status(esa)], [t3_boole])).
% 2.82/3.00  thf('22', plain,
% 2.82/3.00      (![X0 : $i, X1 : $i]:
% 2.82/3.00         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.82/3.00      inference('demod', [status(thm)], ['20', '21'])).
% 2.82/3.00  thf('23', plain,
% 2.82/3.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.82/3.00         ((X0)
% 2.82/3.00           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 2.82/3.00      inference('sup+', [status(thm)], ['13', '22'])).
% 2.82/3.00  thf('24', plain,
% 2.82/3.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.82/3.00         ((k4_xboole_0 @ X0 @ X1)
% 2.82/3.00           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 2.82/3.00              (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 2.82/3.00      inference('sup+', [status(thm)], ['12', '23'])).
% 2.82/3.00  thf('25', plain,
% 2.82/3.00      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.82/3.00         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 2.82/3.00           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 2.82/3.00      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.82/3.00  thf('26', plain,
% 2.82/3.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.82/3.00         ((k4_xboole_0 @ X0 @ X1)
% 2.82/3.00           = (k4_xboole_0 @ X0 @ 
% 2.82/3.00              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 2.82/3.00      inference('demod', [status(thm)], ['24', '25'])).
% 2.82/3.00  thf('27', plain,
% 2.82/3.00      (((k4_xboole_0 @ sk_A @ sk_C)
% 2.82/3.00         = (k4_xboole_0 @ sk_A @ 
% 2.82/3.00            (k2_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_B @ sk_C))))),
% 2.82/3.00      inference('sup+', [status(thm)], ['11', '26'])).
% 2.82/3.00  thf('28', plain,
% 2.82/3.00      (![X5 : $i, X6 : $i]:
% 2.82/3.00         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 2.82/3.00           = (k2_xboole_0 @ X5 @ X6))),
% 2.82/3.00      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.82/3.00  thf('29', plain,
% 2.82/3.00      (((k4_xboole_0 @ sk_A @ sk_C)
% 2.82/3.00         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B)))),
% 2.82/3.00      inference('demod', [status(thm)], ['27', '28'])).
% 2.82/3.00  thf('30', plain,
% 2.82/3.00      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.82/3.00         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 2.82/3.00           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 2.82/3.00      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.82/3.00  thf('31', plain,
% 2.82/3.00      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 2.82/3.00      inference('sup-', [status(thm)], ['14', '15'])).
% 2.82/3.00  thf('32', plain,
% 2.82/3.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.82/3.00         (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.82/3.00      inference('sup+', [status(thm)], ['30', '31'])).
% 2.82/3.00  thf('33', plain, ((r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 2.82/3.00      inference('sup+', [status(thm)], ['29', '32'])).
% 2.82/3.00  thf('34', plain, ($false), inference('demod', [status(thm)], ['0', '33'])).
% 2.82/3.00  
% 2.82/3.00  % SZS output end Refutation
% 2.82/3.00  
% 2.82/3.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TVNzeioXWX

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:44 EST 2020

% Result     : Theorem 19.12s
% Output     : Refutation 19.12s
% Verified   : 
% Statistics : Number of formulae       :   42 (  52 expanded)
%              Number of leaves         :   17 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :  292 ( 366 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :   10 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t81_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t81_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_tarski @ X10 @ ( k2_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t79_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X36: $i,X37: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X36 ) @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( r1_tarski @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t108_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ ( k3_xboole_0 @ X7 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k1_zfmisc_1 @ X0 ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t110_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_tarski @ X15 @ X14 )
      | ( r1_tarski @ ( k5_xboole_0 @ X13 @ X15 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t110_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_xboole_0 @ ( k1_zfmisc_1 @ X0 ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_tarski @ X2 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ ( k1_zfmisc_1 @ X0 ) @ ( k3_xboole_0 @ ( k1_zfmisc_1 @ X0 ) @ X2 ) ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ X0 ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('17',plain,(
    ! [X36: $i,X37: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X36 ) @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( r1_tarski @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_tarski @ X15 @ X14 )
      | ( r1_tarski @ ( k5_xboole_0 @ X13 @ X15 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t110_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_xboole_0 @ ( k1_zfmisc_1 @ X1 ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_tarski @ X2 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ ( k1_zfmisc_1 @ X1 ) @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ X0 ) @ X2 ) ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','21'])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['0','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TVNzeioXWX
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:53:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 19.12/19.35  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 19.12/19.35  % Solved by: fo/fo7.sh
% 19.12/19.35  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 19.12/19.35  % done 15125 iterations in 18.869s
% 19.12/19.35  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 19.12/19.35  % SZS output start Refutation
% 19.12/19.35  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 19.12/19.35  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 19.12/19.35  thf(sk_A_type, type, sk_A: $i).
% 19.12/19.35  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 19.12/19.35  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 19.12/19.35  thf(sk_B_type, type, sk_B: $i).
% 19.12/19.35  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 19.12/19.35  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 19.12/19.35  thf(t81_zfmisc_1, conjecture,
% 19.12/19.35    (![A:$i,B:$i]:
% 19.12/19.35     ( r1_tarski @
% 19.12/19.35       ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) @ 
% 19.12/19.35       ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) ))).
% 19.12/19.35  thf(zf_stmt_0, negated_conjecture,
% 19.12/19.35    (~( ![A:$i,B:$i]:
% 19.12/19.35        ( r1_tarski @
% 19.12/19.35          ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) @ 
% 19.12/19.35          ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 19.12/19.35    inference('cnf.neg', [status(esa)], [t81_zfmisc_1])).
% 19.12/19.35  thf('0', plain,
% 19.12/19.35      (~ (r1_tarski @ 
% 19.12/19.35          (k2_xboole_0 @ (k1_zfmisc_1 @ sk_A) @ (k1_zfmisc_1 @ sk_B)) @ 
% 19.12/19.35          (k1_zfmisc_1 @ (k2_xboole_0 @ sk_A @ sk_B)))),
% 19.12/19.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.12/19.35  thf(t98_xboole_1, axiom,
% 19.12/19.35    (![A:$i,B:$i]:
% 19.12/19.35     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 19.12/19.35  thf('1', plain,
% 19.12/19.35      (![X18 : $i, X19 : $i]:
% 19.12/19.35         ((k2_xboole_0 @ X18 @ X19)
% 19.12/19.35           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 19.12/19.35      inference('cnf', [status(esa)], [t98_xboole_1])).
% 19.12/19.35  thf(d10_xboole_0, axiom,
% 19.12/19.35    (![A:$i,B:$i]:
% 19.12/19.35     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 19.12/19.35  thf('2', plain,
% 19.12/19.35      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 19.12/19.35      inference('cnf', [status(esa)], [d10_xboole_0])).
% 19.12/19.35  thf('3', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 19.12/19.35      inference('simplify', [status(thm)], ['2'])).
% 19.12/19.35  thf(t10_xboole_1, axiom,
% 19.12/19.35    (![A:$i,B:$i,C:$i]:
% 19.12/19.35     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 19.12/19.35  thf('4', plain,
% 19.12/19.35      (![X10 : $i, X11 : $i, X12 : $i]:
% 19.12/19.35         (~ (r1_tarski @ X10 @ X11)
% 19.12/19.35          | (r1_tarski @ X10 @ (k2_xboole_0 @ X12 @ X11)))),
% 19.12/19.35      inference('cnf', [status(esa)], [t10_xboole_1])).
% 19.12/19.35  thf('5', plain,
% 19.12/19.35      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 19.12/19.35      inference('sup-', [status(thm)], ['3', '4'])).
% 19.12/19.35  thf(t79_zfmisc_1, axiom,
% 19.12/19.35    (![A:$i,B:$i]:
% 19.12/19.35     ( ( r1_tarski @ A @ B ) =>
% 19.12/19.35       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 19.12/19.35  thf('6', plain,
% 19.12/19.35      (![X36 : $i, X37 : $i]:
% 19.12/19.35         ((r1_tarski @ (k1_zfmisc_1 @ X36) @ (k1_zfmisc_1 @ X37))
% 19.12/19.35          | ~ (r1_tarski @ X36 @ X37))),
% 19.12/19.35      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 19.12/19.35  thf('7', plain,
% 19.12/19.35      (![X0 : $i, X1 : $i]:
% 19.12/19.35         (r1_tarski @ (k1_zfmisc_1 @ X0) @ 
% 19.12/19.35          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 19.12/19.35      inference('sup-', [status(thm)], ['5', '6'])).
% 19.12/19.35  thf(t108_xboole_1, axiom,
% 19.12/19.35    (![A:$i,B:$i,C:$i]:
% 19.12/19.35     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ))).
% 19.12/19.35  thf('8', plain,
% 19.12/19.35      (![X7 : $i, X8 : $i, X9 : $i]:
% 19.12/19.35         (~ (r1_tarski @ X7 @ X8) | (r1_tarski @ (k3_xboole_0 @ X7 @ X9) @ X8))),
% 19.12/19.35      inference('cnf', [status(esa)], [t108_xboole_1])).
% 19.12/19.35  thf('9', plain,
% 19.12/19.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.12/19.35         (r1_tarski @ (k3_xboole_0 @ (k1_zfmisc_1 @ X0) @ X2) @ 
% 19.12/19.35          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 19.12/19.35      inference('sup-', [status(thm)], ['7', '8'])).
% 19.12/19.35  thf('10', plain,
% 19.12/19.35      (![X0 : $i, X1 : $i]:
% 19.12/19.35         (r1_tarski @ (k1_zfmisc_1 @ X0) @ 
% 19.12/19.35          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 19.12/19.35      inference('sup-', [status(thm)], ['5', '6'])).
% 19.12/19.35  thf(t110_xboole_1, axiom,
% 19.12/19.35    (![A:$i,B:$i,C:$i]:
% 19.12/19.35     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 19.12/19.35       ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 19.12/19.35  thf('11', plain,
% 19.12/19.35      (![X13 : $i, X14 : $i, X15 : $i]:
% 19.12/19.35         (~ (r1_tarski @ X13 @ X14)
% 19.12/19.35          | ~ (r1_tarski @ X15 @ X14)
% 19.12/19.35          | (r1_tarski @ (k5_xboole_0 @ X13 @ X15) @ X14))),
% 19.12/19.35      inference('cnf', [status(esa)], [t110_xboole_1])).
% 19.12/19.35  thf('12', plain,
% 19.12/19.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.12/19.35         ((r1_tarski @ (k5_xboole_0 @ (k1_zfmisc_1 @ X0) @ X2) @ 
% 19.12/19.35           (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 19.12/19.35          | ~ (r1_tarski @ X2 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0))))),
% 19.12/19.35      inference('sup-', [status(thm)], ['10', '11'])).
% 19.12/19.35  thf('13', plain,
% 19.12/19.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.12/19.35         (r1_tarski @ 
% 19.12/19.35          (k5_xboole_0 @ (k1_zfmisc_1 @ X0) @ 
% 19.12/19.35           (k3_xboole_0 @ (k1_zfmisc_1 @ X0) @ X2)) @ 
% 19.12/19.35          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 19.12/19.35      inference('sup-', [status(thm)], ['9', '12'])).
% 19.12/19.35  thf(t100_xboole_1, axiom,
% 19.12/19.35    (![A:$i,B:$i]:
% 19.12/19.35     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 19.12/19.35  thf('14', plain,
% 19.12/19.35      (![X5 : $i, X6 : $i]:
% 19.12/19.35         ((k4_xboole_0 @ X5 @ X6)
% 19.12/19.35           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 19.12/19.35      inference('cnf', [status(esa)], [t100_xboole_1])).
% 19.12/19.35  thf('15', plain,
% 19.12/19.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.12/19.35         (r1_tarski @ (k4_xboole_0 @ (k1_zfmisc_1 @ X0) @ X2) @ 
% 19.12/19.35          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 19.12/19.35      inference('demod', [status(thm)], ['13', '14'])).
% 19.12/19.35  thf(t7_xboole_1, axiom,
% 19.12/19.35    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 19.12/19.35  thf('16', plain,
% 19.12/19.35      (![X16 : $i, X17 : $i]: (r1_tarski @ X16 @ (k2_xboole_0 @ X16 @ X17))),
% 19.12/19.35      inference('cnf', [status(esa)], [t7_xboole_1])).
% 19.12/19.35  thf('17', plain,
% 19.12/19.35      (![X36 : $i, X37 : $i]:
% 19.12/19.35         ((r1_tarski @ (k1_zfmisc_1 @ X36) @ (k1_zfmisc_1 @ X37))
% 19.12/19.35          | ~ (r1_tarski @ X36 @ X37))),
% 19.12/19.35      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 19.12/19.35  thf('18', plain,
% 19.12/19.35      (![X0 : $i, X1 : $i]:
% 19.12/19.35         (r1_tarski @ (k1_zfmisc_1 @ X1) @ 
% 19.12/19.35          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 19.12/19.35      inference('sup-', [status(thm)], ['16', '17'])).
% 19.12/19.35  thf('19', plain,
% 19.12/19.35      (![X13 : $i, X14 : $i, X15 : $i]:
% 19.12/19.35         (~ (r1_tarski @ X13 @ X14)
% 19.12/19.35          | ~ (r1_tarski @ X15 @ X14)
% 19.12/19.35          | (r1_tarski @ (k5_xboole_0 @ X13 @ X15) @ X14))),
% 19.12/19.35      inference('cnf', [status(esa)], [t110_xboole_1])).
% 19.12/19.35  thf('20', plain,
% 19.12/19.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.12/19.35         ((r1_tarski @ (k5_xboole_0 @ (k1_zfmisc_1 @ X1) @ X2) @ 
% 19.12/19.35           (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 19.12/19.35          | ~ (r1_tarski @ X2 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0))))),
% 19.12/19.35      inference('sup-', [status(thm)], ['18', '19'])).
% 19.12/19.35  thf('21', plain,
% 19.12/19.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.12/19.35         (r1_tarski @ 
% 19.12/19.35          (k5_xboole_0 @ (k1_zfmisc_1 @ X1) @ 
% 19.12/19.35           (k4_xboole_0 @ (k1_zfmisc_1 @ X0) @ X2)) @ 
% 19.12/19.35          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 19.12/19.35      inference('sup-', [status(thm)], ['15', '20'])).
% 19.12/19.35  thf('22', plain,
% 19.12/19.35      (![X0 : $i, X1 : $i]:
% 19.12/19.35         (r1_tarski @ 
% 19.12/19.35          (k2_xboole_0 @ (k1_zfmisc_1 @ X1) @ (k1_zfmisc_1 @ X0)) @ 
% 19.12/19.35          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 19.12/19.35      inference('sup+', [status(thm)], ['1', '21'])).
% 19.12/19.35  thf('23', plain, ($false), inference('demod', [status(thm)], ['0', '22'])).
% 19.12/19.35  
% 19.12/19.35  % SZS output end Refutation
% 19.12/19.35  
% 19.12/19.36  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZSiXO16I4D

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:45 EST 2020

% Result     : Theorem 2.48s
% Output     : Refutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   34 (  35 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    8
%              Number of atoms          :  220 ( 228 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   10 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X6 @ ( k2_xboole_0 @ X8 @ X7 ) ) ) ),
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
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X27 ) @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( r1_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t109_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ ( k4_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ X0 ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('11',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X27 ) @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( r1_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t110_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X11 @ X10 )
      | ( r1_tarski @ ( k5_xboole_0 @ X9 @ X11 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t110_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_xboole_0 @ ( k1_zfmisc_1 @ X1 ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_tarski @ X2 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ ( k1_zfmisc_1 @ X1 ) @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ X0 ) @ X2 ) ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','15'])).

thf('17',plain,(
    $false ),
    inference(demod,[status(thm)],['0','16'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZSiXO16I4D
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:47:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.48/2.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.48/2.66  % Solved by: fo/fo7.sh
% 2.48/2.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.48/2.66  % done 3569 iterations in 2.209s
% 2.48/2.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.48/2.66  % SZS output start Refutation
% 2.48/2.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.48/2.66  thf(sk_A_type, type, sk_A: $i).
% 2.48/2.66  thf(sk_B_type, type, sk_B: $i).
% 2.48/2.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.48/2.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.48/2.66  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.48/2.66  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 2.48/2.66  thf(t81_zfmisc_1, conjecture,
% 2.48/2.66    (![A:$i,B:$i]:
% 2.48/2.66     ( r1_tarski @
% 2.48/2.66       ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) @ 
% 2.48/2.66       ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) ))).
% 2.48/2.66  thf(zf_stmt_0, negated_conjecture,
% 2.48/2.66    (~( ![A:$i,B:$i]:
% 2.48/2.66        ( r1_tarski @
% 2.48/2.66          ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) @ 
% 2.48/2.66          ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 2.48/2.66    inference('cnf.neg', [status(esa)], [t81_zfmisc_1])).
% 2.48/2.66  thf('0', plain,
% 2.48/2.66      (~ (r1_tarski @ 
% 2.48/2.66          (k2_xboole_0 @ (k1_zfmisc_1 @ sk_A) @ (k1_zfmisc_1 @ sk_B)) @ 
% 2.48/2.66          (k1_zfmisc_1 @ (k2_xboole_0 @ sk_A @ sk_B)))),
% 2.48/2.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.48/2.66  thf(t98_xboole_1, axiom,
% 2.48/2.66    (![A:$i,B:$i]:
% 2.48/2.66     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 2.48/2.66  thf('1', plain,
% 2.48/2.66      (![X14 : $i, X15 : $i]:
% 2.48/2.66         ((k2_xboole_0 @ X14 @ X15)
% 2.48/2.66           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 2.48/2.66      inference('cnf', [status(esa)], [t98_xboole_1])).
% 2.48/2.66  thf(d10_xboole_0, axiom,
% 2.48/2.66    (![A:$i,B:$i]:
% 2.48/2.66     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.48/2.66  thf('2', plain,
% 2.48/2.66      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 2.48/2.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.48/2.66  thf('3', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.48/2.66      inference('simplify', [status(thm)], ['2'])).
% 2.48/2.66  thf(t10_xboole_1, axiom,
% 2.48/2.66    (![A:$i,B:$i,C:$i]:
% 2.48/2.66     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 2.48/2.66  thf('4', plain,
% 2.48/2.66      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.48/2.66         (~ (r1_tarski @ X6 @ X7) | (r1_tarski @ X6 @ (k2_xboole_0 @ X8 @ X7)))),
% 2.48/2.66      inference('cnf', [status(esa)], [t10_xboole_1])).
% 2.48/2.66  thf('5', plain,
% 2.48/2.66      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 2.48/2.66      inference('sup-', [status(thm)], ['3', '4'])).
% 2.48/2.66  thf(t79_zfmisc_1, axiom,
% 2.48/2.66    (![A:$i,B:$i]:
% 2.48/2.66     ( ( r1_tarski @ A @ B ) =>
% 2.48/2.66       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 2.48/2.66  thf('6', plain,
% 2.48/2.66      (![X27 : $i, X28 : $i]:
% 2.48/2.66         ((r1_tarski @ (k1_zfmisc_1 @ X27) @ (k1_zfmisc_1 @ X28))
% 2.48/2.66          | ~ (r1_tarski @ X27 @ X28))),
% 2.48/2.66      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 2.48/2.66  thf('7', plain,
% 2.48/2.66      (![X0 : $i, X1 : $i]:
% 2.48/2.66         (r1_tarski @ (k1_zfmisc_1 @ X0) @ 
% 2.48/2.66          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.48/2.66      inference('sup-', [status(thm)], ['5', '6'])).
% 2.48/2.66  thf(t109_xboole_1, axiom,
% 2.48/2.66    (![A:$i,B:$i,C:$i]:
% 2.48/2.66     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 2.48/2.66  thf('8', plain,
% 2.48/2.66      (![X3 : $i, X4 : $i, X5 : $i]:
% 2.48/2.66         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ (k4_xboole_0 @ X3 @ X5) @ X4))),
% 2.48/2.66      inference('cnf', [status(esa)], [t109_xboole_1])).
% 2.48/2.66  thf('9', plain,
% 2.48/2.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.48/2.66         (r1_tarski @ (k4_xboole_0 @ (k1_zfmisc_1 @ X0) @ X2) @ 
% 2.48/2.66          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.48/2.66      inference('sup-', [status(thm)], ['7', '8'])).
% 2.48/2.66  thf(t7_xboole_1, axiom,
% 2.48/2.66    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 2.48/2.66  thf('10', plain,
% 2.48/2.66      (![X12 : $i, X13 : $i]: (r1_tarski @ X12 @ (k2_xboole_0 @ X12 @ X13))),
% 2.48/2.66      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.48/2.66  thf('11', plain,
% 2.48/2.66      (![X27 : $i, X28 : $i]:
% 2.48/2.66         ((r1_tarski @ (k1_zfmisc_1 @ X27) @ (k1_zfmisc_1 @ X28))
% 2.48/2.66          | ~ (r1_tarski @ X27 @ X28))),
% 2.48/2.66      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 2.48/2.66  thf('12', plain,
% 2.48/2.66      (![X0 : $i, X1 : $i]:
% 2.48/2.66         (r1_tarski @ (k1_zfmisc_1 @ X1) @ 
% 2.48/2.66          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.48/2.66      inference('sup-', [status(thm)], ['10', '11'])).
% 2.48/2.66  thf(t110_xboole_1, axiom,
% 2.48/2.66    (![A:$i,B:$i,C:$i]:
% 2.48/2.66     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 2.48/2.66       ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 2.48/2.66  thf('13', plain,
% 2.48/2.66      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.48/2.66         (~ (r1_tarski @ X9 @ X10)
% 2.48/2.66          | ~ (r1_tarski @ X11 @ X10)
% 2.48/2.66          | (r1_tarski @ (k5_xboole_0 @ X9 @ X11) @ X10))),
% 2.48/2.66      inference('cnf', [status(esa)], [t110_xboole_1])).
% 2.48/2.66  thf('14', plain,
% 2.48/2.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.48/2.66         ((r1_tarski @ (k5_xboole_0 @ (k1_zfmisc_1 @ X1) @ X2) @ 
% 2.48/2.66           (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 2.48/2.66          | ~ (r1_tarski @ X2 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0))))),
% 2.48/2.66      inference('sup-', [status(thm)], ['12', '13'])).
% 2.48/2.66  thf('15', plain,
% 2.48/2.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.48/2.66         (r1_tarski @ 
% 2.48/2.66          (k5_xboole_0 @ (k1_zfmisc_1 @ X1) @ 
% 2.48/2.66           (k4_xboole_0 @ (k1_zfmisc_1 @ X0) @ X2)) @ 
% 2.48/2.66          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.48/2.66      inference('sup-', [status(thm)], ['9', '14'])).
% 2.48/2.66  thf('16', plain,
% 2.48/2.66      (![X0 : $i, X1 : $i]:
% 2.48/2.66         (r1_tarski @ 
% 2.48/2.66          (k2_xboole_0 @ (k1_zfmisc_1 @ X1) @ (k1_zfmisc_1 @ X0)) @ 
% 2.48/2.66          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.48/2.66      inference('sup+', [status(thm)], ['1', '15'])).
% 2.48/2.66  thf('17', plain, ($false), inference('demod', [status(thm)], ['0', '16'])).
% 2.48/2.66  
% 2.48/2.66  % SZS output end Refutation
% 2.48/2.66  
% 2.48/2.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

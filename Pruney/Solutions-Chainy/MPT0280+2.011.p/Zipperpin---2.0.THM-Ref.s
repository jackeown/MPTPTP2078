%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aaLy4xXETT

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:45 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   26 (  27 expanded)
%              Number of leaves         :   11 (  12 expanded)
%              Depth                    :    6
%              Number of atoms          :  165 ( 173 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X3 @ ( k2_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t79_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X11 ) @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X11 ) @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ X1 ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_tarski @ X2 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    $false ),
    inference(demod,[status(thm)],['0','12'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aaLy4xXETT
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:28:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.50/1.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.50/1.73  % Solved by: fo/fo7.sh
% 1.50/1.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.50/1.73  % done 1312 iterations in 1.274s
% 1.50/1.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.50/1.73  % SZS output start Refutation
% 1.50/1.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.50/1.73  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.50/1.73  thf(sk_B_type, type, sk_B: $i).
% 1.50/1.73  thf(sk_A_type, type, sk_A: $i).
% 1.50/1.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.50/1.73  thf(t81_zfmisc_1, conjecture,
% 1.50/1.73    (![A:$i,B:$i]:
% 1.50/1.73     ( r1_tarski @
% 1.50/1.73       ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) @ 
% 1.50/1.73       ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) ))).
% 1.50/1.73  thf(zf_stmt_0, negated_conjecture,
% 1.50/1.73    (~( ![A:$i,B:$i]:
% 1.50/1.73        ( r1_tarski @
% 1.50/1.73          ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) @ 
% 1.50/1.73          ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 1.50/1.73    inference('cnf.neg', [status(esa)], [t81_zfmisc_1])).
% 1.50/1.73  thf('0', plain,
% 1.50/1.73      (~ (r1_tarski @ 
% 1.50/1.73          (k2_xboole_0 @ (k1_zfmisc_1 @ sk_A) @ (k1_zfmisc_1 @ sk_B)) @ 
% 1.50/1.73          (k1_zfmisc_1 @ (k2_xboole_0 @ sk_A @ sk_B)))),
% 1.50/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.73  thf(d10_xboole_0, axiom,
% 1.50/1.73    (![A:$i,B:$i]:
% 1.50/1.73     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.50/1.73  thf('1', plain,
% 1.50/1.73      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.50/1.73      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.50/1.73  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.50/1.73      inference('simplify', [status(thm)], ['1'])).
% 1.50/1.73  thf(t10_xboole_1, axiom,
% 1.50/1.73    (![A:$i,B:$i,C:$i]:
% 1.50/1.73     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 1.50/1.73  thf('3', plain,
% 1.50/1.73      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.50/1.73         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ X3 @ (k2_xboole_0 @ X5 @ X4)))),
% 1.50/1.73      inference('cnf', [status(esa)], [t10_xboole_1])).
% 1.50/1.73  thf('4', plain,
% 1.50/1.73      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.50/1.73      inference('sup-', [status(thm)], ['2', '3'])).
% 1.50/1.73  thf(t79_zfmisc_1, axiom,
% 1.50/1.73    (![A:$i,B:$i]:
% 1.50/1.73     ( ( r1_tarski @ A @ B ) =>
% 1.50/1.73       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 1.50/1.73  thf('5', plain,
% 1.50/1.73      (![X11 : $i, X12 : $i]:
% 1.50/1.73         ((r1_tarski @ (k1_zfmisc_1 @ X11) @ (k1_zfmisc_1 @ X12))
% 1.50/1.73          | ~ (r1_tarski @ X11 @ X12))),
% 1.50/1.73      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 1.50/1.73  thf('6', plain,
% 1.50/1.73      (![X0 : $i, X1 : $i]:
% 1.50/1.73         (r1_tarski @ (k1_zfmisc_1 @ X0) @ 
% 1.50/1.73          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.50/1.73      inference('sup-', [status(thm)], ['4', '5'])).
% 1.50/1.73  thf(t7_xboole_1, axiom,
% 1.50/1.73    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.50/1.73  thf('7', plain,
% 1.50/1.73      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 1.50/1.73      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.50/1.73  thf('8', plain,
% 1.50/1.73      (![X11 : $i, X12 : $i]:
% 1.50/1.73         ((r1_tarski @ (k1_zfmisc_1 @ X11) @ (k1_zfmisc_1 @ X12))
% 1.50/1.73          | ~ (r1_tarski @ X11 @ X12))),
% 1.50/1.73      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 1.50/1.73  thf('9', plain,
% 1.50/1.73      (![X0 : $i, X1 : $i]:
% 1.50/1.73         (r1_tarski @ (k1_zfmisc_1 @ X1) @ 
% 1.50/1.73          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.50/1.73      inference('sup-', [status(thm)], ['7', '8'])).
% 1.50/1.73  thf(t8_xboole_1, axiom,
% 1.50/1.73    (![A:$i,B:$i,C:$i]:
% 1.50/1.73     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 1.50/1.73       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.50/1.73  thf('10', plain,
% 1.50/1.73      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.50/1.73         (~ (r1_tarski @ X8 @ X9)
% 1.50/1.73          | ~ (r1_tarski @ X10 @ X9)
% 1.50/1.73          | (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 1.50/1.73      inference('cnf', [status(esa)], [t8_xboole_1])).
% 1.50/1.73  thf('11', plain,
% 1.50/1.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.50/1.73         ((r1_tarski @ (k2_xboole_0 @ (k1_zfmisc_1 @ X1) @ X2) @ 
% 1.50/1.73           (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 1.50/1.73          | ~ (r1_tarski @ X2 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0))))),
% 1.50/1.73      inference('sup-', [status(thm)], ['9', '10'])).
% 1.50/1.73  thf('12', plain,
% 1.50/1.73      (![X0 : $i, X1 : $i]:
% 1.50/1.73         (r1_tarski @ 
% 1.50/1.73          (k2_xboole_0 @ (k1_zfmisc_1 @ X1) @ (k1_zfmisc_1 @ X0)) @ 
% 1.50/1.73          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.50/1.73      inference('sup-', [status(thm)], ['6', '11'])).
% 1.50/1.73  thf('13', plain, ($false), inference('demod', [status(thm)], ['0', '12'])).
% 1.50/1.73  
% 1.50/1.73  % SZS output end Refutation
% 1.50/1.73  
% 1.50/1.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

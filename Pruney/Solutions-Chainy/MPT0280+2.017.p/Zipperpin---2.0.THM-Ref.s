%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dBBtVSH8x9

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   26 (  27 expanded)
%              Number of leaves         :   12 (  13 expanded)
%              Depth                    :    5
%              Number of atoms          :  161 ( 169 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_tarski @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X2 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t79_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X10 ) @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('7',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X10 ) @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X9 @ X8 )
      | ( r1_tarski @ ( k2_xboole_0 @ X7 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ X1 ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_tarski @ X2 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    $false ),
    inference(demod,[status(thm)],['0','11'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dBBtVSH8x9
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:37:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 39 iterations in 0.037s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(t81_zfmisc_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( r1_tarski @
% 0.21/0.49       ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) @ 
% 0.21/0.49       ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i]:
% 0.21/0.49        ( r1_tarski @
% 0.21/0.49          ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) @ 
% 0.21/0.49          ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t81_zfmisc_1])).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      (~ (r1_tarski @ 
% 0.21/0.49          (k2_xboole_0 @ (k1_zfmisc_1 @ sk_A) @ (k1_zfmisc_1 @ sk_B)) @ 
% 0.21/0.49          (k1_zfmisc_1 @ (k2_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t36_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.21/0.49      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.21/0.49  thf(t44_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 0.21/0.49       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.49         ((r1_tarski @ X2 @ (k2_xboole_0 @ X3 @ X4))
% 0.21/0.49          | ~ (r1_tarski @ (k4_xboole_0 @ X2 @ X3) @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.49  thf(t79_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r1_tarski @ A @ B ) =>
% 0.21/0.49       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X10 : $i, X11 : $i]:
% 0.21/0.49         ((r1_tarski @ (k1_zfmisc_1 @ X10) @ (k1_zfmisc_1 @ X11))
% 0.21/0.49          | ~ (r1_tarski @ X10 @ X11))),
% 0.21/0.49      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (r1_tarski @ (k1_zfmisc_1 @ X0) @ 
% 0.21/0.49          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.49  thf(t7_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X5 : $i, X6 : $i]: (r1_tarski @ X5 @ (k2_xboole_0 @ X5 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X10 : $i, X11 : $i]:
% 0.21/0.49         ((r1_tarski @ (k1_zfmisc_1 @ X10) @ (k1_zfmisc_1 @ X11))
% 0.21/0.49          | ~ (r1_tarski @ X10 @ X11))),
% 0.21/0.49      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (r1_tarski @ (k1_zfmisc_1 @ X1) @ 
% 0.21/0.49          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.49  thf(t8_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.21/0.49       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.49         (~ (r1_tarski @ X7 @ X8)
% 0.21/0.49          | ~ (r1_tarski @ X9 @ X8)
% 0.21/0.49          | (r1_tarski @ (k2_xboole_0 @ X7 @ X9) @ X8))),
% 0.21/0.49      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((r1_tarski @ (k2_xboole_0 @ (k1_zfmisc_1 @ X1) @ X2) @ 
% 0.21/0.49           (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 0.21/0.49          | ~ (r1_tarski @ X2 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (r1_tarski @ 
% 0.21/0.49          (k2_xboole_0 @ (k1_zfmisc_1 @ X1) @ (k1_zfmisc_1 @ X0)) @ 
% 0.21/0.49          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['5', '10'])).
% 0.21/0.49  thf('12', plain, ($false), inference('demod', [status(thm)], ['0', '11'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

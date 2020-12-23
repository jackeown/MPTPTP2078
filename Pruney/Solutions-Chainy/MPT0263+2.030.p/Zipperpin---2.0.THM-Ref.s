%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6P6w0R5FnM

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:34 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   26 (  29 expanded)
%              Number of leaves         :   12 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :  131 ( 160 expanded)
%              Number of equality atoms :   14 (  17 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('0',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X9 ) @ X10 )
      | ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t58_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
      | ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
        | ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t58_zfmisc_1])).

thf('1',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X8 ) @ X7 )
        = X7 )
      | ~ ( r2_hidden @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('4',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) )
      = X2 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('6',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('8',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('11',plain,(
    ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['8','11'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.17  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6P6w0R5FnM
% 0.17/0.39  % Computer   : n025.cluster.edu
% 0.17/0.39  % Model      : x86_64 x86_64
% 0.17/0.39  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.39  % Memory     : 8042.1875MB
% 0.17/0.39  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.39  % CPULimit   : 60
% 0.17/0.39  % DateTime   : Tue Dec  1 17:54:06 EST 2020
% 0.17/0.39  % CPUTime    : 
% 0.17/0.39  % Running portfolio for 600 s
% 0.17/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.39  % Number of cores: 8
% 0.24/0.39  % Python version: Python 3.6.8
% 0.24/0.39  % Running in FO mode
% 0.25/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.49  % Solved by: fo/fo7.sh
% 0.25/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.49  % done 12 iterations in 0.006s
% 0.25/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.49  % SZS output start Refutation
% 0.25/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.25/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.25/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.25/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.25/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.25/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.25/0.49  thf(l27_zfmisc_1, axiom,
% 0.25/0.49    (![A:$i,B:$i]:
% 0.25/0.49     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.25/0.49  thf('0', plain,
% 0.25/0.49      (![X9 : $i, X10 : $i]:
% 0.25/0.49         ((r1_xboole_0 @ (k1_tarski @ X9) @ X10) | (r2_hidden @ X9 @ X10))),
% 0.25/0.49      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.25/0.49  thf(t58_zfmisc_1, conjecture,
% 0.25/0.49    (![A:$i,B:$i]:
% 0.25/0.49     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.25/0.49       ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.25/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.49    (~( ![A:$i,B:$i]:
% 0.25/0.49        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.25/0.49          ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )),
% 0.25/0.49    inference('cnf.neg', [status(esa)], [t58_zfmisc_1])).
% 0.25/0.49  thf('1', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)),
% 0.25/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.49  thf('2', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.25/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.25/0.49  thf(l22_zfmisc_1, axiom,
% 0.25/0.49    (![A:$i,B:$i]:
% 0.25/0.49     ( ( r2_hidden @ A @ B ) =>
% 0.25/0.49       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.25/0.49  thf('3', plain,
% 0.25/0.49      (![X7 : $i, X8 : $i]:
% 0.25/0.49         (((k2_xboole_0 @ (k1_tarski @ X8) @ X7) = (X7))
% 0.25/0.49          | ~ (r2_hidden @ X8 @ X7))),
% 0.25/0.49      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 0.25/0.49  thf('4', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (sk_B))),
% 0.25/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.25/0.49  thf(t21_xboole_1, axiom,
% 0.25/0.49    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.25/0.49  thf('5', plain,
% 0.25/0.49      (![X2 : $i, X3 : $i]:
% 0.25/0.49         ((k3_xboole_0 @ X2 @ (k2_xboole_0 @ X2 @ X3)) = (X2))),
% 0.25/0.49      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.25/0.49  thf('6', plain,
% 0.25/0.49      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))),
% 0.25/0.49      inference('sup+', [status(thm)], ['4', '5'])).
% 0.25/0.49  thf(commutativity_k3_xboole_0, axiom,
% 0.25/0.49    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.25/0.49  thf('7', plain,
% 0.25/0.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.25/0.49      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.25/0.49  thf('8', plain,
% 0.25/0.49      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.25/0.49      inference('demod', [status(thm)], ['6', '7'])).
% 0.25/0.49  thf('9', plain,
% 0.25/0.49      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 0.25/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.49  thf('10', plain,
% 0.25/0.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.25/0.49      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.25/0.49  thf('11', plain,
% 0.25/0.49      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (k1_tarski @ sk_A))),
% 0.25/0.49      inference('demod', [status(thm)], ['9', '10'])).
% 0.25/0.49  thf('12', plain, ($false),
% 0.25/0.49      inference('simplify_reflect-', [status(thm)], ['8', '11'])).
% 0.25/0.49  
% 0.25/0.49  % SZS output end Refutation
% 0.25/0.49  
% 0.25/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

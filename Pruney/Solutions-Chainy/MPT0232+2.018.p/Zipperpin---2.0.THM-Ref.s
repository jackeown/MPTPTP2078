%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XOTjBOiY7x

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   24 (  33 expanded)
%              Number of leaves         :   10 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :  127 ( 223 expanded)
%              Number of equality atoms :   11 (  19 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t27_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
     => ( ( k2_tarski @ A @ B )
        = ( k1_tarski @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
       => ( ( k2_tarski @ A @ B )
          = ( k1_tarski @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_zfmisc_1])).

thf('0',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
     => ( A = C ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( X12 = X11 )
      | ~ ( r1_tarski @ ( k2_tarski @ X12 @ X13 ) @ ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t26_zfmisc_1])).

thf('3',plain,(
    sk_A = sk_C ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_A @ sk_B ) )
    | ( ( k1_tarski @ sk_A )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k1_tarski @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    sk_A = sk_C ),
    inference('sup-',[status(thm)],['1','2'])).

thf('9',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['6','9'])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k1_tarski @ X9 ) @ ( k2_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf('12',plain,(
    $false ),
    inference(demod,[status(thm)],['10','11'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XOTjBOiY7x
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:56:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 20 iterations in 0.013s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.46  thf(t27_zfmisc_1, conjecture,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.21/0.46       ( ( k2_tarski @ A @ B ) = ( k1_tarski @ C ) ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.46        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.21/0.46          ( ( k2_tarski @ A @ B ) = ( k1_tarski @ C ) ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t27_zfmisc_1])).
% 0.21/0.46  thf('0', plain,
% 0.21/0.46      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('1', plain,
% 0.21/0.46      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t26_zfmisc_1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.21/0.46       ( ( A ) = ( C ) ) ))).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.46         (((X12) = (X11))
% 0.21/0.46          | ~ (r1_tarski @ (k2_tarski @ X12 @ X13) @ (k1_tarski @ X11)))),
% 0.21/0.46      inference('cnf', [status(esa)], [t26_zfmisc_1])).
% 0.21/0.46  thf('3', plain, (((sk_A) = (sk_C))),
% 0.21/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.46  thf('4', plain,
% 0.21/0.46      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_A))),
% 0.21/0.46      inference('demod', [status(thm)], ['0', '3'])).
% 0.21/0.46  thf(d10_xboole_0, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.46  thf('5', plain,
% 0.21/0.46      (![X0 : $i, X2 : $i]:
% 0.21/0.46         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.46  thf('6', plain,
% 0.21/0.46      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_A @ sk_B))
% 0.21/0.46        | ((k1_tarski @ sk_A) = (k2_tarski @ sk_A @ sk_B)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.46  thf('7', plain, (((k2_tarski @ sk_A @ sk_B) != (k1_tarski @ sk_C))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('8', plain, (((sk_A) = (sk_C))),
% 0.21/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.46  thf('9', plain, (((k2_tarski @ sk_A @ sk_B) != (k1_tarski @ sk_A))),
% 0.21/0.46      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.46  thf('10', plain,
% 0.21/0.46      (~ (r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_A @ sk_B))),
% 0.21/0.46      inference('simplify_reflect-', [status(thm)], ['6', '9'])).
% 0.21/0.46  thf(t12_zfmisc_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.21/0.46  thf('11', plain,
% 0.21/0.46      (![X9 : $i, X10 : $i]:
% 0.21/0.46         (r1_tarski @ (k1_tarski @ X9) @ (k2_tarski @ X9 @ X10))),
% 0.21/0.46      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.21/0.46  thf('12', plain, ($false), inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

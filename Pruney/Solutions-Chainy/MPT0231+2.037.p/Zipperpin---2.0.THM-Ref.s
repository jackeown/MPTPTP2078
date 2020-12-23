%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Nkw5pt8NLS

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   20 (  22 expanded)
%              Number of leaves         :   10 (  11 expanded)
%              Depth                    :    5
%              Number of atoms          :   91 ( 109 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t26_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
     => ( A = C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
       => ( A = C ) ) ),
    inference('cnf.neg',[status(esa)],[t26_zfmisc_1])).

thf('0',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k1_tarski @ X3 ) @ ( k2_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X1 ) @ X2 )
      | ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X6 = X5 )
      | ~ ( r1_tarski @ ( k1_tarski @ X6 ) @ ( k1_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t24_zfmisc_1])).

thf('6',plain,(
    sk_A = sk_C ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Nkw5pt8NLS
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:19:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.42  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.42  % Solved by: fo/fo7.sh
% 0.21/0.42  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.42  % done 9 iterations in 0.006s
% 0.21/0.42  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.42  % SZS output start Refutation
% 0.21/0.42  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.42  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.42  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.42  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.42  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.42  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.42  thf(t26_zfmisc_1, conjecture,
% 0.21/0.42    (![A:$i,B:$i,C:$i]:
% 0.21/0.42     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.21/0.42       ( ( A ) = ( C ) ) ))).
% 0.21/0.42  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.42    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.42        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.21/0.42          ( ( A ) = ( C ) ) ) )),
% 0.21/0.42    inference('cnf.neg', [status(esa)], [t26_zfmisc_1])).
% 0.21/0.42  thf('0', plain,
% 0.21/0.42      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C))),
% 0.21/0.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.42  thf(t12_zfmisc_1, axiom,
% 0.21/0.42    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.21/0.42  thf('1', plain,
% 0.21/0.42      (![X3 : $i, X4 : $i]:
% 0.21/0.42         (r1_tarski @ (k1_tarski @ X3) @ (k2_tarski @ X3 @ X4))),
% 0.21/0.42      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.21/0.42  thf(t1_xboole_1, axiom,
% 0.21/0.42    (![A:$i,B:$i,C:$i]:
% 0.21/0.42     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.42       ( r1_tarski @ A @ C ) ))).
% 0.21/0.42  thf('2', plain,
% 0.21/0.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.42         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.42          | ~ (r1_tarski @ X1 @ X2)
% 0.21/0.42          | (r1_tarski @ X0 @ X2))),
% 0.21/0.42      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.42  thf('3', plain,
% 0.21/0.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.42         ((r1_tarski @ (k1_tarski @ X1) @ X2)
% 0.21/0.42          | ~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ X2))),
% 0.21/0.42      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.42  thf('4', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))),
% 0.21/0.42      inference('sup-', [status(thm)], ['0', '3'])).
% 0.21/0.42  thf(t24_zfmisc_1, axiom,
% 0.21/0.42    (![A:$i,B:$i]:
% 0.21/0.42     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.21/0.42       ( ( A ) = ( B ) ) ))).
% 0.21/0.42  thf('5', plain,
% 0.21/0.42      (![X5 : $i, X6 : $i]:
% 0.21/0.42         (((X6) = (X5)) | ~ (r1_tarski @ (k1_tarski @ X6) @ (k1_tarski @ X5)))),
% 0.21/0.42      inference('cnf', [status(esa)], [t24_zfmisc_1])).
% 0.21/0.42  thf('6', plain, (((sk_A) = (sk_C))),
% 0.21/0.42      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.42  thf('7', plain, (((sk_A) != (sk_C))),
% 0.21/0.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.42  thf('8', plain, ($false),
% 0.21/0.42      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.21/0.42  
% 0.21/0.42  % SZS output end Refutation
% 0.21/0.42  
% 0.21/0.43  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

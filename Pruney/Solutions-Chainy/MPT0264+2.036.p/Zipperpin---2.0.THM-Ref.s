%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wQMdQXtY8k

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:42 EST 2020

% Result     : Theorem 1.18s
% Output     : Refutation 1.18s
% Verified   : 
% Statistics : Number of formulae       :   26 (  30 expanded)
%              Number of leaves         :   12 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :  178 ( 234 expanded)
%              Number of equality atoms :   19 (  27 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t59_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          = ( k1_tarski @ A ) )
        & ( r2_hidden @ B @ C )
        & ( A != B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
            = ( k1_tarski @ A ) )
          & ( r2_hidden @ B @ C )
          & ( A != B ) ) ),
    inference('cnf.neg',[status(esa)],[t59_zfmisc_1])).

thf('0',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(l38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k1_tarski @ A ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ( ( r2_hidden @ B @ C )
          | ( A = B ) ) ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( X9 = X11 )
      | ( r2_hidden @ X11 @ X10 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X9 @ X11 ) @ X10 )
       != ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l38_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 )
       != ( k1_tarski @ X2 ) )
      | ( r2_hidden @ X1 @ ( k4_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 ) )
      | ( X2 = X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( sk_A = sk_B )
    | ( r2_hidden @ sk_B @ ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,
    ( ( r2_hidden @ sk_B @ ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) )
    | ( sk_A = sk_B ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r2_hidden @ sk_B @ ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('9',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    $false ),
    inference(demod,[status(thm)],['10','11'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wQMdQXtY8k
% 0.16/0.38  % Computer   : n025.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 18:02:21 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 1.18/1.42  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.18/1.42  % Solved by: fo/fo7.sh
% 1.18/1.42  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.18/1.42  % done 1370 iterations in 0.932s
% 1.18/1.42  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.18/1.42  % SZS output start Refutation
% 1.18/1.42  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.18/1.42  thf(sk_B_type, type, sk_B: $i).
% 1.18/1.42  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.18/1.42  thf(sk_A_type, type, sk_A: $i).
% 1.18/1.42  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.18/1.42  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.18/1.42  thf(sk_C_type, type, sk_C: $i).
% 1.18/1.42  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.18/1.42  thf(t59_zfmisc_1, conjecture,
% 1.18/1.42    (![A:$i,B:$i,C:$i]:
% 1.18/1.42     ( ~( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) & 
% 1.18/1.42          ( r2_hidden @ B @ C ) & ( ( A ) != ( B ) ) ) ))).
% 1.18/1.42  thf(zf_stmt_0, negated_conjecture,
% 1.18/1.42    (~( ![A:$i,B:$i,C:$i]:
% 1.18/1.42        ( ~( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) & 
% 1.18/1.42             ( r2_hidden @ B @ C ) & ( ( A ) != ( B ) ) ) ) )),
% 1.18/1.42    inference('cnf.neg', [status(esa)], [t59_zfmisc_1])).
% 1.18/1.42  thf('0', plain,
% 1.18/1.42      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_tarski @ sk_A))),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf(t48_xboole_1, axiom,
% 1.18/1.42    (![A:$i,B:$i]:
% 1.18/1.42     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.18/1.42  thf('1', plain,
% 1.18/1.42      (![X6 : $i, X7 : $i]:
% 1.18/1.42         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 1.18/1.42           = (k3_xboole_0 @ X6 @ X7))),
% 1.18/1.42      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.18/1.42  thf(l38_zfmisc_1, axiom,
% 1.18/1.42    (![A:$i,B:$i,C:$i]:
% 1.18/1.42     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) <=>
% 1.18/1.42       ( ( ~( r2_hidden @ A @ C ) ) & 
% 1.18/1.42         ( ( r2_hidden @ B @ C ) | ( ( A ) = ( B ) ) ) ) ))).
% 1.18/1.42  thf('2', plain,
% 1.18/1.42      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.18/1.42         (((X9) = (X11))
% 1.18/1.42          | (r2_hidden @ X11 @ X10)
% 1.18/1.42          | ((k4_xboole_0 @ (k2_tarski @ X9 @ X11) @ X10) != (k1_tarski @ X9)))),
% 1.18/1.42      inference('cnf', [status(esa)], [l38_zfmisc_1])).
% 1.18/1.42  thf('3', plain,
% 1.18/1.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.18/1.42         (((k3_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0) != (k1_tarski @ X2))
% 1.18/1.42          | (r2_hidden @ X1 @ (k4_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0))
% 1.18/1.42          | ((X2) = (X1)))),
% 1.18/1.42      inference('sup-', [status(thm)], ['1', '2'])).
% 1.18/1.42  thf('4', plain,
% 1.18/1.42      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 1.18/1.42        | ((sk_A) = (sk_B))
% 1.18/1.42        | (r2_hidden @ sk_B @ (k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 1.18/1.42      inference('sup-', [status(thm)], ['0', '3'])).
% 1.18/1.42  thf('5', plain,
% 1.18/1.42      (((r2_hidden @ sk_B @ (k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))
% 1.18/1.42        | ((sk_A) = (sk_B)))),
% 1.18/1.42      inference('simplify', [status(thm)], ['4'])).
% 1.18/1.42  thf('6', plain, (((sk_A) != (sk_B))),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('7', plain,
% 1.18/1.42      ((r2_hidden @ sk_B @ (k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 1.18/1.42      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 1.18/1.42  thf(d5_xboole_0, axiom,
% 1.18/1.42    (![A:$i,B:$i,C:$i]:
% 1.18/1.42     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.18/1.42       ( ![D:$i]:
% 1.18/1.42         ( ( r2_hidden @ D @ C ) <=>
% 1.18/1.42           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.18/1.42  thf('8', plain,
% 1.18/1.42      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.18/1.42         (~ (r2_hidden @ X4 @ X3)
% 1.18/1.42          | ~ (r2_hidden @ X4 @ X2)
% 1.18/1.42          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 1.18/1.42      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.18/1.42  thf('9', plain,
% 1.18/1.42      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.18/1.42         (~ (r2_hidden @ X4 @ X2)
% 1.18/1.42          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 1.18/1.42      inference('simplify', [status(thm)], ['8'])).
% 1.18/1.42  thf('10', plain, (~ (r2_hidden @ sk_B @ sk_C)),
% 1.18/1.42      inference('sup-', [status(thm)], ['7', '9'])).
% 1.18/1.42  thf('11', plain, ((r2_hidden @ sk_B @ sk_C)),
% 1.18/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.42  thf('12', plain, ($false), inference('demod', [status(thm)], ['10', '11'])).
% 1.18/1.42  
% 1.18/1.42  % SZS output end Refutation
% 1.18/1.42  
% 1.18/1.43  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

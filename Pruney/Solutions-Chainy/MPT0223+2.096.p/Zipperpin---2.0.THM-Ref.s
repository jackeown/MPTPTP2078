%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.61xVRglzW0

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   31 (  34 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :  171 ( 209 expanded)
%              Number of equality atoms :   16 (  20 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('0',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k3_xboole_0 @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X18 ) @ ( k1_tarski @ X19 ) )
      | ( X18 = X19 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf(t18_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t18_zfmisc_1])).

thf('6',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( sk_A = sk_B )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('12',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf(t16_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        & ( A = B ) ) )).

thf('13',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) )
      | ( X16 != X17 ) ) ),
    inference(cnf,[status(esa)],[t16_zfmisc_1])).

thf('14',plain,(
    ! [X17: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X17 ) @ ( k1_tarski @ X17 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    $false ),
    inference('sup-',[status(thm)],['12','14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.61xVRglzW0
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:13:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 50 iterations in 0.025s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(t22_xboole_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i]:
% 0.21/0.48         ((k2_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)) = (X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.21/0.48  thf(t21_xboole_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X4 : $i, X5 : $i]:
% 0.21/0.48         ((k3_xboole_0 @ X4 @ (k2_xboole_0 @ X4 @ X5)) = (X4))),
% 0.21/0.48      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.21/0.48  thf('2', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.21/0.48      inference('sup+', [status(thm)], ['0', '1'])).
% 0.21/0.48  thf(t4_xboole_0, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.48            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.48       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.48            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ X0 @ X1)
% 0.21/0.48          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r2_hidden @ (sk_C @ X0 @ X0) @ X0) | (r1_xboole_0 @ X0 @ X0))),
% 0.21/0.48      inference('sup+', [status(thm)], ['2', '3'])).
% 0.21/0.48  thf(t17_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( A ) != ( B ) ) =>
% 0.21/0.48       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X18 : $i, X19 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ (k1_tarski @ X18) @ (k1_tarski @ X19))
% 0.21/0.48          | ((X18) = (X19)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.21/0.48  thf(t18_zfmisc_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.48         ( k1_tarski @ A ) ) =>
% 0.21/0.48       ( ( A ) = ( B ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i]:
% 0.21/0.48        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.48            ( k1_tarski @ A ) ) =>
% 0.21/0.48          ( ( A ) = ( B ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t18_zfmisc_1])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.48         = (k1_tarski @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.21/0.48          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.21/0.48      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.21/0.48          | ~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((sk_A) = (sk_B)) | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['5', '8'])).
% 0.21/0.48  thf('10', plain, (((sk_A) != (sk_B))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('11', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.21/0.48  thf('12', plain, ((r1_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['4', '11'])).
% 0.21/0.48  thf(t16_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) & 
% 0.21/0.48          ( ( A ) = ( B ) ) ) ))).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (![X16 : $i, X17 : $i]:
% 0.21/0.48         (~ (r1_xboole_0 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 0.21/0.48          | ((X16) != (X17)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t16_zfmisc_1])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (![X17 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X17) @ (k1_tarski @ X17))),
% 0.21/0.48      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.48  thf('15', plain, ($false), inference('sup-', [status(thm)], ['12', '14'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.35/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

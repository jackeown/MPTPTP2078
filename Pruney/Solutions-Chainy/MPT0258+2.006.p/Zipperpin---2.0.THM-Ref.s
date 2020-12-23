%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wOaK2cP6A3

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:24 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   33 (  38 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    9
%              Number of atoms          :  197 ( 264 expanded)
%              Number of equality atoms :   14 (  19 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('0',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t53_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ C @ B ) )
     => ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
        = ( k2_tarski @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ C @ B ) )
       => ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
          = ( k2_tarski @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t53_zfmisc_1])).

thf('1',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r2_hidden @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X15 @ X17 ) @ X18 )
      | ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( r2_hidden @ X15 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_C ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_xboole_0 @ X7 @ ( k4_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ ( k4_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ ( k4_xboole_0 @ X0 @ sk_B ) )
      = ( k2_tarski @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B )
    = ( k2_tarski @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['0','9'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) )
    = ( k2_tarski @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B )
 != ( k2_tarski @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('15',plain,(
    ( k3_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) )
 != ( k2_tarski @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['12','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wOaK2cP6A3
% 0.15/0.38  % Computer   : n014.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 09:46:22 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.24/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.53  % Solved by: fo/fo7.sh
% 0.24/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.53  % done 65 iterations in 0.038s
% 0.24/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.53  % SZS output start Refutation
% 0.24/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.24/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.24/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.24/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.24/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.24/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.53  thf(t48_xboole_1, axiom,
% 0.24/0.53    (![A:$i,B:$i]:
% 0.24/0.53     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.24/0.53  thf('0', plain,
% 0.24/0.53      (![X2 : $i, X3 : $i]:
% 0.24/0.53         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 0.24/0.53           = (k3_xboole_0 @ X2 @ X3))),
% 0.24/0.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.24/0.53  thf(t53_zfmisc_1, conjecture,
% 0.24/0.53    (![A:$i,B:$i,C:$i]:
% 0.24/0.53     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.24/0.53       ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( k2_tarski @ A @ C ) ) ))).
% 0.24/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.24/0.53        ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.24/0.53          ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( k2_tarski @ A @ C ) ) ) )),
% 0.24/0.53    inference('cnf.neg', [status(esa)], [t53_zfmisc_1])).
% 0.24/0.53  thf('1', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('2', plain, ((r2_hidden @ sk_C @ sk_B)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf(t38_zfmisc_1, axiom,
% 0.24/0.53    (![A:$i,B:$i,C:$i]:
% 0.24/0.53     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.24/0.53       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.24/0.53  thf('3', plain,
% 0.24/0.53      (![X15 : $i, X17 : $i, X18 : $i]:
% 0.24/0.53         ((r1_tarski @ (k2_tarski @ X15 @ X17) @ X18)
% 0.24/0.53          | ~ (r2_hidden @ X17 @ X18)
% 0.24/0.53          | ~ (r2_hidden @ X15 @ X18))),
% 0.24/0.53      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.24/0.53  thf('4', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         (~ (r2_hidden @ X0 @ sk_B)
% 0.24/0.53          | (r1_tarski @ (k2_tarski @ X0 @ sk_C) @ sk_B))),
% 0.24/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.24/0.53  thf('5', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_C) @ sk_B)),
% 0.24/0.53      inference('sup-', [status(thm)], ['1', '4'])).
% 0.24/0.53  thf(t85_xboole_1, axiom,
% 0.24/0.53    (![A:$i,B:$i,C:$i]:
% 0.24/0.53     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.24/0.53  thf('6', plain,
% 0.24/0.53      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.24/0.53         (~ (r1_tarski @ X7 @ X8)
% 0.24/0.53          | (r1_xboole_0 @ X7 @ (k4_xboole_0 @ X9 @ X8)))),
% 0.24/0.53      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.24/0.53  thf('7', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         (r1_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ (k4_xboole_0 @ X0 @ sk_B))),
% 0.24/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.24/0.53  thf(t83_xboole_1, axiom,
% 0.24/0.53    (![A:$i,B:$i]:
% 0.24/0.53     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.24/0.53  thf('8', plain,
% 0.24/0.53      (![X4 : $i, X5 : $i]:
% 0.24/0.53         (((k4_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.24/0.53      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.24/0.53  thf('9', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ (k4_xboole_0 @ X0 @ sk_B))
% 0.24/0.53           = (k2_tarski @ sk_A @ sk_C))),
% 0.24/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.24/0.53  thf('10', plain,
% 0.24/0.53      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B)
% 0.24/0.53         = (k2_tarski @ sk_A @ sk_C))),
% 0.24/0.53      inference('sup+', [status(thm)], ['0', '9'])).
% 0.24/0.53  thf(commutativity_k3_xboole_0, axiom,
% 0.24/0.53    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.24/0.53  thf('11', plain,
% 0.24/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.24/0.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.24/0.53  thf('12', plain,
% 0.24/0.53      (((k3_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C))
% 0.24/0.53         = (k2_tarski @ sk_A @ sk_C))),
% 0.24/0.53      inference('demod', [status(thm)], ['10', '11'])).
% 0.24/0.53  thf('13', plain,
% 0.24/0.53      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B)
% 0.24/0.53         != (k2_tarski @ sk_A @ sk_C))),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('14', plain,
% 0.24/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.24/0.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.24/0.53  thf('15', plain,
% 0.24/0.53      (((k3_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C))
% 0.24/0.53         != (k2_tarski @ sk_A @ sk_C))),
% 0.24/0.53      inference('demod', [status(thm)], ['13', '14'])).
% 0.24/0.53  thf('16', plain, ($false),
% 0.24/0.53      inference('simplify_reflect-', [status(thm)], ['12', '15'])).
% 0.24/0.53  
% 0.24/0.53  % SZS output end Refutation
% 0.24/0.53  
% 0.24/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

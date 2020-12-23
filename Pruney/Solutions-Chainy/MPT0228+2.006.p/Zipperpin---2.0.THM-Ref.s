%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PeICH1JmLl

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:06 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   22 (  25 expanded)
%              Number of leaves         :    9 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :  138 ( 172 expanded)
%              Number of equality atoms :   19 (  25 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('1',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(l38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k1_tarski @ A ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ( ( r2_hidden @ B @ C )
          | ( A = B ) ) ) ) )).

thf('2',plain,(
    ! [X33: $i,X35: $i,X36: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X33 @ X35 ) @ X36 )
        = ( k1_tarski @ X33 ) )
      | ~ ( r2_hidden @ X35 @ X36 )
      | ( r2_hidden @ X33 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l38_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t23_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( A != B )
       => ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t23_zfmisc_1])).

thf('4',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_B ) )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('8',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    sk_A = sk_B ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PeICH1JmLl
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:46:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 57 iterations in 0.031s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.48  thf(d1_tarski, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.19/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.19/0.48  thf('0', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.48         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d1_tarski])).
% 0.19/0.48  thf('1', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.19/0.48      inference('simplify', [status(thm)], ['0'])).
% 0.19/0.48  thf(l38_zfmisc_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) <=>
% 0.19/0.48       ( ( ~( r2_hidden @ A @ C ) ) & 
% 0.19/0.48         ( ( r2_hidden @ B @ C ) | ( ( A ) = ( B ) ) ) ) ))).
% 0.19/0.48  thf('2', plain,
% 0.19/0.48      (![X33 : $i, X35 : $i, X36 : $i]:
% 0.19/0.48         (((k4_xboole_0 @ (k2_tarski @ X33 @ X35) @ X36) = (k1_tarski @ X33))
% 0.19/0.48          | ~ (r2_hidden @ X35 @ X36)
% 0.19/0.48          | (r2_hidden @ X33 @ X36))),
% 0.19/0.48      inference('cnf', [status(esa)], [l38_zfmisc_1])).
% 0.19/0.48  thf('3', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.19/0.48          | ((k4_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0))
% 0.19/0.48              = (k1_tarski @ X1)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.48  thf(t23_zfmisc_1, conjecture,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ( A ) != ( B ) ) =>
% 0.19/0.48       ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ B ) ) =
% 0.19/0.48         ( k1_tarski @ A ) ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i,B:$i]:
% 0.19/0.48        ( ( ( A ) != ( B ) ) =>
% 0.19/0.48          ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ B ) ) =
% 0.19/0.48            ( k1_tarski @ A ) ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t23_zfmisc_1])).
% 0.19/0.48  thf('4', plain,
% 0.19/0.48      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_B))
% 0.19/0.48         != (k1_tarski @ sk_A))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('5', plain,
% 0.19/0.48      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.19/0.48        | (r2_hidden @ sk_A @ (k1_tarski @ sk_B)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.48  thf('6', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.19/0.48      inference('simplify', [status(thm)], ['5'])).
% 0.19/0.48  thf('7', plain,
% 0.19/0.48      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d1_tarski])).
% 0.19/0.48  thf('8', plain,
% 0.19/0.48      (![X0 : $i, X3 : $i]:
% 0.19/0.48         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['7'])).
% 0.19/0.48  thf('9', plain, (((sk_A) = (sk_B))),
% 0.19/0.48      inference('sup-', [status(thm)], ['6', '8'])).
% 0.19/0.48  thf('10', plain, (((sk_A) != (sk_B))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('11', plain, ($false),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

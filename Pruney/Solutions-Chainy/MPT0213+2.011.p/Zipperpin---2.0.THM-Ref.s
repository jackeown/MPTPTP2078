%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xKjXHR7vDb

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   23 (  23 expanded)
%              Number of leaves         :   11 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :   99 (  99 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( r2_hidden @ ( sk_D_1 @ X7 @ X4 ) @ X4 )
      | ( X6
       != ( k3_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('2',plain,(
    ! [X4: $i,X7: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X7 @ X4 ) @ X4 )
      | ~ ( r2_hidden @ X7 @ ( k3_tarski @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_B @ ( k3_tarski @ X0 ) ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('4',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t2_zfmisc_1,conjecture,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf(zf_stmt_0,negated_conjecture,(
    ( k3_tarski @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('cnf.neg',[status(esa)],[t2_zfmisc_1])).

thf('6',plain,(
    ( k3_tarski @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('8',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('9',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    $false ),
    inference(simplify,[status(thm)],['9'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xKjXHR7vDb
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:18:01 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  % Running portfolio for 600 s
% 0.20/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 8 iterations in 0.012s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.47  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.21/0.47  thf(t7_xboole_0, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.47          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.47  thf(d4_tarski, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 0.21/0.47       ( ![C:$i]:
% 0.21/0.47         ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.47           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X7 @ X6)
% 0.21/0.47          | (r2_hidden @ (sk_D_1 @ X7 @ X4) @ X4)
% 0.21/0.47          | ((X6) != (k3_tarski @ X4)))),
% 0.21/0.47      inference('cnf', [status(esa)], [d4_tarski])).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X4 : $i, X7 : $i]:
% 0.21/0.47         ((r2_hidden @ (sk_D_1 @ X7 @ X4) @ X4)
% 0.21/0.47          | ~ (r2_hidden @ X7 @ (k3_tarski @ X4)))),
% 0.21/0.47      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (((k3_tarski @ X0) = (k1_xboole_0))
% 0.21/0.47          | (r2_hidden @ (sk_D_1 @ (sk_B @ (k3_tarski @ X0)) @ X0) @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['0', '2'])).
% 0.21/0.47  thf(t7_boole, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( v1_xboole_0 @ B ) ) ))).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X1 : $i, X2 : $i]: (~ (r2_hidden @ X1 @ X2) | ~ (v1_xboole_0 @ X2))),
% 0.21/0.47      inference('cnf', [status(esa)], [t7_boole])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X0 : $i]: (((k3_tarski @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.47  thf(t2_zfmisc_1, conjecture, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (( k3_tarski @ k1_xboole_0 ) != ( k1_xboole_0 )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t2_zfmisc_1])).
% 0.21/0.47  thf('6', plain, (((k3_tarski @ k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.47  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.47  thf('8', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.47      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.47  thf('9', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.47      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.47  thf('10', plain, ($false), inference('simplify', [status(thm)], ['9'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

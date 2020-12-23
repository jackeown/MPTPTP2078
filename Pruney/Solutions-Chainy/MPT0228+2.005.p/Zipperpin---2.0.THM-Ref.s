%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.A1teIwRkQN

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:06 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   30 (  32 expanded)
%              Number of leaves         :   13 (  14 expanded)
%              Depth                    :    9
%              Number of atoms          :  188 ( 212 expanded)
%              Number of equality atoms :   25 (  29 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X23: $i] :
      ( ( k2_tarski @ X23 @ X23 )
      = ( k1_tarski @ X23 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X38 ) @ ( k2_tarski @ X38 @ X39 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t22_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(l35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('3',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r2_hidden @ X26 @ X27 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X26 ) @ X27 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf(l38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k1_tarski @ A ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ( ( r2_hidden @ B @ C )
          | ( A = B ) ) ) ) )).

thf('6',plain,(
    ! [X29: $i,X31: $i,X32: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X29 @ X31 ) @ X32 )
        = ( k1_tarski @ X29 ) )
      | ~ ( r2_hidden @ X31 @ X32 )
      | ( r2_hidden @ X29 @ X32 ) ) ),
    inference(cnf,[status(esa)],[l38_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

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

thf('8',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_B ) )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(simplify,[status(thm)],['9'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('11',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ( X21 = X18 )
      | ( X20
       != ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('12',plain,(
    ! [X18: $i,X21: $i] :
      ( ( X21 = X18 )
      | ~ ( r2_hidden @ X21 @ ( k1_tarski @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    sk_A = sk_B ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.A1teIwRkQN
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:49:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.47/0.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.70  % Solved by: fo/fo7.sh
% 0.47/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.70  % done 620 iterations in 0.251s
% 0.47/0.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.70  % SZS output start Refutation
% 0.47/0.70  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.47/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.70  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.47/0.70  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.47/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.70  thf(t69_enumset1, axiom,
% 0.47/0.70    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.47/0.70  thf('0', plain, (![X23 : $i]: ((k2_tarski @ X23 @ X23) = (k1_tarski @ X23))),
% 0.47/0.70      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.47/0.70  thf(t22_zfmisc_1, axiom,
% 0.47/0.70    (![A:$i,B:$i]:
% 0.47/0.70     ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.47/0.70       ( k1_xboole_0 ) ))).
% 0.47/0.70  thf('1', plain,
% 0.47/0.70      (![X38 : $i, X39 : $i]:
% 0.47/0.70         ((k4_xboole_0 @ (k1_tarski @ X38) @ (k2_tarski @ X38 @ X39))
% 0.47/0.70           = (k1_xboole_0))),
% 0.47/0.70      inference('cnf', [status(esa)], [t22_zfmisc_1])).
% 0.47/0.70  thf('2', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.47/0.70      inference('sup+', [status(thm)], ['0', '1'])).
% 0.47/0.70  thf(l35_zfmisc_1, axiom,
% 0.47/0.70    (![A:$i,B:$i]:
% 0.47/0.70     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.47/0.70       ( r2_hidden @ A @ B ) ))).
% 0.47/0.70  thf('3', plain,
% 0.47/0.70      (![X26 : $i, X27 : $i]:
% 0.47/0.70         ((r2_hidden @ X26 @ X27)
% 0.47/0.70          | ((k4_xboole_0 @ (k1_tarski @ X26) @ X27) != (k1_xboole_0)))),
% 0.47/0.70      inference('cnf', [status(esa)], [l35_zfmisc_1])).
% 0.47/0.70  thf('4', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (((k1_xboole_0) != (k1_xboole_0))
% 0.47/0.70          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['2', '3'])).
% 0.47/0.70  thf('5', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.47/0.70      inference('simplify', [status(thm)], ['4'])).
% 0.47/0.70  thf(l38_zfmisc_1, axiom,
% 0.47/0.70    (![A:$i,B:$i,C:$i]:
% 0.47/0.70     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) <=>
% 0.47/0.70       ( ( ~( r2_hidden @ A @ C ) ) & 
% 0.47/0.70         ( ( r2_hidden @ B @ C ) | ( ( A ) = ( B ) ) ) ) ))).
% 0.47/0.70  thf('6', plain,
% 0.47/0.70      (![X29 : $i, X31 : $i, X32 : $i]:
% 0.47/0.70         (((k4_xboole_0 @ (k2_tarski @ X29 @ X31) @ X32) = (k1_tarski @ X29))
% 0.47/0.70          | ~ (r2_hidden @ X31 @ X32)
% 0.47/0.70          | (r2_hidden @ X29 @ X32))),
% 0.47/0.70      inference('cnf', [status(esa)], [l38_zfmisc_1])).
% 0.47/0.70  thf('7', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         ((r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.47/0.70          | ((k4_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0))
% 0.47/0.70              = (k1_tarski @ X1)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['5', '6'])).
% 0.47/0.70  thf(t23_zfmisc_1, conjecture,
% 0.47/0.70    (![A:$i,B:$i]:
% 0.47/0.70     ( ( ( A ) != ( B ) ) =>
% 0.47/0.70       ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ B ) ) =
% 0.47/0.70         ( k1_tarski @ A ) ) ))).
% 0.47/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.70    (~( ![A:$i,B:$i]:
% 0.47/0.70        ( ( ( A ) != ( B ) ) =>
% 0.47/0.70          ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ B ) ) =
% 0.47/0.70            ( k1_tarski @ A ) ) ) )),
% 0.47/0.70    inference('cnf.neg', [status(esa)], [t23_zfmisc_1])).
% 0.47/0.70  thf('8', plain,
% 0.47/0.70      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_B))
% 0.47/0.70         != (k1_tarski @ sk_A))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('9', plain,
% 0.47/0.70      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.47/0.70        | (r2_hidden @ sk_A @ (k1_tarski @ sk_B)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['7', '8'])).
% 0.47/0.70  thf('10', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.47/0.70      inference('simplify', [status(thm)], ['9'])).
% 0.47/0.70  thf(d1_tarski, axiom,
% 0.47/0.70    (![A:$i,B:$i]:
% 0.47/0.70     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.47/0.70       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.47/0.70  thf('11', plain,
% 0.47/0.70      (![X18 : $i, X20 : $i, X21 : $i]:
% 0.47/0.70         (~ (r2_hidden @ X21 @ X20)
% 0.47/0.70          | ((X21) = (X18))
% 0.47/0.70          | ((X20) != (k1_tarski @ X18)))),
% 0.47/0.70      inference('cnf', [status(esa)], [d1_tarski])).
% 0.47/0.70  thf('12', plain,
% 0.47/0.70      (![X18 : $i, X21 : $i]:
% 0.47/0.70         (((X21) = (X18)) | ~ (r2_hidden @ X21 @ (k1_tarski @ X18)))),
% 0.47/0.70      inference('simplify', [status(thm)], ['11'])).
% 0.47/0.70  thf('13', plain, (((sk_A) = (sk_B))),
% 0.47/0.70      inference('sup-', [status(thm)], ['10', '12'])).
% 0.47/0.70  thf('14', plain, (((sk_A) != (sk_B))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('15', plain, ($false),
% 0.47/0.70      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 0.47/0.70  
% 0.47/0.70  % SZS output end Refutation
% 0.47/0.70  
% 0.47/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

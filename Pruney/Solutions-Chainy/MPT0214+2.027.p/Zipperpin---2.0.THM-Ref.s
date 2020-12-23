%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.q9Rtqnu3Dr

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:47 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   34 (  39 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :    9
%              Number of atoms          :  175 ( 221 expanded)
%              Number of equality atoms :   23 (  31 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( X19 != X18 )
      | ( r2_hidden @ X19 @ X20 )
      | ( X20
       != ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('1',plain,(
    ! [X18: $i] :
      ( r2_hidden @ X18 @ ( k1_tarski @ X18 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t6_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t6_zfmisc_1])).

thf('2',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('3',plain,(
    ! [X33: $i,X34: $i] :
      ( ( X34
        = ( k1_tarski @ X33 ) )
      | ( X34 = k1_xboole_0 )
      | ~ ( r1_tarski @ X34 @ ( k1_tarski @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('4',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ( X21 = X18 )
      | ( X20
       != ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('6',plain,(
    ! [X18: $i,X21: $i] :
      ( ( X21 = X18 )
      | ~ ( r2_hidden @ X21 @ ( k1_tarski @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( X0 = sk_B ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,
    ( ( sk_A = sk_B )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X18: $i] :
      ( r2_hidden @ X18 @ ( k1_tarski @ X18 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('12',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['10','11'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('14',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X1 @ X4 ) )
      | ~ ( r1_xboole_0 @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ~ ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('17',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('18',plain,(
    $false ),
    inference(demod,[status(thm)],['16','17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.q9Rtqnu3Dr
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:46:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.47  % Solved by: fo/fo7.sh
% 0.19/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.47  % done 46 iterations in 0.024s
% 0.19/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.47  % SZS output start Refutation
% 0.19/0.47  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.47  thf(d1_tarski, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.19/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.19/0.47  thf('0', plain,
% 0.19/0.47      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.19/0.47         (((X19) != (X18))
% 0.19/0.47          | (r2_hidden @ X19 @ X20)
% 0.19/0.47          | ((X20) != (k1_tarski @ X18)))),
% 0.19/0.47      inference('cnf', [status(esa)], [d1_tarski])).
% 0.19/0.47  thf('1', plain, (![X18 : $i]: (r2_hidden @ X18 @ (k1_tarski @ X18))),
% 0.19/0.47      inference('simplify', [status(thm)], ['0'])).
% 0.19/0.47  thf(t6_zfmisc_1, conjecture,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.19/0.47       ( ( A ) = ( B ) ) ))).
% 0.19/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.47    (~( ![A:$i,B:$i]:
% 0.19/0.47        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.19/0.47          ( ( A ) = ( B ) ) ) )),
% 0.19/0.47    inference('cnf.neg', [status(esa)], [t6_zfmisc_1])).
% 0.19/0.47  thf('2', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(l3_zfmisc_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.19/0.47       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.19/0.47  thf('3', plain,
% 0.19/0.47      (![X33 : $i, X34 : $i]:
% 0.19/0.47         (((X34) = (k1_tarski @ X33))
% 0.19/0.47          | ((X34) = (k1_xboole_0))
% 0.19/0.47          | ~ (r1_tarski @ X34 @ (k1_tarski @ X33)))),
% 0.19/0.47      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.19/0.47  thf('4', plain,
% 0.19/0.47      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.19/0.47        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_B)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.47  thf('5', plain,
% 0.19/0.47      (![X18 : $i, X20 : $i, X21 : $i]:
% 0.19/0.47         (~ (r2_hidden @ X21 @ X20)
% 0.19/0.47          | ((X21) = (X18))
% 0.19/0.47          | ((X20) != (k1_tarski @ X18)))),
% 0.19/0.47      inference('cnf', [status(esa)], [d1_tarski])).
% 0.19/0.47  thf('6', plain,
% 0.19/0.47      (![X18 : $i, X21 : $i]:
% 0.19/0.47         (((X21) = (X18)) | ~ (r2_hidden @ X21 @ (k1_tarski @ X18)))),
% 0.19/0.47      inference('simplify', [status(thm)], ['5'])).
% 0.19/0.47  thf('7', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.19/0.47          | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.19/0.47          | ((X0) = (sk_B)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['4', '6'])).
% 0.19/0.47  thf('8', plain, ((((sk_A) = (sk_B)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['1', '7'])).
% 0.19/0.47  thf('9', plain, (((sk_A) != (sk_B))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('10', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.19/0.47      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.19/0.47  thf('11', plain, (![X18 : $i]: (r2_hidden @ X18 @ (k1_tarski @ X18))),
% 0.19/0.47      inference('simplify', [status(thm)], ['0'])).
% 0.19/0.47  thf('12', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.19/0.47      inference('sup+', [status(thm)], ['10', '11'])).
% 0.19/0.47  thf(idempotence_k3_xboole_0, axiom,
% 0.19/0.47    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.19/0.47  thf('13', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.19/0.47      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.19/0.47  thf(t4_xboole_0, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.47            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.47       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.19/0.47            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.19/0.47  thf('14', plain,
% 0.19/0.47      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.19/0.47         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X1 @ X4))
% 0.19/0.47          | ~ (r1_xboole_0 @ X1 @ X4))),
% 0.19/0.47      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.19/0.47  thf('15', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]:
% 0.19/0.47         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.47  thf('16', plain, (~ (r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.19/0.47      inference('sup-', [status(thm)], ['12', '15'])).
% 0.19/0.47  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.19/0.47  thf('17', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.19/0.47      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.19/0.47  thf('18', plain, ($false), inference('demod', [status(thm)], ['16', '17'])).
% 0.19/0.47  
% 0.19/0.47  % SZS output end Refutation
% 0.19/0.47  
% 0.19/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

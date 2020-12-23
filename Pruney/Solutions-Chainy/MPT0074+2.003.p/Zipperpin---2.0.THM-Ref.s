%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.S9oHOOYnsD

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:41 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   46 (  52 expanded)
%              Number of leaves         :   21 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :  207 ( 279 expanded)
%              Number of equality atoms :   18 (  24 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t67_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ B @ C ) )
     => ( A = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_tarski @ A @ C )
          & ( r1_xboole_0 @ B @ C ) )
       => ( A = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t67_xboole_1])).

thf('1',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( sk_A != X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['2'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('4',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('5',plain,(
    r1_tarski @ sk_A @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('7',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_C_1 )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('8',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('9',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('11',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('13',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('14',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X6 @ X9 ) )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r1_xboole_0 @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('18',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X17 @ X18 )
      | ~ ( r1_xboole_0 @ X18 @ X19 )
      | ( r1_xboole_0 @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r1_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','20'])).

thf('22',plain,(
    v1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['4','21'])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['3','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.S9oHOOYnsD
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:37:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 81 iterations in 0.044s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.50  thf(l13_xboole_0, axiom,
% 0.22/0.50    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.22/0.50      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.22/0.50  thf(t67_xboole_1, conjecture,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 0.22/0.50         ( r1_xboole_0 @ B @ C ) ) =>
% 0.22/0.50       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.50        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 0.22/0.50            ( r1_xboole_0 @ B @ C ) ) =>
% 0.22/0.50          ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t67_xboole_1])).
% 0.22/0.50  thf('1', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('2', plain, (![X0 : $i]: (((sk_A) != (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.50  thf('3', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.50      inference('simplify', [status(thm)], ['2'])).
% 0.22/0.50  thf(d1_xboole_0, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.22/0.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.50  thf('5', plain, ((r1_tarski @ sk_A @ sk_C_1)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t12_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      (![X10 : $i, X11 : $i]:
% 0.22/0.50         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 0.22/0.50      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.22/0.50  thf('7', plain, (((k2_xboole_0 @ sk_A @ sk_C_1) = (sk_C_1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.50  thf(t46_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (![X13 : $i, X14 : $i]:
% 0.22/0.50         ((k4_xboole_0 @ X13 @ (k2_xboole_0 @ X13 @ X14)) = (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.22/0.50  thf('9', plain, (((k4_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))),
% 0.22/0.50      inference('sup+', [status(thm)], ['7', '8'])).
% 0.22/0.50  thf(t48_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      (![X15 : $i, X16 : $i]:
% 0.22/0.50         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.22/0.50           = (k3_xboole_0 @ X15 @ X16))),
% 0.22/0.50      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_C_1))),
% 0.22/0.50      inference('sup+', [status(thm)], ['9', '10'])).
% 0.22/0.50  thf(t3_boole, axiom,
% 0.22/0.50    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.50  thf('12', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.22/0.50      inference('cnf', [status(esa)], [t3_boole])).
% 0.22/0.50  thf('13', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ sk_C_1))),
% 0.22/0.50      inference('demod', [status(thm)], ['11', '12'])).
% 0.22/0.50  thf(t4_xboole_0, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.50            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.50       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.22/0.50            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X8 @ (k3_xboole_0 @ X6 @ X9))
% 0.22/0.50          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.22/0.50      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X0 @ sk_A) | ~ (r1_xboole_0 @ sk_A @ sk_C_1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.50  thf('16', plain, ((r1_xboole_0 @ sk_B_1 @ sk_C_1)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('17', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t63_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.22/0.50       ( r1_xboole_0 @ A @ C ) ))).
% 0.22/0.50  thf('18', plain,
% 0.22/0.50      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.50         (~ (r1_tarski @ X17 @ X18)
% 0.22/0.50          | ~ (r1_xboole_0 @ X18 @ X19)
% 0.22/0.50          | (r1_xboole_0 @ X17 @ X19))),
% 0.22/0.50      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.22/0.50  thf('19', plain,
% 0.22/0.50      (![X0 : $i]: ((r1_xboole_0 @ sk_A @ X0) | ~ (r1_xboole_0 @ sk_B_1 @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.50  thf('20', plain, ((r1_xboole_0 @ sk_A @ sk_C_1)),
% 0.22/0.50      inference('sup-', [status(thm)], ['16', '19'])).
% 0.22/0.50  thf('21', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_A)),
% 0.22/0.50      inference('demod', [status(thm)], ['15', '20'])).
% 0.22/0.50  thf('22', plain, ((v1_xboole_0 @ sk_A)),
% 0.22/0.50      inference('sup-', [status(thm)], ['4', '21'])).
% 0.22/0.50  thf('23', plain, ($false), inference('demod', [status(thm)], ['3', '22'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

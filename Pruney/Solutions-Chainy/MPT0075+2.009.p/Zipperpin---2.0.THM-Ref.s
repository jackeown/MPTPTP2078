%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0fWAEiDYAW

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:44 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   42 (  48 expanded)
%              Number of leaves         :   20 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :  194 ( 260 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(t68_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( v1_xboole_0 @ C )
     => ~ ( ( r1_tarski @ C @ A )
          & ( r1_tarski @ C @ B )
          & ( r1_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ~ ( v1_xboole_0 @ C )
       => ~ ( ( r1_tarski @ C @ A )
            & ( r1_tarski @ C @ B )
            & ( r1_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t68_xboole_1])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('2',plain,(
    r1_tarski @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('4',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ sk_B_1 )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('10',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    r1_xboole_0 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('15',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_xboole_0 @ X17 @ X18 )
      | ( r1_xboole_0 @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( r1_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['12','17'])).

thf('19',plain,(
    v1_xboole_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['1','18'])).

thf('20',plain,(
    $false ),
    inference(demod,[status(thm)],['0','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0fWAEiDYAW
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:09:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 39 iterations in 0.017s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.48  thf(t68_xboole_1, conjecture,
% 0.22/0.48    (![A:$i,B:$i,C:$i]:
% 0.22/0.48     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.22/0.48       ( ~( ( r1_tarski @ C @ A ) & ( r1_tarski @ C @ B ) & 
% 0.22/0.48            ( r1_xboole_0 @ A @ B ) ) ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.48        ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.22/0.48          ( ~( ( r1_tarski @ C @ A ) & ( r1_tarski @ C @ B ) & 
% 0.22/0.48               ( r1_xboole_0 @ A @ B ) ) ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t68_xboole_1])).
% 0.22/0.48  thf('0', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(d1_xboole_0, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.48  thf('1', plain,
% 0.22/0.48      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.22/0.48      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.48  thf('2', plain, ((r1_tarski @ sk_C_1 @ sk_B_1)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(t12_xboole_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.22/0.48  thf('3', plain,
% 0.22/0.48      (![X9 : $i, X10 : $i]:
% 0.22/0.48         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 0.22/0.48      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.22/0.48  thf('4', plain, (((k2_xboole_0 @ sk_C_1 @ sk_B_1) = (sk_B_1))),
% 0.22/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.48  thf(t46_xboole_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.22/0.48  thf('5', plain,
% 0.22/0.48      (![X12 : $i, X13 : $i]:
% 0.22/0.48         ((k4_xboole_0 @ X12 @ (k2_xboole_0 @ X12 @ X13)) = (k1_xboole_0))),
% 0.22/0.48      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.22/0.48  thf(t48_xboole_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.48  thf('6', plain,
% 0.22/0.48      (![X14 : $i, X15 : $i]:
% 0.22/0.48         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.22/0.48           = (k3_xboole_0 @ X14 @ X15))),
% 0.22/0.48      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.48  thf('7', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 0.22/0.48           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.22/0.48      inference('sup+', [status(thm)], ['5', '6'])).
% 0.22/0.48  thf(t3_boole, axiom,
% 0.22/0.48    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.48  thf('8', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.22/0.48      inference('cnf', [status(esa)], [t3_boole])).
% 0.22/0.48  thf('9', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.22/0.48      inference('demod', [status(thm)], ['7', '8'])).
% 0.22/0.48  thf(t4_xboole_0, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.48            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.48       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.22/0.48            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.22/0.48  thf('10', plain,
% 0.22/0.48      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.22/0.48         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.22/0.48          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.22/0.48      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.22/0.48  thf('11', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.48         (~ (r2_hidden @ X2 @ X0)
% 0.22/0.48          | ~ (r1_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.48  thf('12', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (r1_xboole_0 @ sk_C_1 @ sk_B_1) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.22/0.48      inference('sup-', [status(thm)], ['4', '11'])).
% 0.22/0.48  thf('13', plain, ((r1_xboole_0 @ sk_A @ sk_B_1)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('14', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(t63_xboole_1, axiom,
% 0.22/0.48    (![A:$i,B:$i,C:$i]:
% 0.22/0.48     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.22/0.48       ( r1_xboole_0 @ A @ C ) ))).
% 0.22/0.48  thf('15', plain,
% 0.22/0.48      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.22/0.48         (~ (r1_tarski @ X16 @ X17)
% 0.22/0.48          | ~ (r1_xboole_0 @ X17 @ X18)
% 0.22/0.48          | (r1_xboole_0 @ X16 @ X18))),
% 0.22/0.48      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.22/0.48  thf('16', plain,
% 0.22/0.48      (![X0 : $i]: ((r1_xboole_0 @ sk_C_1 @ X0) | ~ (r1_xboole_0 @ sk_A @ X0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.48  thf('17', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B_1)),
% 0.22/0.48      inference('sup-', [status(thm)], ['13', '16'])).
% 0.22/0.48  thf('18', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C_1)),
% 0.22/0.48      inference('demod', [status(thm)], ['12', '17'])).
% 0.22/0.48  thf('19', plain, ((v1_xboole_0 @ sk_C_1)),
% 0.22/0.48      inference('sup-', [status(thm)], ['1', '18'])).
% 0.22/0.48  thf('20', plain, ($false), inference('demod', [status(thm)], ['0', '19'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

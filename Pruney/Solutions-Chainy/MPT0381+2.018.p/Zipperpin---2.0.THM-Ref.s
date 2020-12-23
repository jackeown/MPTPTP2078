%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dfuyER1cqh

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:27 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   35 (  39 expanded)
%              Number of leaves         :   17 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :  155 ( 187 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t63_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t63_subset_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ( m1_subset_1 @ X19 @ X20 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('4',plain,(
    ! [X19: $i,X20: $i] :
      ( ( m1_subset_1 @ X19 @ X20 )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(clc,[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_A @ sk_B_1 ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t55_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ A )
     => ( ( A != k1_xboole_0 )
       => ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('6',plain,(
    ! [X22: $i,X23: $i] :
      ( ( X22 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X23 @ X22 )
      | ( m1_subset_1 @ ( k1_tarski @ X23 ) @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t55_subset_1])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( m1_subset_1 @ ( k1_tarski @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['0','9'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('11',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('12',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ~ ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('15',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('16',plain,(
    $false ),
    inference(demod,[status(thm)],['14','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dfuyER1cqh
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:13:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 32 iterations in 0.019s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.48  thf(t63_subset_1, conjecture,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( r2_hidden @ A @ B ) =>
% 0.22/0.48       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i,B:$i]:
% 0.22/0.48        ( ( r2_hidden @ A @ B ) =>
% 0.22/0.48          ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t63_subset_1])).
% 0.22/0.48  thf('0', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('1', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(d2_subset_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( v1_xboole_0 @ A ) =>
% 0.22/0.48         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.22/0.48       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.48         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.48  thf('2', plain,
% 0.22/0.48      (![X19 : $i, X20 : $i]:
% 0.22/0.48         (~ (r2_hidden @ X19 @ X20)
% 0.22/0.48          | (m1_subset_1 @ X19 @ X20)
% 0.22/0.48          | (v1_xboole_0 @ X20))),
% 0.22/0.48      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.22/0.48  thf(d1_xboole_0, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.48  thf('3', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.22/0.48      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.48  thf('4', plain,
% 0.22/0.48      (![X19 : $i, X20 : $i]:
% 0.22/0.48         ((m1_subset_1 @ X19 @ X20) | ~ (r2_hidden @ X19 @ X20))),
% 0.22/0.48      inference('clc', [status(thm)], ['2', '3'])).
% 0.22/0.48  thf('5', plain, ((m1_subset_1 @ sk_A @ sk_B_1)),
% 0.22/0.48      inference('sup-', [status(thm)], ['1', '4'])).
% 0.22/0.48  thf(t55_subset_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( m1_subset_1 @ B @ A ) =>
% 0.22/0.48       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.22/0.48         ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.22/0.48  thf('6', plain,
% 0.22/0.48      (![X22 : $i, X23 : $i]:
% 0.22/0.48         (((X22) = (k1_xboole_0))
% 0.22/0.48          | ~ (m1_subset_1 @ X23 @ X22)
% 0.22/0.48          | (m1_subset_1 @ (k1_tarski @ X23) @ (k1_zfmisc_1 @ X22)))),
% 0.22/0.48      inference('cnf', [status(esa)], [t55_subset_1])).
% 0.22/0.48  thf('7', plain,
% 0.22/0.48      (((m1_subset_1 @ (k1_tarski @ sk_A) @ (k1_zfmisc_1 @ sk_B_1))
% 0.22/0.48        | ((sk_B_1) = (k1_xboole_0)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.48  thf('8', plain,
% 0.22/0.48      (~ (m1_subset_1 @ (k1_tarski @ sk_A) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('9', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.22/0.48      inference('clc', [status(thm)], ['7', '8'])).
% 0.22/0.48  thf('10', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.22/0.48      inference('demod', [status(thm)], ['0', '9'])).
% 0.22/0.48  thf(idempotence_k3_xboole_0, axiom,
% 0.22/0.48    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.22/0.48  thf('11', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.22/0.48      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.22/0.48  thf(t4_xboole_0, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.48            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.48       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.22/0.48            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.22/0.48  thf('12', plain,
% 0.22/0.48      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.22/0.48         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.22/0.48          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.22/0.48      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.22/0.48  thf('13', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.48  thf('14', plain, (~ (r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.22/0.48      inference('sup-', [status(thm)], ['10', '13'])).
% 0.22/0.48  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.22/0.48  thf('15', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 0.22/0.48      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.22/0.48  thf('16', plain, ($false), inference('demod', [status(thm)], ['14', '15'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

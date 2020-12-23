%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cfW9j4m2qk

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:06 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   42 (  48 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :  226 ( 282 expanded)
%              Number of equality atoms :   18 (  24 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('0',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X11 ) @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('1',plain,(
    ! [X10: $i] :
      ( ( k2_subset_1 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('2',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t28_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) )
          = ( k2_subset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_subset_1])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) )
      | ( ( k4_subset_1 @ X14 @ X13 @ X15 )
        = ( k2_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ X8 )
      | ( r2_hidden @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('10',plain,(
    ! [X12: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('11',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['9','10'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X5 @ X4 )
      | ( r1_tarski @ X5 @ X3 )
      | ( X4
       != ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('13',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['11','13'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('16',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['6','16'])).

thf('18',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k2_subset_1 @ sk_A ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X10: $i] :
      ( ( k2_subset_1 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('20',plain,(
    ! [X10: $i] :
      ( ( k2_subset_1 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('21',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['17','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cfW9j4m2qk
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:12:36 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.46  % Solved by: fo/fo7.sh
% 0.22/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.46  % done 24 iterations in 0.014s
% 0.22/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.46  % SZS output start Refutation
% 0.22/0.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.46  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.22/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.46  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.22/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.46  thf(dt_k2_subset_1, axiom,
% 0.22/0.46    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.46  thf('0', plain,
% 0.22/0.46      (![X11 : $i]: (m1_subset_1 @ (k2_subset_1 @ X11) @ (k1_zfmisc_1 @ X11))),
% 0.22/0.46      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.22/0.46  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.22/0.46  thf('1', plain, (![X10 : $i]: ((k2_subset_1 @ X10) = (X10))),
% 0.22/0.46      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.22/0.46  thf('2', plain, (![X11 : $i]: (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X11))),
% 0.22/0.46      inference('demod', [status(thm)], ['0', '1'])).
% 0.22/0.46  thf(t28_subset_1, conjecture,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.46       ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ))).
% 0.22/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.46    (~( ![A:$i,B:$i]:
% 0.22/0.46        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.46          ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ) )),
% 0.22/0.46    inference('cnf.neg', [status(esa)], [t28_subset_1])).
% 0.22/0.46  thf('3', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf(redefinition_k4_subset_1, axiom,
% 0.22/0.46    (![A:$i,B:$i,C:$i]:
% 0.22/0.46     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.22/0.46         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.46       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.22/0.46  thf('4', plain,
% 0.22/0.46      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.46         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.22/0.46          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14))
% 0.22/0.46          | ((k4_subset_1 @ X14 @ X13 @ X15) = (k2_xboole_0 @ X13 @ X15)))),
% 0.22/0.46      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.22/0.46  thf('5', plain,
% 0.22/0.46      (![X0 : $i]:
% 0.22/0.46         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.22/0.46          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.46      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.46  thf('6', plain,
% 0.22/0.46      (((k4_subset_1 @ sk_A @ sk_B @ sk_A) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.22/0.46      inference('sup-', [status(thm)], ['2', '5'])).
% 0.22/0.46  thf('7', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf(d2_subset_1, axiom,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( ( v1_xboole_0 @ A ) =>
% 0.22/0.46         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.22/0.46       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.46         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.46  thf('8', plain,
% 0.22/0.46      (![X7 : $i, X8 : $i]:
% 0.22/0.46         (~ (m1_subset_1 @ X7 @ X8)
% 0.22/0.46          | (r2_hidden @ X7 @ X8)
% 0.22/0.46          | (v1_xboole_0 @ X8))),
% 0.22/0.46      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.22/0.46  thf('9', plain,
% 0.22/0.46      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.46        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.46      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.46  thf(fc1_subset_1, axiom,
% 0.22/0.46    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.46  thf('10', plain, (![X12 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.22/0.46      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.22/0.46  thf('11', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.46      inference('clc', [status(thm)], ['9', '10'])).
% 0.22/0.46  thf(d1_zfmisc_1, axiom,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.22/0.46       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.22/0.46  thf('12', plain,
% 0.22/0.46      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.46         (~ (r2_hidden @ X5 @ X4)
% 0.22/0.46          | (r1_tarski @ X5 @ X3)
% 0.22/0.46          | ((X4) != (k1_zfmisc_1 @ X3)))),
% 0.22/0.46      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.22/0.46  thf('13', plain,
% 0.22/0.46      (![X3 : $i, X5 : $i]:
% 0.22/0.46         ((r1_tarski @ X5 @ X3) | ~ (r2_hidden @ X5 @ (k1_zfmisc_1 @ X3)))),
% 0.22/0.46      inference('simplify', [status(thm)], ['12'])).
% 0.22/0.46  thf('14', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.22/0.46      inference('sup-', [status(thm)], ['11', '13'])).
% 0.22/0.46  thf(t12_xboole_1, axiom,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.22/0.46  thf('15', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         (((k2_xboole_0 @ X1 @ X0) = (X0)) | ~ (r1_tarski @ X1 @ X0))),
% 0.22/0.46      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.22/0.46  thf('16', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.22/0.46      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.46  thf('17', plain, (((k4_subset_1 @ sk_A @ sk_B @ sk_A) = (sk_A))),
% 0.22/0.46      inference('demod', [status(thm)], ['6', '16'])).
% 0.22/0.46  thf('18', plain,
% 0.22/0.46      (((k4_subset_1 @ sk_A @ sk_B @ (k2_subset_1 @ sk_A))
% 0.22/0.46         != (k2_subset_1 @ sk_A))),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('19', plain, (![X10 : $i]: ((k2_subset_1 @ X10) = (X10))),
% 0.22/0.46      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.22/0.46  thf('20', plain, (![X10 : $i]: ((k2_subset_1 @ X10) = (X10))),
% 0.22/0.46      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.22/0.46  thf('21', plain, (((k4_subset_1 @ sk_A @ sk_B @ sk_A) != (sk_A))),
% 0.22/0.46      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.22/0.46  thf('22', plain, ($false),
% 0.22/0.46      inference('simplify_reflect-', [status(thm)], ['17', '21'])).
% 0.22/0.46  
% 0.22/0.46  % SZS output end Refutation
% 0.22/0.46  
% 0.22/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

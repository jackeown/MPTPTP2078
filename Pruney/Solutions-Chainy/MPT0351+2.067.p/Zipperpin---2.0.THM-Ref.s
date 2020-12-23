%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DbUqwiWGeA

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
% Statistics : Number of formulae       :   48 (  56 expanded)
%              Number of leaves         :   18 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :  269 ( 349 expanded)
%              Number of equality atoms :   20 (  26 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ( X7
       != ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ( m1_subset_1 @ X10 @ X11 )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('7',plain,(
    ! [X14: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['6','7'])).

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

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('10',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k4_subset_1 @ X16 @ X15 @ X17 )
        = ( k2_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ X11 )
      | ( r2_hidden @ X10 @ X11 )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('15',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X14: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('17',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r1_tarski @ X8 @ X6 )
      | ( X7
       != ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('19',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['17','19'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('21',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('22',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['12','22'])).

thf('24',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k2_subset_1 @ sk_A ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('25',plain,(
    ! [X13: $i] :
      ( ( k2_subset_1 @ X13 )
      = X13 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('26',plain,(
    ! [X13: $i] :
      ( ( k2_subset_1 @ X13 )
      = X13 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('27',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['23','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DbUqwiWGeA
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:57:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 31 iterations in 0.019s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.48  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.48  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.22/0.48  thf(d10_xboole_0, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.48  thf('0', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.22/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.48  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.48      inference('simplify', [status(thm)], ['0'])).
% 0.22/0.48  thf(d1_zfmisc_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.22/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.22/0.48  thf('2', plain,
% 0.22/0.48      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.48         (~ (r1_tarski @ X5 @ X6)
% 0.22/0.48          | (r2_hidden @ X5 @ X7)
% 0.22/0.48          | ((X7) != (k1_zfmisc_1 @ X6)))),
% 0.22/0.48      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.22/0.48  thf('3', plain,
% 0.22/0.48      (![X5 : $i, X6 : $i]:
% 0.22/0.48         ((r2_hidden @ X5 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X5 @ X6))),
% 0.22/0.48      inference('simplify', [status(thm)], ['2'])).
% 0.22/0.48  thf('4', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['1', '3'])).
% 0.22/0.48  thf(d2_subset_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( v1_xboole_0 @ A ) =>
% 0.22/0.48         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.22/0.48       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.48         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.48  thf('5', plain,
% 0.22/0.48      (![X10 : $i, X11 : $i]:
% 0.22/0.48         (~ (r2_hidden @ X10 @ X11)
% 0.22/0.48          | (m1_subset_1 @ X10 @ X11)
% 0.22/0.48          | (v1_xboole_0 @ X11))),
% 0.22/0.48      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.22/0.48  thf('6', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.22/0.48          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.48  thf(fc1_subset_1, axiom,
% 0.22/0.48    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.48  thf('7', plain, (![X14 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 0.22/0.48      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.22/0.48  thf('8', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.22/0.48      inference('clc', [status(thm)], ['6', '7'])).
% 0.22/0.48  thf(t28_subset_1, conjecture,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.48       ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i,B:$i]:
% 0.22/0.48        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.48          ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t28_subset_1])).
% 0.22/0.49  thf('9', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(redefinition_k4_subset_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.22/0.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.49       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.22/0.49          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16))
% 0.22/0.49          | ((k4_subset_1 @ X16 @ X15 @ X17) = (k2_xboole_0 @ X15 @ X17)))),
% 0.22/0.49      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.22/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      (((k4_subset_1 @ sk_A @ sk_B @ sk_A) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['8', '11'])).
% 0.22/0.49  thf('13', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('14', plain,
% 0.22/0.49      (![X10 : $i, X11 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X10 @ X11)
% 0.22/0.49          | (r2_hidden @ X10 @ X11)
% 0.22/0.49          | (v1_xboole_0 @ X11))),
% 0.22/0.49      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.22/0.49  thf('15', plain,
% 0.22/0.49      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.49        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.49  thf('16', plain, (![X14 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 0.22/0.49      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.22/0.49  thf('17', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.49      inference('clc', [status(thm)], ['15', '16'])).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X8 @ X7)
% 0.22/0.49          | (r1_tarski @ X8 @ X6)
% 0.22/0.49          | ((X7) != (k1_zfmisc_1 @ X6)))),
% 0.22/0.49      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      (![X6 : $i, X8 : $i]:
% 0.22/0.49         ((r1_tarski @ X8 @ X6) | ~ (r2_hidden @ X8 @ (k1_zfmisc_1 @ X6)))),
% 0.22/0.49      inference('simplify', [status(thm)], ['18'])).
% 0.22/0.49  thf('20', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.22/0.49      inference('sup-', [status(thm)], ['17', '19'])).
% 0.22/0.49  thf(t12_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.22/0.49  thf('21', plain,
% 0.22/0.49      (![X3 : $i, X4 : $i]:
% 0.22/0.49         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.22/0.49      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.22/0.49  thf('22', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.49  thf('23', plain, (((k4_subset_1 @ sk_A @ sk_B @ sk_A) = (sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['12', '22'])).
% 0.22/0.49  thf('24', plain,
% 0.22/0.49      (((k4_subset_1 @ sk_A @ sk_B @ (k2_subset_1 @ sk_A))
% 0.22/0.49         != (k2_subset_1 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.22/0.49  thf('25', plain, (![X13 : $i]: ((k2_subset_1 @ X13) = (X13))),
% 0.22/0.49      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.22/0.49  thf('26', plain, (![X13 : $i]: ((k2_subset_1 @ X13) = (X13))),
% 0.22/0.49      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.22/0.49  thf('27', plain, (((k4_subset_1 @ sk_A @ sk_B @ sk_A) != (sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.22/0.49  thf('28', plain, ($false),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['23', '27'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

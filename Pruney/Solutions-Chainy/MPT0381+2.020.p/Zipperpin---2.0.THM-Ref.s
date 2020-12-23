%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wW5W4sAB4x

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   31 (  35 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :  144 ( 176 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ~ ( m1_subset_1 @ ( k1_tarski @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_1 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ( m1_subset_1 @ X13 @ X14 )
      | ( v1_xboole_0 @ X14 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ X13 @ X14 )
      | ~ ( r2_hidden @ X13 @ X14 ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ( X16 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X17 @ X16 )
      | ( m1_subset_1 @ ( k1_tarski @ X17 ) @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t55_subset_1])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ X9 )
        = X9 )
      | ~ ( r2_hidden @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('10',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X11 ) @ X12 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('12',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['7','12'])).

thf('14',plain,(
    $false ),
    inference(demod,[status(thm)],['0','13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wW5W4sAB4x
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:18:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 31 iterations in 0.015s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.46  thf(t63_subset_1, conjecture,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( r2_hidden @ A @ B ) =>
% 0.21/0.46       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i,B:$i]:
% 0.21/0.46        ( ( r2_hidden @ A @ B ) =>
% 0.21/0.46          ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t63_subset_1])).
% 0.21/0.46  thf('0', plain,
% 0.21/0.46      (~ (m1_subset_1 @ (k1_tarski @ sk_A) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('1', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(d2_subset_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( ( v1_xboole_0 @ A ) =>
% 0.21/0.46         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.21/0.46       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.46         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      (![X13 : $i, X14 : $i]:
% 0.21/0.46         (~ (r2_hidden @ X13 @ X14)
% 0.21/0.46          | (m1_subset_1 @ X13 @ X14)
% 0.21/0.46          | (v1_xboole_0 @ X14))),
% 0.21/0.46      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.46  thf(d1_xboole_0, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.46  thf('3', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.46      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.46  thf('4', plain,
% 0.21/0.46      (![X13 : $i, X14 : $i]:
% 0.21/0.46         ((m1_subset_1 @ X13 @ X14) | ~ (r2_hidden @ X13 @ X14))),
% 0.21/0.46      inference('clc', [status(thm)], ['2', '3'])).
% 0.21/0.46  thf('5', plain, ((m1_subset_1 @ sk_A @ sk_B_1)),
% 0.21/0.46      inference('sup-', [status(thm)], ['1', '4'])).
% 0.21/0.46  thf(t55_subset_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( m1_subset_1 @ B @ A ) =>
% 0.21/0.46       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.21/0.46         ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.21/0.46  thf('6', plain,
% 0.21/0.46      (![X16 : $i, X17 : $i]:
% 0.21/0.46         (((X16) = (k1_xboole_0))
% 0.21/0.46          | ~ (m1_subset_1 @ X17 @ X16)
% 0.21/0.46          | (m1_subset_1 @ (k1_tarski @ X17) @ (k1_zfmisc_1 @ X16)))),
% 0.21/0.46      inference('cnf', [status(esa)], [t55_subset_1])).
% 0.21/0.46  thf('7', plain,
% 0.21/0.46      (((m1_subset_1 @ (k1_tarski @ sk_A) @ (k1_zfmisc_1 @ sk_B_1))
% 0.21/0.46        | ((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.46  thf('8', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(l22_zfmisc_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( r2_hidden @ A @ B ) =>
% 0.21/0.46       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.21/0.46  thf('9', plain,
% 0.21/0.46      (![X9 : $i, X10 : $i]:
% 0.21/0.46         (((k2_xboole_0 @ (k1_tarski @ X10) @ X9) = (X9))
% 0.21/0.46          | ~ (r2_hidden @ X10 @ X9))),
% 0.21/0.46      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 0.21/0.46  thf('10', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (sk_B_1))),
% 0.21/0.46      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.46  thf(t49_zfmisc_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.21/0.46  thf('11', plain,
% 0.21/0.46      (![X11 : $i, X12 : $i]:
% 0.21/0.46         ((k2_xboole_0 @ (k1_tarski @ X11) @ X12) != (k1_xboole_0))),
% 0.21/0.46      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.21/0.46  thf('12', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.46  thf('13', plain,
% 0.21/0.46      ((m1_subset_1 @ (k1_tarski @ sk_A) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.21/0.46      inference('simplify_reflect-', [status(thm)], ['7', '12'])).
% 0.21/0.46  thf('14', plain, ($false), inference('demod', [status(thm)], ['0', '13'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

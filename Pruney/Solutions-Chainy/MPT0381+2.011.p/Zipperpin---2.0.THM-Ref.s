%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4nI2WZCkgz

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:26 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   32 (  36 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :    8
%              Number of atoms          :  155 ( 187 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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

thf('2',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X11 @ X13 ) @ X14 )
      | ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( r2_hidden @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('6',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('7',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference(demod,[status(thm)],['5','6'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r2_hidden @ X6 @ X8 )
      | ( X8
       != ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    r2_hidden @ ( k1_tarski @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('11',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ( m1_subset_1 @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('13',plain,(
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ X15 @ X16 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    $false ),
    inference(demod,[status(thm)],['0','14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4nI2WZCkgz
% 0.15/0.38  % Computer   : n007.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 09:42:51 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.39  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 0.24/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.51  % Solved by: fo/fo7.sh
% 0.24/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.51  % done 29 iterations in 0.017s
% 0.24/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.51  % SZS output start Refutation
% 0.24/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.24/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.24/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.24/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.24/0.51  thf(t63_subset_1, conjecture,
% 0.24/0.51    (![A:$i,B:$i]:
% 0.24/0.51     ( ( r2_hidden @ A @ B ) =>
% 0.24/0.51       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.24/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.51    (~( ![A:$i,B:$i]:
% 0.24/0.51        ( ( r2_hidden @ A @ B ) =>
% 0.24/0.51          ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )),
% 0.24/0.51    inference('cnf.neg', [status(esa)], [t63_subset_1])).
% 0.24/0.51  thf('0', plain,
% 0.24/0.51      (~ (m1_subset_1 @ (k1_tarski @ sk_A) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('1', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('2', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf(t38_zfmisc_1, axiom,
% 0.24/0.51    (![A:$i,B:$i,C:$i]:
% 0.24/0.51     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.24/0.51       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.24/0.51  thf('3', plain,
% 0.24/0.51      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.24/0.51         ((r1_tarski @ (k2_tarski @ X11 @ X13) @ X14)
% 0.24/0.51          | ~ (r2_hidden @ X13 @ X14)
% 0.24/0.51          | ~ (r2_hidden @ X11 @ X14))),
% 0.24/0.51      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.24/0.51  thf('4', plain,
% 0.24/0.51      (![X0 : $i]:
% 0.24/0.51         (~ (r2_hidden @ X0 @ sk_B_1)
% 0.24/0.51          | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ sk_B_1))),
% 0.24/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.24/0.51  thf('5', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_A) @ sk_B_1)),
% 0.24/0.51      inference('sup-', [status(thm)], ['1', '4'])).
% 0.24/0.51  thf(t69_enumset1, axiom,
% 0.24/0.51    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.24/0.51  thf('6', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.24/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.24/0.51  thf('7', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.24/0.51      inference('demod', [status(thm)], ['5', '6'])).
% 0.24/0.51  thf(d1_zfmisc_1, axiom,
% 0.24/0.51    (![A:$i,B:$i]:
% 0.24/0.51     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.24/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.24/0.51  thf('8', plain,
% 0.24/0.51      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.24/0.51         (~ (r1_tarski @ X6 @ X7)
% 0.24/0.51          | (r2_hidden @ X6 @ X8)
% 0.24/0.51          | ((X8) != (k1_zfmisc_1 @ X7)))),
% 0.24/0.51      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.24/0.51  thf('9', plain,
% 0.24/0.51      (![X6 : $i, X7 : $i]:
% 0.24/0.51         ((r2_hidden @ X6 @ (k1_zfmisc_1 @ X7)) | ~ (r1_tarski @ X6 @ X7))),
% 0.24/0.51      inference('simplify', [status(thm)], ['8'])).
% 0.24/0.51  thf('10', plain, ((r2_hidden @ (k1_tarski @ sk_A) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.24/0.51      inference('sup-', [status(thm)], ['7', '9'])).
% 0.24/0.51  thf(d2_subset_1, axiom,
% 0.24/0.51    (![A:$i,B:$i]:
% 0.24/0.51     ( ( ( v1_xboole_0 @ A ) =>
% 0.24/0.51         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.24/0.51       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.24/0.51         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.24/0.51  thf('11', plain,
% 0.24/0.51      (![X15 : $i, X16 : $i]:
% 0.24/0.51         (~ (r2_hidden @ X15 @ X16)
% 0.24/0.51          | (m1_subset_1 @ X15 @ X16)
% 0.24/0.51          | (v1_xboole_0 @ X16))),
% 0.24/0.51      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.24/0.51  thf(d1_xboole_0, axiom,
% 0.24/0.51    (![A:$i]:
% 0.24/0.51     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.24/0.51  thf('12', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.24/0.51      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.24/0.51  thf('13', plain,
% 0.24/0.51      (![X15 : $i, X16 : $i]:
% 0.24/0.51         ((m1_subset_1 @ X15 @ X16) | ~ (r2_hidden @ X15 @ X16))),
% 0.24/0.51      inference('clc', [status(thm)], ['11', '12'])).
% 0.24/0.51  thf('14', plain,
% 0.24/0.51      ((m1_subset_1 @ (k1_tarski @ sk_A) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.24/0.51      inference('sup-', [status(thm)], ['10', '13'])).
% 0.24/0.51  thf('15', plain, ($false), inference('demod', [status(thm)], ['0', '14'])).
% 0.24/0.51  
% 0.24/0.51  % SZS output end Refutation
% 0.24/0.51  
% 0.24/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

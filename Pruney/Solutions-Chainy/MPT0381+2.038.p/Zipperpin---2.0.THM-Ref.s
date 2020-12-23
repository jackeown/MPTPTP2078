%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QgiGjHgrsc

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   34 (  38 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :  153 ( 185 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_A @ sk_B ),
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
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( m1_subset_1 @ X4 @ X5 )
      | ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('4',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(clc,[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t55_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ A )
     => ( ( A != k1_xboole_0 )
       => ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X12 @ X11 )
      | ( m1_subset_1 @ ( k1_tarski @ X12 ) @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t55_subset_1])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( m1_subset_1 @ ( k1_tarski @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['0','9'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('11',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( r2_hidden @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ X0 ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('16',plain,(
    $false ),
    inference('sup-',[status(thm)],['14','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QgiGjHgrsc
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:01:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.44  % Solved by: fo/fo7.sh
% 0.21/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.44  % done 27 iterations in 0.009s
% 0.21/0.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.44  % SZS output start Refutation
% 0.21/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.44  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.44  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.44  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.44  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.44  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.44  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.44  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.44  thf(t63_subset_1, conjecture,
% 0.21/0.44    (![A:$i,B:$i]:
% 0.21/0.44     ( ( r2_hidden @ A @ B ) =>
% 0.21/0.44       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.21/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.44    (~( ![A:$i,B:$i]:
% 0.21/0.44        ( ( r2_hidden @ A @ B ) =>
% 0.21/0.44          ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )),
% 0.21/0.44    inference('cnf.neg', [status(esa)], [t63_subset_1])).
% 0.21/0.44  thf('0', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf('1', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf(d2_subset_1, axiom,
% 0.21/0.44    (![A:$i,B:$i]:
% 0.21/0.44     ( ( ( v1_xboole_0 @ A ) =>
% 0.21/0.44         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.21/0.44       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.44         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.44  thf('2', plain,
% 0.21/0.44      (![X4 : $i, X5 : $i]:
% 0.21/0.44         (~ (r2_hidden @ X4 @ X5)
% 0.21/0.44          | (m1_subset_1 @ X4 @ X5)
% 0.21/0.44          | (v1_xboole_0 @ X5))),
% 0.21/0.44      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.44  thf(t7_boole, axiom,
% 0.21/0.44    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( v1_xboole_0 @ B ) ) ))).
% 0.21/0.44  thf('3', plain,
% 0.21/0.44      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.44      inference('cnf', [status(esa)], [t7_boole])).
% 0.21/0.44  thf('4', plain,
% 0.21/0.44      (![X4 : $i, X5 : $i]: ((m1_subset_1 @ X4 @ X5) | ~ (r2_hidden @ X4 @ X5))),
% 0.21/0.44      inference('clc', [status(thm)], ['2', '3'])).
% 0.21/0.44  thf('5', plain, ((m1_subset_1 @ sk_A @ sk_B)),
% 0.21/0.44      inference('sup-', [status(thm)], ['1', '4'])).
% 0.21/0.44  thf(t55_subset_1, axiom,
% 0.21/0.44    (![A:$i,B:$i]:
% 0.21/0.44     ( ( m1_subset_1 @ B @ A ) =>
% 0.21/0.44       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.21/0.44         ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.21/0.44  thf('6', plain,
% 0.21/0.44      (![X11 : $i, X12 : $i]:
% 0.21/0.44         (((X11) = (k1_xboole_0))
% 0.21/0.44          | ~ (m1_subset_1 @ X12 @ X11)
% 0.21/0.44          | (m1_subset_1 @ (k1_tarski @ X12) @ (k1_zfmisc_1 @ X11)))),
% 0.21/0.44      inference('cnf', [status(esa)], [t55_subset_1])).
% 0.21/0.44  thf('7', plain,
% 0.21/0.44      (((m1_subset_1 @ (k1_tarski @ sk_A) @ (k1_zfmisc_1 @ sk_B))
% 0.21/0.44        | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.44      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.44  thf('8', plain,
% 0.21/0.44      (~ (m1_subset_1 @ (k1_tarski @ sk_A) @ (k1_zfmisc_1 @ sk_B))),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf('9', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.44      inference('clc', [status(thm)], ['7', '8'])).
% 0.21/0.44  thf('10', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.21/0.44      inference('demod', [status(thm)], ['0', '9'])).
% 0.21/0.44  thf(t4_subset_1, axiom,
% 0.21/0.44    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.44  thf('11', plain,
% 0.21/0.44      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.21/0.44      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.44  thf(l3_subset_1, axiom,
% 0.21/0.44    (![A:$i,B:$i]:
% 0.21/0.44     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.44       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.21/0.44  thf('12', plain,
% 0.21/0.44      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.44         (~ (r2_hidden @ X7 @ X8)
% 0.21/0.44          | (r2_hidden @ X7 @ X9)
% 0.21/0.44          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.21/0.44      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.21/0.44  thf('13', plain,
% 0.21/0.44      (![X0 : $i, X1 : $i]:
% 0.21/0.44         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.21/0.44      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.44  thf('14', plain, (![X0 : $i]: (r2_hidden @ sk_A @ X0)),
% 0.21/0.44      inference('sup-', [status(thm)], ['10', '13'])).
% 0.21/0.44  thf(t152_zfmisc_1, axiom,
% 0.21/0.44    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.21/0.44  thf('15', plain,
% 0.21/0.44      (![X2 : $i, X3 : $i]: ~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.21/0.44      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.21/0.44  thf('16', plain, ($false), inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.44  
% 0.21/0.44  % SZS output end Refutation
% 0.21/0.44  
% 0.21/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

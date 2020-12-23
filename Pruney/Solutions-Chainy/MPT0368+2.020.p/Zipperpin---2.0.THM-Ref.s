%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UmIThssX05

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:14 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   33 (  53 expanded)
%              Number of leaves         :   12 (  20 expanded)
%              Depth                    :   11
%              Number of atoms          :  195 ( 410 expanded)
%              Number of equality atoms :   11 (  27 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('0',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X4 = X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X4 ) @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t49_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ! [C: $i] :
            ( ( m1_subset_1 @ C @ A )
           => ( r2_hidden @ C @ B ) )
       => ( A = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ( r2_hidden @ C @ B ) )
         => ( A = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t49_subset_1])).

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ sk_B_1 @ X0 ) @ X0 )
      | ( X0 = sk_B_1 )
      | ( r2_hidden @ ( sk_C @ sk_B_1 @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,
    ( ( sk_A = sk_B_1 )
    | ( r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) ),
    inference(eq_fact,[status(thm)],['4'])).

thf('6',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( m1_subset_1 @ X5 @ X6 )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('10',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ X5 @ X6 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X11: $i] :
      ( ( r2_hidden @ X11 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X11 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X4 = X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X4 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('15',plain,
    ( ~ ( r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ( sk_A = sk_B_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('17',plain,(
    sk_A = sk_B_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UmIThssX05
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:14:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.58  % Solved by: fo/fo7.sh
% 0.37/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.58  % done 152 iterations in 0.121s
% 0.37/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.58  % SZS output start Refutation
% 0.37/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.58  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.37/0.58  thf(t2_tarski, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.37/0.58       ( ( A ) = ( B ) ) ))).
% 0.37/0.58  thf('0', plain,
% 0.37/0.58      (![X3 : $i, X4 : $i]:
% 0.37/0.58         (((X4) = (X3))
% 0.37/0.58          | (r2_hidden @ (sk_C @ X3 @ X4) @ X3)
% 0.37/0.58          | (r2_hidden @ (sk_C @ X3 @ X4) @ X4))),
% 0.37/0.58      inference('cnf', [status(esa)], [t2_tarski])).
% 0.37/0.58  thf(t49_subset_1, conjecture,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.58       ( ( ![C:$i]: ( ( m1_subset_1 @ C @ A ) => ( r2_hidden @ C @ B ) ) ) =>
% 0.37/0.58         ( ( A ) = ( B ) ) ) ))).
% 0.37/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.58    (~( ![A:$i,B:$i]:
% 0.37/0.58        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.58          ( ( ![C:$i]: ( ( m1_subset_1 @ C @ A ) => ( r2_hidden @ C @ B ) ) ) =>
% 0.37/0.58            ( ( A ) = ( B ) ) ) ) )),
% 0.37/0.58    inference('cnf.neg', [status(esa)], [t49_subset_1])).
% 0.37/0.58  thf('1', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(l3_subset_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.37/0.58  thf('2', plain,
% 0.37/0.58      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.37/0.58         (~ (r2_hidden @ X8 @ X9)
% 0.37/0.58          | (r2_hidden @ X8 @ X10)
% 0.37/0.58          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.37/0.58      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.37/0.58  thf('3', plain,
% 0.37/0.58      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.37/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.58  thf('4', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         ((r2_hidden @ (sk_C @ sk_B_1 @ X0) @ X0)
% 0.37/0.58          | ((X0) = (sk_B_1))
% 0.37/0.58          | (r2_hidden @ (sk_C @ sk_B_1 @ X0) @ sk_A))),
% 0.37/0.58      inference('sup-', [status(thm)], ['0', '3'])).
% 0.37/0.58  thf('5', plain,
% 0.37/0.58      ((((sk_A) = (sk_B_1)) | (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ sk_A))),
% 0.37/0.58      inference('eq_fact', [status(thm)], ['4'])).
% 0.37/0.58  thf('6', plain, (((sk_A) != (sk_B_1))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('7', plain, ((r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)),
% 0.37/0.58      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.37/0.58  thf(d2_subset_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( ( v1_xboole_0 @ A ) =>
% 0.37/0.58         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.37/0.58       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.37/0.58         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.37/0.58  thf('8', plain,
% 0.37/0.58      (![X5 : $i, X6 : $i]:
% 0.37/0.58         (~ (r2_hidden @ X5 @ X6)
% 0.37/0.58          | (m1_subset_1 @ X5 @ X6)
% 0.37/0.58          | (v1_xboole_0 @ X6))),
% 0.37/0.58      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.37/0.58  thf(d1_xboole_0, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.37/0.58  thf('9', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.37/0.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.37/0.58  thf('10', plain,
% 0.37/0.58      (![X5 : $i, X6 : $i]: ((m1_subset_1 @ X5 @ X6) | ~ (r2_hidden @ X5 @ X6))),
% 0.37/0.58      inference('clc', [status(thm)], ['8', '9'])).
% 0.37/0.58  thf('11', plain, ((m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)),
% 0.37/0.58      inference('sup-', [status(thm)], ['7', '10'])).
% 0.37/0.58  thf('12', plain,
% 0.37/0.58      (![X11 : $i]: ((r2_hidden @ X11 @ sk_B_1) | ~ (m1_subset_1 @ X11 @ sk_A))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('13', plain, ((r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ sk_B_1)),
% 0.37/0.58      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.58  thf('14', plain,
% 0.37/0.58      (![X3 : $i, X4 : $i]:
% 0.37/0.58         (((X4) = (X3))
% 0.37/0.58          | ~ (r2_hidden @ (sk_C @ X3 @ X4) @ X3)
% 0.37/0.58          | ~ (r2_hidden @ (sk_C @ X3 @ X4) @ X4))),
% 0.37/0.58      inference('cnf', [status(esa)], [t2_tarski])).
% 0.37/0.58  thf('15', plain,
% 0.37/0.58      ((~ (r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ sk_A) | ((sk_A) = (sk_B_1)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['13', '14'])).
% 0.37/0.58  thf('16', plain, ((r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)),
% 0.37/0.58      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.37/0.58  thf('17', plain, (((sk_A) = (sk_B_1))),
% 0.37/0.58      inference('demod', [status(thm)], ['15', '16'])).
% 0.37/0.58  thf('18', plain, (((sk_A) != (sk_B_1))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('19', plain, ($false),
% 0.37/0.58      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 0.37/0.58  
% 0.37/0.58  % SZS output end Refutation
% 0.37/0.58  
% 0.37/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

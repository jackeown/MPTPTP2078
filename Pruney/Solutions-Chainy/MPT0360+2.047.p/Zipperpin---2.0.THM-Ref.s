%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RxdrMlBSl9

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:47 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   39 (  48 expanded)
%              Number of leaves         :   16 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :  217 ( 334 expanded)
%              Number of equality atoms :   11 (  17 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t40_subset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( ( r1_tarski @ B @ C )
          & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) )
       => ( B = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
       => ( ( ( r1_tarski @ B @ C )
            & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) )
         => ( B = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t40_subset_1])).

thf('1',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_subset_1 @ X21 @ X22 )
        = ( k4_xboole_0 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('7',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('8',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( r2_hidden @ X14 @ X12 )
      | ( X13
       != ( k4_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('9',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k4_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ X0 ) ),
    inference(clc,[status(thm)],['11','16'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('18',plain,(
    ! [X20: $i] :
      ( ( X20 = k1_xboole_0 )
      | ~ ( r1_tarski @ X20 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('19',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RxdrMlBSl9
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:00:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 38 iterations in 0.022s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.50  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.22/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.50  thf(d3_tarski, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      (![X1 : $i, X3 : $i]:
% 0.22/0.50         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.22/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.50  thf(t40_subset_1, conjecture,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.50       ( ( ( r1_tarski @ B @ C ) & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.22/0.50         ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.50        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.50          ( ( ( r1_tarski @ B @ C ) & 
% 0.22/0.50              ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.22/0.50            ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t40_subset_1])).
% 0.22/0.50  thf('1', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.22/0.50          | (r2_hidden @ X0 @ X2)
% 0.22/0.50          | ~ (r1_tarski @ X1 @ X2))),
% 0.22/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1))
% 0.22/0.50          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((r1_tarski @ sk_B @ X0)
% 0.22/0.50          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['0', '3'])).
% 0.22/0.50  thf('5', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(d5_subset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.50       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      (![X21 : $i, X22 : $i]:
% 0.22/0.50         (((k3_subset_1 @ X21 @ X22) = (k4_xboole_0 @ X21 @ X22))
% 0.22/0.50          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.50  thf(d5_xboole_0, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.22/0.50       ( ![D:$i]:
% 0.22/0.50         ( ( r2_hidden @ D @ C ) <=>
% 0.22/0.50           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X14 @ X13)
% 0.22/0.50          | ~ (r2_hidden @ X14 @ X12)
% 0.22/0.50          | ((X13) != (k4_xboole_0 @ X11 @ X12)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      (![X11 : $i, X12 : $i, X14 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X14 @ X12)
% 0.22/0.50          | ~ (r2_hidden @ X14 @ (k4_xboole_0 @ X11 @ X12)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['8'])).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1))
% 0.22/0.50          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['7', '9'])).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((r1_tarski @ sk_B @ X0) | ~ (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_C_1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['4', '10'])).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      (![X1 : $i, X3 : $i]:
% 0.22/0.50         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.22/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.50  thf('13', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.22/0.50          | (r2_hidden @ X0 @ X2)
% 0.22/0.50          | ~ (r1_tarski @ X1 @ X2))),
% 0.22/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_1) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.50  thf('16', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((r1_tarski @ sk_B @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_C_1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['12', '15'])).
% 0.22/0.50  thf('17', plain, (![X0 : $i]: (r1_tarski @ sk_B @ X0)),
% 0.22/0.50      inference('clc', [status(thm)], ['11', '16'])).
% 0.22/0.50  thf(t3_xboole_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.50  thf('18', plain,
% 0.22/0.50      (![X20 : $i]:
% 0.22/0.50         (((X20) = (k1_xboole_0)) | ~ (r1_tarski @ X20 @ k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.22/0.50  thf('19', plain, (((sk_B) = (k1_xboole_0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.50  thf('20', plain, (((sk_B) != (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('21', plain, ($false),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

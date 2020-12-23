%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cSuiNtOu7Z

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:13 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   41 (  66 expanded)
%              Number of leaves         :   16 (  26 expanded)
%              Depth                    :   12
%              Number of atoms          :  207 ( 436 expanded)
%              Number of equality atoms :    8 (  22 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf('0',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ X14 )
      | ( r2_hidden @ X13 @ X14 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X16: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('4',plain,(
    r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['2','3'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( r1_tarski @ X11 @ X9 )
      | ( X10
       != ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('6',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['4','6'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('8',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r2_xboole_0 @ X3 @ X5 )
      | ( X3 = X5 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('9',plain,
    ( ( sk_B_1 = sk_A )
    | ( r2_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    r2_xboole_0 @ sk_B_1 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf(t6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ~ ( r2_hidden @ C @ A ) ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('13',plain,(
    r2_hidden @ ( sk_C @ sk_A @ sk_B_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
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

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ X13 @ X14 )
      | ~ ( r2_hidden @ X13 @ X14 ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ ( sk_C @ sk_A @ sk_B_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X17: $i] :
      ( ( r2_hidden @ X17 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X17 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r2_hidden @ ( sk_C @ sk_A @ sk_B_1 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_xboole_0 @ X6 @ X7 )
      | ~ ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('21',plain,(
    ~ ( r2_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r2_xboole_0 @ sk_B_1 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['21','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cSuiNtOu7Z
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:31:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 45 iterations in 0.020s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.20/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(t49_subset_1, conjecture,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.47       ( ( ![C:$i]: ( ( m1_subset_1 @ C @ A ) => ( r2_hidden @ C @ B ) ) ) =>
% 0.20/0.47         ( ( A ) = ( B ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i]:
% 0.20/0.47        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.47          ( ( ![C:$i]: ( ( m1_subset_1 @ C @ A ) => ( r2_hidden @ C @ B ) ) ) =>
% 0.20/0.47            ( ( A ) = ( B ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t49_subset_1])).
% 0.20/0.47  thf('0', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(d2_subset_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( v1_xboole_0 @ A ) =>
% 0.20/0.47         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.20/0.47       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.47         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (![X13 : $i, X14 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X13 @ X14)
% 0.20/0.47          | (r2_hidden @ X13 @ X14)
% 0.20/0.47          | (v1_xboole_0 @ X14))),
% 0.20/0.47      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.47        | (r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.47  thf(fc1_subset_1, axiom,
% 0.20/0.47    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.47  thf('3', plain, (![X16 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 0.20/0.47      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.47  thf('4', plain, ((r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.47      inference('clc', [status(thm)], ['2', '3'])).
% 0.20/0.47  thf(d1_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.20/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X11 @ X10)
% 0.20/0.47          | (r1_tarski @ X11 @ X9)
% 0.20/0.47          | ((X10) != (k1_zfmisc_1 @ X9)))),
% 0.20/0.47      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (![X9 : $i, X11 : $i]:
% 0.20/0.47         ((r1_tarski @ X11 @ X9) | ~ (r2_hidden @ X11 @ (k1_zfmisc_1 @ X9)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.47  thf('7', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 0.20/0.47      inference('sup-', [status(thm)], ['4', '6'])).
% 0.20/0.47  thf(d8_xboole_0, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.20/0.47       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X3 : $i, X5 : $i]:
% 0.20/0.47         ((r2_xboole_0 @ X3 @ X5) | ((X3) = (X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.20/0.47      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.20/0.47  thf('9', plain, ((((sk_B_1) = (sk_A)) | (r2_xboole_0 @ sk_B_1 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.47  thf('10', plain, (((sk_A) != (sk_B_1))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('11', plain, ((r2_xboole_0 @ sk_B_1 @ sk_A)),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.20/0.47  thf(t6_xboole_0, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ~( ( r2_xboole_0 @ A @ B ) & 
% 0.20/0.47          ( ![C:$i]:
% 0.20/0.47            ( ~( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ) ) ) ))).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (![X6 : $i, X7 : $i]:
% 0.20/0.47         (~ (r2_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.20/0.47      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.20/0.47  thf('13', plain, ((r2_hidden @ (sk_C @ sk_A @ sk_B_1) @ sk_A)),
% 0.20/0.47      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X13 : $i, X14 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X13 @ X14)
% 0.20/0.47          | (m1_subset_1 @ X13 @ X14)
% 0.20/0.47          | (v1_xboole_0 @ X14))),
% 0.20/0.47      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.47  thf(d1_xboole_0, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.47      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      (![X13 : $i, X14 : $i]:
% 0.20/0.47         ((m1_subset_1 @ X13 @ X14) | ~ (r2_hidden @ X13 @ X14))),
% 0.20/0.47      inference('clc', [status(thm)], ['14', '15'])).
% 0.20/0.47  thf('17', plain, ((m1_subset_1 @ (sk_C @ sk_A @ sk_B_1) @ sk_A)),
% 0.20/0.47      inference('sup-', [status(thm)], ['13', '16'])).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      (![X17 : $i]: ((r2_hidden @ X17 @ sk_B_1) | ~ (m1_subset_1 @ X17 @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('19', plain, ((r2_hidden @ (sk_C @ sk_A @ sk_B_1) @ sk_B_1)),
% 0.20/0.47      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      (![X6 : $i, X7 : $i]:
% 0.20/0.47         (~ (r2_xboole_0 @ X6 @ X7) | ~ (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.20/0.47      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.20/0.47  thf('21', plain, (~ (r2_xboole_0 @ sk_B_1 @ sk_A)),
% 0.20/0.47      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.47  thf('22', plain, ((r2_xboole_0 @ sk_B_1 @ sk_A)),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.20/0.47  thf('23', plain, ($false), inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

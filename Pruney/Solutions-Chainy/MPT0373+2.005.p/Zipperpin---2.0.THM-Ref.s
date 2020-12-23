%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bLivV9kmTE

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   39 (  44 expanded)
%              Number of leaves         :   17 (  20 expanded)
%              Depth                    :   11
%              Number of atoms          :  199 ( 258 expanded)
%              Number of equality atoms :   14 (  18 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t55_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ A )
     => ( ( A != k1_xboole_0 )
       => ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ A )
       => ( ( A != k1_xboole_0 )
         => ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t55_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B_1 @ sk_A ),
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
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ X19 )
      | ( r2_hidden @ X18 @ X19 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(l35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('3',plain,(
    ! [X15: $i,X17: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X15 ) @ X17 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('4',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( ( k4_xboole_0 @ X4 @ X5 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('6',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['6'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ( r2_hidden @ X10 @ X12 )
      | ( X12
       != ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('9',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ( m1_subset_1 @ X18 @ X19 )
      | ( v1_xboole_0 @ X19 ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ( m1_subset_1 @ X18 @ X19 )
      | ~ ( r2_hidden @ X18 @ X19 ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ~ ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['14','15'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('17',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('18',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['18','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bLivV9kmTE
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:02:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 39 iterations in 0.018s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(t55_subset_1, conjecture,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ B @ A ) =>
% 0.21/0.47       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.21/0.47         ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i]:
% 0.21/0.47        ( ( m1_subset_1 @ B @ A ) =>
% 0.21/0.47          ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.21/0.47            ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t55_subset_1])).
% 0.21/0.47  thf('0', plain, ((m1_subset_1 @ sk_B_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(d2_subset_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( v1_xboole_0 @ A ) =>
% 0.21/0.47         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.21/0.47       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.47         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (![X18 : $i, X19 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X18 @ X19)
% 0.21/0.47          | (r2_hidden @ X18 @ X19)
% 0.21/0.47          | (v1_xboole_0 @ X19))),
% 0.21/0.47      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.47  thf('2', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_B_1 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.47  thf(l35_zfmisc_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.47       ( r2_hidden @ A @ B ) ))).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X15 : $i, X17 : $i]:
% 0.21/0.47         (((k4_xboole_0 @ (k1_tarski @ X15) @ X17) = (k1_xboole_0))
% 0.21/0.47          | ~ (r2_hidden @ X15 @ X17))),
% 0.21/0.47      inference('cnf', [status(esa)], [l35_zfmisc_1])).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (((v1_xboole_0 @ sk_A)
% 0.21/0.47        | ((k4_xboole_0 @ (k1_tarski @ sk_B_1) @ sk_A) = (k1_xboole_0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.47  thf(l32_xboole_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X4 : $i, X5 : $i]:
% 0.21/0.47         ((r1_tarski @ X4 @ X5) | ((k4_xboole_0 @ X4 @ X5) != (k1_xboole_0)))),
% 0.21/0.47      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.47        | (v1_xboole_0 @ sk_A)
% 0.21/0.47        | (r1_tarski @ (k1_tarski @ sk_B_1) @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (((r1_tarski @ (k1_tarski @ sk_B_1) @ sk_A) | (v1_xboole_0 @ sk_A))),
% 0.21/0.47      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.47  thf(d1_zfmisc_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.21/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.47         (~ (r1_tarski @ X10 @ X11)
% 0.21/0.47          | (r2_hidden @ X10 @ X12)
% 0.21/0.47          | ((X12) != (k1_zfmisc_1 @ X11)))),
% 0.21/0.47      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (![X10 : $i, X11 : $i]:
% 0.21/0.47         ((r2_hidden @ X10 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X10 @ X11))),
% 0.21/0.47      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (((v1_xboole_0 @ sk_A)
% 0.21/0.47        | (r2_hidden @ (k1_tarski @ sk_B_1) @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['7', '9'])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X18 : $i, X19 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X18 @ X19)
% 0.21/0.47          | (m1_subset_1 @ X18 @ X19)
% 0.21/0.47          | (v1_xboole_0 @ X19))),
% 0.21/0.47      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.47  thf(d1_xboole_0, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.47      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (![X18 : $i, X19 : $i]:
% 0.21/0.47         ((m1_subset_1 @ X18 @ X19) | ~ (r2_hidden @ X18 @ X19))),
% 0.21/0.47      inference('clc', [status(thm)], ['11', '12'])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (((v1_xboole_0 @ sk_A)
% 0.21/0.47        | (m1_subset_1 @ (k1_tarski @ sk_B_1) @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['10', '13'])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      (~ (m1_subset_1 @ (k1_tarski @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('16', plain, ((v1_xboole_0 @ sk_A)),
% 0.21/0.47      inference('clc', [status(thm)], ['14', '15'])).
% 0.21/0.47  thf(l13_xboole_0, axiom,
% 0.21/0.47    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.21/0.47      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.47  thf('18', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.47  thf('19', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('20', plain, ($false),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['18', '19'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

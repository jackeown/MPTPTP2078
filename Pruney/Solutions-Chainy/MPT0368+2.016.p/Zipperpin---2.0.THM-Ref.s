%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TvWfkmr08z

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   42 (  70 expanded)
%              Number of leaves         :   17 (  28 expanded)
%              Depth                    :   12
%              Number of atoms          :  223 ( 476 expanded)
%              Number of equality atoms :    6 (  18 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ( m1_subset_1 @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ X12 @ X13 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(clc,[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( m1_subset_1 @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

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

thf('5',plain,(
    ! [X18: $i] :
      ( ( r2_hidden @ X18 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X18 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,
    ( ( r1_tarski @ sk_A @ sk_B_1 )
    | ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(simplify,[status(thm)],['8'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('10',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r2_xboole_0 @ X7 @ X9 )
      | ( X7 = X9 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('11',plain,
    ( ( sk_A = sk_B_1 )
    | ( r2_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r2_xboole_0 @ sk_A @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf(t6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ~ ( r2_hidden @ C @ A ) ) ) )).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('15',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('17',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ( r2_hidden @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_xboole_0 @ X10 @ X11 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X11 @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('21',plain,(
    ~ ( r2_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r2_xboole_0 @ sk_A @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['21','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TvWfkmr08z
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:59:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 84 iterations in 0.063s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.21/0.51  thf(d3_tarski, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      (![X4 : $i, X6 : $i]:
% 0.21/0.51         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.51  thf(d2_subset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( v1_xboole_0 @ A ) =>
% 0.21/0.51         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.21/0.51       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.51         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (![X12 : $i, X13 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X12 @ X13)
% 0.21/0.51          | (m1_subset_1 @ X12 @ X13)
% 0.21/0.51          | (v1_xboole_0 @ X13))),
% 0.21/0.51      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.51  thf(d1_xboole_0, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X12 : $i, X13 : $i]:
% 0.21/0.51         ((m1_subset_1 @ X12 @ X13) | ~ (r2_hidden @ X12 @ X13))),
% 0.21/0.51      inference('clc', [status(thm)], ['1', '2'])).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((r1_tarski @ X0 @ X1) | (m1_subset_1 @ (sk_C @ X1 @ X0) @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['0', '3'])).
% 0.21/0.51  thf(t49_subset_1, conjecture,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.51       ( ( ![C:$i]: ( ( m1_subset_1 @ C @ A ) => ( r2_hidden @ C @ B ) ) ) =>
% 0.21/0.51         ( ( A ) = ( B ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i]:
% 0.21/0.51        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.51          ( ( ![C:$i]: ( ( m1_subset_1 @ C @ A ) => ( r2_hidden @ C @ B ) ) ) =>
% 0.21/0.51            ( ( A ) = ( B ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t49_subset_1])).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (![X18 : $i]: ((r2_hidden @ X18 @ sk_B_1) | ~ (m1_subset_1 @ X18 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r1_tarski @ sk_A @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (![X4 : $i, X6 : $i]:
% 0.21/0.51         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (((r1_tarski @ sk_A @ sk_B_1) | (r1_tarski @ sk_A @ sk_B_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.51  thf('9', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.21/0.51      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.51  thf(d8_xboole_0, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.21/0.51       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X7 : $i, X9 : $i]:
% 0.21/0.51         ((r2_xboole_0 @ X7 @ X9) | ((X7) = (X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.21/0.51  thf('11', plain, ((((sk_A) = (sk_B_1)) | (r2_xboole_0 @ sk_A @ sk_B_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.51  thf('12', plain, (((sk_A) != (sk_B_1))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('13', plain, ((r2_xboole_0 @ sk_A @ sk_B_1)),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf(t6_xboole_0, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ~( ( r2_xboole_0 @ A @ B ) & 
% 0.21/0.51          ( ![C:$i]:
% 0.21/0.51            ( ~( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ) ) ) ))).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i]:
% 0.21/0.51         (~ (r2_xboole_0 @ X10 @ X11)
% 0.21/0.51          | (r2_hidden @ (sk_C_1 @ X11 @ X10) @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.21/0.51  thf('15', plain, ((r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1)),
% 0.21/0.51      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.51  thf('16', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(l3_subset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X15 @ X16)
% 0.21/0.51          | (r2_hidden @ X15 @ X17)
% 0.21/0.51          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.21/0.51      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.51  thf('19', plain, ((r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['15', '18'])).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i]:
% 0.21/0.51         (~ (r2_xboole_0 @ X10 @ X11)
% 0.21/0.51          | ~ (r2_hidden @ (sk_C_1 @ X11 @ X10) @ X10))),
% 0.21/0.51      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.21/0.51  thf('21', plain, (~ (r2_xboole_0 @ sk_A @ sk_B_1)),
% 0.21/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.51  thf('22', plain, ((r2_xboole_0 @ sk_A @ sk_B_1)),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf('23', plain, ($false), inference('demod', [status(thm)], ['21', '22'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

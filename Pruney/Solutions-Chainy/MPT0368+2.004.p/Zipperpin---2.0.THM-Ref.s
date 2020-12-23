%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pJ1kTdNFem

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:12 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   42 (  48 expanded)
%              Number of leaves         :   17 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :  213 ( 289 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ X13 @ X14 )
      | ~ ( r2_hidden @ X13 @ X14 ) ) ),
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
    ! [X17: $i] :
      ( ( r2_hidden @ X17 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X17 @ sk_A ) ) ),
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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('11',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_A )
    | ( sk_B_1 = sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ~ ( r1_tarski @ sk_B_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ X14 )
      | ( r2_hidden @ X13 @ X14 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('17',plain,(
    ! [X16: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('18',plain,(
    r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('19',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ ( k3_tarski @ X11 ) )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('20',plain,(
    r1_tarski @ sk_B_1 @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('21',plain,(
    ! [X12: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('22',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['13','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pJ1kTdNFem
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:49:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.45  % Solved by: fo/fo7.sh
% 0.20/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.45  % done 50 iterations in 0.027s
% 0.20/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.45  % SZS output start Refutation
% 0.20/0.45  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.45  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.45  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.45  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.45  thf(d3_tarski, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.45       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.45  thf('0', plain,
% 0.20/0.45      (![X4 : $i, X6 : $i]:
% 0.20/0.45         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.20/0.45      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.45  thf(d2_subset_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( ( v1_xboole_0 @ A ) =>
% 0.20/0.45         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.20/0.45       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.45         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.45  thf('1', plain,
% 0.20/0.45      (![X13 : $i, X14 : $i]:
% 0.20/0.45         (~ (r2_hidden @ X13 @ X14)
% 0.20/0.45          | (m1_subset_1 @ X13 @ X14)
% 0.20/0.45          | (v1_xboole_0 @ X14))),
% 0.20/0.45      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.45  thf(d1_xboole_0, axiom,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.45  thf('2', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.45      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.45  thf('3', plain,
% 0.20/0.45      (![X13 : $i, X14 : $i]:
% 0.20/0.45         ((m1_subset_1 @ X13 @ X14) | ~ (r2_hidden @ X13 @ X14))),
% 0.20/0.45      inference('clc', [status(thm)], ['1', '2'])).
% 0.20/0.45  thf('4', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         ((r1_tarski @ X0 @ X1) | (m1_subset_1 @ (sk_C @ X1 @ X0) @ X0))),
% 0.20/0.45      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.45  thf(t49_subset_1, conjecture,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.45       ( ( ![C:$i]: ( ( m1_subset_1 @ C @ A ) => ( r2_hidden @ C @ B ) ) ) =>
% 0.20/0.45         ( ( A ) = ( B ) ) ) ))).
% 0.20/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.45    (~( ![A:$i,B:$i]:
% 0.20/0.45        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.45          ( ( ![C:$i]: ( ( m1_subset_1 @ C @ A ) => ( r2_hidden @ C @ B ) ) ) =>
% 0.20/0.45            ( ( A ) = ( B ) ) ) ) )),
% 0.20/0.45    inference('cnf.neg', [status(esa)], [t49_subset_1])).
% 0.20/0.45  thf('5', plain,
% 0.20/0.45      (![X17 : $i]: ((r2_hidden @ X17 @ sk_B_1) | ~ (m1_subset_1 @ X17 @ sk_A))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('6', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         ((r1_tarski @ sk_A @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B_1))),
% 0.20/0.45      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.45  thf('7', plain,
% 0.20/0.45      (![X4 : $i, X6 : $i]:
% 0.20/0.45         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.20/0.45      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.45  thf('8', plain,
% 0.20/0.45      (((r1_tarski @ sk_A @ sk_B_1) | (r1_tarski @ sk_A @ sk_B_1))),
% 0.20/0.45      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.45  thf('9', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.20/0.45      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.45  thf(d10_xboole_0, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.45  thf('10', plain,
% 0.20/0.45      (![X7 : $i, X9 : $i]:
% 0.20/0.45         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.20/0.45      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.45  thf('11', plain, ((~ (r1_tarski @ sk_B_1 @ sk_A) | ((sk_B_1) = (sk_A)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.45  thf('12', plain, (((sk_A) != (sk_B_1))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('13', plain, (~ (r1_tarski @ sk_B_1 @ sk_A)),
% 0.20/0.45      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 0.20/0.45  thf('14', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('15', plain,
% 0.20/0.45      (![X13 : $i, X14 : $i]:
% 0.20/0.45         (~ (m1_subset_1 @ X13 @ X14)
% 0.20/0.45          | (r2_hidden @ X13 @ X14)
% 0.20/0.45          | (v1_xboole_0 @ X14))),
% 0.20/0.45      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.45  thf('16', plain,
% 0.20/0.45      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.45        | (r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.45  thf(fc1_subset_1, axiom,
% 0.20/0.45    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.45  thf('17', plain, (![X16 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 0.20/0.45      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.45  thf('18', plain, ((r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.45      inference('clc', [status(thm)], ['16', '17'])).
% 0.20/0.45  thf(l49_zfmisc_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.20/0.45  thf('19', plain,
% 0.20/0.45      (![X10 : $i, X11 : $i]:
% 0.20/0.45         ((r1_tarski @ X10 @ (k3_tarski @ X11)) | ~ (r2_hidden @ X10 @ X11))),
% 0.20/0.45      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.20/0.45  thf('20', plain, ((r1_tarski @ sk_B_1 @ (k3_tarski @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.45  thf(t99_zfmisc_1, axiom,
% 0.20/0.45    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.20/0.45  thf('21', plain, (![X12 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X12)) = (X12))),
% 0.20/0.45      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.20/0.45  thf('22', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 0.20/0.45      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.45  thf('23', plain, ($false), inference('demod', [status(thm)], ['13', '22'])).
% 0.20/0.45  
% 0.20/0.45  % SZS output end Refutation
% 0.20/0.45  
% 0.20/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

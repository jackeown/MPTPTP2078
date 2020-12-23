%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dIAXATjmom

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:12 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   48 (  80 expanded)
%              Number of leaves         :   17 (  30 expanded)
%              Depth                    :   12
%              Number of atoms          :  275 ( 567 expanded)
%              Number of equality atoms :   10 (  30 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
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
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X13: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('4',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['2','3'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r1_tarski @ X6 @ X4 )
      | ( X5
       != ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('6',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['4','6'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('9',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('12',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X12 ) @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('13',plain,(
    ! [X11: $i] :
      ( ( k2_subset_1 @ X11 )
      = X11 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('14',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ B )
               => ( r2_hidden @ D @ C ) )
           => ( r1_tarski @ B @ C ) ) ) ) )).

thf('16',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( r1_tarski @ X16 @ X14 )
      | ( m1_subset_1 @ ( sk_D @ X14 @ X16 ) @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t48_subset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D @ sk_B @ X0 ) @ X0 )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('20',plain,(
    m1_subset_1 @ ( sk_D @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X17: $i] :
      ( ( r2_hidden @ X17 @ sk_B )
      | ~ ( m1_subset_1 @ X17 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    r2_hidden @ ( sk_D @ sk_B @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( r1_tarski @ X16 @ X14 )
      | ~ ( r2_hidden @ ( sk_D @ X14 @ X16 ) @ X14 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t48_subset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_B @ X0 ) @ sk_B )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('28',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['11','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dIAXATjmom
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:53:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 60 iterations in 0.043s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.20/0.50  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.20/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(t49_subset_1, conjecture,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.50       ( ( ![C:$i]: ( ( m1_subset_1 @ C @ A ) => ( r2_hidden @ C @ B ) ) ) =>
% 0.20/0.50         ( ( A ) = ( B ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i]:
% 0.20/0.50        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.50          ( ( ![C:$i]: ( ( m1_subset_1 @ C @ A ) => ( r2_hidden @ C @ B ) ) ) =>
% 0.20/0.50            ( ( A ) = ( B ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t49_subset_1])).
% 0.20/0.50  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(d2_subset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( v1_xboole_0 @ A ) =>
% 0.20/0.50         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.20/0.50       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.50         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (![X8 : $i, X9 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X8 @ X9)
% 0.20/0.50          | (r2_hidden @ X8 @ X9)
% 0.20/0.50          | (v1_xboole_0 @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.50        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.50  thf(fc1_subset_1, axiom,
% 0.20/0.50    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.50  thf('3', plain, (![X13 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.50  thf('4', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.50      inference('clc', [status(thm)], ['2', '3'])).
% 0.20/0.50  thf(d1_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.20/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X6 @ X5)
% 0.20/0.50          | (r1_tarski @ X6 @ X4)
% 0.20/0.50          | ((X5) != (k1_zfmisc_1 @ X4)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (![X4 : $i, X6 : $i]:
% 0.20/0.50         ((r1_tarski @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k1_zfmisc_1 @ X4)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.50  thf('7', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.20/0.50      inference('sup-', [status(thm)], ['4', '6'])).
% 0.20/0.50  thf(d10_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X0 : $i, X2 : $i]:
% 0.20/0.50         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.50  thf('9', plain, ((~ (r1_tarski @ sk_A @ sk_B) | ((sk_A) = (sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.50  thf('10', plain, (((sk_A) != (sk_B))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('11', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.20/0.50  thf(dt_k2_subset_1, axiom,
% 0.20/0.50    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X12 : $i]: (m1_subset_1 @ (k2_subset_1 @ X12) @ (k1_zfmisc_1 @ X12))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.20/0.50  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.20/0.50  thf('13', plain, (![X11 : $i]: ((k2_subset_1 @ X11) = (X11))),
% 0.20/0.50      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.50  thf('14', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 0.20/0.50      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.50  thf('15', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t48_subset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.50       ( ![C:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.50           ( ( ![D:$i]: ( ( m1_subset_1 @ D @ B ) => ( r2_hidden @ D @ C ) ) ) =>
% 0.20/0.50             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.20/0.50          | (r1_tarski @ X16 @ X14)
% 0.20/0.50          | (m1_subset_1 @ (sk_D @ X14 @ X16) @ X16)
% 0.20/0.50          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t48_subset_1])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.50          | (m1_subset_1 @ (sk_D @ sk_B @ X0) @ X0)
% 0.20/0.50          | (r1_tarski @ X0 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (((r1_tarski @ sk_A @ sk_B) | (m1_subset_1 @ (sk_D @ sk_B @ sk_A) @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['14', '17'])).
% 0.20/0.50  thf('19', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.20/0.50  thf('20', plain, ((m1_subset_1 @ (sk_D @ sk_B @ sk_A) @ sk_A)),
% 0.20/0.50      inference('clc', [status(thm)], ['18', '19'])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (![X17 : $i]: ((r2_hidden @ X17 @ sk_B) | ~ (m1_subset_1 @ X17 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('22', plain, ((r2_hidden @ (sk_D @ sk_B @ sk_A) @ sk_B)),
% 0.20/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.50  thf('23', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.20/0.50          | (r1_tarski @ X16 @ X14)
% 0.20/0.50          | ~ (r2_hidden @ (sk_D @ X14 @ X16) @ X14)
% 0.20/0.50          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t48_subset_1])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.50          | ~ (r2_hidden @ (sk_D @ sk_B @ X0) @ sk_B)
% 0.20/0.50          | (r1_tarski @ X0 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      (((r1_tarski @ sk_A @ sk_B)
% 0.20/0.50        | ~ (m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['22', '25'])).
% 0.20/0.50  thf('27', plain, (![X12 : $i]: (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X12))),
% 0.20/0.50      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.50  thf('28', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.20/0.50      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.50  thf('29', plain, ($false), inference('demod', [status(thm)], ['11', '28'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

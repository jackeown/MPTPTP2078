%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.p8kXfcVj0q

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:12 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   51 (  85 expanded)
%              Number of leaves         :   19 (  33 expanded)
%              Depth                    :   13
%              Number of atoms          :  287 ( 584 expanded)
%              Number of equality atoms :   10 (  30 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

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
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ X7 )
      | ( r2_hidden @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X11: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('4',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['2','3'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ ( k3_tarski @ X4 ) )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('6',plain,(
    r1_tarski @ sk_B @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('7',plain,(
    ! [X5: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('8',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['6','7'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('13',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X10 ) @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('14',plain,(
    ! [X9: $i] :
      ( ( k2_subset_1 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('15',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                 => ( r2_hidden @ D @ C ) ) )
           => ( r1_tarski @ B @ C ) ) ) ) )).

thf('17',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( r1_tarski @ X14 @ X12 )
      | ( m1_subset_1 @ ( sk_D @ X12 @ X14 @ X13 ) @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D @ sk_B @ X0 @ sk_A ) @ sk_A )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_B @ sk_A @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('21',plain,(
    m1_subset_1 @ ( sk_D @ sk_B @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X15: $i] :
      ( ( r2_hidden @ X15 @ sk_B )
      | ~ ( m1_subset_1 @ X15 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    r2_hidden @ ( sk_D @ sk_B @ sk_A @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( r1_tarski @ X14 @ X12 )
      | ~ ( r2_hidden @ ( sk_D @ X12 @ X14 @ X13 ) @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_B @ X0 @ sk_A ) @ sk_B )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('29',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['12','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.p8kXfcVj0q
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:21:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 0.22/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.45  % Solved by: fo/fo7.sh
% 0.22/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.45  % done 38 iterations in 0.022s
% 0.22/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.45  % SZS output start Refutation
% 0.22/0.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.45  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.22/0.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.45  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.45  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.22/0.45  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.22/0.45  thf(t49_subset_1, conjecture,
% 0.22/0.45    (![A:$i,B:$i]:
% 0.22/0.45     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.45       ( ( ![C:$i]: ( ( m1_subset_1 @ C @ A ) => ( r2_hidden @ C @ B ) ) ) =>
% 0.22/0.45         ( ( A ) = ( B ) ) ) ))).
% 0.22/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.45    (~( ![A:$i,B:$i]:
% 0.22/0.45        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.45          ( ( ![C:$i]: ( ( m1_subset_1 @ C @ A ) => ( r2_hidden @ C @ B ) ) ) =>
% 0.22/0.45            ( ( A ) = ( B ) ) ) ) )),
% 0.22/0.45    inference('cnf.neg', [status(esa)], [t49_subset_1])).
% 0.22/0.45  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf(d2_subset_1, axiom,
% 0.22/0.45    (![A:$i,B:$i]:
% 0.22/0.45     ( ( ( v1_xboole_0 @ A ) =>
% 0.22/0.45         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.22/0.45       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.45         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.45  thf('1', plain,
% 0.22/0.45      (![X6 : $i, X7 : $i]:
% 0.22/0.45         (~ (m1_subset_1 @ X6 @ X7)
% 0.22/0.45          | (r2_hidden @ X6 @ X7)
% 0.22/0.45          | (v1_xboole_0 @ X7))),
% 0.22/0.45      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.22/0.45  thf('2', plain,
% 0.22/0.45      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.45        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.45      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.45  thf(fc1_subset_1, axiom,
% 0.22/0.45    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.45  thf('3', plain, (![X11 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.22/0.45      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.22/0.45  thf('4', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.45      inference('clc', [status(thm)], ['2', '3'])).
% 0.22/0.45  thf(l49_zfmisc_1, axiom,
% 0.22/0.45    (![A:$i,B:$i]:
% 0.22/0.45     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.22/0.45  thf('5', plain,
% 0.22/0.45      (![X3 : $i, X4 : $i]:
% 0.22/0.45         ((r1_tarski @ X3 @ (k3_tarski @ X4)) | ~ (r2_hidden @ X3 @ X4))),
% 0.22/0.45      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.22/0.45  thf('6', plain, ((r1_tarski @ sk_B @ (k3_tarski @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.45      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.45  thf(t99_zfmisc_1, axiom,
% 0.22/0.45    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.22/0.45  thf('7', plain, (![X5 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X5)) = (X5))),
% 0.22/0.45      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.22/0.45  thf('8', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.22/0.45      inference('demod', [status(thm)], ['6', '7'])).
% 0.22/0.45  thf(d10_xboole_0, axiom,
% 0.22/0.45    (![A:$i,B:$i]:
% 0.22/0.45     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.45  thf('9', plain,
% 0.22/0.45      (![X0 : $i, X2 : $i]:
% 0.22/0.45         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.45      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.45  thf('10', plain, ((~ (r1_tarski @ sk_A @ sk_B) | ((sk_A) = (sk_B)))),
% 0.22/0.45      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.45  thf('11', plain, (((sk_A) != (sk_B))),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf('12', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.22/0.45      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.22/0.45  thf(dt_k2_subset_1, axiom,
% 0.22/0.45    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.45  thf('13', plain,
% 0.22/0.45      (![X10 : $i]: (m1_subset_1 @ (k2_subset_1 @ X10) @ (k1_zfmisc_1 @ X10))),
% 0.22/0.45      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.22/0.45  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.22/0.45  thf('14', plain, (![X9 : $i]: ((k2_subset_1 @ X9) = (X9))),
% 0.22/0.45      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.22/0.45  thf('15', plain, (![X10 : $i]: (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X10))),
% 0.22/0.45      inference('demod', [status(thm)], ['13', '14'])).
% 0.22/0.45  thf('16', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf(t7_subset_1, axiom,
% 0.22/0.45    (![A:$i,B:$i]:
% 0.22/0.45     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.45       ( ![C:$i]:
% 0.22/0.45         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.45           ( ( ![D:$i]:
% 0.22/0.45               ( ( m1_subset_1 @ D @ A ) =>
% 0.22/0.45                 ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 0.22/0.45             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.22/0.45  thf('17', plain,
% 0.22/0.45      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.45         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.22/0.45          | (r1_tarski @ X14 @ X12)
% 0.22/0.45          | (m1_subset_1 @ (sk_D @ X12 @ X14 @ X13) @ X13)
% 0.22/0.45          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.22/0.45      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.22/0.45  thf('18', plain,
% 0.22/0.45      (![X0 : $i]:
% 0.22/0.45         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.45          | (m1_subset_1 @ (sk_D @ sk_B @ X0 @ sk_A) @ sk_A)
% 0.22/0.45          | (r1_tarski @ X0 @ sk_B))),
% 0.22/0.45      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.45  thf('19', plain,
% 0.22/0.45      (((r1_tarski @ sk_A @ sk_B)
% 0.22/0.45        | (m1_subset_1 @ (sk_D @ sk_B @ sk_A @ sk_A) @ sk_A))),
% 0.22/0.45      inference('sup-', [status(thm)], ['15', '18'])).
% 0.22/0.45  thf('20', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.22/0.45      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.22/0.45  thf('21', plain, ((m1_subset_1 @ (sk_D @ sk_B @ sk_A @ sk_A) @ sk_A)),
% 0.22/0.45      inference('clc', [status(thm)], ['19', '20'])).
% 0.22/0.45  thf('22', plain,
% 0.22/0.45      (![X15 : $i]: ((r2_hidden @ X15 @ sk_B) | ~ (m1_subset_1 @ X15 @ sk_A))),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf('23', plain, ((r2_hidden @ (sk_D @ sk_B @ sk_A @ sk_A) @ sk_B)),
% 0.22/0.45      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.45  thf('24', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf('25', plain,
% 0.22/0.45      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.45         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.22/0.45          | (r1_tarski @ X14 @ X12)
% 0.22/0.45          | ~ (r2_hidden @ (sk_D @ X12 @ X14 @ X13) @ X12)
% 0.22/0.45          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.22/0.45      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.22/0.45  thf('26', plain,
% 0.22/0.45      (![X0 : $i]:
% 0.22/0.45         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.45          | ~ (r2_hidden @ (sk_D @ sk_B @ X0 @ sk_A) @ sk_B)
% 0.22/0.45          | (r1_tarski @ X0 @ sk_B))),
% 0.22/0.45      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.45  thf('27', plain,
% 0.22/0.45      (((r1_tarski @ sk_A @ sk_B)
% 0.22/0.45        | ~ (m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.45      inference('sup-', [status(thm)], ['23', '26'])).
% 0.22/0.45  thf('28', plain, (![X10 : $i]: (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X10))),
% 0.22/0.45      inference('demod', [status(thm)], ['13', '14'])).
% 0.22/0.45  thf('29', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.22/0.45      inference('demod', [status(thm)], ['27', '28'])).
% 0.22/0.45  thf('30', plain, ($false), inference('demod', [status(thm)], ['12', '29'])).
% 0.22/0.45  
% 0.22/0.45  % SZS output end Refutation
% 0.22/0.45  
% 0.22/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uvZn9n6676

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:48 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   50 (  63 expanded)
%              Number of leaves         :   19 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :  275 ( 464 expanded)
%              Number of equality atoms :   12 (  21 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

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
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_2 ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k3_subset_1 @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k3_subset_1 @ sk_A @ sk_C_2 ) ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('8',plain,(
    r1_tarski @ sk_B_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_2 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_C_2 ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('14',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_2 @ X0 )
      | ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ~ ( r1_xboole_0 @ sk_C_2 @ ( k3_subset_1 @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['6','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('19',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_2 )
    = ( k4_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( r1_xboole_0 @ sk_C_2 @ ( k4_xboole_0 @ sk_A @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['16','19'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('21',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('22',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('23',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('24',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['20','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uvZn9n6676
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:33:48 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 45 iterations in 0.023s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.47  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.47  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.20/0.47  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.47  thf(t7_xboole_0, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.47          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.20/0.47      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.47  thf(t40_subset_1, conjecture,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.47       ( ( ( r1_tarski @ B @ C ) & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.20/0.47         ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.47        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.47          ( ( ( r1_tarski @ B @ C ) & 
% 0.20/0.47              ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.20/0.47            ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t40_subset_1])).
% 0.20/0.47  thf('1', plain, ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_C_2))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(d3_tarski, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.47          | (r2_hidden @ X0 @ X2)
% 0.20/0.47          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_C_2))
% 0.20/0.47          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      ((((sk_B_1) = (k1_xboole_0))
% 0.20/0.47        | (r2_hidden @ (sk_B @ sk_B_1) @ (k3_subset_1 @ sk_A @ sk_C_2)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.47  thf('5', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      ((r2_hidden @ (sk_B @ sk_B_1) @ (k3_subset_1 @ sk_A @ sk_C_2))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.20/0.47      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.47  thf('8', plain, ((r1_tarski @ sk_B_1 @ sk_C_2)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.47          | (r2_hidden @ X0 @ X2)
% 0.20/0.47          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_2) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      ((((sk_B_1) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ sk_B_1) @ sk_C_2))),
% 0.20/0.47      inference('sup-', [status(thm)], ['7', '10'])).
% 0.20/0.47  thf('12', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('13', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ sk_C_2)),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 0.20/0.47  thf(t3_xboole_0, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.20/0.47            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.47       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.47            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X6 @ X4)
% 0.20/0.47          | ~ (r2_hidden @ X6 @ X7)
% 0.20/0.47          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.20/0.47      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (r1_xboole_0 @ sk_C_2 @ X0) | ~ (r2_hidden @ (sk_B @ sk_B_1) @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.47  thf('16', plain, (~ (r1_xboole_0 @ sk_C_2 @ (k3_subset_1 @ sk_A @ sk_C_2))),
% 0.20/0.47      inference('sup-', [status(thm)], ['6', '15'])).
% 0.20/0.47  thf('17', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(d5_subset_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.47       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      (![X11 : $i, X12 : $i]:
% 0.20/0.47         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 0.20/0.47          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 0.20/0.47      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      (((k3_subset_1 @ sk_A @ sk_C_2) = (k4_xboole_0 @ sk_A @ sk_C_2))),
% 0.20/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.48  thf('20', plain, (~ (r1_xboole_0 @ sk_C_2 @ (k4_xboole_0 @ sk_A @ sk_C_2))),
% 0.20/0.48      inference('demod', [status(thm)], ['16', '19'])).
% 0.20/0.48  thf(t79_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X10)),
% 0.20/0.48      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i]:
% 0.20/0.48         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i]:
% 0.20/0.48         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X5))),
% 0.20/0.48      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X6 @ X4)
% 0.20/0.48          | ~ (r2_hidden @ X6 @ X7)
% 0.20/0.48          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.20/0.48      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         ((r1_xboole_0 @ X1 @ X0)
% 0.20/0.48          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.20/0.48          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X2))),
% 0.20/0.48      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((r1_xboole_0 @ X0 @ X1)
% 0.20/0.48          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.20/0.48          | (r1_xboole_0 @ X0 @ X1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['22', '25'])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.20/0.48      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['21', '27'])).
% 0.20/0.48  thf('29', plain, ($false), inference('demod', [status(thm)], ['20', '28'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

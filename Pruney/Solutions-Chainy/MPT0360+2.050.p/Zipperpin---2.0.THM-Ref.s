%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ARuvgbwasz

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:47 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   39 (  49 expanded)
%              Number of leaves         :   16 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :  210 ( 345 expanded)
%              Number of equality atoms :   14 (  23 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
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
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ),
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
      ( ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('9',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('10',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('11',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf('14',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('15',plain,(
    r1_tarski @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_C_1 ),
    inference('simplify_reflect-',[status(thm)],['18','19'])).

thf('21',plain,(
    $false ),
    inference(demod,[status(thm)],['13','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ARuvgbwasz
% 0.15/0.37  % Computer   : n012.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 20:04:22 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.24/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.49  % Solved by: fo/fo7.sh
% 0.24/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.49  % done 19 iterations in 0.016s
% 0.24/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.49  % SZS output start Refutation
% 0.24/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.24/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.24/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.24/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.49  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.24/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.49  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.24/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.49  thf(t7_xboole_0, axiom,
% 0.24/0.49    (![A:$i]:
% 0.24/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.24/0.49          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.24/0.49  thf('0', plain,
% 0.24/0.49      (![X10 : $i]:
% 0.24/0.49         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.24/0.49      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.24/0.49  thf(t40_subset_1, conjecture,
% 0.24/0.49    (![A:$i,B:$i,C:$i]:
% 0.24/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.24/0.49       ( ( ( r1_tarski @ B @ C ) & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.24/0.49         ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.24/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.24/0.49        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.24/0.49          ( ( ( r1_tarski @ B @ C ) & 
% 0.24/0.49              ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.24/0.49            ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.24/0.49    inference('cnf.neg', [status(esa)], [t40_subset_1])).
% 0.24/0.49  thf('1', plain, ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_C_1))),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf(d3_tarski, axiom,
% 0.24/0.49    (![A:$i,B:$i]:
% 0.24/0.49     ( ( r1_tarski @ A @ B ) <=>
% 0.24/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.24/0.49  thf('2', plain,
% 0.24/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.49         (~ (r2_hidden @ X0 @ X1)
% 0.24/0.49          | (r2_hidden @ X0 @ X2)
% 0.24/0.49          | ~ (r1_tarski @ X1 @ X2))),
% 0.24/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.24/0.49  thf('3', plain,
% 0.24/0.49      (![X0 : $i]:
% 0.24/0.49         ((r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1))
% 0.24/0.49          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.24/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.24/0.49  thf('4', plain,
% 0.24/0.49      ((((sk_B_1) = (k1_xboole_0))
% 0.24/0.49        | (r2_hidden @ (sk_B @ sk_B_1) @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.24/0.49      inference('sup-', [status(thm)], ['0', '3'])).
% 0.24/0.49  thf('5', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('6', plain,
% 0.24/0.49      ((r2_hidden @ (sk_B @ sk_B_1) @ (k3_subset_1 @ sk_A @ sk_C_1))),
% 0.24/0.49      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.24/0.49  thf('7', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf(d5_subset_1, axiom,
% 0.24/0.49    (![A:$i,B:$i]:
% 0.24/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.24/0.49       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.24/0.49  thf('8', plain,
% 0.24/0.49      (![X11 : $i, X12 : $i]:
% 0.24/0.49         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 0.24/0.49          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 0.24/0.49      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.24/0.49  thf('9', plain,
% 0.24/0.49      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.24/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.24/0.49  thf(d5_xboole_0, axiom,
% 0.24/0.49    (![A:$i,B:$i,C:$i]:
% 0.24/0.49     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.24/0.49       ( ![D:$i]:
% 0.24/0.49         ( ( r2_hidden @ D @ C ) <=>
% 0.24/0.49           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.24/0.49  thf('10', plain,
% 0.24/0.49      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.24/0.49         (~ (r2_hidden @ X8 @ X7)
% 0.24/0.49          | ~ (r2_hidden @ X8 @ X6)
% 0.24/0.49          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.24/0.49      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.24/0.49  thf('11', plain,
% 0.24/0.49      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.24/0.49         (~ (r2_hidden @ X8 @ X6)
% 0.24/0.49          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.24/0.49      inference('simplify', [status(thm)], ['10'])).
% 0.24/0.49  thf('12', plain,
% 0.24/0.49      (![X0 : $i]:
% 0.24/0.49         (~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1))
% 0.24/0.49          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.24/0.49      inference('sup-', [status(thm)], ['9', '11'])).
% 0.24/0.49  thf('13', plain, (~ (r2_hidden @ (sk_B @ sk_B_1) @ sk_C_1)),
% 0.24/0.49      inference('sup-', [status(thm)], ['6', '12'])).
% 0.24/0.49  thf('14', plain,
% 0.24/0.49      (![X10 : $i]:
% 0.24/0.49         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.24/0.49      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.24/0.49  thf('15', plain, ((r1_tarski @ sk_B_1 @ sk_C_1)),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('16', plain,
% 0.24/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.49         (~ (r2_hidden @ X0 @ X1)
% 0.24/0.49          | (r2_hidden @ X0 @ X2)
% 0.24/0.49          | ~ (r1_tarski @ X1 @ X2))),
% 0.24/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.24/0.49  thf('17', plain,
% 0.24/0.49      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_1) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.24/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.24/0.49  thf('18', plain,
% 0.24/0.49      ((((sk_B_1) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ sk_B_1) @ sk_C_1))),
% 0.24/0.49      inference('sup-', [status(thm)], ['14', '17'])).
% 0.24/0.49  thf('19', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('20', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ sk_C_1)),
% 0.24/0.49      inference('simplify_reflect-', [status(thm)], ['18', '19'])).
% 0.24/0.49  thf('21', plain, ($false), inference('demod', [status(thm)], ['13', '20'])).
% 0.24/0.49  
% 0.24/0.49  % SZS output end Refutation
% 0.24/0.49  
% 0.24/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

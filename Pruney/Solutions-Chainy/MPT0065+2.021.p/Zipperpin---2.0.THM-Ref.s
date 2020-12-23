%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qO8aMyroUx

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:27 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   23 (  32 expanded)
%              Number of leaves         :    8 (  13 expanded)
%              Depth                    :    7
%              Number of atoms          :  100 ( 181 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(t58_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_xboole_0 @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r2_xboole_0 @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r2_xboole_0 @ A @ B )
          & ( r1_tarski @ B @ C ) )
       => ( r2_xboole_0 @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t58_xboole_1])).

thf('0',plain,(
    ~ ( r2_xboole_0 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('3',plain,
    ( ( sk_B = sk_C )
    | ( r2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('6',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['4','5'])).

thf(l58_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r2_xboole_0 @ B @ C ) )
     => ( r2_xboole_0 @ A @ C ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r2_xboole_0 @ X4 @ X5 )
      | ( r2_xboole_0 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l58_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_xboole_0 @ sk_A @ X0 )
      | ~ ( r2_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( sk_B = sk_C )
    | ( r2_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    ~ ( r2_xboole_0 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    sk_B = sk_C ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    r2_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    $false ),
    inference(demod,[status(thm)],['0','11','12'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qO8aMyroUx
% 0.16/0.37  % Computer   : n017.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 10:35:46 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.24/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.49  % Solved by: fo/fo7.sh
% 0.24/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.49  % done 12 iterations in 0.008s
% 0.24/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.49  % SZS output start Refutation
% 0.24/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.24/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.49  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.24/0.49  thf(t58_xboole_1, conjecture,
% 0.24/0.49    (![A:$i,B:$i,C:$i]:
% 0.24/0.49     ( ( ( r2_xboole_0 @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.24/0.49       ( r2_xboole_0 @ A @ C ) ))).
% 0.24/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.24/0.49        ( ( ( r2_xboole_0 @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.24/0.49          ( r2_xboole_0 @ A @ C ) ) )),
% 0.24/0.49    inference('cnf.neg', [status(esa)], [t58_xboole_1])).
% 0.24/0.49  thf('0', plain, (~ (r2_xboole_0 @ sk_A @ sk_C)),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('1', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf(d8_xboole_0, axiom,
% 0.24/0.49    (![A:$i,B:$i]:
% 0.24/0.49     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.24/0.49       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.24/0.49  thf('2', plain,
% 0.24/0.49      (![X0 : $i, X2 : $i]:
% 0.24/0.49         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.24/0.49      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.24/0.49  thf('3', plain, ((((sk_B) = (sk_C)) | (r2_xboole_0 @ sk_B @ sk_C))),
% 0.24/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.24/0.49  thf('4', plain, ((r2_xboole_0 @ sk_A @ sk_B)),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('5', plain,
% 0.24/0.49      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.24/0.49      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.24/0.49  thf('6', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.24/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.24/0.49  thf(l58_xboole_1, axiom,
% 0.24/0.49    (![A:$i,B:$i,C:$i]:
% 0.24/0.49     ( ( ( r1_tarski @ A @ B ) & ( r2_xboole_0 @ B @ C ) ) =>
% 0.24/0.49       ( r2_xboole_0 @ A @ C ) ))).
% 0.24/0.49  thf('7', plain,
% 0.24/0.49      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.24/0.49         (~ (r1_tarski @ X3 @ X4)
% 0.24/0.49          | ~ (r2_xboole_0 @ X4 @ X5)
% 0.24/0.49          | (r2_xboole_0 @ X3 @ X5))),
% 0.24/0.49      inference('cnf', [status(esa)], [l58_xboole_1])).
% 0.24/0.49  thf('8', plain,
% 0.24/0.49      (![X0 : $i]: ((r2_xboole_0 @ sk_A @ X0) | ~ (r2_xboole_0 @ sk_B @ X0))),
% 0.24/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.24/0.49  thf('9', plain, ((((sk_B) = (sk_C)) | (r2_xboole_0 @ sk_A @ sk_C))),
% 0.24/0.49      inference('sup-', [status(thm)], ['3', '8'])).
% 0.24/0.49  thf('10', plain, (~ (r2_xboole_0 @ sk_A @ sk_C)),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('11', plain, (((sk_B) = (sk_C))),
% 0.24/0.49      inference('clc', [status(thm)], ['9', '10'])).
% 0.24/0.49  thf('12', plain, ((r2_xboole_0 @ sk_A @ sk_B)),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('13', plain, ($false),
% 0.24/0.49      inference('demod', [status(thm)], ['0', '11', '12'])).
% 0.24/0.49  
% 0.24/0.49  % SZS output end Refutation
% 0.24/0.49  
% 0.24/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

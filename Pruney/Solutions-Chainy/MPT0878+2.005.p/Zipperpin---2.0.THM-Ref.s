%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qejc2cNtVq

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   31 (  93 expanded)
%              Number of leaves         :    7 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :  244 (1081 expanded)
%              Number of equality atoms :   58 ( 234 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t38_mcart_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_zfmisc_1 @ A @ A @ A )
        = ( k3_zfmisc_1 @ B @ B @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_zfmisc_1 @ A @ A @ A )
          = ( k3_zfmisc_1 @ B @ B @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t38_mcart_1])).

thf('0',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
    = ( k3_zfmisc_1 @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) )
    <=> ( ( k3_zfmisc_1 @ A @ B @ C )
       != k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X0 @ X1 @ X3 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
    = ( k3_zfmisc_1 @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( k3_zfmisc_1 @ A @ B @ C )
        = ( k3_zfmisc_1 @ D @ E @ F ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( C = k1_xboole_0 )
        | ( ( A = D )
          & ( B = E )
          & ( C = F ) ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ( X6 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X6 @ X5 @ X4 )
       != ( k3_zfmisc_1 @ X7 @ X8 @ X9 ) )
      | ( X4 = X9 ) ) ),
    inference(cnf,[status(esa)],[t36_mcart_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( sk_B = X0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( sk_B = X0 )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
       != ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( sk_B = sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['6'])).

thf('8',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('10',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('11',plain,(
    ! [X1: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ sk_B @ X1 @ X3 )
      = sk_B ) ),
    inference(demod,[status(thm)],['2','9','10'])).

thf('12',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['0','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
       != k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('14',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('15',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('16',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('17',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
       != sk_B )
      | ( X2 = sk_B )
      | ( X1 = sk_B )
      | ( X0 = sk_B ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf('19',plain,
    ( ( sk_B != sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['20','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qejc2cNtVq
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 19:37:21 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 23 iterations in 0.015s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.49  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(t38_mcart_1, conjecture,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( k3_zfmisc_1 @ A @ A @ A ) = ( k3_zfmisc_1 @ B @ B @ B ) ) =>
% 0.22/0.49       ( ( A ) = ( B ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i,B:$i]:
% 0.22/0.49        ( ( ( k3_zfmisc_1 @ A @ A @ A ) = ( k3_zfmisc_1 @ B @ B @ B ) ) =>
% 0.22/0.49          ( ( A ) = ( B ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t38_mcart_1])).
% 0.22/0.49  thf('0', plain,
% 0.22/0.49      (((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k3_zfmisc_1 @ sk_B @ sk_B @ sk_B))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(t35_mcart_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.49         ( ( C ) != ( k1_xboole_0 ) ) ) <=>
% 0.22/0.49       ( ( k3_zfmisc_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) ))).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.22/0.49         (((X0) != (k1_xboole_0))
% 0.22/0.49          | ((k3_zfmisc_1 @ X0 @ X1 @ X3) = (k1_xboole_0)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      (![X1 : $i, X3 : $i]:
% 0.22/0.49         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X3) = (k1_xboole_0))),
% 0.22/0.49      inference('simplify', [status(thm)], ['1'])).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      (((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k3_zfmisc_1 @ sk_B @ sk_B @ sk_B))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(t36_mcart_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.22/0.49     ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.22/0.49       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.22/0.49         ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.22/0.49         ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ) ))).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.49         (((X4) = (k1_xboole_0))
% 0.22/0.49          | ((X5) = (k1_xboole_0))
% 0.22/0.49          | ((X6) = (k1_xboole_0))
% 0.22/0.49          | ((k3_zfmisc_1 @ X6 @ X5 @ X4) != (k3_zfmisc_1 @ X7 @ X8 @ X9))
% 0.22/0.49          | ((X4) = (X9)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t36_mcart_1])).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         (((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) != (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.22/0.49          | ((sk_B) = (X0))
% 0.22/0.49          | ((sk_B) = (k1_xboole_0))
% 0.22/0.49          | ((sk_B) = (k1_xboole_0))
% 0.22/0.49          | ((sk_B) = (k1_xboole_0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         (((sk_B) = (k1_xboole_0))
% 0.22/0.49          | ((sk_B) = (X0))
% 0.22/0.49          | ((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) != (k3_zfmisc_1 @ X2 @ X1 @ X0)))),
% 0.22/0.49      inference('simplify', [status(thm)], ['5'])).
% 0.22/0.49  thf('7', plain, ((((sk_B) = (sk_A)) | ((sk_B) = (k1_xboole_0)))),
% 0.22/0.49      inference('eq_res', [status(thm)], ['6'])).
% 0.22/0.49  thf('8', plain, (((sk_A) != (sk_B))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('9', plain, (((sk_B) = (k1_xboole_0))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.22/0.49  thf('10', plain, (((sk_B) = (k1_xboole_0))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      (![X1 : $i, X3 : $i]: ((k3_zfmisc_1 @ sk_B @ X1 @ X3) = (sk_B))),
% 0.22/0.49      inference('demod', [status(thm)], ['2', '9', '10'])).
% 0.22/0.49  thf('12', plain, (((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (sk_B))),
% 0.22/0.49      inference('demod', [status(thm)], ['0', '11'])).
% 0.22/0.49  thf('13', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         (((k3_zfmisc_1 @ X0 @ X1 @ X2) != (k1_xboole_0))
% 0.22/0.49          | ((X2) = (k1_xboole_0))
% 0.22/0.49          | ((X1) = (k1_xboole_0))
% 0.22/0.49          | ((X0) = (k1_xboole_0)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.22/0.49  thf('14', plain, (((sk_B) = (k1_xboole_0))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.22/0.49  thf('15', plain, (((sk_B) = (k1_xboole_0))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.22/0.49  thf('16', plain, (((sk_B) = (k1_xboole_0))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.22/0.49  thf('17', plain, (((sk_B) = (k1_xboole_0))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         (((k3_zfmisc_1 @ X0 @ X1 @ X2) != (sk_B))
% 0.22/0.49          | ((X2) = (sk_B))
% 0.22/0.49          | ((X1) = (sk_B))
% 0.22/0.49          | ((X0) = (sk_B)))),
% 0.22/0.49      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      ((((sk_B) != (sk_B))
% 0.22/0.49        | ((sk_A) = (sk_B))
% 0.22/0.49        | ((sk_A) = (sk_B))
% 0.22/0.49        | ((sk_A) = (sk_B)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['12', '18'])).
% 0.22/0.49  thf('20', plain, (((sk_A) = (sk_B))),
% 0.22/0.49      inference('simplify', [status(thm)], ['19'])).
% 0.22/0.49  thf('21', plain, (((sk_A) != (sk_B))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('22', plain, ($false),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['20', '21'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

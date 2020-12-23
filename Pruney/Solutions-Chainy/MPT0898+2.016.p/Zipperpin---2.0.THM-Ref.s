%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Y1l8zOzMaM

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   32 ( 105 expanded)
%              Number of leaves         :    7 (  29 expanded)
%              Depth                    :   11
%              Number of atoms          :  294 (1477 expanded)
%              Number of equality atoms :   67 ( 300 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t58_mcart_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_zfmisc_1 @ A @ A @ A @ A )
        = ( k4_zfmisc_1 @ B @ B @ B @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_zfmisc_1 @ A @ A @ A @ A )
          = ( k4_zfmisc_1 @ B @ B @ B @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t58_mcart_1])).

thf('0',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t55_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 ) )
    <=> ( ( k4_zfmisc_1 @ A @ B @ C @ D )
       != k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i,X4: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X4 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('2',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( k4_zfmisc_1 @ k1_xboole_0 @ X1 @ X2 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t56_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( ( k4_zfmisc_1 @ A @ B @ C @ D )
        = ( k4_zfmisc_1 @ E @ F @ G @ H ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( C = k1_xboole_0 )
        | ( D = k1_xboole_0 )
        | ( ( A = E )
          & ( B = F )
          & ( C = G )
          & ( D = H ) ) ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X8 @ X7 @ X6 @ X5 )
       != ( k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12 ) )
      | ( X8 = X9 ) ) ),
    inference(cnf,[status(esa)],[t56_mcart_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( sk_B = X3 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( sk_B = X3 )
      | ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
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
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( k4_zfmisc_1 @ sk_B @ X1 @ X2 @ X4 )
      = sk_B ) ),
    inference(demod,[status(thm)],['2','9','10'])).

thf('12',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['0','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X3 )
       != k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

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
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X3 )
       != sk_B )
      | ( X3 = sk_B )
      | ( X2 = sk_B )
      | ( X1 = sk_B )
      | ( X0 = sk_B ) ) ),
    inference(demod,[status(thm)],['13','14','15','16','17','18'])).

thf('20',plain,
    ( ( sk_B != sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Y1l8zOzMaM
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:10:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 26 iterations in 0.019s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(t58_mcart_1, conjecture,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( k4_zfmisc_1 @ A @ A @ A @ A ) = ( k4_zfmisc_1 @ B @ B @ B @ B ) ) =>
% 0.21/0.47       ( ( A ) = ( B ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i]:
% 0.21/0.47        ( ( ( k4_zfmisc_1 @ A @ A @ A @ A ) = ( k4_zfmisc_1 @ B @ B @ B @ B ) ) =>
% 0.21/0.47          ( ( A ) = ( B ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t58_mcart_1])).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.21/0.47         = (k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t55_mcart_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.47     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.47         ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) ) <=>
% 0.21/0.47       ( ( k4_zfmisc_1 @ A @ B @ C @ D ) != ( k1_xboole_0 ) ) ))).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i, X4 : $i]:
% 0.21/0.47         (((X0) != (k1_xboole_0))
% 0.21/0.47          | ((k4_zfmisc_1 @ X0 @ X1 @ X2 @ X4) = (k1_xboole_0)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.21/0.47         ((k4_zfmisc_1 @ k1_xboole_0 @ X1 @ X2 @ X4) = (k1_xboole_0))),
% 0.21/0.47      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.21/0.47         = (k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t56_mcart_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.21/0.47     ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 0.21/0.47       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.47         ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.21/0.47         ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 0.21/0.47           ( ( D ) = ( H ) ) ) ) ))).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, 
% 0.21/0.47         X12 : $i]:
% 0.21/0.47         (((X5) = (k1_xboole_0))
% 0.21/0.47          | ((X6) = (k1_xboole_0))
% 0.21/0.47          | ((X7) = (k1_xboole_0))
% 0.21/0.47          | ((X8) = (k1_xboole_0))
% 0.21/0.47          | ((k4_zfmisc_1 @ X8 @ X7 @ X6 @ X5)
% 0.21/0.47              != (k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12))
% 0.21/0.47          | ((X8) = (X9)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t56_mcart_1])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.47         (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.21/0.47            != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.47          | ((sk_B) = (X3))
% 0.21/0.47          | ((sk_B) = (k1_xboole_0))
% 0.21/0.47          | ((sk_B) = (k1_xboole_0))
% 0.21/0.47          | ((sk_B) = (k1_xboole_0))
% 0.21/0.47          | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.47         (((sk_B) = (k1_xboole_0))
% 0.21/0.47          | ((sk_B) = (X3))
% 0.21/0.47          | ((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.21/0.47              != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)))),
% 0.21/0.47      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.47  thf('7', plain, ((((sk_B) = (sk_A)) | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.47      inference('eq_res', [status(thm)], ['6'])).
% 0.21/0.47  thf('8', plain, (((sk_A) != (sk_B))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('9', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.21/0.47  thf('10', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.21/0.47         ((k4_zfmisc_1 @ sk_B @ X1 @ X2 @ X4) = (sk_B))),
% 0.21/0.47      inference('demod', [status(thm)], ['2', '9', '10'])).
% 0.21/0.47  thf('12', plain, (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) = (sk_B))),
% 0.21/0.47      inference('demod', [status(thm)], ['0', '11'])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.47         (((k4_zfmisc_1 @ X0 @ X1 @ X2 @ X3) != (k1_xboole_0))
% 0.21/0.47          | ((X3) = (k1_xboole_0))
% 0.21/0.47          | ((X2) = (k1_xboole_0))
% 0.21/0.47          | ((X1) = (k1_xboole_0))
% 0.21/0.47          | ((X0) = (k1_xboole_0)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.21/0.47  thf('14', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.21/0.47  thf('15', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.21/0.47  thf('16', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.21/0.47  thf('17', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.21/0.47  thf('18', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.47         (((k4_zfmisc_1 @ X0 @ X1 @ X2 @ X3) != (sk_B))
% 0.21/0.47          | ((X3) = (sk_B))
% 0.21/0.47          | ((X2) = (sk_B))
% 0.21/0.47          | ((X1) = (sk_B))
% 0.21/0.47          | ((X0) = (sk_B)))),
% 0.21/0.47      inference('demod', [status(thm)], ['13', '14', '15', '16', '17', '18'])).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      ((((sk_B) != (sk_B))
% 0.21/0.47        | ((sk_A) = (sk_B))
% 0.21/0.47        | ((sk_A) = (sk_B))
% 0.21/0.47        | ((sk_A) = (sk_B))
% 0.21/0.47        | ((sk_A) = (sk_B)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['12', '19'])).
% 0.21/0.47  thf('21', plain, (((sk_A) = (sk_B))),
% 0.21/0.47      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.47  thf('22', plain, (((sk_A) != (sk_B))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('23', plain, ($false),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

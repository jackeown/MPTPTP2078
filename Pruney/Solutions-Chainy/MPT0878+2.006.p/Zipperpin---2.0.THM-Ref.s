%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cOQ7vruY9S

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   27 (  44 expanded)
%              Number of leaves         :    7 (  14 expanded)
%              Depth                    :    9
%              Number of atoms          :  226 ( 442 expanded)
%              Number of equality atoms :   50 (  89 expanded)
%              Maximal formula depth    :   14 (   6 average)

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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
       != k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('2',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
     != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
    = ( k3_zfmisc_1 @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t37_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( k3_zfmisc_1 @ A @ B @ C )
        = ( k3_zfmisc_1 @ D @ E @ F ) )
     => ( ( ( k3_zfmisc_1 @ A @ B @ C )
          = k1_xboole_0 )
        | ( ( A = D )
          & ( B = E )
          & ( C = F ) ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( ( k3_zfmisc_1 @ X4 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X4 @ X5 @ X6 )
       != ( k3_zfmisc_1 @ X7 @ X8 @ X9 ) )
      | ( X6 = X9 ) ) ),
    inference(cnf,[status(esa)],[t37_mcart_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A ) )
      | ( X0 = sk_B )
      | ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = sk_B ) ),
    inference(eq_res,[status(thm)],['6'])).

thf('8',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','9'])).

thf('11',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ( k3_zfmisc_1 @ sk_A @ sk_A @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
       != k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('14',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    sk_A = sk_B ),
    inference('sup+',[status(thm)],['11','15'])).

thf('17',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cOQ7vruY9S
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:40:47 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 12 iterations in 0.008s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.46  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.46  thf(t38_mcart_1, conjecture,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( ( k3_zfmisc_1 @ A @ A @ A ) = ( k3_zfmisc_1 @ B @ B @ B ) ) =>
% 0.21/0.46       ( ( A ) = ( B ) ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i,B:$i]:
% 0.21/0.46        ( ( ( k3_zfmisc_1 @ A @ A @ A ) = ( k3_zfmisc_1 @ B @ B @ B ) ) =>
% 0.21/0.46          ( ( A ) = ( B ) ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t38_mcart_1])).
% 0.21/0.46  thf('0', plain,
% 0.21/0.46      (((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k3_zfmisc_1 @ sk_B @ sk_B @ sk_B))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t35_mcart_1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.46         ( ( C ) != ( k1_xboole_0 ) ) ) <=>
% 0.21/0.46       ( ( k3_zfmisc_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) ))).
% 0.21/0.46  thf('1', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.46         (((k3_zfmisc_1 @ X0 @ X1 @ X2) != (k1_xboole_0))
% 0.21/0.46          | ((X2) = (k1_xboole_0))
% 0.21/0.46          | ((X1) = (k1_xboole_0))
% 0.21/0.46          | ((X0) = (k1_xboole_0)))),
% 0.21/0.46      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      ((((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) != (k1_xboole_0))
% 0.21/0.46        | ((sk_B) = (k1_xboole_0))
% 0.21/0.46        | ((sk_B) = (k1_xboole_0))
% 0.21/0.46        | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.46  thf('3', plain,
% 0.21/0.46      ((((sk_B) = (k1_xboole_0))
% 0.21/0.46        | ((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) != (k1_xboole_0)))),
% 0.21/0.46      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.46  thf('4', plain,
% 0.21/0.46      (((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k3_zfmisc_1 @ sk_B @ sk_B @ sk_B))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t37_mcart_1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.21/0.46     ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.21/0.46       ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k1_xboole_0 ) ) | 
% 0.21/0.46         ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ) ))).
% 0.21/0.46  thf('5', plain,
% 0.21/0.46      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.46         (((k3_zfmisc_1 @ X4 @ X5 @ X6) = (k1_xboole_0))
% 0.21/0.46          | ((k3_zfmisc_1 @ X4 @ X5 @ X6) != (k3_zfmisc_1 @ X7 @ X8 @ X9))
% 0.21/0.46          | ((X6) = (X9)))),
% 0.21/0.46      inference('cnf', [status(esa)], [t37_mcart_1])).
% 0.21/0.46  thf('6', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.46         (((k3_zfmisc_1 @ X2 @ X1 @ X0) != (k3_zfmisc_1 @ sk_A @ sk_A @ sk_A))
% 0.21/0.46          | ((X0) = (sk_B))
% 0.21/0.46          | ((k3_zfmisc_1 @ X2 @ X1 @ X0) = (k1_xboole_0)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.46  thf('7', plain,
% 0.21/0.46      ((((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))
% 0.21/0.46        | ((sk_A) = (sk_B)))),
% 0.21/0.46      inference('eq_res', [status(thm)], ['6'])).
% 0.21/0.46  thf('8', plain, (((sk_A) != (sk_B))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('9', plain, (((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))),
% 0.21/0.46      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.21/0.46  thf('10', plain,
% 0.21/0.46      ((((sk_B) = (k1_xboole_0)) | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.21/0.46      inference('demod', [status(thm)], ['3', '9'])).
% 0.21/0.46  thf('11', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.46      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.46  thf('12', plain, (((k3_zfmisc_1 @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))),
% 0.21/0.46      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.21/0.46  thf('13', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.46         (((k3_zfmisc_1 @ X0 @ X1 @ X2) != (k1_xboole_0))
% 0.21/0.46          | ((X2) = (k1_xboole_0))
% 0.21/0.46          | ((X1) = (k1_xboole_0))
% 0.21/0.46          | ((X0) = (k1_xboole_0)))),
% 0.21/0.46      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.21/0.46  thf('14', plain,
% 0.21/0.46      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.46        | ((sk_A) = (k1_xboole_0))
% 0.21/0.46        | ((sk_A) = (k1_xboole_0))
% 0.21/0.46        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.46  thf('15', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.46      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.46  thf('16', plain, (((sk_A) = (sk_B))),
% 0.21/0.46      inference('sup+', [status(thm)], ['11', '15'])).
% 0.21/0.46  thf('17', plain, (((sk_A) != (sk_B))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('18', plain, ($false),
% 0.21/0.46      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

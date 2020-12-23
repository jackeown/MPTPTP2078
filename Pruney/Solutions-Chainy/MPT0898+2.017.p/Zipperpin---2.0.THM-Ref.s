%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4R7MkFLiTl

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:44 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   27 (  44 expanded)
%              Number of leaves         :    7 (  14 expanded)
%              Depth                    :    9
%              Number of atoms          :  269 ( 524 expanded)
%              Number of equality atoms :   56 (  97 expanded)
%              Maximal formula depth    :   17 (   7 average)

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
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X3 )
       != k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('2',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
     != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t57_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( ( k4_zfmisc_1 @ A @ B @ C @ D )
        = ( k4_zfmisc_1 @ E @ F @ G @ H ) )
     => ( ( ( k4_zfmisc_1 @ A @ B @ C @ D )
          = k1_xboole_0 )
        | ( ( A = E )
          & ( B = F )
          & ( C = G )
          & ( D = H ) ) ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( ( k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8 )
        = k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8 )
       != ( k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12 ) )
      | ( X8 = X12 ) ) ),
    inference(cnf,[status(esa)],[t57_mcart_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A ) )
      | ( X0 = sk_B )
      | ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = sk_B ) ),
    inference(eq_res,[status(thm)],['6'])).

thf('8',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
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
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X3 )
       != k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('14',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
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
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4R7MkFLiTl
% 0.11/0.33  % Computer   : n011.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 11:14:42 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running portfolio for 600 s
% 0.11/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.11/0.33  % Number of cores: 8
% 0.11/0.34  % Python version: Python 3.6.8
% 0.11/0.34  % Running in FO mode
% 0.19/0.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.45  % Solved by: fo/fo7.sh
% 0.19/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.45  % done 13 iterations in 0.009s
% 0.19/0.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.45  % SZS output start Refutation
% 0.19/0.45  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.19/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.45  thf(t58_mcart_1, conjecture,
% 0.19/0.45    (![A:$i,B:$i]:
% 0.19/0.45     ( ( ( k4_zfmisc_1 @ A @ A @ A @ A ) = ( k4_zfmisc_1 @ B @ B @ B @ B ) ) =>
% 0.19/0.45       ( ( A ) = ( B ) ) ))).
% 0.19/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.45    (~( ![A:$i,B:$i]:
% 0.19/0.45        ( ( ( k4_zfmisc_1 @ A @ A @ A @ A ) = ( k4_zfmisc_1 @ B @ B @ B @ B ) ) =>
% 0.19/0.45          ( ( A ) = ( B ) ) ) )),
% 0.19/0.45    inference('cnf.neg', [status(esa)], [t58_mcart_1])).
% 0.19/0.45  thf('0', plain,
% 0.19/0.45      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.19/0.45         = (k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf(t55_mcart_1, axiom,
% 0.19/0.45    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.45     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.45         ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) ) <=>
% 0.19/0.45       ( ( k4_zfmisc_1 @ A @ B @ C @ D ) != ( k1_xboole_0 ) ) ))).
% 0.19/0.45  thf('1', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.45         (((k4_zfmisc_1 @ X0 @ X1 @ X2 @ X3) != (k1_xboole_0))
% 0.19/0.45          | ((X3) = (k1_xboole_0))
% 0.19/0.45          | ((X2) = (k1_xboole_0))
% 0.19/0.45          | ((X1) = (k1_xboole_0))
% 0.19/0.45          | ((X0) = (k1_xboole_0)))),
% 0.19/0.45      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.19/0.45  thf('2', plain,
% 0.19/0.45      ((((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) != (k1_xboole_0))
% 0.19/0.45        | ((sk_B) = (k1_xboole_0))
% 0.19/0.45        | ((sk_B) = (k1_xboole_0))
% 0.19/0.45        | ((sk_B) = (k1_xboole_0))
% 0.19/0.45        | ((sk_B) = (k1_xboole_0)))),
% 0.19/0.45      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.45  thf('3', plain,
% 0.19/0.45      ((((sk_B) = (k1_xboole_0))
% 0.19/0.45        | ((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) != (k1_xboole_0)))),
% 0.19/0.45      inference('simplify', [status(thm)], ['2'])).
% 0.19/0.45  thf('4', plain,
% 0.19/0.45      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.19/0.45         = (k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf(t57_mcart_1, axiom,
% 0.19/0.45    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.19/0.45     ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 0.19/0.45       ( ( ( k4_zfmisc_1 @ A @ B @ C @ D ) = ( k1_xboole_0 ) ) | 
% 0.19/0.45         ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 0.19/0.45           ( ( D ) = ( H ) ) ) ) ))).
% 0.19/0.45  thf('5', plain,
% 0.19/0.45      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, 
% 0.19/0.45         X12 : $i]:
% 0.19/0.45         (((k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8) = (k1_xboole_0))
% 0.19/0.45          | ((k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8)
% 0.19/0.45              != (k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12))
% 0.19/0.45          | ((X8) = (X12)))),
% 0.19/0.45      inference('cnf', [status(esa)], [t57_mcart_1])).
% 0.19/0.45  thf('6', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.45         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.19/0.45            != (k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A))
% 0.19/0.45          | ((X0) = (sk_B))
% 0.19/0.45          | ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) = (k1_xboole_0)))),
% 0.19/0.45      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.45  thf('7', plain,
% 0.19/0.45      ((((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))
% 0.19/0.45        | ((sk_A) = (sk_B)))),
% 0.19/0.45      inference('eq_res', [status(thm)], ['6'])).
% 0.19/0.45  thf('8', plain, (((sk_A) != (sk_B))),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('9', plain,
% 0.19/0.45      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))),
% 0.19/0.45      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.19/0.45  thf('10', plain,
% 0.19/0.45      ((((sk_B) = (k1_xboole_0)) | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.19/0.45      inference('demod', [status(thm)], ['3', '9'])).
% 0.19/0.45  thf('11', plain, (((sk_B) = (k1_xboole_0))),
% 0.19/0.45      inference('simplify', [status(thm)], ['10'])).
% 0.19/0.45  thf('12', plain,
% 0.19/0.45      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))),
% 0.19/0.45      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.19/0.45  thf('13', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.45         (((k4_zfmisc_1 @ X0 @ X1 @ X2 @ X3) != (k1_xboole_0))
% 0.19/0.45          | ((X3) = (k1_xboole_0))
% 0.19/0.45          | ((X2) = (k1_xboole_0))
% 0.19/0.45          | ((X1) = (k1_xboole_0))
% 0.19/0.45          | ((X0) = (k1_xboole_0)))),
% 0.19/0.45      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.19/0.45  thf('14', plain,
% 0.19/0.45      ((((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.45        | ((sk_A) = (k1_xboole_0))
% 0.19/0.45        | ((sk_A) = (k1_xboole_0))
% 0.19/0.45        | ((sk_A) = (k1_xboole_0))
% 0.19/0.45        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.45      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.45  thf('15', plain, (((sk_A) = (k1_xboole_0))),
% 0.19/0.45      inference('simplify', [status(thm)], ['14'])).
% 0.19/0.45  thf('16', plain, (((sk_A) = (sk_B))),
% 0.19/0.45      inference('sup+', [status(thm)], ['11', '15'])).
% 0.19/0.45  thf('17', plain, (((sk_A) != (sk_B))),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('18', plain, ($false),
% 0.19/0.45      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 0.19/0.45  
% 0.19/0.45  % SZS output end Refutation
% 0.19/0.45  
% 0.19/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

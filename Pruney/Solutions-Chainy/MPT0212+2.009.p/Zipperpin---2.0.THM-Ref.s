%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UiuTwE4tBx

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:41 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   31 (  49 expanded)
%              Number of leaves         :   11 (  18 expanded)
%              Depth                    :    9
%              Number of atoms          :  206 ( 370 expanded)
%              Number of equality atoms :   30 (  57 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('0',plain,(
    ! [X9: $i,X12: $i] :
      ( ( X12
        = ( k1_zfmisc_1 @ X9 ) )
      | ( r1_tarski @ ( sk_C_1 @ X12 @ X9 ) @ X9 )
      | ( r2_hidden @ ( sk_C_1 @ X12 @ X9 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( sk_C_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X5 @ X4 )
      | ( X5 = X2 )
      | ( X4
       != ( k1_tarski @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('4',plain,(
    ! [X2: $i,X5: $i] :
      ( ( X5 = X2 )
      | ~ ( r2_hidden @ X5 @ ( k1_tarski @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(eq_fact,[status(thm)],['5'])).

thf('7',plain,
    ( ( ( sk_C_1 @ ( k1_tarski @ k1_xboole_0 ) @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( ( k1_tarski @ k1_xboole_0 )
      = ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t1_zfmisc_1,conjecture,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ( k1_zfmisc_1 @ k1_xboole_0 )
 != ( k1_tarski @ k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t1_zfmisc_1])).

thf('8',plain,(
    ( k1_zfmisc_1 @ k1_xboole_0 )
 != ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( sk_C_1 @ ( k1_tarski @ k1_xboole_0 ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X9: $i,X12: $i] :
      ( ( X12
        = ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ ( sk_C_1 @ X12 @ X9 ) @ X9 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X12 @ X9 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('11',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( r2_hidden @ ( sk_C_1 @ ( k1_tarski @ k1_xboole_0 ) @ k1_xboole_0 ) @ ( k1_tarski @ k1_xboole_0 ) )
    | ( ( k1_tarski @ k1_xboole_0 )
      = ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('13',plain,
    ( ( sk_C_1 @ ( k1_tarski @ k1_xboole_0 ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('14',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( X3 != X2 )
      | ( r2_hidden @ X3 @ X4 )
      | ( X4
       != ( k1_tarski @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('15',plain,(
    ! [X2: $i] :
      ( r2_hidden @ X2 @ ( k1_tarski @ X2 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( k1_tarski @ k1_xboole_0 )
    = ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','12','13','15'])).

thf('17',plain,(
    ( k1_zfmisc_1 @ k1_xboole_0 )
 != ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.17/0.17  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UiuTwE4tBx
% 0.18/0.37  % Computer   : n024.cluster.edu
% 0.18/0.37  % Model      : x86_64 x86_64
% 0.18/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.18/0.37  % Memory     : 8042.1875MB
% 0.18/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.18/0.37  % CPULimit   : 60
% 0.18/0.37  % DateTime   : Tue Dec  1 15:00:51 EST 2020
% 0.18/0.37  % CPUTime    : 
% 0.18/0.37  % Running portfolio for 600 s
% 0.18/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.18/0.37  % Number of cores: 8
% 0.18/0.37  % Python version: Python 3.6.8
% 0.18/0.38  % Running in FO mode
% 0.24/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.50  % Solved by: fo/fo7.sh
% 0.24/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.50  % done 26 iterations in 0.022s
% 0.24/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.50  % SZS output start Refutation
% 0.24/0.50  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.24/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.24/0.50  thf(d1_zfmisc_1, axiom,
% 0.24/0.50    (![A:$i,B:$i]:
% 0.24/0.50     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.24/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.24/0.50  thf('0', plain,
% 0.24/0.50      (![X9 : $i, X12 : $i]:
% 0.24/0.50         (((X12) = (k1_zfmisc_1 @ X9))
% 0.24/0.50          | (r1_tarski @ (sk_C_1 @ X12 @ X9) @ X9)
% 0.24/0.50          | (r2_hidden @ (sk_C_1 @ X12 @ X9) @ X12))),
% 0.24/0.50      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.24/0.50  thf(t3_xboole_1, axiom,
% 0.24/0.50    (![A:$i]:
% 0.24/0.50     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.24/0.50  thf('1', plain,
% 0.24/0.50      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (r1_tarski @ X1 @ k1_xboole_0))),
% 0.24/0.50      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.24/0.50  thf('2', plain,
% 0.24/0.50      (![X0 : $i]:
% 0.24/0.50         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.24/0.50          | ((X0) = (k1_zfmisc_1 @ k1_xboole_0))
% 0.24/0.50          | ((sk_C_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.24/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.24/0.50  thf(d1_tarski, axiom,
% 0.24/0.50    (![A:$i,B:$i]:
% 0.24/0.50     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.24/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.24/0.50  thf('3', plain,
% 0.24/0.50      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.24/0.50         (~ (r2_hidden @ X5 @ X4) | ((X5) = (X2)) | ((X4) != (k1_tarski @ X2)))),
% 0.24/0.50      inference('cnf', [status(esa)], [d1_tarski])).
% 0.24/0.50  thf('4', plain,
% 0.24/0.50      (![X2 : $i, X5 : $i]:
% 0.24/0.50         (((X5) = (X2)) | ~ (r2_hidden @ X5 @ (k1_tarski @ X2)))),
% 0.24/0.50      inference('simplify', [status(thm)], ['3'])).
% 0.24/0.50  thf('5', plain,
% 0.24/0.50      (![X0 : $i]:
% 0.24/0.50         (((sk_C_1 @ (k1_tarski @ X0) @ k1_xboole_0) = (k1_xboole_0))
% 0.24/0.50          | ((k1_tarski @ X0) = (k1_zfmisc_1 @ k1_xboole_0))
% 0.24/0.50          | ((sk_C_1 @ (k1_tarski @ X0) @ k1_xboole_0) = (X0)))),
% 0.24/0.50      inference('sup-', [status(thm)], ['2', '4'])).
% 0.24/0.50  thf('6', plain,
% 0.24/0.50      (![X0 : $i]:
% 0.24/0.50         (((X0) != (k1_xboole_0))
% 0.24/0.50          | ((k1_tarski @ X0) = (k1_zfmisc_1 @ k1_xboole_0))
% 0.24/0.50          | ((sk_C_1 @ (k1_tarski @ X0) @ k1_xboole_0) = (k1_xboole_0)))),
% 0.24/0.50      inference('eq_fact', [status(thm)], ['5'])).
% 0.24/0.50  thf('7', plain,
% 0.24/0.50      ((((sk_C_1 @ (k1_tarski @ k1_xboole_0) @ k1_xboole_0) = (k1_xboole_0))
% 0.24/0.50        | ((k1_tarski @ k1_xboole_0) = (k1_zfmisc_1 @ k1_xboole_0)))),
% 0.24/0.50      inference('simplify', [status(thm)], ['6'])).
% 0.24/0.50  thf(t1_zfmisc_1, conjecture,
% 0.24/0.50    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.24/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.50    (( k1_zfmisc_1 @ k1_xboole_0 ) != ( k1_tarski @ k1_xboole_0 )),
% 0.24/0.50    inference('cnf.neg', [status(esa)], [t1_zfmisc_1])).
% 0.24/0.50  thf('8', plain, (((k1_zfmisc_1 @ k1_xboole_0) != (k1_tarski @ k1_xboole_0))),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('9', plain,
% 0.24/0.50      (((sk_C_1 @ (k1_tarski @ k1_xboole_0) @ k1_xboole_0) = (k1_xboole_0))),
% 0.24/0.50      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.24/0.50  thf('10', plain,
% 0.24/0.50      (![X9 : $i, X12 : $i]:
% 0.24/0.50         (((X12) = (k1_zfmisc_1 @ X9))
% 0.24/0.50          | ~ (r1_tarski @ (sk_C_1 @ X12 @ X9) @ X9)
% 0.24/0.50          | ~ (r2_hidden @ (sk_C_1 @ X12 @ X9) @ X12))),
% 0.24/0.50      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.24/0.50  thf('11', plain,
% 0.24/0.50      ((~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0)
% 0.24/0.50        | ~ (r2_hidden @ (sk_C_1 @ (k1_tarski @ k1_xboole_0) @ k1_xboole_0) @ 
% 0.24/0.50             (k1_tarski @ k1_xboole_0))
% 0.24/0.50        | ((k1_tarski @ k1_xboole_0) = (k1_zfmisc_1 @ k1_xboole_0)))),
% 0.24/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.24/0.50  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.24/0.50  thf('12', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.24/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.24/0.50  thf('13', plain,
% 0.24/0.50      (((sk_C_1 @ (k1_tarski @ k1_xboole_0) @ k1_xboole_0) = (k1_xboole_0))),
% 0.24/0.50      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.24/0.50  thf('14', plain,
% 0.24/0.50      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.24/0.50         (((X3) != (X2)) | (r2_hidden @ X3 @ X4) | ((X4) != (k1_tarski @ X2)))),
% 0.24/0.50      inference('cnf', [status(esa)], [d1_tarski])).
% 0.24/0.50  thf('15', plain, (![X2 : $i]: (r2_hidden @ X2 @ (k1_tarski @ X2))),
% 0.24/0.50      inference('simplify', [status(thm)], ['14'])).
% 0.24/0.50  thf('16', plain, (((k1_tarski @ k1_xboole_0) = (k1_zfmisc_1 @ k1_xboole_0))),
% 0.24/0.50      inference('demod', [status(thm)], ['11', '12', '13', '15'])).
% 0.24/0.50  thf('17', plain,
% 0.24/0.50      (((k1_zfmisc_1 @ k1_xboole_0) != (k1_tarski @ k1_xboole_0))),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf('18', plain, ($false),
% 0.24/0.50      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 0.24/0.50  
% 0.24/0.50  % SZS output end Refutation
% 0.24/0.50  
% 0.24/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

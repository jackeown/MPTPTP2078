%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cRbLpEC0zI

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:40 EST 2020

% Result     : Theorem 0.78s
% Output     : Refutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :   35 (  54 expanded)
%              Number of leaves         :   12 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :  234 ( 407 expanded)
%              Number of equality atoms :   30 (  57 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('0',plain,(
    ! [X17: $i,X20: $i] :
      ( ( X20
        = ( k1_zfmisc_1 @ X17 ) )
      | ( r1_tarski @ ( sk_C_2 @ X20 @ X17 ) @ X17 )
      | ( r2_hidden @ ( sk_C_2 @ X20 @ X17 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( sk_C_2 @ X0 @ k1_xboole_0 )
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
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( X8 = X5 )
      | ( X7
       != ( k1_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('4',plain,(
    ! [X5: $i,X8: $i] :
      ( ( X8 = X5 )
      | ~ ( r2_hidden @ X8 @ ( k1_tarski @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(eq_fact,[status(thm)],['5'])).

thf('7',plain,
    ( ( ( sk_C_2 @ ( k1_tarski @ k1_xboole_0 ) @ k1_xboole_0 )
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
    ( ( sk_C_2 @ ( k1_tarski @ k1_xboole_0 ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X17: $i,X20: $i] :
      ( ( X20
        = ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ ( sk_C_2 @ X20 @ X17 ) @ X17 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X20 @ X17 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('11',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( r2_hidden @ ( sk_C_2 @ ( k1_tarski @ k1_xboole_0 ) @ k1_xboole_0 ) @ ( k1_tarski @ k1_xboole_0 ) )
    | ( ( k1_tarski @ k1_xboole_0 )
      = ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( sk_C_2 @ ( k1_tarski @ k1_xboole_0 ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('17',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( X6 != X5 )
      | ( r2_hidden @ X6 @ X7 )
      | ( X7
       != ( k1_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('18',plain,(
    ! [X5: $i] :
      ( r2_hidden @ X5 @ ( k1_tarski @ X5 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( k1_tarski @ k1_xboole_0 )
    = ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','15','16','18'])).

thf('20',plain,(
    ( k1_zfmisc_1 @ k1_xboole_0 )
 != ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cRbLpEC0zI
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:31:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.78/0.97  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.78/0.97  % Solved by: fo/fo7.sh
% 0.78/0.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.78/0.97  % done 810 iterations in 0.522s
% 0.78/0.97  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.78/0.97  % SZS output start Refutation
% 0.78/0.97  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.78/0.97  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.78/0.97  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.78/0.97  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.78/0.97  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.78/0.97  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.78/0.97  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.78/0.97  thf(d1_zfmisc_1, axiom,
% 0.78/0.97    (![A:$i,B:$i]:
% 0.78/0.97     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.78/0.97       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.78/0.97  thf('0', plain,
% 0.78/0.97      (![X17 : $i, X20 : $i]:
% 0.78/0.97         (((X20) = (k1_zfmisc_1 @ X17))
% 0.78/0.97          | (r1_tarski @ (sk_C_2 @ X20 @ X17) @ X17)
% 0.78/0.97          | (r2_hidden @ (sk_C_2 @ X20 @ X17) @ X20))),
% 0.78/0.97      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.78/0.97  thf(t3_xboole_1, axiom,
% 0.78/0.97    (![A:$i]:
% 0.78/0.97     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.78/0.97  thf('1', plain,
% 0.78/0.97      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 0.78/0.97      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.78/0.97  thf('2', plain,
% 0.78/0.97      (![X0 : $i]:
% 0.78/0.97         ((r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0)
% 0.78/0.97          | ((X0) = (k1_zfmisc_1 @ k1_xboole_0))
% 0.78/0.97          | ((sk_C_2 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.78/0.97      inference('sup-', [status(thm)], ['0', '1'])).
% 0.78/0.97  thf(d1_tarski, axiom,
% 0.78/0.97    (![A:$i,B:$i]:
% 0.78/0.97     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.78/0.97       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.78/0.97  thf('3', plain,
% 0.78/0.97      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.78/0.97         (~ (r2_hidden @ X8 @ X7) | ((X8) = (X5)) | ((X7) != (k1_tarski @ X5)))),
% 0.78/0.97      inference('cnf', [status(esa)], [d1_tarski])).
% 0.78/0.97  thf('4', plain,
% 0.78/0.97      (![X5 : $i, X8 : $i]:
% 0.78/0.97         (((X8) = (X5)) | ~ (r2_hidden @ X8 @ (k1_tarski @ X5)))),
% 0.78/0.97      inference('simplify', [status(thm)], ['3'])).
% 0.78/0.97  thf('5', plain,
% 0.78/0.97      (![X0 : $i]:
% 0.78/0.97         (((sk_C_2 @ (k1_tarski @ X0) @ k1_xboole_0) = (k1_xboole_0))
% 0.78/0.97          | ((k1_tarski @ X0) = (k1_zfmisc_1 @ k1_xboole_0))
% 0.78/0.97          | ((sk_C_2 @ (k1_tarski @ X0) @ k1_xboole_0) = (X0)))),
% 0.78/0.97      inference('sup-', [status(thm)], ['2', '4'])).
% 0.78/0.97  thf('6', plain,
% 0.78/0.97      (![X0 : $i]:
% 0.78/0.97         (((X0) != (k1_xboole_0))
% 0.78/0.97          | ((k1_tarski @ X0) = (k1_zfmisc_1 @ k1_xboole_0))
% 0.78/0.97          | ((sk_C_2 @ (k1_tarski @ X0) @ k1_xboole_0) = (k1_xboole_0)))),
% 0.78/0.97      inference('eq_fact', [status(thm)], ['5'])).
% 0.78/0.97  thf('7', plain,
% 0.78/0.97      ((((sk_C_2 @ (k1_tarski @ k1_xboole_0) @ k1_xboole_0) = (k1_xboole_0))
% 0.78/0.97        | ((k1_tarski @ k1_xboole_0) = (k1_zfmisc_1 @ k1_xboole_0)))),
% 0.78/0.97      inference('simplify', [status(thm)], ['6'])).
% 0.78/0.97  thf(t1_zfmisc_1, conjecture,
% 0.78/0.97    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.78/0.97  thf(zf_stmt_0, negated_conjecture,
% 0.78/0.97    (( k1_zfmisc_1 @ k1_xboole_0 ) != ( k1_tarski @ k1_xboole_0 )),
% 0.78/0.97    inference('cnf.neg', [status(esa)], [t1_zfmisc_1])).
% 0.78/0.97  thf('8', plain, (((k1_zfmisc_1 @ k1_xboole_0) != (k1_tarski @ k1_xboole_0))),
% 0.78/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.97  thf('9', plain,
% 0.78/0.97      (((sk_C_2 @ (k1_tarski @ k1_xboole_0) @ k1_xboole_0) = (k1_xboole_0))),
% 0.78/0.97      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.78/0.97  thf('10', plain,
% 0.78/0.97      (![X17 : $i, X20 : $i]:
% 0.78/0.97         (((X20) = (k1_zfmisc_1 @ X17))
% 0.78/0.97          | ~ (r1_tarski @ (sk_C_2 @ X20 @ X17) @ X17)
% 0.78/0.97          | ~ (r2_hidden @ (sk_C_2 @ X20 @ X17) @ X20))),
% 0.78/0.97      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.78/0.97  thf('11', plain,
% 0.78/0.97      ((~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0)
% 0.78/0.97        | ~ (r2_hidden @ (sk_C_2 @ (k1_tarski @ k1_xboole_0) @ k1_xboole_0) @ 
% 0.78/0.97             (k1_tarski @ k1_xboole_0))
% 0.78/0.97        | ((k1_tarski @ k1_xboole_0) = (k1_zfmisc_1 @ k1_xboole_0)))),
% 0.78/0.97      inference('sup-', [status(thm)], ['9', '10'])).
% 0.78/0.97  thf(d3_tarski, axiom,
% 0.78/0.97    (![A:$i,B:$i]:
% 0.78/0.97     ( ( r1_tarski @ A @ B ) <=>
% 0.78/0.97       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.78/0.97  thf('12', plain,
% 0.78/0.97      (![X1 : $i, X3 : $i]:
% 0.78/0.97         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.78/0.97      inference('cnf', [status(esa)], [d3_tarski])).
% 0.78/0.97  thf('13', plain,
% 0.78/0.97      (![X1 : $i, X3 : $i]:
% 0.78/0.97         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.78/0.97      inference('cnf', [status(esa)], [d3_tarski])).
% 0.78/0.97  thf('14', plain,
% 0.78/0.97      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.78/0.97      inference('sup-', [status(thm)], ['12', '13'])).
% 0.78/0.97  thf('15', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.78/0.97      inference('simplify', [status(thm)], ['14'])).
% 0.78/0.97  thf('16', plain,
% 0.78/0.97      (((sk_C_2 @ (k1_tarski @ k1_xboole_0) @ k1_xboole_0) = (k1_xboole_0))),
% 0.78/0.97      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.78/0.97  thf('17', plain,
% 0.78/0.97      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.78/0.97         (((X6) != (X5)) | (r2_hidden @ X6 @ X7) | ((X7) != (k1_tarski @ X5)))),
% 0.78/0.97      inference('cnf', [status(esa)], [d1_tarski])).
% 0.78/0.97  thf('18', plain, (![X5 : $i]: (r2_hidden @ X5 @ (k1_tarski @ X5))),
% 0.78/0.97      inference('simplify', [status(thm)], ['17'])).
% 0.78/0.97  thf('19', plain, (((k1_tarski @ k1_xboole_0) = (k1_zfmisc_1 @ k1_xboole_0))),
% 0.78/0.97      inference('demod', [status(thm)], ['11', '15', '16', '18'])).
% 0.78/0.97  thf('20', plain,
% 0.78/0.97      (((k1_zfmisc_1 @ k1_xboole_0) != (k1_tarski @ k1_xboole_0))),
% 0.78/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.97  thf('21', plain, ($false),
% 0.78/0.97      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.78/0.97  
% 0.78/0.97  % SZS output end Refutation
% 0.78/0.97  
% 0.78/0.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

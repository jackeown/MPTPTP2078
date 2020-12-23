%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pkJU0m6qpH

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:41 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   33 (  51 expanded)
%              Number of leaves         :   11 (  18 expanded)
%              Depth                    :   11
%              Number of atoms          :  224 ( 391 expanded)
%              Number of equality atoms :   32 (  58 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X2: $i,X6: $i] :
      ( ( X6
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C @ X6 @ X2 )
        = X2 )
      | ( r2_hidden @ ( sk_C @ X6 @ X2 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( r1_tarski @ X11 @ X9 )
      | ( X10
       != ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('2',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ ( k1_zfmisc_1 @ X0 ) @ X1 )
        = X1 )
      | ( ( k1_zfmisc_1 @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( r1_tarski @ ( sk_C @ ( k1_zfmisc_1 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('4',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k1_zfmisc_1 @ k1_xboole_0 )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ X0 )
        = X0 )
      | ( ( sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != X0 )
      | ( ( sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ X0 )
        = X0 )
      | ( ( k1_zfmisc_1 @ k1_xboole_0 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['5'])).

thf('7',plain,
    ( ( ( k1_zfmisc_1 @ k1_xboole_0 )
      = ( k1_tarski @ k1_xboole_0 ) )
    | ( ( sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ k1_xboole_0 )
      = k1_xboole_0 ) ),
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
    ( ( sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X2: $i,X6: $i] :
      ( ( X6
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C @ X6 @ X2 )
       != X2 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X2 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('11',plain,
    ( ~ ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ( ( sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k1_zfmisc_1 @ k1_xboole_0 )
      = ( k1_tarski @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('13',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ( X10
       != ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('14',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,
    ( ( sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('17',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_zfmisc_1 @ k1_xboole_0 )
      = ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['11','15','16'])).

thf('18',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ( k1_zfmisc_1 @ k1_xboole_0 )
 != ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['18','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pkJU0m6qpH
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:52:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.44  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.44  % Solved by: fo/fo7.sh
% 0.19/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.44  % done 19 iterations in 0.017s
% 0.19/0.44  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.44  % SZS output start Refutation
% 0.19/0.44  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.44  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.44  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.44  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.44  thf(d1_tarski, axiom,
% 0.19/0.44    (![A:$i,B:$i]:
% 0.19/0.44     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.19/0.44       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.19/0.44  thf('0', plain,
% 0.19/0.44      (![X2 : $i, X6 : $i]:
% 0.19/0.44         (((X6) = (k1_tarski @ X2))
% 0.19/0.44          | ((sk_C @ X6 @ X2) = (X2))
% 0.19/0.44          | (r2_hidden @ (sk_C @ X6 @ X2) @ X6))),
% 0.19/0.44      inference('cnf', [status(esa)], [d1_tarski])).
% 0.19/0.44  thf(d1_zfmisc_1, axiom,
% 0.19/0.44    (![A:$i,B:$i]:
% 0.19/0.44     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.19/0.44       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.19/0.44  thf('1', plain,
% 0.19/0.44      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.19/0.44         (~ (r2_hidden @ X11 @ X10)
% 0.19/0.44          | (r1_tarski @ X11 @ X9)
% 0.19/0.44          | ((X10) != (k1_zfmisc_1 @ X9)))),
% 0.19/0.44      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.19/0.44  thf('2', plain,
% 0.19/0.44      (![X9 : $i, X11 : $i]:
% 0.19/0.44         ((r1_tarski @ X11 @ X9) | ~ (r2_hidden @ X11 @ (k1_zfmisc_1 @ X9)))),
% 0.19/0.44      inference('simplify', [status(thm)], ['1'])).
% 0.19/0.44  thf('3', plain,
% 0.19/0.44      (![X0 : $i, X1 : $i]:
% 0.19/0.44         (((sk_C @ (k1_zfmisc_1 @ X0) @ X1) = (X1))
% 0.19/0.44          | ((k1_zfmisc_1 @ X0) = (k1_tarski @ X1))
% 0.19/0.44          | (r1_tarski @ (sk_C @ (k1_zfmisc_1 @ X0) @ X1) @ X0))),
% 0.19/0.44      inference('sup-', [status(thm)], ['0', '2'])).
% 0.19/0.44  thf(t3_xboole_1, axiom,
% 0.19/0.44    (![A:$i]:
% 0.19/0.44     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.44  thf('4', plain,
% 0.19/0.44      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (r1_tarski @ X1 @ k1_xboole_0))),
% 0.19/0.44      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.19/0.44  thf('5', plain,
% 0.19/0.44      (![X0 : $i]:
% 0.19/0.44         (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ X0))
% 0.19/0.44          | ((sk_C @ (k1_zfmisc_1 @ k1_xboole_0) @ X0) = (X0))
% 0.19/0.44          | ((sk_C @ (k1_zfmisc_1 @ k1_xboole_0) @ X0) = (k1_xboole_0)))),
% 0.19/0.44      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.44  thf('6', plain,
% 0.19/0.44      (![X0 : $i]:
% 0.19/0.44         (((k1_xboole_0) != (X0))
% 0.19/0.44          | ((sk_C @ (k1_zfmisc_1 @ k1_xboole_0) @ X0) = (X0))
% 0.19/0.44          | ((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ X0)))),
% 0.19/0.44      inference('eq_fact', [status(thm)], ['5'])).
% 0.19/0.44  thf('7', plain,
% 0.19/0.44      ((((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))
% 0.19/0.44        | ((sk_C @ (k1_zfmisc_1 @ k1_xboole_0) @ k1_xboole_0) = (k1_xboole_0)))),
% 0.19/0.44      inference('simplify', [status(thm)], ['6'])).
% 0.19/0.44  thf(t1_zfmisc_1, conjecture,
% 0.19/0.44    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.19/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.44    (( k1_zfmisc_1 @ k1_xboole_0 ) != ( k1_tarski @ k1_xboole_0 )),
% 0.19/0.44    inference('cnf.neg', [status(esa)], [t1_zfmisc_1])).
% 0.19/0.44  thf('8', plain, (((k1_zfmisc_1 @ k1_xboole_0) != (k1_tarski @ k1_xboole_0))),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf('9', plain,
% 0.19/0.44      (((sk_C @ (k1_zfmisc_1 @ k1_xboole_0) @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.44      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.19/0.44  thf('10', plain,
% 0.19/0.44      (![X2 : $i, X6 : $i]:
% 0.19/0.44         (((X6) = (k1_tarski @ X2))
% 0.19/0.44          | ((sk_C @ X6 @ X2) != (X2))
% 0.19/0.44          | ~ (r2_hidden @ (sk_C @ X6 @ X2) @ X6))),
% 0.19/0.44      inference('cnf', [status(esa)], [d1_tarski])).
% 0.19/0.44  thf('11', plain,
% 0.19/0.44      ((~ (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.19/0.44        | ((sk_C @ (k1_zfmisc_1 @ k1_xboole_0) @ k1_xboole_0) != (k1_xboole_0))
% 0.19/0.44        | ((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0)))),
% 0.19/0.44      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.44  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.19/0.44  thf('12', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.19/0.44      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.44  thf('13', plain,
% 0.19/0.44      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.19/0.44         (~ (r1_tarski @ X8 @ X9)
% 0.19/0.44          | (r2_hidden @ X8 @ X10)
% 0.19/0.44          | ((X10) != (k1_zfmisc_1 @ X9)))),
% 0.19/0.44      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.19/0.44  thf('14', plain,
% 0.19/0.44      (![X8 : $i, X9 : $i]:
% 0.19/0.44         ((r2_hidden @ X8 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X8 @ X9))),
% 0.19/0.44      inference('simplify', [status(thm)], ['13'])).
% 0.19/0.44  thf('15', plain,
% 0.19/0.44      (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.19/0.44      inference('sup-', [status(thm)], ['12', '14'])).
% 0.19/0.44  thf('16', plain,
% 0.19/0.44      (((sk_C @ (k1_zfmisc_1 @ k1_xboole_0) @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.44      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.19/0.44  thf('17', plain,
% 0.19/0.44      ((((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.44        | ((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0)))),
% 0.19/0.44      inference('demod', [status(thm)], ['11', '15', '16'])).
% 0.19/0.44  thf('18', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.19/0.44      inference('simplify', [status(thm)], ['17'])).
% 0.19/0.44  thf('19', plain,
% 0.19/0.44      (((k1_zfmisc_1 @ k1_xboole_0) != (k1_tarski @ k1_xboole_0))),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf('20', plain, ($false),
% 0.19/0.44      inference('simplify_reflect-', [status(thm)], ['18', '19'])).
% 0.19/0.44  
% 0.19/0.44  % SZS output end Refutation
% 0.19/0.44  
% 0.19/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

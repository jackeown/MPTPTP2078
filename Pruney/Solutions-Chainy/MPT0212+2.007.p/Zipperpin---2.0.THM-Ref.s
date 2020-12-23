%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vF0vpccSFh

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:41 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   36 (  56 expanded)
%              Number of leaves         :   12 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :  229 ( 404 expanded)
%              Number of equality atoms :   32 (  60 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('0',plain,(
    ! [X21: $i,X24: $i] :
      ( ( X24
        = ( k1_zfmisc_1 @ X21 ) )
      | ( r1_tarski @ ( sk_C_1 @ X24 @ X21 ) @ X21 )
      | ( r2_hidden @ ( sk_C_1 @ X24 @ X21 ) @ X24 ) ) ),
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
    ! [X21: $i,X24: $i] :
      ( ( X24
        = ( k1_zfmisc_1 @ X21 ) )
      | ~ ( r1_tarski @ ( sk_C_1 @ X24 @ X21 ) @ X21 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X24 @ X21 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('11',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( r2_hidden @ ( sk_C_1 @ ( k1_tarski @ k1_xboole_0 ) @ k1_xboole_0 ) @ ( k1_tarski @ k1_xboole_0 ) )
    | ( ( k1_tarski @ k1_xboole_0 )
      = ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('13',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('16',plain,(
    r1_tarski @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_C_1 @ ( k1_tarski @ k1_xboole_0 ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('18',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( X6 != X5 )
      | ( r2_hidden @ X6 @ X7 )
      | ( X7
       != ( k1_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('19',plain,(
    ! [X5: $i] :
      ( r2_hidden @ X5 @ ( k1_tarski @ X5 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( k1_tarski @ k1_xboole_0 )
    = ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','16','17','19'])).

thf('21',plain,(
    ( k1_zfmisc_1 @ k1_xboole_0 )
 != ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['20','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vF0vpccSFh
% 0.13/0.37  % Computer   : n010.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 17:54:30 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.24/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.50  % Solved by: fo/fo7.sh
% 0.24/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.50  % done 38 iterations in 0.032s
% 0.24/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.50  % SZS output start Refutation
% 0.24/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.24/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.24/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.50  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.24/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.50  thf(d1_zfmisc_1, axiom,
% 0.24/0.50    (![A:$i,B:$i]:
% 0.24/0.50     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.24/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.24/0.50  thf('0', plain,
% 0.24/0.50      (![X21 : $i, X24 : $i]:
% 0.24/0.50         (((X24) = (k1_zfmisc_1 @ X21))
% 0.24/0.50          | (r1_tarski @ (sk_C_1 @ X24 @ X21) @ X21)
% 0.24/0.50          | (r2_hidden @ (sk_C_1 @ X24 @ X21) @ X24))),
% 0.24/0.50      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.24/0.50  thf(t3_xboole_1, axiom,
% 0.24/0.50    (![A:$i]:
% 0.24/0.50     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.24/0.50  thf('1', plain,
% 0.24/0.50      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
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
% 0.24/0.50      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.24/0.50         (~ (r2_hidden @ X8 @ X7) | ((X8) = (X5)) | ((X7) != (k1_tarski @ X5)))),
% 0.24/0.50      inference('cnf', [status(esa)], [d1_tarski])).
% 0.24/0.50  thf('4', plain,
% 0.24/0.50      (![X5 : $i, X8 : $i]:
% 0.24/0.50         (((X8) = (X5)) | ~ (r2_hidden @ X8 @ (k1_tarski @ X5)))),
% 0.24/0.50      inference('simplify', [status(thm)], ['3'])).
% 0.24/0.51  thf('5', plain,
% 0.24/0.51      (![X0 : $i]:
% 0.24/0.51         (((sk_C_1 @ (k1_tarski @ X0) @ k1_xboole_0) = (k1_xboole_0))
% 0.24/0.51          | ((k1_tarski @ X0) = (k1_zfmisc_1 @ k1_xboole_0))
% 0.24/0.51          | ((sk_C_1 @ (k1_tarski @ X0) @ k1_xboole_0) = (X0)))),
% 0.24/0.51      inference('sup-', [status(thm)], ['2', '4'])).
% 0.24/0.51  thf('6', plain,
% 0.24/0.51      (![X0 : $i]:
% 0.24/0.51         (((X0) != (k1_xboole_0))
% 0.24/0.51          | ((k1_tarski @ X0) = (k1_zfmisc_1 @ k1_xboole_0))
% 0.24/0.51          | ((sk_C_1 @ (k1_tarski @ X0) @ k1_xboole_0) = (k1_xboole_0)))),
% 0.24/0.51      inference('eq_fact', [status(thm)], ['5'])).
% 0.24/0.51  thf('7', plain,
% 0.24/0.51      ((((sk_C_1 @ (k1_tarski @ k1_xboole_0) @ k1_xboole_0) = (k1_xboole_0))
% 0.24/0.51        | ((k1_tarski @ k1_xboole_0) = (k1_zfmisc_1 @ k1_xboole_0)))),
% 0.24/0.51      inference('simplify', [status(thm)], ['6'])).
% 0.24/0.51  thf(t1_zfmisc_1, conjecture,
% 0.24/0.51    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.24/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.51    (( k1_zfmisc_1 @ k1_xboole_0 ) != ( k1_tarski @ k1_xboole_0 )),
% 0.24/0.51    inference('cnf.neg', [status(esa)], [t1_zfmisc_1])).
% 0.24/0.51  thf('8', plain, (((k1_zfmisc_1 @ k1_xboole_0) != (k1_tarski @ k1_xboole_0))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('9', plain,
% 0.24/0.51      (((sk_C_1 @ (k1_tarski @ k1_xboole_0) @ k1_xboole_0) = (k1_xboole_0))),
% 0.24/0.51      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.24/0.51  thf('10', plain,
% 0.24/0.51      (![X21 : $i, X24 : $i]:
% 0.24/0.51         (((X24) = (k1_zfmisc_1 @ X21))
% 0.24/0.51          | ~ (r1_tarski @ (sk_C_1 @ X24 @ X21) @ X21)
% 0.24/0.51          | ~ (r2_hidden @ (sk_C_1 @ X24 @ X21) @ X24))),
% 0.24/0.51      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.24/0.51  thf('11', plain,
% 0.24/0.51      ((~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0)
% 0.24/0.51        | ~ (r2_hidden @ (sk_C_1 @ (k1_tarski @ k1_xboole_0) @ k1_xboole_0) @ 
% 0.24/0.51             (k1_tarski @ k1_xboole_0))
% 0.24/0.51        | ((k1_tarski @ k1_xboole_0) = (k1_zfmisc_1 @ k1_xboole_0)))),
% 0.24/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.24/0.51  thf(t36_xboole_1, axiom,
% 0.24/0.51    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.24/0.51  thf('12', plain,
% 0.24/0.51      (![X2 : $i, X3 : $i]: (r1_tarski @ (k4_xboole_0 @ X2 @ X3) @ X2)),
% 0.24/0.51      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.24/0.51  thf('13', plain,
% 0.24/0.51      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 0.24/0.51      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.24/0.51  thf('14', plain,
% 0.24/0.51      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.24/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.24/0.51  thf('15', plain,
% 0.24/0.51      (![X2 : $i, X3 : $i]: (r1_tarski @ (k4_xboole_0 @ X2 @ X3) @ X2)),
% 0.24/0.51      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.24/0.51  thf('16', plain, ((r1_tarski @ k1_xboole_0 @ k1_xboole_0)),
% 0.24/0.51      inference('sup+', [status(thm)], ['14', '15'])).
% 0.24/0.51  thf('17', plain,
% 0.24/0.51      (((sk_C_1 @ (k1_tarski @ k1_xboole_0) @ k1_xboole_0) = (k1_xboole_0))),
% 0.24/0.51      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.24/0.51  thf('18', plain,
% 0.24/0.51      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.24/0.51         (((X6) != (X5)) | (r2_hidden @ X6 @ X7) | ((X7) != (k1_tarski @ X5)))),
% 0.24/0.51      inference('cnf', [status(esa)], [d1_tarski])).
% 0.24/0.51  thf('19', plain, (![X5 : $i]: (r2_hidden @ X5 @ (k1_tarski @ X5))),
% 0.24/0.51      inference('simplify', [status(thm)], ['18'])).
% 0.24/0.51  thf('20', plain, (((k1_tarski @ k1_xboole_0) = (k1_zfmisc_1 @ k1_xboole_0))),
% 0.24/0.51      inference('demod', [status(thm)], ['11', '16', '17', '19'])).
% 0.24/0.51  thf('21', plain,
% 0.24/0.51      (((k1_zfmisc_1 @ k1_xboole_0) != (k1_tarski @ k1_xboole_0))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('22', plain, ($false),
% 0.24/0.51      inference('simplify_reflect-', [status(thm)], ['20', '21'])).
% 0.24/0.51  
% 0.24/0.51  % SZS output end Refutation
% 0.24/0.51  
% 0.24/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

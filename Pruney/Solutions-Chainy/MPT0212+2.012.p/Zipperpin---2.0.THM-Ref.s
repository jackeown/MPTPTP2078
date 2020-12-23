%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.i7N6LyPGmj

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:41 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   38 (  61 expanded)
%              Number of leaves         :   13 (  22 expanded)
%              Depth                    :   11
%              Number of atoms          :  259 ( 474 expanded)
%              Number of equality atoms :   39 (  76 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
    ! [X37: $i,X40: $i] :
      ( ( X40
        = ( k1_zfmisc_1 @ X37 ) )
      | ( r1_tarski @ ( sk_C @ X40 @ X37 ) @ X37 )
      | ( r2_hidden @ ( sk_C @ X40 @ X37 ) @ X40 ) ) ),
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
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( sk_C @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('3',plain,(
    ! [X8: $i] :
      ( ( k2_tarski @ X8 @ X8 )
      = ( k1_tarski @ X8 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ( X6 = X5 )
      | ( X6 = X2 )
      | ( X4
       != ( k2_tarski @ X5 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('5',plain,(
    ! [X2: $i,X5: $i,X6: $i] :
      ( ( X6 = X2 )
      | ( X6 = X5 )
      | ~ ( r2_hidden @ X6 @ ( k2_tarski @ X5 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(eq_fact,[status(thm)],['8'])).

thf('10',plain,
    ( ( ( sk_C @ ( k1_tarski @ k1_xboole_0 ) @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( ( k1_tarski @ k1_xboole_0 )
      = ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t1_zfmisc_1,conjecture,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ( k1_zfmisc_1 @ k1_xboole_0 )
 != ( k1_tarski @ k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t1_zfmisc_1])).

thf('11',plain,(
    ( k1_zfmisc_1 @ k1_xboole_0 )
 != ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( sk_C @ ( k1_tarski @ k1_xboole_0 ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X37: $i,X40: $i] :
      ( ( X40
        = ( k1_zfmisc_1 @ X37 ) )
      | ~ ( r1_tarski @ ( sk_C @ X40 @ X37 ) @ X37 )
      | ~ ( r2_hidden @ ( sk_C @ X40 @ X37 ) @ X40 ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('14',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( r2_hidden @ ( sk_C @ ( k1_tarski @ k1_xboole_0 ) @ k1_xboole_0 ) @ ( k1_tarski @ k1_xboole_0 ) )
    | ( ( k1_tarski @ k1_xboole_0 )
      = ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('16',plain,
    ( ( sk_C @ ( k1_tarski @ k1_xboole_0 ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('17',plain,(
    ! [X8: $i] :
      ( ( k2_tarski @ X8 @ X8 )
      = ( k1_tarski @ X8 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('18',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( X3 != X2 )
      | ( r2_hidden @ X3 @ X4 )
      | ( X4
       != ( k2_tarski @ X5 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('19',plain,(
    ! [X2: $i,X5: $i] :
      ( r2_hidden @ X2 @ ( k2_tarski @ X5 @ X2 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','19'])).

thf('21',plain,
    ( ( k1_tarski @ k1_xboole_0 )
    = ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','15','16','20'])).

thf('22',plain,(
    ( k1_zfmisc_1 @ k1_xboole_0 )
 != ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.i7N6LyPGmj
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:57:45 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 38 iterations in 0.026s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.49  thf(d1_zfmisc_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.22/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.22/0.49  thf('0', plain,
% 0.22/0.49      (![X37 : $i, X40 : $i]:
% 0.22/0.49         (((X40) = (k1_zfmisc_1 @ X37))
% 0.22/0.49          | (r1_tarski @ (sk_C @ X40 @ X37) @ X37)
% 0.22/0.49          | (r2_hidden @ (sk_C @ X40 @ X37) @ X40))),
% 0.22/0.49      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.22/0.49  thf(t3_xboole_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (r1_tarski @ X1 @ k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.22/0.49          | ((X0) = (k1_zfmisc_1 @ k1_xboole_0))
% 0.22/0.49          | ((sk_C @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.49  thf(t69_enumset1, axiom,
% 0.22/0.49    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.49  thf('3', plain, (![X8 : $i]: ((k2_tarski @ X8 @ X8) = (k1_tarski @ X8))),
% 0.22/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.49  thf(d2_tarski, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.22/0.49       ( ![D:$i]:
% 0.22/0.49         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (![X2 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X6 @ X4)
% 0.22/0.49          | ((X6) = (X5))
% 0.22/0.49          | ((X6) = (X2))
% 0.22/0.49          | ((X4) != (k2_tarski @ X5 @ X2)))),
% 0.22/0.49      inference('cnf', [status(esa)], [d2_tarski])).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      (![X2 : $i, X5 : $i, X6 : $i]:
% 0.22/0.49         (((X6) = (X2))
% 0.22/0.49          | ((X6) = (X5))
% 0.22/0.49          | ~ (r2_hidden @ X6 @ (k2_tarski @ X5 @ X2)))),
% 0.22/0.49      inference('simplify', [status(thm)], ['4'])).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['3', '5'])).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.22/0.49      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (((sk_C @ (k1_tarski @ X0) @ k1_xboole_0) = (k1_xboole_0))
% 0.22/0.49          | ((k1_tarski @ X0) = (k1_zfmisc_1 @ k1_xboole_0))
% 0.22/0.49          | ((sk_C @ (k1_tarski @ X0) @ k1_xboole_0) = (X0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['2', '7'])).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (((X0) != (k1_xboole_0))
% 0.22/0.49          | ((k1_tarski @ X0) = (k1_zfmisc_1 @ k1_xboole_0))
% 0.22/0.49          | ((sk_C @ (k1_tarski @ X0) @ k1_xboole_0) = (k1_xboole_0)))),
% 0.22/0.49      inference('eq_fact', [status(thm)], ['8'])).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      ((((sk_C @ (k1_tarski @ k1_xboole_0) @ k1_xboole_0) = (k1_xboole_0))
% 0.22/0.49        | ((k1_tarski @ k1_xboole_0) = (k1_zfmisc_1 @ k1_xboole_0)))),
% 0.22/0.49      inference('simplify', [status(thm)], ['9'])).
% 0.22/0.49  thf(t1_zfmisc_1, conjecture,
% 0.22/0.49    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (( k1_zfmisc_1 @ k1_xboole_0 ) != ( k1_tarski @ k1_xboole_0 )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t1_zfmisc_1])).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      (((k1_zfmisc_1 @ k1_xboole_0) != (k1_tarski @ k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      (((sk_C @ (k1_tarski @ k1_xboole_0) @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.22/0.49  thf('13', plain,
% 0.22/0.49      (![X37 : $i, X40 : $i]:
% 0.22/0.49         (((X40) = (k1_zfmisc_1 @ X37))
% 0.22/0.49          | ~ (r1_tarski @ (sk_C @ X40 @ X37) @ X37)
% 0.22/0.49          | ~ (r2_hidden @ (sk_C @ X40 @ X37) @ X40))),
% 0.22/0.49      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.22/0.49  thf('14', plain,
% 0.22/0.49      ((~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0)
% 0.22/0.49        | ~ (r2_hidden @ (sk_C @ (k1_tarski @ k1_xboole_0) @ k1_xboole_0) @ 
% 0.22/0.49             (k1_tarski @ k1_xboole_0))
% 0.22/0.49        | ((k1_tarski @ k1_xboole_0) = (k1_zfmisc_1 @ k1_xboole_0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.49  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.49  thf('15', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.22/0.49      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.49  thf('16', plain,
% 0.22/0.49      (((sk_C @ (k1_tarski @ k1_xboole_0) @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.22/0.49  thf('17', plain, (![X8 : $i]: ((k2_tarski @ X8 @ X8) = (k1_tarski @ X8))),
% 0.22/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.49         (((X3) != (X2))
% 0.22/0.49          | (r2_hidden @ X3 @ X4)
% 0.22/0.49          | ((X4) != (k2_tarski @ X5 @ X2)))),
% 0.22/0.49      inference('cnf', [status(esa)], [d2_tarski])).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      (![X2 : $i, X5 : $i]: (r2_hidden @ X2 @ (k2_tarski @ X5 @ X2))),
% 0.22/0.49      inference('simplify', [status(thm)], ['18'])).
% 0.22/0.49  thf('20', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['17', '19'])).
% 0.22/0.49  thf('21', plain, (((k1_tarski @ k1_xboole_0) = (k1_zfmisc_1 @ k1_xboole_0))),
% 0.22/0.49      inference('demod', [status(thm)], ['14', '15', '16', '20'])).
% 0.22/0.49  thf('22', plain,
% 0.22/0.49      (((k1_zfmisc_1 @ k1_xboole_0) != (k1_tarski @ k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('23', plain, ($false),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

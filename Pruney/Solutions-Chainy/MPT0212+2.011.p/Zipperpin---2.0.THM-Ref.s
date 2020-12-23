%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BrnXEyeeOH

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:41 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   43 (  68 expanded)
%              Number of leaves         :   14 (  25 expanded)
%              Depth                    :   11
%              Number of atoms          :  282 ( 508 expanded)
%              Number of equality atoms :   41 (  79 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('0',plain,(
    ! [X40: $i,X43: $i] :
      ( ( X43
        = ( k1_zfmisc_1 @ X40 ) )
      | ( r1_tarski @ ( sk_C @ X43 @ X40 ) @ X40 )
      | ( r2_hidden @ ( sk_C @ X43 @ X40 ) @ X43 ) ) ),
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
    ! [X11: $i] :
      ( ( k2_tarski @ X11 @ X11 )
      = ( k1_tarski @ X11 ) ) ),
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
    ! [X5: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X7 )
      | ( X9 = X8 )
      | ( X9 = X5 )
      | ( X7
       != ( k2_tarski @ X8 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('5',plain,(
    ! [X5: $i,X8: $i,X9: $i] :
      ( ( X9 = X5 )
      | ( X9 = X8 )
      | ~ ( r2_hidden @ X9 @ ( k2_tarski @ X8 @ X5 ) ) ) ),
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
    ! [X40: $i,X43: $i] :
      ( ( X43
        = ( k1_zfmisc_1 @ X40 ) )
      | ~ ( r1_tarski @ ( sk_C @ X43 @ X40 ) @ X40 )
      | ~ ( r2_hidden @ ( sk_C @ X43 @ X40 ) @ X43 ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('14',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( r2_hidden @ ( sk_C @ ( k1_tarski @ k1_xboole_0 ) @ k1_xboole_0 ) @ ( k1_tarski @ k1_xboole_0 ) )
    | ( ( k1_tarski @ k1_xboole_0 )
      = ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('16',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('19',plain,(
    r1_tarski @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( sk_C @ ( k1_tarski @ k1_xboole_0 ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('21',plain,(
    ! [X11: $i] :
      ( ( k2_tarski @ X11 @ X11 )
      = ( k1_tarski @ X11 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('22',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X6 != X5 )
      | ( r2_hidden @ X6 @ X7 )
      | ( X7
       != ( k2_tarski @ X8 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('23',plain,(
    ! [X5: $i,X8: $i] :
      ( r2_hidden @ X5 @ ( k2_tarski @ X8 @ X5 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','23'])).

thf('25',plain,
    ( ( k1_tarski @ k1_xboole_0 )
    = ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','19','20','24'])).

thf('26',plain,(
    ( k1_zfmisc_1 @ k1_xboole_0 )
 != ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BrnXEyeeOH
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:14:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 47 iterations in 0.020s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.48  thf(d1_zfmisc_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.22/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.22/0.48  thf('0', plain,
% 0.22/0.48      (![X40 : $i, X43 : $i]:
% 0.22/0.48         (((X43) = (k1_zfmisc_1 @ X40))
% 0.22/0.48          | (r1_tarski @ (sk_C @ X43 @ X40) @ X40)
% 0.22/0.48          | (r2_hidden @ (sk_C @ X43 @ X40) @ X43))),
% 0.22/0.48      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.22/0.48  thf(t3_xboole_1, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.48  thf('1', plain,
% 0.22/0.48      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 0.22/0.48      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.22/0.48  thf('2', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.22/0.48          | ((X0) = (k1_zfmisc_1 @ k1_xboole_0))
% 0.22/0.48          | ((sk_C @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.48  thf(t69_enumset1, axiom,
% 0.22/0.48    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.48  thf('3', plain, (![X11 : $i]: ((k2_tarski @ X11 @ X11) = (k1_tarski @ X11))),
% 0.22/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.48  thf(d2_tarski, axiom,
% 0.22/0.48    (![A:$i,B:$i,C:$i]:
% 0.22/0.48     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.22/0.48       ( ![D:$i]:
% 0.22/0.48         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.22/0.48  thf('4', plain,
% 0.22/0.48      (![X5 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.48         (~ (r2_hidden @ X9 @ X7)
% 0.22/0.48          | ((X9) = (X8))
% 0.22/0.48          | ((X9) = (X5))
% 0.22/0.48          | ((X7) != (k2_tarski @ X8 @ X5)))),
% 0.22/0.48      inference('cnf', [status(esa)], [d2_tarski])).
% 0.22/0.48  thf('5', plain,
% 0.22/0.48      (![X5 : $i, X8 : $i, X9 : $i]:
% 0.22/0.48         (((X9) = (X5))
% 0.22/0.48          | ((X9) = (X8))
% 0.22/0.48          | ~ (r2_hidden @ X9 @ (k2_tarski @ X8 @ X5)))),
% 0.22/0.48      inference('simplify', [status(thm)], ['4'])).
% 0.22/0.48  thf('6', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['3', '5'])).
% 0.22/0.48  thf('7', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.22/0.48      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.48  thf('8', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (((sk_C @ (k1_tarski @ X0) @ k1_xboole_0) = (k1_xboole_0))
% 0.22/0.48          | ((k1_tarski @ X0) = (k1_zfmisc_1 @ k1_xboole_0))
% 0.22/0.48          | ((sk_C @ (k1_tarski @ X0) @ k1_xboole_0) = (X0)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['2', '7'])).
% 0.22/0.48  thf('9', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (((X0) != (k1_xboole_0))
% 0.22/0.48          | ((k1_tarski @ X0) = (k1_zfmisc_1 @ k1_xboole_0))
% 0.22/0.48          | ((sk_C @ (k1_tarski @ X0) @ k1_xboole_0) = (k1_xboole_0)))),
% 0.22/0.48      inference('eq_fact', [status(thm)], ['8'])).
% 0.22/0.48  thf('10', plain,
% 0.22/0.48      ((((sk_C @ (k1_tarski @ k1_xboole_0) @ k1_xboole_0) = (k1_xboole_0))
% 0.22/0.48        | ((k1_tarski @ k1_xboole_0) = (k1_zfmisc_1 @ k1_xboole_0)))),
% 0.22/0.48      inference('simplify', [status(thm)], ['9'])).
% 0.22/0.48  thf(t1_zfmisc_1, conjecture,
% 0.22/0.48    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (( k1_zfmisc_1 @ k1_xboole_0 ) != ( k1_tarski @ k1_xboole_0 )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t1_zfmisc_1])).
% 0.22/0.48  thf('11', plain,
% 0.22/0.48      (((k1_zfmisc_1 @ k1_xboole_0) != (k1_tarski @ k1_xboole_0))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('12', plain,
% 0.22/0.48      (((sk_C @ (k1_tarski @ k1_xboole_0) @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.48      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.22/0.48  thf('13', plain,
% 0.22/0.48      (![X40 : $i, X43 : $i]:
% 0.22/0.48         (((X43) = (k1_zfmisc_1 @ X40))
% 0.22/0.48          | ~ (r1_tarski @ (sk_C @ X43 @ X40) @ X40)
% 0.22/0.48          | ~ (r2_hidden @ (sk_C @ X43 @ X40) @ X43))),
% 0.22/0.48      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.22/0.48  thf('14', plain,
% 0.22/0.48      ((~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0)
% 0.22/0.48        | ~ (r2_hidden @ (sk_C @ (k1_tarski @ k1_xboole_0) @ k1_xboole_0) @ 
% 0.22/0.48             (k1_tarski @ k1_xboole_0))
% 0.22/0.48        | ((k1_tarski @ k1_xboole_0) = (k1_zfmisc_1 @ k1_xboole_0)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.48  thf(t36_xboole_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.22/0.48  thf('15', plain,
% 0.22/0.48      (![X2 : $i, X3 : $i]: (r1_tarski @ (k4_xboole_0 @ X2 @ X3) @ X2)),
% 0.22/0.48      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.22/0.48  thf('16', plain,
% 0.22/0.48      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 0.22/0.48      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.22/0.48  thf('17', plain,
% 0.22/0.48      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.48  thf('18', plain,
% 0.22/0.48      (![X2 : $i, X3 : $i]: (r1_tarski @ (k4_xboole_0 @ X2 @ X3) @ X2)),
% 0.22/0.48      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.22/0.48  thf('19', plain, ((r1_tarski @ k1_xboole_0 @ k1_xboole_0)),
% 0.22/0.48      inference('sup+', [status(thm)], ['17', '18'])).
% 0.22/0.48  thf('20', plain,
% 0.22/0.48      (((sk_C @ (k1_tarski @ k1_xboole_0) @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.48      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.22/0.48  thf('21', plain,
% 0.22/0.48      (![X11 : $i]: ((k2_tarski @ X11 @ X11) = (k1_tarski @ X11))),
% 0.22/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.48  thf('22', plain,
% 0.22/0.48      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.48         (((X6) != (X5))
% 0.22/0.48          | (r2_hidden @ X6 @ X7)
% 0.22/0.48          | ((X7) != (k2_tarski @ X8 @ X5)))),
% 0.22/0.48      inference('cnf', [status(esa)], [d2_tarski])).
% 0.22/0.48  thf('23', plain,
% 0.22/0.48      (![X5 : $i, X8 : $i]: (r2_hidden @ X5 @ (k2_tarski @ X8 @ X5))),
% 0.22/0.48      inference('simplify', [status(thm)], ['22'])).
% 0.22/0.48  thf('24', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.22/0.48      inference('sup+', [status(thm)], ['21', '23'])).
% 0.22/0.48  thf('25', plain, (((k1_tarski @ k1_xboole_0) = (k1_zfmisc_1 @ k1_xboole_0))),
% 0.22/0.48      inference('demod', [status(thm)], ['14', '19', '20', '24'])).
% 0.22/0.48  thf('26', plain,
% 0.22/0.48      (((k1_zfmisc_1 @ k1_xboole_0) != (k1_tarski @ k1_xboole_0))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('27', plain, ($false),
% 0.22/0.48      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

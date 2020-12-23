%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IcKAw8U01I

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:01 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   35 (  74 expanded)
%              Number of leaves         :   12 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :  193 ( 540 expanded)
%              Number of equality atoms :   34 ( 104 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t21_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = k1_xboole_0 )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = k1_xboole_0 )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t21_zfmisc_1])).

thf('0',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X11 ) @ ( k1_tarski @ X12 ) )
        = ( k1_tarski @ X11 ) )
      | ( X11 = X12 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('2',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ sk_A ) )
    | ( sk_A = sk_B ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['2','3'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('5',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('7',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','7'])).

thf(l35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('9',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X7 ) @ X9 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['4','10'])).

thf('12',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['2','3'])).

thf('13',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['2','3'])).

thf('15',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X11 != X10 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X11 ) @ ( k1_tarski @ X10 ) )
       != ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('16',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X10 ) @ ( k1_tarski @ X10 ) )
     != ( k1_tarski @ X10 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
 != ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['2','3'])).

thf('19',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['2','3'])).

thf('20',plain,(
    ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['13','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IcKAw8U01I
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:48:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.45  % Solved by: fo/fo7.sh
% 0.20/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.45  % done 18 iterations in 0.015s
% 0.20/0.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.45  % SZS output start Refutation
% 0.20/0.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.45  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.45  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.45  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.45  thf(t21_zfmisc_1, conjecture,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.45         ( k1_xboole_0 ) ) =>
% 0.20/0.45       ( ( A ) = ( B ) ) ))).
% 0.20/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.45    (~( ![A:$i,B:$i]:
% 0.20/0.45        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.45            ( k1_xboole_0 ) ) =>
% 0.20/0.45          ( ( A ) = ( B ) ) ) )),
% 0.20/0.45    inference('cnf.neg', [status(esa)], [t21_zfmisc_1])).
% 0.20/0.45  thf('0', plain,
% 0.20/0.45      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf(t20_zfmisc_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.45         ( k1_tarski @ A ) ) <=>
% 0.20/0.45       ( ( A ) != ( B ) ) ))).
% 0.20/0.45  thf('1', plain,
% 0.20/0.45      (![X11 : $i, X12 : $i]:
% 0.20/0.45         (((k4_xboole_0 @ (k1_tarski @ X11) @ (k1_tarski @ X12))
% 0.20/0.45            = (k1_tarski @ X11))
% 0.20/0.45          | ((X11) = (X12)))),
% 0.20/0.45      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.45  thf('2', plain, ((((k1_xboole_0) = (k1_tarski @ sk_A)) | ((sk_A) = (sk_B)))),
% 0.20/0.45      inference('sup+', [status(thm)], ['0', '1'])).
% 0.20/0.45  thf('3', plain, (((sk_A) != (sk_B))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('4', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.20/0.45      inference('simplify_reflect-', [status(thm)], ['2', '3'])).
% 0.20/0.45  thf(t69_enumset1, axiom,
% 0.20/0.45    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.45  thf('5', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.20/0.45      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.45  thf(d2_tarski, axiom,
% 0.20/0.45    (![A:$i,B:$i,C:$i]:
% 0.20/0.45     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.20/0.45       ( ![D:$i]:
% 0.20/0.45         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.20/0.45  thf('6', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.45         (((X1) != (X0))
% 0.20/0.45          | (r2_hidden @ X1 @ X2)
% 0.20/0.45          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.20/0.45      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.45  thf('7', plain,
% 0.20/0.45      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.20/0.45      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.45  thf('8', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.45      inference('sup+', [status(thm)], ['5', '7'])).
% 0.20/0.45  thf(l35_zfmisc_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.45       ( r2_hidden @ A @ B ) ))).
% 0.20/0.45  thf('9', plain,
% 0.20/0.45      (![X7 : $i, X9 : $i]:
% 0.20/0.45         (((k4_xboole_0 @ (k1_tarski @ X7) @ X9) = (k1_xboole_0))
% 0.20/0.45          | ~ (r2_hidden @ X7 @ X9))),
% 0.20/0.45      inference('cnf', [status(esa)], [l35_zfmisc_1])).
% 0.20/0.45  thf('10', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.20/0.45      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.45  thf('11', plain,
% 0.20/0.45      (((k4_xboole_0 @ k1_xboole_0 @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.20/0.45      inference('sup+', [status(thm)], ['4', '10'])).
% 0.20/0.45  thf('12', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.20/0.45      inference('simplify_reflect-', [status(thm)], ['2', '3'])).
% 0.20/0.45  thf('13', plain,
% 0.20/0.45      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.45      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.45  thf('14', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.20/0.45      inference('simplify_reflect-', [status(thm)], ['2', '3'])).
% 0.20/0.45  thf('15', plain,
% 0.20/0.45      (![X10 : $i, X11 : $i]:
% 0.20/0.45         (((X11) != (X10))
% 0.20/0.45          | ((k4_xboole_0 @ (k1_tarski @ X11) @ (k1_tarski @ X10))
% 0.20/0.45              != (k1_tarski @ X11)))),
% 0.20/0.45      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.45  thf('16', plain,
% 0.20/0.45      (![X10 : $i]:
% 0.20/0.45         ((k4_xboole_0 @ (k1_tarski @ X10) @ (k1_tarski @ X10))
% 0.20/0.45           != (k1_tarski @ X10))),
% 0.20/0.45      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.45  thf('17', plain,
% 0.20/0.45      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0) != (k1_tarski @ sk_A))),
% 0.20/0.45      inference('sup-', [status(thm)], ['14', '16'])).
% 0.20/0.45  thf('18', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.20/0.45      inference('simplify_reflect-', [status(thm)], ['2', '3'])).
% 0.20/0.45  thf('19', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.20/0.45      inference('simplify_reflect-', [status(thm)], ['2', '3'])).
% 0.20/0.45  thf('20', plain,
% 0.20/0.45      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.45      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.20/0.45  thf('21', plain, ($false),
% 0.20/0.45      inference('simplify_reflect-', [status(thm)], ['13', '20'])).
% 0.20/0.45  
% 0.20/0.45  % SZS output end Refutation
% 0.20/0.45  
% 0.20/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

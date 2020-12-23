%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5Ih5vw8XZ9

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:59 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   27 (  48 expanded)
%              Number of leaves         :   10 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :  133 ( 322 expanded)
%              Number of equality atoms :   24 (  62 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X34: $i,X35: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X34 ) @ ( k1_tarski @ X35 ) )
        = ( k1_tarski @ X34 ) )
      | ( X34 = X35 ) ) ),
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

thf('5',plain,(
    ! [X33: $i,X34: $i] :
      ( ( X34 != X33 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X34 ) @ ( k1_tarski @ X33 ) )
       != ( k1_tarski @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('6',plain,(
    ! [X33: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X33 ) @ ( k1_tarski @ X33 ) )
     != ( k1_tarski @ X33 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
 != ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['2','3'])).

thf('9',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['2','3'])).

thf('10',plain,(
    ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('11',plain,(
    ! [X10: $i] :
      ( r1_xboole_0 @ X10 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,(
    $false ),
    inference(simplify,[status(thm)],['14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5Ih5vw8XZ9
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:40:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 31 iterations in 0.019s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(t21_zfmisc_1, conjecture,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.22/0.48         ( k1_xboole_0 ) ) =>
% 0.22/0.48       ( ( A ) = ( B ) ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i,B:$i]:
% 0.22/0.48        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.22/0.48            ( k1_xboole_0 ) ) =>
% 0.22/0.48          ( ( A ) = ( B ) ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t21_zfmisc_1])).
% 0.22/0.48  thf('0', plain,
% 0.22/0.48      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(t20_zfmisc_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.22/0.48         ( k1_tarski @ A ) ) <=>
% 0.22/0.48       ( ( A ) != ( B ) ) ))).
% 0.22/0.48  thf('1', plain,
% 0.22/0.48      (![X34 : $i, X35 : $i]:
% 0.22/0.48         (((k4_xboole_0 @ (k1_tarski @ X34) @ (k1_tarski @ X35))
% 0.22/0.48            = (k1_tarski @ X34))
% 0.22/0.48          | ((X34) = (X35)))),
% 0.22/0.48      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.22/0.48  thf('2', plain, ((((k1_xboole_0) = (k1_tarski @ sk_A)) | ((sk_A) = (sk_B)))),
% 0.22/0.48      inference('sup+', [status(thm)], ['0', '1'])).
% 0.22/0.48  thf('3', plain, (((sk_A) != (sk_B))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('4', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.22/0.48      inference('simplify_reflect-', [status(thm)], ['2', '3'])).
% 0.22/0.48  thf('5', plain,
% 0.22/0.48      (![X33 : $i, X34 : $i]:
% 0.22/0.48         (((X34) != (X33))
% 0.22/0.48          | ((k4_xboole_0 @ (k1_tarski @ X34) @ (k1_tarski @ X33))
% 0.22/0.48              != (k1_tarski @ X34)))),
% 0.22/0.48      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.22/0.48  thf('6', plain,
% 0.22/0.48      (![X33 : $i]:
% 0.22/0.48         ((k4_xboole_0 @ (k1_tarski @ X33) @ (k1_tarski @ X33))
% 0.22/0.48           != (k1_tarski @ X33))),
% 0.22/0.48      inference('simplify', [status(thm)], ['5'])).
% 0.22/0.48  thf('7', plain,
% 0.22/0.48      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0) != (k1_tarski @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['4', '6'])).
% 0.22/0.48  thf('8', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.22/0.48      inference('simplify_reflect-', [status(thm)], ['2', '3'])).
% 0.22/0.48  thf('9', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.22/0.48      inference('simplify_reflect-', [status(thm)], ['2', '3'])).
% 0.22/0.48  thf('10', plain,
% 0.22/0.48      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.48      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.22/0.48  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.22/0.48  thf('11', plain, (![X10 : $i]: (r1_xboole_0 @ X10 @ k1_xboole_0)),
% 0.22/0.48      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.22/0.48  thf(t83_xboole_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.48  thf('12', plain,
% 0.22/0.48      (![X11 : $i, X12 : $i]:
% 0.22/0.48         (((k4_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_xboole_0 @ X11 @ X12))),
% 0.22/0.48      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.22/0.48  thf('13', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.48  thf('14', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.48      inference('demod', [status(thm)], ['10', '13'])).
% 0.22/0.48  thf('15', plain, ($false), inference('simplify', [status(thm)], ['14'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

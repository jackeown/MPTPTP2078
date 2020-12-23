%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4CW5VthCLp

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:37 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   33 ( 106 expanded)
%              Number of leaves         :   10 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :  168 ( 831 expanded)
%              Number of equality atoms :   24 (  94 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t27_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
     => ( ( k2_tarski @ A @ B )
        = ( k1_tarski @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
       => ( ( k2_tarski @ A @ B )
          = ( k1_tarski @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_zfmisc_1])).

thf('0',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k1_tarski @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
     => ( A = C ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( X10 = X9 )
      | ~ ( r1_tarski @ ( k2_tarski @ X10 @ X11 ) @ ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t26_zfmisc_1])).

thf('3',plain,(
    sk_A = sk_C ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    sk_A = sk_C ),
    inference('sup-',[status(thm)],['1','2'])).

thf('7',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X7
        = ( k1_tarski @ X6 ) )
      | ( X7 = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('9',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('11',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('12',plain,(
    k1_xboole_0
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['4','11'])).

thf('13',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('14',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( X10 = X9 )
      | ~ ( r1_tarski @ ( k2_tarski @ X10 @ X11 ) @ ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t26_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( sk_A = X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ ( k1_tarski @ X8 ) )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('17',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X8 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference(demod,[status(thm)],['15','17'])).

thf('19',plain,(
    k1_xboole_0 != sk_A ),
    inference(demod,[status(thm)],['12','18'])).

thf('20',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference(demod,[status(thm)],['15','17'])).

thf('21',plain,(
    $false ),
    inference('simplify_reflect+',[status(thm)],['19','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4CW5VthCLp
% 0.15/0.36  % Computer   : n014.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 15:46:22 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 24 iterations in 0.017s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.49  thf(t27_zfmisc_1, conjecture,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.22/0.49       ( ( k2_tarski @ A @ B ) = ( k1_tarski @ C ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.49        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.22/0.49          ( ( k2_tarski @ A @ B ) = ( k1_tarski @ C ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t27_zfmisc_1])).
% 0.22/0.49  thf('0', plain, (((k2_tarski @ sk_A @ sk_B) != (k1_tarski @ sk_C))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(t26_zfmisc_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.22/0.49       ( ( A ) = ( C ) ) ))).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.49         (((X10) = (X9))
% 0.22/0.49          | ~ (r1_tarski @ (k2_tarski @ X10 @ X11) @ (k1_tarski @ X9)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t26_zfmisc_1])).
% 0.22/0.49  thf('3', plain, (((sk_A) = (sk_C))),
% 0.22/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.49  thf('4', plain, (((k2_tarski @ sk_A @ sk_B) != (k1_tarski @ sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['0', '3'])).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('6', plain, (((sk_A) = (sk_C))),
% 0.22/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['5', '6'])).
% 0.22/0.49  thf(l3_zfmisc_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.22/0.49       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      (![X6 : $i, X7 : $i]:
% 0.22/0.49         (((X7) = (k1_tarski @ X6))
% 0.22/0.49          | ((X7) = (k1_xboole_0))
% 0.22/0.49          | ~ (r1_tarski @ X7 @ (k1_tarski @ X6)))),
% 0.22/0.49      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.22/0.49        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_A)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.49  thf('10', plain, (((k2_tarski @ sk_A @ sk_B) != (k1_tarski @ sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['0', '3'])).
% 0.22/0.49  thf('11', plain, (((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.22/0.49  thf('12', plain, (((k1_xboole_0) != (k1_tarski @ sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['4', '11'])).
% 0.22/0.49  thf('13', plain, (((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.22/0.49  thf('14', plain,
% 0.22/0.49      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.49         (((X10) = (X9))
% 0.22/0.49          | ~ (r1_tarski @ (k2_tarski @ X10 @ X11) @ (k1_tarski @ X9)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t26_zfmisc_1])).
% 0.22/0.49  thf('15', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) | ((sk_A) = (X0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.49  thf('16', plain,
% 0.22/0.49      (![X7 : $i, X8 : $i]:
% 0.22/0.49         ((r1_tarski @ X7 @ (k1_tarski @ X8)) | ((X7) != (k1_xboole_0)))),
% 0.22/0.49      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.22/0.49  thf('17', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X8))),
% 0.22/0.49      inference('simplify', [status(thm)], ['16'])).
% 0.22/0.49  thf('18', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 0.22/0.49      inference('demod', [status(thm)], ['15', '17'])).
% 0.22/0.49  thf('19', plain, (((k1_xboole_0) != (sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['12', '18'])).
% 0.22/0.49  thf('20', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 0.22/0.49      inference('demod', [status(thm)], ['15', '17'])).
% 0.22/0.49  thf('21', plain, ($false),
% 0.22/0.49      inference('simplify_reflect+', [status(thm)], ['19', '20'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

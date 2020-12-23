%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jo1fbRHIr3

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 (  55 expanded)
%              Number of leaves         :   13 (  21 expanded)
%              Depth                    :   11
%              Number of atoms          :  239 ( 380 expanded)
%              Number of equality atoms :   40 (  69 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t9_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k1_tarski @ A )
        = ( k2_tarski @ B @ C ) )
     => ( B = C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k1_tarski @ A )
          = ( k2_tarski @ B @ C ) )
       => ( B = C ) ) ),
    inference('cnf.neg',[status(esa)],[t9_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k1_tarski @ A )
        = ( k2_tarski @ B @ C ) )
     => ( A = B ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( X14 = X13 )
      | ( ( k1_tarski @ X14 )
       != ( k2_tarski @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t8_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ sk_A ) )
      | ( X0 = sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    sk_A = sk_B ),
    inference(eq_res,[status(thm)],['3'])).

thf('5',plain,
    ( ( k1_tarski @ sk_B )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','4'])).

thf(t43_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k2_tarski @ X7 @ X8 ) @ ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ sk_B @ sk_C @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('8',plain,(
    ! [X10: $i] :
      ( ( k2_tarski @ X10 @ X10 )
      = ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('9',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k2_tarski @ X7 @ X8 ) @ ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_enumset1 @ X11 @ X11 @ X12 )
      = ( k2_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ sk_B @ sk_C @ X0 )
      = ( k2_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['7','10','11'])).

thf(t102_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ C @ B @ A ) ) )).

thf('13',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X6 @ X5 @ X4 )
      = ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t102_enumset1])).

thf('14',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_enumset1 @ X11 @ X11 @ X12 )
      = ( k2_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('15',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( X14 = X13 )
      | ( ( k1_tarski @ X14 )
       != ( k2_tarski @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t8_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X2 )
       != ( k1_enumset1 @ X1 @ X1 @ X0 ) )
      | ( X2 = X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X2 )
       != ( k1_enumset1 @ X1 @ X0 @ X0 ) )
      | ( X2 = X0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k2_tarski @ sk_B @ sk_C ) )
      | ( X0 = sk_C ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,
    ( ( k1_tarski @ sk_B )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','4'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ sk_B ) )
      | ( X0 = sk_C ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    sk_B = sk_C ),
    inference(eq_res,[status(thm)],['20'])).

thf('22',plain,(
    sk_B != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jo1fbRHIr3
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:49:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 59 iterations in 0.026s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.49  thf(t9_zfmisc_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( k1_tarski @ A ) = ( k2_tarski @ B @ C ) ) => ( ( B ) = ( C ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.49        ( ( ( k1_tarski @ A ) = ( k2_tarski @ B @ C ) ) => ( ( B ) = ( C ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t9_zfmisc_1])).
% 0.21/0.49  thf('0', plain, (((k1_tarski @ sk_A) = (k2_tarski @ sk_B @ sk_C))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain, (((k1_tarski @ sk_A) = (k2_tarski @ sk_B @ sk_C))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t8_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( k1_tarski @ A ) = ( k2_tarski @ B @ C ) ) => ( ( A ) = ( B ) ) ))).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.49         (((X14) = (X13)) | ((k1_tarski @ X14) != (k2_tarski @ X13 @ X15)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t8_zfmisc_1])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X0 : $i]: (((k1_tarski @ X0) != (k1_tarski @ sk_A)) | ((X0) = (sk_B)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.49  thf('4', plain, (((sk_A) = (sk_B))),
% 0.21/0.49      inference('eq_res', [status(thm)], ['3'])).
% 0.21/0.49  thf('5', plain, (((k1_tarski @ sk_B) = (k2_tarski @ sk_B @ sk_C))),
% 0.21/0.49      inference('demod', [status(thm)], ['0', '4'])).
% 0.21/0.49  thf(t43_enumset1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.21/0.49       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ))).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.49         ((k1_enumset1 @ X7 @ X8 @ X9)
% 0.21/0.49           = (k2_xboole_0 @ (k2_tarski @ X7 @ X8) @ (k1_tarski @ X9)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((k1_enumset1 @ sk_B @ sk_C @ X0)
% 0.21/0.49           = (k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ X0)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.49  thf(t69_enumset1, axiom,
% 0.21/0.49    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.49  thf('8', plain, (![X10 : $i]: ((k2_tarski @ X10 @ X10) = (k1_tarski @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.49         ((k1_enumset1 @ X7 @ X8 @ X9)
% 0.21/0.49           = (k2_xboole_0 @ (k2_tarski @ X7 @ X8) @ (k1_tarski @ X9)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((k1_enumset1 @ X0 @ X0 @ X1)
% 0.21/0.49           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['8', '9'])).
% 0.21/0.49  thf(t70_enumset1, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X11 : $i, X12 : $i]:
% 0.21/0.49         ((k1_enumset1 @ X11 @ X11 @ X12) = (k2_tarski @ X11 @ X12))),
% 0.21/0.49      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X0 : $i]: ((k1_enumset1 @ sk_B @ sk_C @ X0) = (k2_tarski @ sk_B @ X0))),
% 0.21/0.49      inference('demod', [status(thm)], ['7', '10', '11'])).
% 0.21/0.49  thf(t102_enumset1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ C @ B @ A ) ))).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.49         ((k1_enumset1 @ X6 @ X5 @ X4) = (k1_enumset1 @ X4 @ X5 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [t102_enumset1])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X11 : $i, X12 : $i]:
% 0.21/0.49         ((k1_enumset1 @ X11 @ X11 @ X12) = (k2_tarski @ X11 @ X12))),
% 0.21/0.49      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.49         (((X14) = (X13)) | ((k1_tarski @ X14) != (k2_tarski @ X13 @ X15)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t8_zfmisc_1])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (((k1_tarski @ X2) != (k1_enumset1 @ X1 @ X1 @ X0)) | ((X2) = (X1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (((k1_tarski @ X2) != (k1_enumset1 @ X1 @ X0 @ X0)) | ((X2) = (X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['13', '16'])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k1_tarski @ X0) != (k2_tarski @ sk_B @ sk_C)) | ((X0) = (sk_C)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['12', '17'])).
% 0.21/0.49  thf('19', plain, (((k1_tarski @ sk_B) = (k2_tarski @ sk_B @ sk_C))),
% 0.21/0.49      inference('demod', [status(thm)], ['0', '4'])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (![X0 : $i]: (((k1_tarski @ X0) != (k1_tarski @ sk_B)) | ((X0) = (sk_C)))),
% 0.21/0.49      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.49  thf('21', plain, (((sk_B) = (sk_C))),
% 0.21/0.49      inference('eq_res', [status(thm)], ['20'])).
% 0.21/0.49  thf('22', plain, (((sk_B) != (sk_C))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('23', plain, ($false),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

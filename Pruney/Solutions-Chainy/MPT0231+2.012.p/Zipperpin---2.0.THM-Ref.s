%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6L9UrwZIqG

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:29 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   52 (  66 expanded)
%              Number of leaves         :   16 (  25 expanded)
%              Depth                    :   16
%              Number of atoms          :  334 ( 456 expanded)
%              Number of equality atoms :   51 (  68 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t26_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
     => ( A = C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
       => ( A = C ) ) ),
    inference('cnf.neg',[status(esa)],[t26_zfmisc_1])).

thf('0',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X12
        = ( k1_tarski @ X11 ) )
      | ( X12 = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('3',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k1_tarski @ X14 ) @ ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf('5',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X12
        = ( k1_tarski @ X11 ) )
      | ( X12 = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('7',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k1_tarski @ X14 ) @ ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf('9',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_C ) )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = X2 )
      | ~ ( r1_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_C ) )
    | ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('13',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = X2 )
      | ~ ( r1_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_C ) )
    | ( k1_xboole_0
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('18',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_C ) )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ ( k1_tarski @ X13 ) )
      | ( X12
       != ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('20',plain,(
    ! [X13: $i] :
      ( r1_tarski @ ( k1_tarski @ X13 ) @ ( k1_tarski @ X13 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','20'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('22',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t25_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        & ( A != B )
        & ( A != C ) ) )).

thf('23',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( X17 = X16 )
      | ( X17 = X18 )
      | ~ ( r1_tarski @ ( k1_tarski @ X17 ) @ ( k2_tarski @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t25_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = sk_C ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( sk_A = X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('32',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','32'])).

thf('34',plain,(
    $false ),
    inference(simplify,[status(thm)],['33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6L9UrwZIqG
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:24:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.19/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.49  % Solved by: fo/fo7.sh
% 0.19/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.49  % done 58 iterations in 0.039s
% 0.19/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.49  % SZS output start Refutation
% 0.19/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.49  thf(t26_zfmisc_1, conjecture,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.19/0.49       ( ( A ) = ( C ) ) ))).
% 0.19/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.49        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.19/0.49          ( ( A ) = ( C ) ) ) )),
% 0.19/0.49    inference('cnf.neg', [status(esa)], [t26_zfmisc_1])).
% 0.19/0.49  thf('0', plain, (((sk_A) != (sk_C))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('1', plain,
% 0.19/0.49      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(l3_zfmisc_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.19/0.49       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.19/0.49  thf('2', plain,
% 0.19/0.49      (![X11 : $i, X12 : $i]:
% 0.19/0.49         (((X12) = (k1_tarski @ X11))
% 0.19/0.49          | ((X12) = (k1_xboole_0))
% 0.19/0.49          | ~ (r1_tarski @ X12 @ (k1_tarski @ X11)))),
% 0.19/0.49      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.19/0.49  thf('3', plain,
% 0.19/0.49      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.19/0.49        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.49  thf(t12_zfmisc_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.19/0.49  thf('4', plain,
% 0.19/0.49      (![X14 : $i, X15 : $i]:
% 0.19/0.49         (r1_tarski @ (k1_tarski @ X14) @ (k2_tarski @ X14 @ X15))),
% 0.19/0.49      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.19/0.49  thf('5', plain,
% 0.19/0.49      (((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))
% 0.19/0.49        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.19/0.49      inference('sup+', [status(thm)], ['3', '4'])).
% 0.19/0.49  thf('6', plain,
% 0.19/0.49      (![X11 : $i, X12 : $i]:
% 0.19/0.49         (((X12) = (k1_tarski @ X11))
% 0.19/0.49          | ((X12) = (k1_xboole_0))
% 0.19/0.49          | ~ (r1_tarski @ X12 @ (k1_tarski @ X11)))),
% 0.19/0.49      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.19/0.49  thf('7', plain,
% 0.19/0.49      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.19/0.49        | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.19/0.49        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_C)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.49  thf('8', plain,
% 0.19/0.49      (![X14 : $i, X15 : $i]:
% 0.19/0.49         (r1_tarski @ (k1_tarski @ X14) @ (k2_tarski @ X14 @ X15))),
% 0.19/0.49      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.19/0.49  thf('9', plain,
% 0.19/0.49      (((r1_tarski @ (k1_tarski @ sk_A) @ k1_xboole_0)
% 0.19/0.49        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_C))
% 0.19/0.49        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.19/0.49      inference('sup+', [status(thm)], ['7', '8'])).
% 0.19/0.49  thf(t28_xboole_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.49  thf('10', plain,
% 0.19/0.49      (![X2 : $i, X3 : $i]:
% 0.19/0.49         (((k3_xboole_0 @ X2 @ X3) = (X2)) | ~ (r1_tarski @ X2 @ X3))),
% 0.19/0.49      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.49  thf('11', plain,
% 0.19/0.49      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.19/0.49        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_C))
% 0.19/0.49        | ((k3_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0)
% 0.19/0.49            = (k1_tarski @ sk_A)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.49  thf(commutativity_k3_xboole_0, axiom,
% 0.19/0.49    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.19/0.49  thf('12', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.49      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.49  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.19/0.49  thf('13', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.19/0.49      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.49  thf('14', plain,
% 0.19/0.49      (![X2 : $i, X3 : $i]:
% 0.19/0.49         (((k3_xboole_0 @ X2 @ X3) = (X2)) | ~ (r1_tarski @ X2 @ X3))),
% 0.19/0.49      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.49  thf('15', plain,
% 0.19/0.49      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.49  thf('16', plain,
% 0.19/0.49      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.49      inference('sup+', [status(thm)], ['12', '15'])).
% 0.19/0.49  thf('17', plain,
% 0.19/0.49      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.19/0.49        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_C))
% 0.19/0.49        | ((k1_xboole_0) = (k1_tarski @ sk_A)))),
% 0.19/0.49      inference('demod', [status(thm)], ['11', '16'])).
% 0.19/0.49  thf('18', plain,
% 0.19/0.49      ((((k1_tarski @ sk_A) = (k1_tarski @ sk_C))
% 0.19/0.49        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.19/0.49      inference('simplify', [status(thm)], ['17'])).
% 0.19/0.49  thf('19', plain,
% 0.19/0.49      (![X12 : $i, X13 : $i]:
% 0.19/0.49         ((r1_tarski @ X12 @ (k1_tarski @ X13)) | ((X12) != (k1_tarski @ X13)))),
% 0.19/0.49      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.19/0.49  thf('20', plain,
% 0.19/0.49      (![X13 : $i]: (r1_tarski @ (k1_tarski @ X13) @ (k1_tarski @ X13))),
% 0.19/0.49      inference('simplify', [status(thm)], ['19'])).
% 0.19/0.49  thf('21', plain,
% 0.19/0.49      (((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))
% 0.19/0.49        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.19/0.49      inference('sup+', [status(thm)], ['18', '20'])).
% 0.19/0.49  thf(t69_enumset1, axiom,
% 0.19/0.49    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.19/0.49  thf('22', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.19/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.49  thf(t25_zfmisc_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.19/0.49          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 0.19/0.49  thf('23', plain,
% 0.19/0.49      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.49         (((X17) = (X16))
% 0.19/0.49          | ((X17) = (X18))
% 0.19/0.49          | ~ (r1_tarski @ (k1_tarski @ X17) @ (k2_tarski @ X16 @ X18)))),
% 0.19/0.49      inference('cnf', [status(esa)], [t25_zfmisc_1])).
% 0.19/0.49  thf('24', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         (~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.19/0.49          | ((X1) = (X0))
% 0.19/0.49          | ((X1) = (X0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.49  thf('25', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         (((X1) = (X0)) | ~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.19/0.49      inference('simplify', [status(thm)], ['24'])).
% 0.19/0.49  thf('26', plain,
% 0.19/0.49      ((((k1_tarski @ sk_A) = (k1_xboole_0)) | ((sk_A) = (sk_C)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['21', '25'])).
% 0.19/0.49  thf('27', plain, (((sk_A) != (sk_C))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('28', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.19/0.49      inference('simplify_reflect-', [status(thm)], ['26', '27'])).
% 0.19/0.49  thf('29', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         (((X1) = (X0)) | ~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.19/0.49      inference('simplify', [status(thm)], ['24'])).
% 0.19/0.49  thf('30', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) | ((sk_A) = (X0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['28', '29'])).
% 0.19/0.49  thf('31', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.19/0.49      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.49  thf('32', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 0.19/0.49      inference('demod', [status(thm)], ['30', '31'])).
% 0.19/0.49  thf('33', plain, (((sk_A) != (sk_A))),
% 0.19/0.49      inference('demod', [status(thm)], ['0', '32'])).
% 0.19/0.49  thf('34', plain, ($false), inference('simplify', [status(thm)], ['33'])).
% 0.19/0.49  
% 0.19/0.49  % SZS output end Refutation
% 0.19/0.49  
% 0.19/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

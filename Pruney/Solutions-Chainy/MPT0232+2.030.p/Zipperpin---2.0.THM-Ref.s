%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.19cksM9mqX

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:37 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   39 (  54 expanded)
%              Number of leaves         :   16 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :  259 ( 414 expanded)
%              Number of equality atoms :   28 (  41 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('2',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) )
    = ( k1_tarski @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
     => ( A = C ) ) )).

thf('4',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( X21 = X20 )
      | ~ ( r1_tarski @ ( k2_tarski @ X21 @ X22 ) @ ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t26_zfmisc_1])).

thf('5',plain,(
    sk_A = sk_C ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    sk_A = sk_C ),
    inference('sup-',[status(thm)],['3','4'])).

thf('7',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['2','5','6'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('8',plain,(
    ! [X14: $i] :
      ( ( k2_tarski @ X14 @ X14 )
      = ( k1_tarski @ X14 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t45_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k2_tarski @ X10 @ X11 ) @ ( k2_tarski @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t45_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t117_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ C @ B @ D @ A ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X9 @ X7 @ X6 @ X8 )
      = ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t117_enumset1])).

thf(l123_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ B @ C @ A @ D ) ) )).

thf('12',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X4 @ X2 @ X3 @ X5 )
      = ( k2_enumset1 @ X2 @ X3 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l123_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X9 @ X7 @ X6 @ X8 )
      = ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t117_enumset1])).

thf(t77_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_enumset1 @ A @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_enumset1 @ X15 @ X15 @ X15 @ X16 )
      = ( k2_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t77_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['7','10','13','16'])).

thf('18',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k1_tarski @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    sk_A = sk_C ),
    inference('sup-',[status(thm)],['3','4'])).

thf('20',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['17','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.19cksM9mqX
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:53:32 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.42/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.62  % Solved by: fo/fo7.sh
% 0.42/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.62  % done 258 iterations in 0.162s
% 0.42/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.62  % SZS output start Refutation
% 0.42/0.62  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.42/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.42/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.42/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.42/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.42/0.62  thf(t27_zfmisc_1, conjecture,
% 0.42/0.62    (![A:$i,B:$i,C:$i]:
% 0.42/0.62     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.42/0.62       ( ( k2_tarski @ A @ B ) = ( k1_tarski @ C ) ) ))).
% 0.42/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.62    (~( ![A:$i,B:$i,C:$i]:
% 0.42/0.62        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.42/0.62          ( ( k2_tarski @ A @ B ) = ( k1_tarski @ C ) ) ) )),
% 0.42/0.62    inference('cnf.neg', [status(esa)], [t27_zfmisc_1])).
% 0.42/0.62  thf('0', plain,
% 0.42/0.62      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(t12_xboole_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.42/0.62  thf('1', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (((k2_xboole_0 @ X1 @ X0) = (X0)) | ~ (r1_tarski @ X1 @ X0))),
% 0.42/0.62      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.42/0.62  thf('2', plain,
% 0.42/0.62      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C))
% 0.42/0.62         = (k1_tarski @ sk_C))),
% 0.42/0.62      inference('sup-', [status(thm)], ['0', '1'])).
% 0.42/0.62  thf('3', plain,
% 0.42/0.62      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(t26_zfmisc_1, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i]:
% 0.42/0.62     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.42/0.62       ( ( A ) = ( C ) ) ))).
% 0.42/0.62  thf('4', plain,
% 0.42/0.62      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.42/0.62         (((X21) = (X20))
% 0.42/0.62          | ~ (r1_tarski @ (k2_tarski @ X21 @ X22) @ (k1_tarski @ X20)))),
% 0.42/0.62      inference('cnf', [status(esa)], [t26_zfmisc_1])).
% 0.42/0.62  thf('5', plain, (((sk_A) = (sk_C))),
% 0.42/0.62      inference('sup-', [status(thm)], ['3', '4'])).
% 0.42/0.62  thf('6', plain, (((sk_A) = (sk_C))),
% 0.42/0.62      inference('sup-', [status(thm)], ['3', '4'])).
% 0.42/0.62  thf('7', plain,
% 0.42/0.62      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_A))
% 0.42/0.62         = (k1_tarski @ sk_A))),
% 0.42/0.62      inference('demod', [status(thm)], ['2', '5', '6'])).
% 0.42/0.62  thf(t69_enumset1, axiom,
% 0.42/0.62    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.42/0.62  thf('8', plain, (![X14 : $i]: ((k2_tarski @ X14 @ X14) = (k1_tarski @ X14))),
% 0.42/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.42/0.62  thf(t45_enumset1, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.62     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.42/0.62       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.42/0.62  thf('9', plain,
% 0.42/0.62      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.42/0.62         ((k2_enumset1 @ X10 @ X11 @ X12 @ X13)
% 0.42/0.62           = (k2_xboole_0 @ (k2_tarski @ X10 @ X11) @ (k2_tarski @ X12 @ X13)))),
% 0.42/0.62      inference('cnf', [status(esa)], [t45_enumset1])).
% 0.42/0.62  thf('10', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0)
% 0.42/0.62           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)))),
% 0.42/0.62      inference('sup+', [status(thm)], ['8', '9'])).
% 0.42/0.62  thf(t117_enumset1, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.62     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ C @ B @ D @ A ) ))).
% 0.42/0.62  thf('11', plain,
% 0.42/0.62      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.42/0.62         ((k2_enumset1 @ X9 @ X7 @ X6 @ X8) = (k2_enumset1 @ X6 @ X7 @ X8 @ X9))),
% 0.42/0.62      inference('cnf', [status(esa)], [t117_enumset1])).
% 0.42/0.62  thf(l123_enumset1, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.62     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ C @ A @ D ) ))).
% 0.42/0.62  thf('12', plain,
% 0.42/0.62      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.42/0.62         ((k2_enumset1 @ X4 @ X2 @ X3 @ X5) = (k2_enumset1 @ X2 @ X3 @ X4 @ X5))),
% 0.42/0.62      inference('cnf', [status(esa)], [l123_enumset1])).
% 0.42/0.62  thf('13', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.42/0.62         ((k2_enumset1 @ X0 @ X1 @ X2 @ X3) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.42/0.62      inference('sup+', [status(thm)], ['11', '12'])).
% 0.42/0.62  thf('14', plain,
% 0.42/0.62      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.42/0.62         ((k2_enumset1 @ X9 @ X7 @ X6 @ X8) = (k2_enumset1 @ X6 @ X7 @ X8 @ X9))),
% 0.42/0.62      inference('cnf', [status(esa)], [t117_enumset1])).
% 0.42/0.62  thf(t77_enumset1, axiom,
% 0.42/0.62    (![A:$i,B:$i]: ( ( k2_enumset1 @ A @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.42/0.62  thf('15', plain,
% 0.42/0.62      (![X15 : $i, X16 : $i]:
% 0.42/0.62         ((k2_enumset1 @ X15 @ X15 @ X15 @ X16) = (k2_tarski @ X15 @ X16))),
% 0.42/0.62      inference('cnf', [status(esa)], [t77_enumset1])).
% 0.42/0.62  thf('16', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         ((k2_enumset1 @ X0 @ X0 @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.42/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.42/0.62  thf('17', plain, (((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_A))),
% 0.42/0.62      inference('demod', [status(thm)], ['7', '10', '13', '16'])).
% 0.42/0.62  thf('18', plain, (((k2_tarski @ sk_A @ sk_B) != (k1_tarski @ sk_C))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('19', plain, (((sk_A) = (sk_C))),
% 0.42/0.62      inference('sup-', [status(thm)], ['3', '4'])).
% 0.42/0.62  thf('20', plain, (((k2_tarski @ sk_A @ sk_B) != (k1_tarski @ sk_A))),
% 0.42/0.62      inference('demod', [status(thm)], ['18', '19'])).
% 0.42/0.62  thf('21', plain, ($false),
% 0.42/0.62      inference('simplify_reflect-', [status(thm)], ['17', '20'])).
% 0.42/0.62  
% 0.42/0.62  % SZS output end Refutation
% 0.42/0.62  
% 0.46/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

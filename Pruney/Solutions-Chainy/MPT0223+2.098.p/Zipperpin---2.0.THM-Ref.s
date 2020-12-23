%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kGEBeuCR7L

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   39 (  63 expanded)
%              Number of leaves         :   13 (  23 expanded)
%              Depth                    :   11
%              Number of atoms          :  295 ( 542 expanded)
%              Number of equality atoms :   32 (  65 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t18_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t18_zfmisc_1])).

thf('0',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t23_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X2 @ X3 ) @ ( k3_xboole_0 @ X2 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X13 ) @ ( k1_tarski @ X14 ) )
      | ( X13 = X14 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf(t78_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ A @ C ) ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_xboole_0 @ X8 @ X9 )
      | ( ( k3_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) )
        = ( k3_xboole_0 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t78_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 = X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) )
        = ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) )
      | ( sk_A = sk_B ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('9',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ sk_A )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X13 ) @ ( k1_tarski @ X14 ) )
      | ( X13 = X14 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf(t76_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_xboole_0 @ X5 @ X6 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X7 @ X5 ) @ ( k3_xboole_0 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t76_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 = X0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k1_tarski @ X1 ) ) @ ( k3_xboole_0 @ X2 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_xboole_0 @ X5 @ X6 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X7 @ X5 ) @ ( k3_xboole_0 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t76_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X2 = X0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X3 @ ( k3_xboole_0 @ X1 @ ( k1_tarski @ X2 ) ) ) @ ( k3_xboole_0 @ X3 @ ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ X1 @ ( k1_tarski @ X2 ) ) ) @ ( k1_tarski @ sk_A ) )
      | ( X2 = X0 ) ) ),
    inference('sup+',[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ sk_A )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('18',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      | ( X2 = X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t16_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        & ( A = B ) ) )).

thf('19',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X11 ) @ ( k1_tarski @ X12 ) )
      | ( X11 != X12 ) ) ),
    inference(cnf,[status(esa)],[t16_zfmisc_1])).

thf('20',plain,(
    ! [X12: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X12 ) @ ( k1_tarski @ X12 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X2: $i] : ( X2 = X0 ) ),
    inference(clc,[status(thm)],['18','20'])).

thf('22',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] : ( X0 != sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    $false ),
    inference(simplify,[status(thm)],['23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kGEBeuCR7L
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:54:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.21/0.34  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 24 iterations in 0.022s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.50  thf(t18_zfmisc_1, conjecture,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.50         ( k1_tarski @ A ) ) =>
% 0.21/0.50       ( ( A ) = ( B ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i]:
% 0.21/0.50        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.50            ( k1_tarski @ A ) ) =>
% 0.21/0.50          ( ( A ) = ( B ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t18_zfmisc_1])).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.50         = (k1_tarski @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t23_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.21/0.50       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.50         ((k3_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ X4))
% 0.21/0.50           = (k2_xboole_0 @ (k3_xboole_0 @ X2 @ X3) @ (k3_xboole_0 @ X2 @ X4)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t23_xboole_1])).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.21/0.50           (k2_xboole_0 @ (k1_tarski @ sk_B) @ X0))
% 0.21/0.50           = (k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.21/0.50              (k3_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 0.21/0.50      inference('sup+', [status(thm)], ['0', '1'])).
% 0.21/0.50  thf(t22_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) = (X0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.21/0.50           (k2_xboole_0 @ (k1_tarski @ sk_B) @ X0)) = (k1_tarski @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.50  thf(t17_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( A ) != ( B ) ) =>
% 0.21/0.50       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X13 : $i, X14 : $i]:
% 0.21/0.50         ((r1_xboole_0 @ (k1_tarski @ X13) @ (k1_tarski @ X14))
% 0.21/0.50          | ((X13) = (X14)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.21/0.50  thf(t78_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( r1_xboole_0 @ A @ B ) =>
% 0.21/0.50       ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.21/0.50         ( k3_xboole_0 @ A @ C ) ) ))).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.50         (~ (r1_xboole_0 @ X8 @ X9)
% 0.21/0.50          | ((k3_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10))
% 0.21/0.50              = (k3_xboole_0 @ X8 @ X10)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t78_xboole_1])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (((X1) = (X0))
% 0.21/0.50          | ((k3_xboole_0 @ (k1_tarski @ X1) @ 
% 0.21/0.50              (k2_xboole_0 @ (k1_tarski @ X0) @ X2))
% 0.21/0.50              = (k3_xboole_0 @ (k1_tarski @ X1) @ X2)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((k1_tarski @ sk_A) = (k3_xboole_0 @ (k1_tarski @ sk_A) @ X0))
% 0.21/0.50          | ((sk_A) = (sk_B)))),
% 0.21/0.50      inference('sup+', [status(thm)], ['4', '7'])).
% 0.21/0.50  thf('9', plain, (((sk_A) != (sk_B))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k1_tarski @ sk_A) = (k3_xboole_0 @ (k1_tarski @ sk_A) @ X0))),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (![X13 : $i, X14 : $i]:
% 0.21/0.50         ((r1_xboole_0 @ (k1_tarski @ X13) @ (k1_tarski @ X14))
% 0.21/0.50          | ((X13) = (X14)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.21/0.50  thf(t76_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( r1_xboole_0 @ A @ B ) =>
% 0.21/0.50       ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ))).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.50         (~ (r1_xboole_0 @ X5 @ X6)
% 0.21/0.50          | (r1_xboole_0 @ (k3_xboole_0 @ X7 @ X5) @ (k3_xboole_0 @ X7 @ X6)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t76_xboole_1])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (((X1) = (X0))
% 0.21/0.50          | (r1_xboole_0 @ (k3_xboole_0 @ X2 @ (k1_tarski @ X1)) @ 
% 0.21/0.50             (k3_xboole_0 @ X2 @ (k1_tarski @ X0))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.50         (~ (r1_xboole_0 @ X5 @ X6)
% 0.21/0.50          | (r1_xboole_0 @ (k3_xboole_0 @ X7 @ X5) @ (k3_xboole_0 @ X7 @ X6)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t76_xboole_1])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.50         (((X2) = (X0))
% 0.21/0.50          | (r1_xboole_0 @ 
% 0.21/0.50             (k3_xboole_0 @ X3 @ (k3_xboole_0 @ X1 @ (k1_tarski @ X2))) @ 
% 0.21/0.50             (k3_xboole_0 @ X3 @ (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         ((r1_xboole_0 @ 
% 0.21/0.50           (k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.21/0.50            (k3_xboole_0 @ X1 @ (k1_tarski @ X2))) @ 
% 0.21/0.50           (k1_tarski @ sk_A))
% 0.21/0.50          | ((X2) = (X0)))),
% 0.21/0.50      inference('sup+', [status(thm)], ['10', '15'])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k1_tarski @ sk_A) = (k3_xboole_0 @ (k1_tarski @ sk_A) @ X0))),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (![X0 : $i, X2 : $i]:
% 0.21/0.50         ((r1_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.21/0.50          | ((X2) = (X0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.50  thf(t16_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) & 
% 0.21/0.50          ( ( A ) = ( B ) ) ) ))).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (![X11 : $i, X12 : $i]:
% 0.21/0.50         (~ (r1_xboole_0 @ (k1_tarski @ X11) @ (k1_tarski @ X12))
% 0.21/0.50          | ((X11) != (X12)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t16_zfmisc_1])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (![X12 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X12) @ (k1_tarski @ X12))),
% 0.21/0.50      inference('simplify', [status(thm)], ['19'])).
% 0.21/0.50  thf('21', plain, (![X0 : $i, X2 : $i]: ((X2) = (X0))),
% 0.21/0.50      inference('clc', [status(thm)], ['18', '20'])).
% 0.21/0.50  thf('22', plain, (((sk_A) != (sk_B))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('23', plain, (![X0 : $i]: ((X0) != (sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.50  thf('24', plain, ($false), inference('simplify', [status(thm)], ['23'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

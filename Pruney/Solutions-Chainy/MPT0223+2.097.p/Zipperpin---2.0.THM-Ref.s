%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gVpFhsBChq

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:43 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   34 (  38 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :  218 ( 256 expanded)
%              Number of equality atoms :   24 (  30 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) )
      = ( k4_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['4','5','6'])).

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

thf('8',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('9',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X23 ) @ ( k1_tarski @ X24 ) )
      | ( X23 = X24 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf(t76_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_xboole_0 @ X12 @ X13 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X14 @ X12 ) @ ( k3_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t76_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 = X0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k1_tarski @ X1 ) ) @ ( k3_xboole_0 @ X2 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ X0 ) ) )
      | ( sk_B = X0 ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,
    ( ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
    | ( sk_B = sk_A ) ),
    inference('sup+',[status(thm)],['7','12'])).

thf('14',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

thf(t16_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        & ( A = B ) ) )).

thf('16',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X21 ) @ ( k1_tarski @ X22 ) )
      | ( X21 != X22 ) ) ),
    inference(cnf,[status(esa)],[t16_zfmisc_1])).

thf('17',plain,(
    ! [X22: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X22 ) @ ( k1_tarski @ X22 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    $false ),
    inference('sup-',[status(thm)],['15','17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gVpFhsBChq
% 0.13/0.32  % Computer   : n022.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 15:17:11 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.32  % Running portfolio for 600 s
% 0.13/0.32  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.32  % Number of cores: 8
% 0.13/0.33  % Python version: Python 3.6.8
% 0.13/0.33  % Running in FO mode
% 0.18/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.18/0.50  % Solved by: fo/fo7.sh
% 0.18/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.50  % done 100 iterations in 0.063s
% 0.18/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.18/0.50  % SZS output start Refutation
% 0.18/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.18/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.18/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.18/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.18/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.18/0.50  thf(t21_xboole_1, axiom,
% 0.18/0.50    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.18/0.50  thf('0', plain,
% 0.18/0.50      (![X0 : $i, X1 : $i]:
% 0.18/0.50         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) = (X0))),
% 0.18/0.50      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.18/0.50  thf(t47_xboole_1, axiom,
% 0.18/0.50    (![A:$i,B:$i]:
% 0.18/0.50     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.18/0.50  thf('1', plain,
% 0.18/0.50      (![X5 : $i, X6 : $i]:
% 0.18/0.50         ((k4_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6))
% 0.18/0.50           = (k4_xboole_0 @ X5 @ X6))),
% 0.18/0.50      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.18/0.50  thf('2', plain,
% 0.18/0.50      (![X0 : $i, X1 : $i]:
% 0.18/0.50         ((k4_xboole_0 @ X0 @ X0)
% 0.18/0.50           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.18/0.50      inference('sup+', [status(thm)], ['0', '1'])).
% 0.18/0.50  thf(t48_xboole_1, axiom,
% 0.18/0.50    (![A:$i,B:$i]:
% 0.18/0.50     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.18/0.50  thf('3', plain,
% 0.18/0.50      (![X7 : $i, X8 : $i]:
% 0.18/0.50         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.18/0.50           = (k3_xboole_0 @ X7 @ X8))),
% 0.18/0.50      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.18/0.50  thf('4', plain,
% 0.18/0.50      (![X0 : $i, X1 : $i]:
% 0.18/0.50         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0))
% 0.18/0.50           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.18/0.50      inference('sup+', [status(thm)], ['2', '3'])).
% 0.18/0.50  thf('5', plain,
% 0.18/0.50      (![X7 : $i, X8 : $i]:
% 0.18/0.50         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.18/0.50           = (k3_xboole_0 @ X7 @ X8))),
% 0.18/0.50      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.18/0.50  thf('6', plain,
% 0.18/0.50      (![X0 : $i, X1 : $i]:
% 0.18/0.50         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) = (X0))),
% 0.18/0.50      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.18/0.50  thf('7', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.18/0.50      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.18/0.50  thf(t18_zfmisc_1, conjecture,
% 0.18/0.50    (![A:$i,B:$i]:
% 0.18/0.50     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.18/0.50         ( k1_tarski @ A ) ) =>
% 0.18/0.50       ( ( A ) = ( B ) ) ))).
% 0.18/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.50    (~( ![A:$i,B:$i]:
% 0.18/0.50        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.18/0.50            ( k1_tarski @ A ) ) =>
% 0.18/0.50          ( ( A ) = ( B ) ) ) )),
% 0.18/0.50    inference('cnf.neg', [status(esa)], [t18_zfmisc_1])).
% 0.18/0.50  thf('8', plain,
% 0.18/0.50      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.18/0.50         = (k1_tarski @ sk_A))),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf(t17_zfmisc_1, axiom,
% 0.18/0.50    (![A:$i,B:$i]:
% 0.18/0.50     ( ( ( A ) != ( B ) ) =>
% 0.18/0.50       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.18/0.50  thf('9', plain,
% 0.18/0.50      (![X23 : $i, X24 : $i]:
% 0.18/0.50         ((r1_xboole_0 @ (k1_tarski @ X23) @ (k1_tarski @ X24))
% 0.18/0.50          | ((X23) = (X24)))),
% 0.18/0.50      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.18/0.50  thf(t76_xboole_1, axiom,
% 0.18/0.50    (![A:$i,B:$i,C:$i]:
% 0.18/0.50     ( ( r1_xboole_0 @ A @ B ) =>
% 0.18/0.50       ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ))).
% 0.18/0.50  thf('10', plain,
% 0.18/0.50      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.18/0.50         (~ (r1_xboole_0 @ X12 @ X13)
% 0.18/0.50          | (r1_xboole_0 @ (k3_xboole_0 @ X14 @ X12) @ 
% 0.18/0.50             (k3_xboole_0 @ X14 @ X13)))),
% 0.18/0.50      inference('cnf', [status(esa)], [t76_xboole_1])).
% 0.18/0.50  thf('11', plain,
% 0.18/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.50         (((X1) = (X0))
% 0.18/0.50          | (r1_xboole_0 @ (k3_xboole_0 @ X2 @ (k1_tarski @ X1)) @ 
% 0.18/0.50             (k3_xboole_0 @ X2 @ (k1_tarski @ X0))))),
% 0.18/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.18/0.50  thf('12', plain,
% 0.18/0.50      (![X0 : $i]:
% 0.18/0.50         ((r1_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.18/0.50           (k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ X0)))
% 0.18/0.50          | ((sk_B) = (X0)))),
% 0.18/0.50      inference('sup+', [status(thm)], ['8', '11'])).
% 0.18/0.50  thf('13', plain,
% 0.18/0.50      (((r1_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.18/0.50        | ((sk_B) = (sk_A)))),
% 0.18/0.50      inference('sup+', [status(thm)], ['7', '12'])).
% 0.18/0.50  thf('14', plain, (((sk_A) != (sk_B))),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('15', plain, ((r1_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))),
% 0.18/0.50      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 0.18/0.50  thf(t16_zfmisc_1, axiom,
% 0.18/0.50    (![A:$i,B:$i]:
% 0.18/0.50     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) & 
% 0.18/0.50          ( ( A ) = ( B ) ) ) ))).
% 0.18/0.50  thf('16', plain,
% 0.18/0.50      (![X21 : $i, X22 : $i]:
% 0.18/0.50         (~ (r1_xboole_0 @ (k1_tarski @ X21) @ (k1_tarski @ X22))
% 0.18/0.50          | ((X21) != (X22)))),
% 0.18/0.50      inference('cnf', [status(esa)], [t16_zfmisc_1])).
% 0.18/0.50  thf('17', plain,
% 0.18/0.50      (![X22 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X22) @ (k1_tarski @ X22))),
% 0.18/0.50      inference('simplify', [status(thm)], ['16'])).
% 0.18/0.50  thf('18', plain, ($false), inference('sup-', [status(thm)], ['15', '17'])).
% 0.18/0.50  
% 0.18/0.50  % SZS output end Refutation
% 0.18/0.50  
% 0.18/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

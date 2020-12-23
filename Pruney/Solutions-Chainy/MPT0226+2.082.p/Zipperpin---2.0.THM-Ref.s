%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RsXDeTg51c

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:01 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   31 (  52 expanded)
%              Number of leaves         :   12 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :  156 ( 345 expanded)
%              Number of equality atoms :   29 (  67 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X11 != X10 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X11 ) @ ( k1_tarski @ X10 ) )
       != ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('6',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X10 ) @ ( k1_tarski @ X10 ) )
     != ( k1_tarski @ X10 ) ) ),
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

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('14',plain,(
    ! [X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X3 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,(
    $false ),
    inference(simplify,[status(thm)],['16'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RsXDeTg51c
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:43:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.45  % Solved by: fo/fo7.sh
% 0.19/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.45  % done 13 iterations in 0.012s
% 0.19/0.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.45  % SZS output start Refutation
% 0.19/0.45  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.45  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.45  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.45  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.19/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.45  thf(t21_zfmisc_1, conjecture,
% 0.19/0.45    (![A:$i,B:$i]:
% 0.19/0.45     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.19/0.45         ( k1_xboole_0 ) ) =>
% 0.19/0.45       ( ( A ) = ( B ) ) ))).
% 0.19/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.45    (~( ![A:$i,B:$i]:
% 0.19/0.45        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.19/0.45            ( k1_xboole_0 ) ) =>
% 0.19/0.45          ( ( A ) = ( B ) ) ) )),
% 0.19/0.45    inference('cnf.neg', [status(esa)], [t21_zfmisc_1])).
% 0.19/0.45  thf('0', plain,
% 0.19/0.45      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf(t20_zfmisc_1, axiom,
% 0.19/0.45    (![A:$i,B:$i]:
% 0.19/0.45     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.19/0.45         ( k1_tarski @ A ) ) <=>
% 0.19/0.45       ( ( A ) != ( B ) ) ))).
% 0.19/0.45  thf('1', plain,
% 0.19/0.45      (![X11 : $i, X12 : $i]:
% 0.19/0.45         (((k4_xboole_0 @ (k1_tarski @ X11) @ (k1_tarski @ X12))
% 0.19/0.45            = (k1_tarski @ X11))
% 0.19/0.45          | ((X11) = (X12)))),
% 0.19/0.45      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.19/0.45  thf('2', plain, ((((k1_xboole_0) = (k1_tarski @ sk_A)) | ((sk_A) = (sk_B)))),
% 0.19/0.45      inference('sup+', [status(thm)], ['0', '1'])).
% 0.19/0.45  thf('3', plain, (((sk_A) != (sk_B))),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('4', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.19/0.45      inference('simplify_reflect-', [status(thm)], ['2', '3'])).
% 0.19/0.45  thf('5', plain,
% 0.19/0.45      (![X10 : $i, X11 : $i]:
% 0.19/0.45         (((X11) != (X10))
% 0.19/0.45          | ((k4_xboole_0 @ (k1_tarski @ X11) @ (k1_tarski @ X10))
% 0.19/0.45              != (k1_tarski @ X11)))),
% 0.19/0.45      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.19/0.45  thf('6', plain,
% 0.19/0.45      (![X10 : $i]:
% 0.19/0.45         ((k4_xboole_0 @ (k1_tarski @ X10) @ (k1_tarski @ X10))
% 0.19/0.45           != (k1_tarski @ X10))),
% 0.19/0.45      inference('simplify', [status(thm)], ['5'])).
% 0.19/0.45  thf('7', plain,
% 0.19/0.45      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0) != (k1_tarski @ sk_A))),
% 0.19/0.45      inference('sup-', [status(thm)], ['4', '6'])).
% 0.19/0.45  thf('8', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.19/0.45      inference('simplify_reflect-', [status(thm)], ['2', '3'])).
% 0.19/0.45  thf('9', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.19/0.45      inference('simplify_reflect-', [status(thm)], ['2', '3'])).
% 0.19/0.45  thf('10', plain,
% 0.19/0.45      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0))),
% 0.19/0.45      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.19/0.45  thf(idempotence_k3_xboole_0, axiom,
% 0.19/0.45    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.19/0.45  thf('11', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.19/0.45      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.19/0.45  thf(t100_xboole_1, axiom,
% 0.19/0.45    (![A:$i,B:$i]:
% 0.19/0.45     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.19/0.45  thf('12', plain,
% 0.19/0.45      (![X1 : $i, X2 : $i]:
% 0.19/0.45         ((k4_xboole_0 @ X1 @ X2)
% 0.19/0.45           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.19/0.45      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.19/0.45  thf('13', plain,
% 0.19/0.45      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.19/0.45      inference('sup+', [status(thm)], ['11', '12'])).
% 0.19/0.45  thf(t92_xboole_1, axiom,
% 0.19/0.45    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.19/0.45  thf('14', plain, (![X3 : $i]: ((k5_xboole_0 @ X3 @ X3) = (k1_xboole_0))),
% 0.19/0.45      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.19/0.45  thf('15', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.19/0.45      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.45  thf('16', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.19/0.45      inference('demod', [status(thm)], ['10', '15'])).
% 0.19/0.45  thf('17', plain, ($false), inference('simplify', [status(thm)], ['16'])).
% 0.19/0.45  
% 0.19/0.45  % SZS output end Refutation
% 0.19/0.45  
% 0.19/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

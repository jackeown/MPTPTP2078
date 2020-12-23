%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gYIRyiMKDV

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:24 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   16 (  16 expanded)
%              Number of leaves         :    9 (   9 expanded)
%              Depth                    :    4
%              Number of atoms          :   76 (  76 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t14_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t14_zfmisc_1])).

thf('0',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k1_tarski @ X14 ) @ ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_xboole_0 @ X5 @ X4 )
        = X4 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    $false ),
    inference(simplify,[status(thm)],['4'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gYIRyiMKDV
% 0.15/0.37  % Computer   : n019.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 17:39:52 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.23/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.50  % Solved by: fo/fo7.sh
% 0.23/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.50  % done 14 iterations in 0.013s
% 0.23/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.50  % SZS output start Refutation
% 0.23/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.23/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.23/0.50  thf(t14_zfmisc_1, conjecture,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.23/0.50       ( k2_tarski @ A @ B ) ))).
% 0.23/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.50    (~( ![A:$i,B:$i]:
% 0.23/0.50        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.23/0.50          ( k2_tarski @ A @ B ) ) )),
% 0.23/0.50    inference('cnf.neg', [status(esa)], [t14_zfmisc_1])).
% 0.23/0.50  thf('0', plain,
% 0.23/0.50      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_A @ sk_B))
% 0.23/0.50         != (k2_tarski @ sk_A @ sk_B))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf(t12_zfmisc_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.23/0.50  thf('1', plain,
% 0.23/0.50      (![X14 : $i, X15 : $i]:
% 0.23/0.50         (r1_tarski @ (k1_tarski @ X14) @ (k2_tarski @ X14 @ X15))),
% 0.23/0.50      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.23/0.50  thf(t12_xboole_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.23/0.50  thf('2', plain,
% 0.23/0.50      (![X4 : $i, X5 : $i]:
% 0.23/0.50         (((k2_xboole_0 @ X5 @ X4) = (X4)) | ~ (r1_tarski @ X5 @ X4))),
% 0.23/0.50      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.23/0.50  thf('3', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i]:
% 0.23/0.50         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.23/0.50           = (k2_tarski @ X1 @ X0))),
% 0.23/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.50  thf('4', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.23/0.50      inference('demod', [status(thm)], ['0', '3'])).
% 0.23/0.50  thf('5', plain, ($false), inference('simplify', [status(thm)], ['4'])).
% 0.23/0.50  
% 0.23/0.50  % SZS output end Refutation
% 0.23/0.50  
% 0.23/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

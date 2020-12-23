%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CKQub0egBe

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:49 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   17 (  21 expanded)
%              Number of leaves         :    7 (   9 expanded)
%              Depth                    :    6
%              Number of atoms          :   73 ( 105 expanded)
%              Number of equality atoms :   14 (  22 expanded)
%              Maximal formula depth    :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t15_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ A @ B )
        = k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_xboole_0 @ A @ B )
          = k1_xboole_0 )
       => ( A = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t15_xboole_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X2 ) )
      = ( k2_xboole_0 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('3',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('5',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup+',[status(thm)],['0','5'])).

thf('7',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CKQub0egBe
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:38:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.47  % Solved by: fo/fo7.sh
% 0.22/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.47  % done 4 iterations in 0.006s
% 0.22/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.47  % SZS output start Refutation
% 0.22/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.47  thf(t15_xboole_1, conjecture,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( ( k2_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) =>
% 0.22/0.47       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.47    (~( ![A:$i,B:$i]:
% 0.22/0.47        ( ( ( k2_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) =>
% 0.22/0.47          ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.22/0.47    inference('cnf.neg', [status(esa)], [t15_xboole_1])).
% 0.22/0.47  thf('0', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('1', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf(t6_xboole_1, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.47  thf('2', plain,
% 0.22/0.47      (![X1 : $i, X2 : $i]:
% 0.22/0.47         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X2))
% 0.22/0.47           = (k2_xboole_0 @ X1 @ X2))),
% 0.22/0.47      inference('cnf', [status(esa)], [t6_xboole_1])).
% 0.22/0.47  thf('3', plain,
% 0.22/0.47      (((k2_xboole_0 @ sk_A @ k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.47      inference('sup+', [status(thm)], ['1', '2'])).
% 0.22/0.47  thf(t1_boole, axiom,
% 0.22/0.47    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.47  thf('4', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.22/0.47      inference('cnf', [status(esa)], [t1_boole])).
% 0.22/0.47  thf('5', plain, (((sk_A) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.47      inference('demod', [status(thm)], ['3', '4'])).
% 0.22/0.47  thf('6', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.47      inference('sup+', [status(thm)], ['0', '5'])).
% 0.22/0.47  thf('7', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('8', plain, ($false),
% 0.22/0.47      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.22/0.47  
% 0.22/0.47  % SZS output end Refutation
% 0.22/0.47  
% 0.22/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

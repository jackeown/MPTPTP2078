%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VeQK3nj9yQ

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:03 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   15 (  15 expanded)
%              Number of leaves         :    9 (   9 expanded)
%              Depth                    :    3
%              Number of atoms          :   53 (  53 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    7 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t12_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_tarski @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    $false ),
    inference(demod,[status(thm)],['0','3'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VeQK3nj9yQ
% 0.14/0.37  % Computer   : n009.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 19:48:11 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.24/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.49  % Solved by: fo/fo7.sh
% 0.24/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.49  % done 5 iterations in 0.007s
% 0.24/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.49  % SZS output start Refutation
% 0.24/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.24/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.24/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.24/0.49  thf(t12_zfmisc_1, conjecture,
% 0.24/0.49    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.24/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.49    (~( ![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )),
% 0.24/0.49    inference('cnf.neg', [status(esa)], [t12_zfmisc_1])).
% 0.24/0.49  thf('0', plain,
% 0.24/0.49      (~ (r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_A @ sk_B))),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf(t41_enumset1, axiom,
% 0.24/0.49    (![A:$i,B:$i]:
% 0.24/0.49     ( ( k2_tarski @ A @ B ) =
% 0.24/0.49       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.24/0.49  thf('1', plain,
% 0.24/0.49      (![X2 : $i, X3 : $i]:
% 0.24/0.49         ((k2_tarski @ X2 @ X3)
% 0.24/0.49           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k1_tarski @ X3)))),
% 0.24/0.49      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.24/0.49  thf(t7_xboole_1, axiom,
% 0.24/0.49    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.24/0.49  thf('2', plain,
% 0.24/0.49      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X0 @ X1))),
% 0.24/0.49      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.24/0.49  thf('3', plain,
% 0.24/0.49      (![X0 : $i, X1 : $i]:
% 0.24/0.49         (r1_tarski @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.24/0.49      inference('sup+', [status(thm)], ['1', '2'])).
% 0.24/0.49  thf('4', plain, ($false), inference('demod', [status(thm)], ['0', '3'])).
% 0.24/0.49  
% 0.24/0.49  % SZS output end Refutation
% 0.24/0.49  
% 0.24/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.m9t3M7aWXz

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:23 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   13 (  15 expanded)
%              Number of leaves         :    7 (   8 expanded)
%              Depth                    :    4
%              Number of atoms          :   58 (  78 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t52_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
          = ( k1_tarski @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l31_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X3 @ ( k1_tarski @ X2 ) )
        = ( k1_tarski @ X2 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('2',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['2','3'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.m9t3M7aWXz
% 0.15/0.39  % Computer   : n025.cluster.edu
% 0.15/0.39  % Model      : x86_64 x86_64
% 0.15/0.39  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.39  % Memory     : 8042.1875MB
% 0.15/0.39  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.39  % CPULimit   : 60
% 0.15/0.39  % DateTime   : Tue Dec  1 11:06:51 EST 2020
% 0.15/0.39  % CPUTime    : 
% 0.15/0.39  % Running portfolio for 600 s
% 0.15/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.39  % Number of cores: 8
% 0.15/0.39  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 0.25/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.49  % Solved by: fo/fo7.sh
% 0.25/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.49  % done 3 iterations in 0.005s
% 0.25/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.49  % SZS output start Refutation
% 0.25/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.25/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.25/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.25/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.25/0.49  thf(t52_zfmisc_1, conjecture,
% 0.25/0.49    (![A:$i,B:$i]:
% 0.25/0.49     ( ( r2_hidden @ A @ B ) =>
% 0.25/0.49       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 0.25/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.49    (~( ![A:$i,B:$i]:
% 0.25/0.49        ( ( r2_hidden @ A @ B ) =>
% 0.25/0.49          ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ) )),
% 0.25/0.49    inference('cnf.neg', [status(esa)], [t52_zfmisc_1])).
% 0.25/0.49  thf('0', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.25/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.49  thf(l31_zfmisc_1, axiom,
% 0.25/0.49    (![A:$i,B:$i]:
% 0.25/0.49     ( ( r2_hidden @ A @ B ) =>
% 0.25/0.49       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 0.25/0.49  thf('1', plain,
% 0.25/0.49      (![X2 : $i, X3 : $i]:
% 0.25/0.49         (((k3_xboole_0 @ X3 @ (k1_tarski @ X2)) = (k1_tarski @ X2))
% 0.25/0.49          | ~ (r2_hidden @ X2 @ X3))),
% 0.25/0.49      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 0.25/0.49  thf('2', plain,
% 0.25/0.49      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.25/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.25/0.49  thf('3', plain,
% 0.25/0.49      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (k1_tarski @ sk_A))),
% 0.25/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.49  thf('4', plain, ($false),
% 0.25/0.49      inference('simplify_reflect-', [status(thm)], ['2', '3'])).
% 0.25/0.49  
% 0.25/0.49  % SZS output end Refutation
% 0.25/0.49  
% 0.25/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

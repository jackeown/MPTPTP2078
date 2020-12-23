%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RUkYIDWoM1

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:35 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   20 (  22 expanded)
%              Number of leaves         :   10 (  11 expanded)
%              Depth                    :    5
%              Number of atoms          :   99 ( 121 expanded)
%              Number of equality atoms :    9 (  11 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('0',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X7 ) @ X8 )
      | ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t58_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
      | ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
        | ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t58_zfmisc_1])).

thf('1',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(l31_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X10 @ ( k1_tarski @ X9 ) )
        = ( k1_tarski @ X9 ) )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('7',plain,(
    ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['4','7'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RUkYIDWoM1
% 0.10/0.30  % Computer   : n019.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % DateTime   : Tue Dec  1 09:46:07 EST 2020
% 0.10/0.31  % CPUTime    : 
% 0.10/0.31  % Running portfolio for 600 s
% 0.10/0.31  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.10/0.31  % Number of cores: 8
% 0.10/0.31  % Python version: Python 3.6.8
% 0.17/0.31  % Running in FO mode
% 0.17/0.42  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.17/0.42  % Solved by: fo/fo7.sh
% 0.17/0.42  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.17/0.42  % done 11 iterations in 0.011s
% 0.17/0.42  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.17/0.42  % SZS output start Refutation
% 0.17/0.42  thf(sk_B_type, type, sk_B: $i).
% 0.17/0.42  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.17/0.42  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.17/0.42  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.17/0.42  thf(sk_A_type, type, sk_A: $i).
% 0.17/0.42  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.17/0.42  thf(l27_zfmisc_1, axiom,
% 0.17/0.42    (![A:$i,B:$i]:
% 0.17/0.42     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.17/0.42  thf('0', plain,
% 0.17/0.42      (![X7 : $i, X8 : $i]:
% 0.17/0.42         ((r1_xboole_0 @ (k1_tarski @ X7) @ X8) | (r2_hidden @ X7 @ X8))),
% 0.17/0.42      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.17/0.42  thf(t58_zfmisc_1, conjecture,
% 0.17/0.42    (![A:$i,B:$i]:
% 0.17/0.42     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.17/0.42       ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.17/0.42  thf(zf_stmt_0, negated_conjecture,
% 0.17/0.42    (~( ![A:$i,B:$i]:
% 0.17/0.42        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.17/0.42          ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )),
% 0.17/0.42    inference('cnf.neg', [status(esa)], [t58_zfmisc_1])).
% 0.17/0.42  thf('1', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)),
% 0.17/0.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.42  thf('2', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.17/0.42      inference('sup-', [status(thm)], ['0', '1'])).
% 0.17/0.42  thf(l31_zfmisc_1, axiom,
% 0.17/0.42    (![A:$i,B:$i]:
% 0.17/0.42     ( ( r2_hidden @ A @ B ) =>
% 0.17/0.42       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 0.17/0.42  thf('3', plain,
% 0.17/0.42      (![X9 : $i, X10 : $i]:
% 0.17/0.42         (((k3_xboole_0 @ X10 @ (k1_tarski @ X9)) = (k1_tarski @ X9))
% 0.17/0.42          | ~ (r2_hidden @ X9 @ X10))),
% 0.17/0.42      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 0.17/0.42  thf('4', plain,
% 0.17/0.42      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.17/0.42      inference('sup-', [status(thm)], ['2', '3'])).
% 0.17/0.42  thf('5', plain,
% 0.17/0.42      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 0.17/0.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.42  thf(commutativity_k3_xboole_0, axiom,
% 0.17/0.42    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.17/0.42  thf('6', plain,
% 0.17/0.42      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.17/0.42      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.17/0.42  thf('7', plain,
% 0.17/0.42      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (k1_tarski @ sk_A))),
% 0.17/0.42      inference('demod', [status(thm)], ['5', '6'])).
% 0.17/0.42  thf('8', plain, ($false),
% 0.17/0.42      inference('simplify_reflect-', [status(thm)], ['4', '7'])).
% 0.17/0.42  
% 0.17/0.42  % SZS output end Refutation
% 0.17/0.42  
% 0.17/0.43  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

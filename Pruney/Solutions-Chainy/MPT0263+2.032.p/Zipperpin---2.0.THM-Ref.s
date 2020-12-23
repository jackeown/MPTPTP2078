%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NvSuA0lvze

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:35 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   20 (  22 expanded)
%              Number of leaves         :   10 (  11 expanded)
%              Depth                    :    5
%              Number of atoms          :   99 ( 121 expanded)
%              Number of equality atoms :    9 (  11 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('0',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X12 ) @ X13 )
      | ( r2_hidden @ X12 @ X13 ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X15 @ ( k1_tarski @ X14 ) )
        = ( k1_tarski @ X14 ) )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
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
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NvSuA0lvze
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:09:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.18/0.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.18/0.44  % Solved by: fo/fo7.sh
% 0.18/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.44  % done 12 iterations in 0.012s
% 0.18/0.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.18/0.44  % SZS output start Refutation
% 0.18/0.44  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.18/0.44  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.44  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.18/0.44  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.18/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.44  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.18/0.44  thf(l27_zfmisc_1, axiom,
% 0.18/0.44    (![A:$i,B:$i]:
% 0.18/0.44     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.18/0.44  thf('0', plain,
% 0.18/0.44      (![X12 : $i, X13 : $i]:
% 0.18/0.44         ((r1_xboole_0 @ (k1_tarski @ X12) @ X13) | (r2_hidden @ X12 @ X13))),
% 0.18/0.44      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.18/0.44  thf(t58_zfmisc_1, conjecture,
% 0.18/0.44    (![A:$i,B:$i]:
% 0.18/0.44     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.18/0.44       ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.18/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.44    (~( ![A:$i,B:$i]:
% 0.18/0.44        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.18/0.44          ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )),
% 0.18/0.44    inference('cnf.neg', [status(esa)], [t58_zfmisc_1])).
% 0.18/0.44  thf('1', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)),
% 0.18/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.44  thf('2', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.18/0.44      inference('sup-', [status(thm)], ['0', '1'])).
% 0.18/0.44  thf(l31_zfmisc_1, axiom,
% 0.18/0.44    (![A:$i,B:$i]:
% 0.18/0.44     ( ( r2_hidden @ A @ B ) =>
% 0.18/0.44       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 0.18/0.44  thf('3', plain,
% 0.18/0.44      (![X14 : $i, X15 : $i]:
% 0.18/0.44         (((k3_xboole_0 @ X15 @ (k1_tarski @ X14)) = (k1_tarski @ X14))
% 0.18/0.44          | ~ (r2_hidden @ X14 @ X15))),
% 0.18/0.44      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 0.18/0.44  thf('4', plain,
% 0.18/0.44      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.18/0.44      inference('sup-', [status(thm)], ['2', '3'])).
% 0.18/0.44  thf('5', plain,
% 0.18/0.44      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 0.18/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.44  thf(commutativity_k3_xboole_0, axiom,
% 0.18/0.44    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.18/0.44  thf('6', plain,
% 0.18/0.44      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.18/0.44      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.18/0.44  thf('7', plain,
% 0.18/0.44      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (k1_tarski @ sk_A))),
% 0.18/0.44      inference('demod', [status(thm)], ['5', '6'])).
% 0.18/0.44  thf('8', plain, ($false),
% 0.18/0.44      inference('simplify_reflect-', [status(thm)], ['4', '7'])).
% 0.18/0.44  
% 0.18/0.44  % SZS output end Refutation
% 0.18/0.44  
% 0.18/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

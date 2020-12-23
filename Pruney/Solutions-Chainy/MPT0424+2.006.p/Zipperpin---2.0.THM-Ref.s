%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vbgSdzlql2

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:17 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   23 (  27 expanded)
%              Number of leaves         :   11 (  13 expanded)
%              Depth                    :    7
%              Number of atoms          :   98 ( 138 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t56_setfam_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( k3_tarski @ A ) @ B )
        & ( r2_hidden @ C @ A ) )
     => ( r1_tarski @ C @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ ( k3_tarski @ A ) @ B )
          & ( r2_hidden @ C @ A ) )
       => ( r1_tarski @ C @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t56_setfam_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( k3_tarski @ sk_A ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ ( k3_tarski @ X6 ) )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('4',plain,(
    r1_tarski @ sk_C @ ( k3_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('6',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k3_tarski @ sk_A ) )
    = ( k3_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 )
      | ( r1_tarski @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
    $false ),
    inference(demod,[status(thm)],['0','9'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vbgSdzlql2
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:51:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 11 iterations in 0.008s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.46  thf(t56_setfam_1, conjecture,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( ( r1_tarski @ ( k3_tarski @ A ) @ B ) & ( r2_hidden @ C @ A ) ) =>
% 0.20/0.46       ( r1_tarski @ C @ B ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.46        ( ( ( r1_tarski @ ( k3_tarski @ A ) @ B ) & ( r2_hidden @ C @ A ) ) =>
% 0.20/0.46          ( r1_tarski @ C @ B ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t56_setfam_1])).
% 0.20/0.46  thf('0', plain, (~ (r1_tarski @ sk_C @ sk_B)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('1', plain, ((r1_tarski @ (k3_tarski @ sk_A) @ sk_B)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('2', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(l49_zfmisc_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (![X5 : $i, X6 : $i]:
% 0.20/0.46         ((r1_tarski @ X5 @ (k3_tarski @ X6)) | ~ (r2_hidden @ X5 @ X6))),
% 0.20/0.46      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.20/0.46  thf('4', plain, ((r1_tarski @ sk_C @ (k3_tarski @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.46  thf(t12_xboole_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (![X3 : $i, X4 : $i]:
% 0.20/0.46         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.20/0.46      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      (((k2_xboole_0 @ sk_C @ (k3_tarski @ sk_A)) = (k3_tarski @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.46  thf(t11_xboole_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.46         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 0.20/0.46      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (r1_tarski @ (k3_tarski @ sk_A) @ X0) | (r1_tarski @ sk_C @ X0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.46  thf('9', plain, ((r1_tarski @ sk_C @ sk_B)),
% 0.20/0.46      inference('sup-', [status(thm)], ['1', '8'])).
% 0.20/0.46  thf('10', plain, ($false), inference('demod', [status(thm)], ['0', '9'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

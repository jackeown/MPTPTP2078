%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0ZtdYsbCds

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:36 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   24 (  28 expanded)
%              Number of leaves         :   12 (  14 expanded)
%              Depth                    :    6
%              Number of atoms          :  128 ( 180 expanded)
%              Number of equality atoms :    9 (  13 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t48_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ C @ B ) )
     => ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ C @ B ) )
       => ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t48_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X22: $i,X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X22 @ X24 ) @ X25 )
      | ~ ( r2_hidden @ X24 @ X25 )
      | ~ ( r2_hidden @ X22 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_C ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t45_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( B
        = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) ) )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X4 @ X5 ) )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( sk_B
    = ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0ZtdYsbCds
% 0.16/0.37  % Computer   : n021.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 16:22:49 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.24/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.45  % Solved by: fo/fo7.sh
% 0.24/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.45  % done 38 iterations in 0.013s
% 0.24/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.45  % SZS output start Refutation
% 0.24/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.45  thf(sk_C_type, type, sk_C: $i).
% 0.24/0.45  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.24/0.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.45  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.24/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.45  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.24/0.45  thf(t48_zfmisc_1, conjecture,
% 0.24/0.45    (![A:$i,B:$i,C:$i]:
% 0.24/0.45     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.24/0.45       ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( B ) ) ))).
% 0.24/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.45    (~( ![A:$i,B:$i,C:$i]:
% 0.24/0.45        ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.24/0.45          ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( B ) ) ) )),
% 0.24/0.45    inference('cnf.neg', [status(esa)], [t48_zfmisc_1])).
% 0.24/0.45  thf('0', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.24/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.45  thf('1', plain, ((r2_hidden @ sk_C @ sk_B)),
% 0.24/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.45  thf(t38_zfmisc_1, axiom,
% 0.24/0.45    (![A:$i,B:$i,C:$i]:
% 0.24/0.45     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.24/0.45       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.24/0.45  thf('2', plain,
% 0.24/0.45      (![X22 : $i, X24 : $i, X25 : $i]:
% 0.24/0.45         ((r1_tarski @ (k2_tarski @ X22 @ X24) @ X25)
% 0.24/0.45          | ~ (r2_hidden @ X24 @ X25)
% 0.24/0.45          | ~ (r2_hidden @ X22 @ X25))),
% 0.24/0.45      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.24/0.45  thf('3', plain,
% 0.24/0.45      (![X0 : $i]:
% 0.24/0.45         (~ (r2_hidden @ X0 @ sk_B)
% 0.24/0.45          | (r1_tarski @ (k2_tarski @ X0 @ sk_C) @ sk_B))),
% 0.24/0.45      inference('sup-', [status(thm)], ['1', '2'])).
% 0.24/0.45  thf('4', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_C) @ sk_B)),
% 0.24/0.45      inference('sup-', [status(thm)], ['0', '3'])).
% 0.24/0.45  thf(t45_xboole_1, axiom,
% 0.24/0.45    (![A:$i,B:$i]:
% 0.24/0.45     ( ( r1_tarski @ A @ B ) =>
% 0.24/0.45       ( ( B ) = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ))).
% 0.24/0.45  thf('5', plain,
% 0.24/0.45      (![X4 : $i, X5 : $i]:
% 0.24/0.45         (((X5) = (k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4)))
% 0.24/0.45          | ~ (r1_tarski @ X4 @ X5))),
% 0.24/0.45      inference('cnf', [status(esa)], [t45_xboole_1])).
% 0.24/0.45  thf(t39_xboole_1, axiom,
% 0.24/0.45    (![A:$i,B:$i]:
% 0.24/0.45     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.24/0.45  thf('6', plain,
% 0.24/0.45      (![X2 : $i, X3 : $i]:
% 0.24/0.45         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 0.24/0.45           = (k2_xboole_0 @ X2 @ X3))),
% 0.24/0.45      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.24/0.45  thf('7', plain,
% 0.24/0.45      (![X4 : $i, X5 : $i]:
% 0.24/0.45         (((X5) = (k2_xboole_0 @ X4 @ X5)) | ~ (r1_tarski @ X4 @ X5))),
% 0.24/0.45      inference('demod', [status(thm)], ['5', '6'])).
% 0.24/0.45  thf('8', plain,
% 0.24/0.45      (((sk_B) = (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B))),
% 0.24/0.45      inference('sup-', [status(thm)], ['4', '7'])).
% 0.24/0.45  thf('9', plain,
% 0.24/0.45      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B) != (sk_B))),
% 0.24/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.45  thf('10', plain, ($false),
% 0.24/0.45      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.24/0.45  
% 0.24/0.45  % SZS output end Refutation
% 0.24/0.45  
% 0.24/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

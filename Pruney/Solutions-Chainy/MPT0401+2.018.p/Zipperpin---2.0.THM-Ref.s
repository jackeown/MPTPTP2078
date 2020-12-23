%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UPQVXoKk5p

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   27 (  31 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    6
%              Number of atoms          :  113 ( 153 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(t24_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ B @ ( k1_tarski @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r1_tarski @ C @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_setfam_1 @ B @ ( k1_tarski @ A ) )
       => ! [C: $i] :
            ( ( r2_hidden @ C @ B )
           => ( r1_tarski @ C @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t24_setfam_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_setfam_1 @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t18_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X16 ) @ ( k3_tarski @ X17 ) )
      | ~ ( r1_setfam_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t18_setfam_1])).

thf('3',plain,(
    r1_tarski @ ( k3_tarski @ sk_B ) @ ( k3_tarski @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('4',plain,(
    ! [X15: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('5',plain,(
    r1_tarski @ ( k3_tarski @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    r2_hidden @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('7',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ ( k3_tarski @ X14 ) )
      | ~ ( r2_hidden @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('8',plain,(
    r1_tarski @ sk_C @ ( k3_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C @ X0 )
      | ~ ( r1_tarski @ ( k3_tarski @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    $false ),
    inference(demod,[status(thm)],['0','11'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UPQVXoKk5p
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:26:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 15 iterations in 0.010s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.46  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.46  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 0.21/0.46  thf(t24_setfam_1, conjecture,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( r1_setfam_1 @ B @ ( k1_tarski @ A ) ) =>
% 0.21/0.46       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r1_tarski @ C @ A ) ) ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i,B:$i]:
% 0.21/0.46        ( ( r1_setfam_1 @ B @ ( k1_tarski @ A ) ) =>
% 0.21/0.46          ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r1_tarski @ C @ A ) ) ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t24_setfam_1])).
% 0.21/0.46  thf('0', plain, (~ (r1_tarski @ sk_C @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('1', plain, ((r1_setfam_1 @ sk_B @ (k1_tarski @ sk_A))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t18_setfam_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( r1_setfam_1 @ A @ B ) =>
% 0.21/0.46       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      (![X16 : $i, X17 : $i]:
% 0.21/0.46         ((r1_tarski @ (k3_tarski @ X16) @ (k3_tarski @ X17))
% 0.21/0.46          | ~ (r1_setfam_1 @ X16 @ X17))),
% 0.21/0.46      inference('cnf', [status(esa)], [t18_setfam_1])).
% 0.21/0.46  thf('3', plain,
% 0.21/0.46      ((r1_tarski @ (k3_tarski @ sk_B) @ (k3_tarski @ (k1_tarski @ sk_A)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.46  thf(t31_zfmisc_1, axiom,
% 0.21/0.46    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.21/0.46  thf('4', plain, (![X15 : $i]: ((k3_tarski @ (k1_tarski @ X15)) = (X15))),
% 0.21/0.46      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.21/0.46  thf('5', plain, ((r1_tarski @ (k3_tarski @ sk_B) @ sk_A)),
% 0.21/0.46      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.46  thf('6', plain, ((r2_hidden @ sk_C @ sk_B)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(l49_zfmisc_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.21/0.46  thf('7', plain,
% 0.21/0.46      (![X13 : $i, X14 : $i]:
% 0.21/0.46         ((r1_tarski @ X13 @ (k3_tarski @ X14)) | ~ (r2_hidden @ X13 @ X14))),
% 0.21/0.46      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.21/0.46  thf('8', plain, ((r1_tarski @ sk_C @ (k3_tarski @ sk_B))),
% 0.21/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.46  thf(t1_xboole_1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.46       ( r1_tarski @ A @ C ) ))).
% 0.21/0.46  thf('9', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.46         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.46          | ~ (r1_tarski @ X1 @ X2)
% 0.21/0.46          | (r1_tarski @ X0 @ X2))),
% 0.21/0.46      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.46  thf('10', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         ((r1_tarski @ sk_C @ X0) | ~ (r1_tarski @ (k3_tarski @ sk_B) @ X0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.46  thf('11', plain, ((r1_tarski @ sk_C @ sk_A)),
% 0.21/0.46      inference('sup-', [status(thm)], ['5', '10'])).
% 0.21/0.46  thf('12', plain, ($false), inference('demod', [status(thm)], ['0', '11'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

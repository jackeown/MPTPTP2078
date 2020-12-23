%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.t3FHyYuLTB

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   28 (  32 expanded)
%              Number of leaves         :   12 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :  145 ( 177 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :   12 (   6 average)

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

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t47_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C )
     => ( r2_hidden @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C )
       => ( r2_hidden @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t47_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('3',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) @ sk_C ),
    inference(demod,[status(thm)],['1','2'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) )
    | ( sk_C
      = ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('7',plain,
    ( sk_C
    = ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('9',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ),
    inference('sup+',[status(thm)],['7','10'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_tarski @ ( k2_tarski @ X9 @ X11 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('13',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    $false ),
    inference(demod,[status(thm)],['0','13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.t3FHyYuLTB
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:36:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 22 iterations in 0.015s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.47  thf(t47_zfmisc_1, conjecture,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 0.21/0.47       ( r2_hidden @ A @ C ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.47        ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 0.21/0.47          ( r2_hidden @ A @ C ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t47_zfmisc_1])).
% 0.21/0.47  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      ((r1_tarski @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ sk_C)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(commutativity_k2_xboole_0, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      ((r1_tarski @ (k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) @ sk_C)),
% 0.21/0.47      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf(d10_xboole_0, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X2 : $i, X4 : $i]:
% 0.21/0.47         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.21/0.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      ((~ (r1_tarski @ sk_C @ (k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))
% 0.21/0.47        | ((sk_C) = (k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.47  thf(t7_xboole_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X5 : $i, X6 : $i]: (r1_tarski @ X5 @ (k2_xboole_0 @ X5 @ X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (((sk_C) = (k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 0.21/0.47      inference('demod', [status(thm)], ['5', '6'])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (![X5 : $i, X6 : $i]: (r1_tarski @ X5 @ (k2_xboole_0 @ X5 @ X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.21/0.47      inference('sup+', [status(thm)], ['8', '9'])).
% 0.21/0.47  thf('11', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)),
% 0.21/0.47      inference('sup+', [status(thm)], ['7', '10'])).
% 0.21/0.47  thf(t38_zfmisc_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.21/0.47       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.47         ((r2_hidden @ X9 @ X10) | ~ (r1_tarski @ (k2_tarski @ X9 @ X11) @ X10))),
% 0.21/0.47      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.21/0.47  thf('13', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.21/0.47      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.47  thf('14', plain, ($false), inference('demod', [status(thm)], ['0', '13'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

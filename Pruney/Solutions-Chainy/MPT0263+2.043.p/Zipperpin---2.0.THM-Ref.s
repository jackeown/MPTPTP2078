%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OyXlcQVNi4

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:36 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   36 (  39 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :   10
%              Number of atoms          :  201 ( 230 expanded)
%              Number of equality atoms :   22 (  25 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('0',plain,(
    ! [X18: $i,X20: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X18 ) @ X20 )
        = ( k1_tarski @ X18 ) )
      | ( r2_hidden @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('1',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_xboole_0 @ X9 @ X11 )
      | ( ( k4_xboole_0 @ X9 @ X11 )
       != X9 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['2'])).

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

thf('4',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf(l35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('6',plain,(
    ! [X21: $i,X23: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X21 ) @ X23 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('7',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','6'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( ( k4_xboole_0 @ X2 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('9',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(simplify,[status(thm)],['9'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('12',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('14',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('17',plain,(
    ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['14','17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OyXlcQVNi4
% 0.15/0.36  % Computer   : n023.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 19:04:36 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 0.23/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.50  % Solved by: fo/fo7.sh
% 0.23/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.50  % done 25 iterations in 0.021s
% 0.23/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.50  % SZS output start Refutation
% 0.23/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.23/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.23/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.23/0.50  thf(l33_zfmisc_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.23/0.50       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.23/0.50  thf('0', plain,
% 0.23/0.50      (![X18 : $i, X20 : $i]:
% 0.23/0.50         (((k4_xboole_0 @ (k1_tarski @ X18) @ X20) = (k1_tarski @ X18))
% 0.23/0.50          | (r2_hidden @ X18 @ X20))),
% 0.23/0.50      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.23/0.50  thf(t83_xboole_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.23/0.50  thf('1', plain,
% 0.23/0.50      (![X9 : $i, X11 : $i]:
% 0.23/0.50         ((r1_xboole_0 @ X9 @ X11) | ((k4_xboole_0 @ X9 @ X11) != (X9)))),
% 0.23/0.50      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.23/0.50  thf('2', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i]:
% 0.23/0.50         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.23/0.50          | (r2_hidden @ X0 @ X1)
% 0.23/0.50          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.23/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.23/0.50  thf('3', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i]:
% 0.23/0.50         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.23/0.50      inference('simplify', [status(thm)], ['2'])).
% 0.23/0.50  thf(t58_zfmisc_1, conjecture,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.23/0.50       ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.23/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.50    (~( ![A:$i,B:$i]:
% 0.23/0.50        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.23/0.50          ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )),
% 0.23/0.50    inference('cnf.neg', [status(esa)], [t58_zfmisc_1])).
% 0.23/0.50  thf('4', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('5', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.23/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.23/0.50  thf(l35_zfmisc_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.23/0.50       ( r2_hidden @ A @ B ) ))).
% 0.23/0.50  thf('6', plain,
% 0.23/0.50      (![X21 : $i, X23 : $i]:
% 0.23/0.50         (((k4_xboole_0 @ (k1_tarski @ X21) @ X23) = (k1_xboole_0))
% 0.23/0.50          | ~ (r2_hidden @ X21 @ X23))),
% 0.23/0.50      inference('cnf', [status(esa)], [l35_zfmisc_1])).
% 0.23/0.50  thf('7', plain,
% 0.23/0.50      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.23/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.23/0.50  thf(l32_xboole_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.23/0.50  thf('8', plain,
% 0.23/0.50      (![X2 : $i, X3 : $i]:
% 0.23/0.50         ((r1_tarski @ X2 @ X3) | ((k4_xboole_0 @ X2 @ X3) != (k1_xboole_0)))),
% 0.23/0.50      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.23/0.50  thf('9', plain,
% 0.23/0.50      ((((k1_xboole_0) != (k1_xboole_0))
% 0.23/0.50        | (r1_tarski @ (k1_tarski @ sk_A) @ sk_B))),
% 0.23/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.23/0.50  thf('10', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.23/0.50      inference('simplify', [status(thm)], ['9'])).
% 0.23/0.50  thf(t28_xboole_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.23/0.50  thf('11', plain,
% 0.23/0.50      (![X5 : $i, X6 : $i]:
% 0.23/0.50         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.23/0.50      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.23/0.50  thf('12', plain,
% 0.23/0.50      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))),
% 0.23/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.23/0.50  thf(commutativity_k3_xboole_0, axiom,
% 0.23/0.50    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.23/0.50  thf('13', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.23/0.50      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.23/0.50  thf('14', plain,
% 0.23/0.50      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.23/0.50      inference('demod', [status(thm)], ['12', '13'])).
% 0.23/0.50  thf('15', plain,
% 0.23/0.50      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('16', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.23/0.50      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.23/0.50  thf('17', plain,
% 0.23/0.50      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (k1_tarski @ sk_A))),
% 0.23/0.50      inference('demod', [status(thm)], ['15', '16'])).
% 0.23/0.50  thf('18', plain, ($false),
% 0.23/0.50      inference('simplify_reflect-', [status(thm)], ['14', '17'])).
% 0.23/0.50  
% 0.23/0.50  % SZS output end Refutation
% 0.23/0.50  
% 0.23/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

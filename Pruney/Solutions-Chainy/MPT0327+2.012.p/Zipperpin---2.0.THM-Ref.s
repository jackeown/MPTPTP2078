%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.emhwXIC1O6

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:51 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   34 (  53 expanded)
%              Number of leaves         :   14 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :  202 ( 366 expanded)
%              Number of equality atoms :   23 (  42 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t140_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k2_xboole_0 @ ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t140_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ C @ B ) )
     => ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
        = B ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( r2_hidden @ X18 @ X17 )
      | ( ( k2_xboole_0 @ ( k2_tarski @ X16 @ X18 ) @ X17 )
        = X17 ) ) ),
    inference(cnf,[status(esa)],[t48_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ X0 ) @ sk_B )
        = sk_B )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_tarski @ X10 @ X9 )
      = ( k2_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X14 @ X15 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X14 @ X15 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k2_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ X0 ) )
        = sk_B )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','8'])).

thf('10',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['0','9'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('11',plain,(
    ! [X11: $i] :
      ( ( k2_tarski @ X11 @ X11 )
      = ( k1_tarski @ X11 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('12',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('17',plain,(
    ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('18',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['12','17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.emhwXIC1O6
% 0.15/0.35  % Computer   : n014.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 19:38:22 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.22/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.46  % Solved by: fo/fo7.sh
% 0.22/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.46  % done 21 iterations in 0.009s
% 0.22/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.46  % SZS output start Refutation
% 0.22/0.46  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.22/0.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.46  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.46  thf(t140_zfmisc_1, conjecture,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( r2_hidden @ A @ B ) =>
% 0.22/0.46       ( ( k2_xboole_0 @
% 0.22/0.46           ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.22/0.46         ( B ) ) ))).
% 0.22/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.46    (~( ![A:$i,B:$i]:
% 0.22/0.46        ( ( r2_hidden @ A @ B ) =>
% 0.22/0.46          ( ( k2_xboole_0 @
% 0.22/0.46              ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.22/0.46            ( B ) ) ) )),
% 0.22/0.46    inference('cnf.neg', [status(esa)], [t140_zfmisc_1])).
% 0.22/0.46  thf('0', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('1', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf(t48_zfmisc_1, axiom,
% 0.22/0.46    (![A:$i,B:$i,C:$i]:
% 0.22/0.46     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.22/0.46       ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( B ) ) ))).
% 0.22/0.46  thf('2', plain,
% 0.22/0.46      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.22/0.46         (~ (r2_hidden @ X16 @ X17)
% 0.22/0.46          | ~ (r2_hidden @ X18 @ X17)
% 0.22/0.46          | ((k2_xboole_0 @ (k2_tarski @ X16 @ X18) @ X17) = (X17)))),
% 0.22/0.46      inference('cnf', [status(esa)], [t48_zfmisc_1])).
% 0.22/0.46  thf('3', plain,
% 0.22/0.46      (![X0 : $i]:
% 0.22/0.46         (((k2_xboole_0 @ (k2_tarski @ sk_A @ X0) @ sk_B) = (sk_B))
% 0.22/0.46          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.22/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.46  thf(commutativity_k2_tarski, axiom,
% 0.22/0.46    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.22/0.46  thf('4', plain,
% 0.22/0.46      (![X9 : $i, X10 : $i]: ((k2_tarski @ X10 @ X9) = (k2_tarski @ X9 @ X10))),
% 0.22/0.46      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.22/0.46  thf(l51_zfmisc_1, axiom,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.46  thf('5', plain,
% 0.22/0.46      (![X14 : $i, X15 : $i]:
% 0.22/0.46         ((k3_tarski @ (k2_tarski @ X14 @ X15)) = (k2_xboole_0 @ X14 @ X15))),
% 0.22/0.46      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.22/0.46  thf('6', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.46      inference('sup+', [status(thm)], ['4', '5'])).
% 0.22/0.46  thf('7', plain,
% 0.22/0.46      (![X14 : $i, X15 : $i]:
% 0.22/0.46         ((k3_tarski @ (k2_tarski @ X14 @ X15)) = (k2_xboole_0 @ X14 @ X15))),
% 0.22/0.46      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.22/0.46  thf('8', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.46      inference('sup+', [status(thm)], ['6', '7'])).
% 0.22/0.46  thf('9', plain,
% 0.22/0.46      (![X0 : $i]:
% 0.22/0.46         (((k2_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ X0)) = (sk_B))
% 0.22/0.46          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.22/0.46      inference('demod', [status(thm)], ['3', '8'])).
% 0.22/0.46  thf('10', plain,
% 0.22/0.46      (((k2_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_A)) = (sk_B))),
% 0.22/0.46      inference('sup-', [status(thm)], ['0', '9'])).
% 0.22/0.46  thf(t69_enumset1, axiom,
% 0.22/0.46    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.46  thf('11', plain,
% 0.22/0.46      (![X11 : $i]: ((k2_tarski @ X11 @ X11) = (k1_tarski @ X11))),
% 0.22/0.46      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.46  thf('12', plain, (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B))),
% 0.22/0.46      inference('demod', [status(thm)], ['10', '11'])).
% 0.22/0.46  thf('13', plain,
% 0.22/0.46      (((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.22/0.46         (k1_tarski @ sk_A)) != (sk_B))),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('14', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.46      inference('sup+', [status(thm)], ['6', '7'])).
% 0.22/0.46  thf(t39_xboole_1, axiom,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.46  thf('15', plain,
% 0.22/0.46      (![X2 : $i, X3 : $i]:
% 0.22/0.46         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 0.22/0.46           = (k2_xboole_0 @ X2 @ X3))),
% 0.22/0.46      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.22/0.46  thf('16', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.46      inference('sup+', [status(thm)], ['6', '7'])).
% 0.22/0.46  thf('17', plain, (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (sk_B))),
% 0.22/0.46      inference('demod', [status(thm)], ['13', '14', '15', '16'])).
% 0.22/0.46  thf('18', plain, ($false),
% 0.22/0.46      inference('simplify_reflect-', [status(thm)], ['12', '17'])).
% 0.22/0.46  
% 0.22/0.46  % SZS output end Refutation
% 0.22/0.46  
% 0.22/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

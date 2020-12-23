%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UjV8GaR61d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:49 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :   31 (  34 expanded)
%              Number of leaves         :   13 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :  221 ( 245 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t86_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) ) @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ B @ A ) ) ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) ) @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ B @ A ) ) ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t86_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t79_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X13 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X13 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_tarski @ X2 @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,(
    $false ),
    inference(demod,[status(thm)],['0','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UjV8GaR61d
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:06:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.55/0.78  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.55/0.78  % Solved by: fo/fo7.sh
% 0.55/0.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.78  % done 538 iterations in 0.324s
% 0.55/0.78  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.55/0.78  % SZS output start Refutation
% 0.55/0.78  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.55/0.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.55/0.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.55/0.78  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.78  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.55/0.78  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.55/0.78  thf(t86_zfmisc_1, conjecture,
% 0.55/0.78    (![A:$i,B:$i]:
% 0.55/0.78     ( r1_tarski @
% 0.55/0.78       ( k2_xboole_0 @
% 0.55/0.78         ( k1_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) ) @ 
% 0.55/0.78         ( k1_zfmisc_1 @ ( k4_xboole_0 @ B @ A ) ) ) @ 
% 0.55/0.78       ( k1_zfmisc_1 @ ( k5_xboole_0 @ A @ B ) ) ))).
% 0.55/0.78  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.78    (~( ![A:$i,B:$i]:
% 0.55/0.78        ( r1_tarski @
% 0.55/0.78          ( k2_xboole_0 @
% 0.55/0.78            ( k1_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) ) @ 
% 0.55/0.78            ( k1_zfmisc_1 @ ( k4_xboole_0 @ B @ A ) ) ) @ 
% 0.55/0.78          ( k1_zfmisc_1 @ ( k5_xboole_0 @ A @ B ) ) ) )),
% 0.55/0.78    inference('cnf.neg', [status(esa)], [t86_zfmisc_1])).
% 0.55/0.78  thf('0', plain,
% 0.55/0.78      (~ (r1_tarski @ 
% 0.55/0.78          (k2_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_B)) @ 
% 0.55/0.78           (k1_zfmisc_1 @ (k4_xboole_0 @ sk_B @ sk_A))) @ 
% 0.55/0.78          (k1_zfmisc_1 @ (k5_xboole_0 @ sk_A @ sk_B)))),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf(commutativity_k5_xboole_0, axiom,
% 0.55/0.78    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.55/0.78  thf('1', plain,
% 0.55/0.78      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.55/0.78      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.55/0.78  thf(d6_xboole_0, axiom,
% 0.55/0.78    (![A:$i,B:$i]:
% 0.55/0.78     ( ( k5_xboole_0 @ A @ B ) =
% 0.55/0.78       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.55/0.78  thf('2', plain,
% 0.55/0.78      (![X2 : $i, X3 : $i]:
% 0.55/0.78         ((k5_xboole_0 @ X2 @ X3)
% 0.55/0.78           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 0.55/0.78      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.55/0.78  thf(t7_xboole_1, axiom,
% 0.55/0.78    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.55/0.78  thf('3', plain,
% 0.55/0.78      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 0.55/0.78      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.55/0.78  thf('4', plain,
% 0.55/0.78      (![X0 : $i, X1 : $i]:
% 0.55/0.78         (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))),
% 0.55/0.78      inference('sup+', [status(thm)], ['2', '3'])).
% 0.55/0.78  thf('5', plain,
% 0.55/0.78      (![X0 : $i, X1 : $i]:
% 0.55/0.78         (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0))),
% 0.55/0.78      inference('sup+', [status(thm)], ['1', '4'])).
% 0.55/0.78  thf(t79_zfmisc_1, axiom,
% 0.55/0.78    (![A:$i,B:$i]:
% 0.55/0.78     ( ( r1_tarski @ A @ B ) =>
% 0.55/0.78       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.55/0.78  thf('6', plain,
% 0.55/0.78      (![X13 : $i, X14 : $i]:
% 0.55/0.78         ((r1_tarski @ (k1_zfmisc_1 @ X13) @ (k1_zfmisc_1 @ X14))
% 0.55/0.78          | ~ (r1_tarski @ X13 @ X14))),
% 0.55/0.78      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 0.55/0.78  thf('7', plain,
% 0.55/0.78      (![X0 : $i, X1 : $i]:
% 0.55/0.78         (r1_tarski @ (k1_zfmisc_1 @ (k4_xboole_0 @ X0 @ X1)) @ 
% 0.55/0.78          (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.55/0.78      inference('sup-', [status(thm)], ['5', '6'])).
% 0.55/0.78  thf('8', plain,
% 0.55/0.78      (![X2 : $i, X3 : $i]:
% 0.55/0.78         ((k5_xboole_0 @ X2 @ X3)
% 0.55/0.78           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 0.55/0.78      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.55/0.78  thf('9', plain,
% 0.55/0.78      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 0.55/0.78      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.55/0.78  thf('10', plain,
% 0.55/0.78      (![X13 : $i, X14 : $i]:
% 0.55/0.78         ((r1_tarski @ (k1_zfmisc_1 @ X13) @ (k1_zfmisc_1 @ X14))
% 0.55/0.78          | ~ (r1_tarski @ X13 @ X14))),
% 0.55/0.78      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 0.55/0.78  thf('11', plain,
% 0.55/0.78      (![X0 : $i, X1 : $i]:
% 0.55/0.78         (r1_tarski @ (k1_zfmisc_1 @ X1) @ 
% 0.55/0.78          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.55/0.78      inference('sup-', [status(thm)], ['9', '10'])).
% 0.55/0.78  thf('12', plain,
% 0.55/0.78      (![X0 : $i, X1 : $i]:
% 0.55/0.78         (r1_tarski @ (k1_zfmisc_1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 0.55/0.78          (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.55/0.78      inference('sup+', [status(thm)], ['8', '11'])).
% 0.55/0.78  thf(t8_xboole_1, axiom,
% 0.55/0.78    (![A:$i,B:$i,C:$i]:
% 0.55/0.78     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.55/0.78       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.55/0.78  thf('13', plain,
% 0.55/0.78      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.55/0.78         (~ (r1_tarski @ X8 @ X9)
% 0.55/0.78          | ~ (r1_tarski @ X10 @ X9)
% 0.55/0.78          | (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 0.55/0.78      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.55/0.78  thf('14', plain,
% 0.55/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.78         ((r1_tarski @ 
% 0.55/0.78           (k2_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ X1 @ X0)) @ X2) @ 
% 0.55/0.78           (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0)))
% 0.55/0.78          | ~ (r1_tarski @ X2 @ (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0))))),
% 0.55/0.78      inference('sup-', [status(thm)], ['12', '13'])).
% 0.55/0.78  thf('15', plain,
% 0.55/0.78      (![X0 : $i, X1 : $i]:
% 0.55/0.78         (r1_tarski @ 
% 0.55/0.78          (k2_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 0.55/0.78           (k1_zfmisc_1 @ (k4_xboole_0 @ X0 @ X1))) @ 
% 0.55/0.78          (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.55/0.78      inference('sup-', [status(thm)], ['7', '14'])).
% 0.55/0.78  thf('16', plain, ($false), inference('demod', [status(thm)], ['0', '15'])).
% 0.55/0.78  
% 0.55/0.78  % SZS output end Refutation
% 0.55/0.78  
% 0.55/0.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

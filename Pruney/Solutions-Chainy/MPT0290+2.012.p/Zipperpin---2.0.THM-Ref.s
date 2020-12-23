%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QL0HaDvSc1

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:54 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   35 (  40 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :  221 ( 257 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t97_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_tarski @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( r1_tarski @ ( k3_tarski @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t97_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k3_xboole_0 @ X3 @ ( k2_xboole_0 @ X3 @ X4 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t31_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ ( k2_xboole_0 @ B @ C ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X7 @ X8 ) @ ( k3_xboole_0 @ X7 @ X9 ) ) @ ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t31_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t95_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X14 ) @ ( k3_tarski @ X15 ) )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t95_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_tarski @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X14 ) @ ( k3_tarski @ X15 ) )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t95_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_tarski @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X2 )
      | ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ ( k3_tarski @ X0 ) @ X2 ) )
      | ~ ( r1_tarski @ ( k3_tarski @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_tarski @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k3_tarski @ X1 ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    $false ),
    inference(demod,[status(thm)],['0','17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QL0HaDvSc1
% 0.14/0.36  % Computer   : n013.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 10:50:10 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.36/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.56  % Solved by: fo/fo7.sh
% 0.36/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.56  % done 190 iterations in 0.085s
% 0.36/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.56  % SZS output start Refutation
% 0.36/0.56  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.36/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.56  thf(t97_zfmisc_1, conjecture,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( r1_tarski @
% 0.36/0.56       ( k3_tarski @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.36/0.56       ( k3_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.36/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.56    (~( ![A:$i,B:$i]:
% 0.36/0.56        ( r1_tarski @
% 0.36/0.56          ( k3_tarski @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.36/0.56          ( k3_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )),
% 0.36/0.56    inference('cnf.neg', [status(esa)], [t97_zfmisc_1])).
% 0.36/0.56  thf('0', plain,
% 0.36/0.56      (~ (r1_tarski @ (k3_tarski @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 0.36/0.56          (k3_xboole_0 @ (k3_tarski @ sk_A) @ (k3_tarski @ sk_B)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(t21_xboole_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.36/0.56  thf('1', plain,
% 0.36/0.56      (![X3 : $i, X4 : $i]:
% 0.36/0.56         ((k3_xboole_0 @ X3 @ (k2_xboole_0 @ X3 @ X4)) = (X3))),
% 0.36/0.56      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.36/0.56  thf(t22_xboole_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.36/0.56  thf('2', plain,
% 0.36/0.56      (![X5 : $i, X6 : $i]:
% 0.36/0.56         ((k2_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)) = (X5))),
% 0.36/0.56      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.36/0.56  thf('3', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.36/0.56      inference('sup+', [status(thm)], ['1', '2'])).
% 0.36/0.56  thf(t31_xboole_1, axiom,
% 0.36/0.56    (![A:$i,B:$i,C:$i]:
% 0.36/0.56     ( r1_tarski @
% 0.36/0.56       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ 
% 0.36/0.56       ( k2_xboole_0 @ B @ C ) ))).
% 0.36/0.56  thf('4', plain,
% 0.36/0.56      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.36/0.56         (r1_tarski @ 
% 0.36/0.56          (k2_xboole_0 @ (k3_xboole_0 @ X7 @ X8) @ (k3_xboole_0 @ X7 @ X9)) @ 
% 0.36/0.56          (k2_xboole_0 @ X8 @ X9))),
% 0.36/0.56      inference('cnf', [status(esa)], [t31_xboole_1])).
% 0.36/0.56  thf('5', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]:
% 0.36/0.56         (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X0))),
% 0.36/0.56      inference('sup+', [status(thm)], ['3', '4'])).
% 0.36/0.56  thf('6', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.36/0.56      inference('sup+', [status(thm)], ['1', '2'])).
% 0.36/0.56  thf('7', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.36/0.56      inference('demod', [status(thm)], ['5', '6'])).
% 0.36/0.56  thf(t95_zfmisc_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( r1_tarski @ A @ B ) =>
% 0.36/0.56       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.36/0.56  thf('8', plain,
% 0.36/0.56      (![X14 : $i, X15 : $i]:
% 0.36/0.56         ((r1_tarski @ (k3_tarski @ X14) @ (k3_tarski @ X15))
% 0.36/0.56          | ~ (r1_tarski @ X14 @ X15))),
% 0.36/0.56      inference('cnf', [status(esa)], [t95_zfmisc_1])).
% 0.36/0.56  thf('9', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]:
% 0.36/0.56         (r1_tarski @ (k3_tarski @ (k3_xboole_0 @ X1 @ X0)) @ (k3_tarski @ X0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.56  thf(t48_xboole_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.36/0.56  thf('10', plain,
% 0.36/0.56      (![X12 : $i, X13 : $i]:
% 0.36/0.56         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.36/0.56           = (k3_xboole_0 @ X12 @ X13))),
% 0.36/0.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.36/0.56  thf(t36_xboole_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.36/0.56  thf('11', plain,
% 0.36/0.56      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 0.36/0.56      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.36/0.56  thf('12', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.36/0.56      inference('sup+', [status(thm)], ['10', '11'])).
% 0.36/0.56  thf('13', plain,
% 0.36/0.56      (![X14 : $i, X15 : $i]:
% 0.36/0.56         ((r1_tarski @ (k3_tarski @ X14) @ (k3_tarski @ X15))
% 0.36/0.56          | ~ (r1_tarski @ X14 @ X15))),
% 0.36/0.56      inference('cnf', [status(esa)], [t95_zfmisc_1])).
% 0.36/0.56  thf('14', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]:
% 0.36/0.56         (r1_tarski @ (k3_tarski @ (k3_xboole_0 @ X0 @ X1)) @ (k3_tarski @ X0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['12', '13'])).
% 0.36/0.56  thf(t19_xboole_1, axiom,
% 0.36/0.56    (![A:$i,B:$i,C:$i]:
% 0.36/0.56     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.36/0.56       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.36/0.56  thf('15', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.56         (~ (r1_tarski @ X0 @ X1)
% 0.36/0.56          | ~ (r1_tarski @ X0 @ X2)
% 0.36/0.56          | (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.36/0.56  thf('16', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.56         ((r1_tarski @ (k3_tarski @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.36/0.56           (k3_xboole_0 @ (k3_tarski @ X0) @ X2))
% 0.36/0.56          | ~ (r1_tarski @ (k3_tarski @ (k3_xboole_0 @ X0 @ X1)) @ X2))),
% 0.36/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.36/0.56  thf('17', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]:
% 0.36/0.56         (r1_tarski @ (k3_tarski @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.36/0.56          (k3_xboole_0 @ (k3_tarski @ X1) @ (k3_tarski @ X0)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['9', '16'])).
% 0.36/0.56  thf('18', plain, ($false), inference('demod', [status(thm)], ['0', '17'])).
% 0.36/0.56  
% 0.36/0.56  % SZS output end Refutation
% 0.36/0.56  
% 0.36/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

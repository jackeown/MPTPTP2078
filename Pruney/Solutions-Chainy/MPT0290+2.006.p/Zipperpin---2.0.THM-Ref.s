%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.D8gC8Wjecr

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:53 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   44 (  45 expanded)
%              Number of leaves         :   19 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :  282 ( 290 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t45_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( B
        = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ) )).

thf('3',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X20
        = ( k2_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      | ~ ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 = k1_xboole_0 )
      | ~ ( r1_tarski @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['4','9'])).

thf(t31_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ ( k2_xboole_0 @ B @ C ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ ( k3_xboole_0 @ X11 @ X13 ) ) @ ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t31_xboole_1])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf(t95_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('15',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X23 ) @ ( k3_tarski @ X24 ) )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t95_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_tarski @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('17',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('18',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X23 ) @ ( k3_tarski @ X24 ) )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t95_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_tarski @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X8 @ X10 )
      | ( r1_tarski @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ ( k3_tarski @ X0 ) @ X2 ) )
      | ~ ( r1_tarski @ ( k3_tarski @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_tarski @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k3_tarski @ X1 ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['0','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.D8gC8Wjecr
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:40:10 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.59/1.80  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.59/1.80  % Solved by: fo/fo7.sh
% 1.59/1.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.59/1.80  % done 2665 iterations in 1.356s
% 1.59/1.80  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.59/1.80  % SZS output start Refutation
% 1.59/1.80  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.59/1.80  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.59/1.80  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.59/1.80  thf(sk_A_type, type, sk_A: $i).
% 1.59/1.80  thf(sk_B_type, type, sk_B: $i).
% 1.59/1.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.59/1.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.59/1.80  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.59/1.80  thf(t97_zfmisc_1, conjecture,
% 1.59/1.80    (![A:$i,B:$i]:
% 1.59/1.80     ( r1_tarski @
% 1.59/1.80       ( k3_tarski @ ( k3_xboole_0 @ A @ B ) ) @ 
% 1.59/1.80       ( k3_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 1.59/1.80  thf(zf_stmt_0, negated_conjecture,
% 1.59/1.80    (~( ![A:$i,B:$i]:
% 1.59/1.80        ( r1_tarski @
% 1.59/1.80          ( k3_tarski @ ( k3_xboole_0 @ A @ B ) ) @ 
% 1.59/1.80          ( k3_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )),
% 1.59/1.80    inference('cnf.neg', [status(esa)], [t97_zfmisc_1])).
% 1.59/1.80  thf('0', plain,
% 1.59/1.80      (~ (r1_tarski @ (k3_tarski @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 1.59/1.80          (k3_xboole_0 @ (k3_tarski @ sk_A) @ (k3_tarski @ sk_B)))),
% 1.59/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.59/1.80  thf(d10_xboole_0, axiom,
% 1.59/1.80    (![A:$i,B:$i]:
% 1.59/1.80     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.59/1.80  thf('1', plain,
% 1.59/1.80      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.59/1.80      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.59/1.80  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.59/1.80      inference('simplify', [status(thm)], ['1'])).
% 1.59/1.80  thf(t45_xboole_1, axiom,
% 1.59/1.80    (![A:$i,B:$i]:
% 1.59/1.80     ( ( r1_tarski @ A @ B ) =>
% 1.59/1.80       ( ( B ) = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ))).
% 1.59/1.80  thf('3', plain,
% 1.59/1.80      (![X19 : $i, X20 : $i]:
% 1.59/1.80         (((X20) = (k2_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))
% 1.59/1.80          | ~ (r1_tarski @ X19 @ X20))),
% 1.59/1.80      inference('cnf', [status(esa)], [t45_xboole_1])).
% 1.59/1.80  thf('4', plain,
% 1.59/1.80      (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 1.59/1.80      inference('sup-', [status(thm)], ['2', '3'])).
% 1.59/1.80  thf(t7_xboole_1, axiom,
% 1.59/1.80    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.59/1.80  thf('5', plain,
% 1.59/1.80      (![X21 : $i, X22 : $i]: (r1_tarski @ X21 @ (k2_xboole_0 @ X21 @ X22))),
% 1.59/1.80      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.59/1.80  thf(t43_xboole_1, axiom,
% 1.59/1.80    (![A:$i,B:$i,C:$i]:
% 1.59/1.80     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 1.59/1.80       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 1.59/1.80  thf('6', plain,
% 1.59/1.80      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.59/1.80         ((r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 1.59/1.80          | ~ (r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 1.59/1.80      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.59/1.80  thf('7', plain,
% 1.59/1.80      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 1.59/1.80      inference('sup-', [status(thm)], ['5', '6'])).
% 1.59/1.80  thf(t38_xboole_1, axiom,
% 1.59/1.80    (![A:$i,B:$i]:
% 1.59/1.80     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 1.59/1.80       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.59/1.80  thf('8', plain,
% 1.59/1.80      (![X14 : $i, X15 : $i]:
% 1.59/1.80         (((X14) = (k1_xboole_0))
% 1.59/1.80          | ~ (r1_tarski @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 1.59/1.80      inference('cnf', [status(esa)], [t38_xboole_1])).
% 1.59/1.80  thf('9', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.59/1.80      inference('sup-', [status(thm)], ['7', '8'])).
% 1.59/1.80  thf('10', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 1.59/1.80      inference('demod', [status(thm)], ['4', '9'])).
% 1.59/1.80  thf(t31_xboole_1, axiom,
% 1.59/1.80    (![A:$i,B:$i,C:$i]:
% 1.59/1.80     ( r1_tarski @
% 1.59/1.80       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ 
% 1.59/1.80       ( k2_xboole_0 @ B @ C ) ))).
% 1.59/1.80  thf('11', plain,
% 1.59/1.80      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.59/1.80         (r1_tarski @ 
% 1.59/1.80          (k2_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ (k3_xboole_0 @ X11 @ X13)) @ 
% 1.59/1.80          (k2_xboole_0 @ X12 @ X13))),
% 1.59/1.80      inference('cnf', [status(esa)], [t31_xboole_1])).
% 1.59/1.80  thf(t11_xboole_1, axiom,
% 1.59/1.80    (![A:$i,B:$i,C:$i]:
% 1.59/1.80     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 1.59/1.80  thf('12', plain,
% 1.59/1.80      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.59/1.80         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 1.59/1.80      inference('cnf', [status(esa)], [t11_xboole_1])).
% 1.59/1.80  thf('13', plain,
% 1.59/1.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.59/1.80         (r1_tarski @ (k3_xboole_0 @ X2 @ X1) @ (k2_xboole_0 @ X1 @ X0))),
% 1.59/1.80      inference('sup-', [status(thm)], ['11', '12'])).
% 1.59/1.80  thf('14', plain,
% 1.59/1.80      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.59/1.80      inference('sup+', [status(thm)], ['10', '13'])).
% 1.59/1.80  thf(t95_zfmisc_1, axiom,
% 1.59/1.80    (![A:$i,B:$i]:
% 1.59/1.80     ( ( r1_tarski @ A @ B ) =>
% 1.59/1.80       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 1.59/1.80  thf('15', plain,
% 1.59/1.80      (![X23 : $i, X24 : $i]:
% 1.59/1.80         ((r1_tarski @ (k3_tarski @ X23) @ (k3_tarski @ X24))
% 1.59/1.80          | ~ (r1_tarski @ X23 @ X24))),
% 1.59/1.80      inference('cnf', [status(esa)], [t95_zfmisc_1])).
% 1.59/1.80  thf('16', plain,
% 1.59/1.80      (![X0 : $i, X1 : $i]:
% 1.59/1.80         (r1_tarski @ (k3_tarski @ (k3_xboole_0 @ X1 @ X0)) @ (k3_tarski @ X0))),
% 1.59/1.80      inference('sup-', [status(thm)], ['14', '15'])).
% 1.59/1.80  thf(t17_xboole_1, axiom,
% 1.59/1.80    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.59/1.80  thf('17', plain,
% 1.59/1.80      (![X6 : $i, X7 : $i]: (r1_tarski @ (k3_xboole_0 @ X6 @ X7) @ X6)),
% 1.59/1.80      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.59/1.80  thf('18', plain,
% 1.59/1.80      (![X23 : $i, X24 : $i]:
% 1.59/1.80         ((r1_tarski @ (k3_tarski @ X23) @ (k3_tarski @ X24))
% 1.59/1.80          | ~ (r1_tarski @ X23 @ X24))),
% 1.59/1.80      inference('cnf', [status(esa)], [t95_zfmisc_1])).
% 1.59/1.80  thf('19', plain,
% 1.59/1.80      (![X0 : $i, X1 : $i]:
% 1.59/1.80         (r1_tarski @ (k3_tarski @ (k3_xboole_0 @ X0 @ X1)) @ (k3_tarski @ X0))),
% 1.59/1.80      inference('sup-', [status(thm)], ['17', '18'])).
% 1.59/1.80  thf(t19_xboole_1, axiom,
% 1.59/1.80    (![A:$i,B:$i,C:$i]:
% 1.59/1.80     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 1.59/1.80       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 1.59/1.80  thf('20', plain,
% 1.59/1.80      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.59/1.80         (~ (r1_tarski @ X8 @ X9)
% 1.59/1.80          | ~ (r1_tarski @ X8 @ X10)
% 1.59/1.80          | (r1_tarski @ X8 @ (k3_xboole_0 @ X9 @ X10)))),
% 1.59/1.80      inference('cnf', [status(esa)], [t19_xboole_1])).
% 1.59/1.80  thf('21', plain,
% 1.59/1.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.59/1.80         ((r1_tarski @ (k3_tarski @ (k3_xboole_0 @ X0 @ X1)) @ 
% 1.59/1.80           (k3_xboole_0 @ (k3_tarski @ X0) @ X2))
% 1.59/1.80          | ~ (r1_tarski @ (k3_tarski @ (k3_xboole_0 @ X0 @ X1)) @ X2))),
% 1.59/1.80      inference('sup-', [status(thm)], ['19', '20'])).
% 1.59/1.80  thf('22', plain,
% 1.59/1.80      (![X0 : $i, X1 : $i]:
% 1.59/1.80         (r1_tarski @ (k3_tarski @ (k3_xboole_0 @ X1 @ X0)) @ 
% 1.59/1.80          (k3_xboole_0 @ (k3_tarski @ X1) @ (k3_tarski @ X0)))),
% 1.59/1.80      inference('sup-', [status(thm)], ['16', '21'])).
% 1.59/1.80  thf('23', plain, ($false), inference('demod', [status(thm)], ['0', '22'])).
% 1.59/1.80  
% 1.59/1.80  % SZS output end Refutation
% 1.59/1.80  
% 1.59/1.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

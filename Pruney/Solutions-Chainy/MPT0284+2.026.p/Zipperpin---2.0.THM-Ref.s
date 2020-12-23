%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NA0I8T0lFX

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:50 EST 2020

% Result     : Theorem 19.71s
% Output     : Refutation 19.71s
% Verified   : 
% Statistics : Number of formulae       :   33 (  35 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :  234 ( 253 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X5 @ ( k2_xboole_0 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t79_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X15 ) @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('11',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X15 ) @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('14',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X12 @ X11 )
      | ( r1_tarski @ ( k2_xboole_0 @ X10 @ X12 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_tarski @ X2 @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('17',plain,(
    $false ),
    inference(demod,[status(thm)],['0','16'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NA0I8T0lFX
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:09:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 19.71/19.93  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 19.71/19.93  % Solved by: fo/fo7.sh
% 19.71/19.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 19.71/19.93  % done 11107 iterations in 19.461s
% 19.71/19.93  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 19.71/19.93  % SZS output start Refutation
% 19.71/19.93  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 19.71/19.93  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 19.71/19.93  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 19.71/19.93  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 19.71/19.93  thf(sk_B_type, type, sk_B: $i).
% 19.71/19.93  thf(sk_A_type, type, sk_A: $i).
% 19.71/19.93  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 19.71/19.93  thf(t86_zfmisc_1, conjecture,
% 19.71/19.93    (![A:$i,B:$i]:
% 19.71/19.93     ( r1_tarski @
% 19.71/19.93       ( k2_xboole_0 @
% 19.71/19.93         ( k1_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) ) @ 
% 19.71/19.93         ( k1_zfmisc_1 @ ( k4_xboole_0 @ B @ A ) ) ) @ 
% 19.71/19.93       ( k1_zfmisc_1 @ ( k5_xboole_0 @ A @ B ) ) ))).
% 19.71/19.93  thf(zf_stmt_0, negated_conjecture,
% 19.71/19.93    (~( ![A:$i,B:$i]:
% 19.71/19.93        ( r1_tarski @
% 19.71/19.93          ( k2_xboole_0 @
% 19.71/19.93            ( k1_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) ) @ 
% 19.71/19.93            ( k1_zfmisc_1 @ ( k4_xboole_0 @ B @ A ) ) ) @ 
% 19.71/19.93          ( k1_zfmisc_1 @ ( k5_xboole_0 @ A @ B ) ) ) )),
% 19.71/19.93    inference('cnf.neg', [status(esa)], [t86_zfmisc_1])).
% 19.71/19.93  thf('0', plain,
% 19.71/19.93      (~ (r1_tarski @ 
% 19.71/19.93          (k2_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_B)) @ 
% 19.71/19.93           (k1_zfmisc_1 @ (k4_xboole_0 @ sk_B @ sk_A))) @ 
% 19.71/19.93          (k1_zfmisc_1 @ (k5_xboole_0 @ sk_A @ sk_B)))),
% 19.71/19.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.71/19.93  thf(d6_xboole_0, axiom,
% 19.71/19.93    (![A:$i,B:$i]:
% 19.71/19.93     ( ( k5_xboole_0 @ A @ B ) =
% 19.71/19.93       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 19.71/19.93  thf('1', plain,
% 19.71/19.93      (![X0 : $i, X1 : $i]:
% 19.71/19.93         ((k5_xboole_0 @ X0 @ X1)
% 19.71/19.93           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 19.71/19.93      inference('cnf', [status(esa)], [d6_xboole_0])).
% 19.71/19.93  thf(d10_xboole_0, axiom,
% 19.71/19.93    (![A:$i,B:$i]:
% 19.71/19.93     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 19.71/19.93  thf('2', plain,
% 19.71/19.93      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 19.71/19.93      inference('cnf', [status(esa)], [d10_xboole_0])).
% 19.71/19.93  thf('3', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 19.71/19.93      inference('simplify', [status(thm)], ['2'])).
% 19.71/19.93  thf(t10_xboole_1, axiom,
% 19.71/19.93    (![A:$i,B:$i,C:$i]:
% 19.71/19.93     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 19.71/19.93  thf('4', plain,
% 19.71/19.93      (![X5 : $i, X6 : $i, X7 : $i]:
% 19.71/19.93         (~ (r1_tarski @ X5 @ X6) | (r1_tarski @ X5 @ (k2_xboole_0 @ X7 @ X6)))),
% 19.71/19.93      inference('cnf', [status(esa)], [t10_xboole_1])).
% 19.71/19.93  thf('5', plain,
% 19.71/19.93      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 19.71/19.93      inference('sup-', [status(thm)], ['3', '4'])).
% 19.71/19.93  thf(t79_zfmisc_1, axiom,
% 19.71/19.93    (![A:$i,B:$i]:
% 19.71/19.93     ( ( r1_tarski @ A @ B ) =>
% 19.71/19.93       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 19.71/19.93  thf('6', plain,
% 19.71/19.93      (![X15 : $i, X16 : $i]:
% 19.71/19.93         ((r1_tarski @ (k1_zfmisc_1 @ X15) @ (k1_zfmisc_1 @ X16))
% 19.71/19.93          | ~ (r1_tarski @ X15 @ X16))),
% 19.71/19.93      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 19.71/19.93  thf('7', plain,
% 19.71/19.93      (![X0 : $i, X1 : $i]:
% 19.71/19.93         (r1_tarski @ (k1_zfmisc_1 @ X0) @ 
% 19.71/19.93          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 19.71/19.93      inference('sup-', [status(thm)], ['5', '6'])).
% 19.71/19.93  thf('8', plain,
% 19.71/19.93      (![X0 : $i, X1 : $i]:
% 19.71/19.93         (r1_tarski @ (k1_zfmisc_1 @ (k4_xboole_0 @ X0 @ X1)) @ 
% 19.71/19.93          (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0)))),
% 19.71/19.93      inference('sup+', [status(thm)], ['1', '7'])).
% 19.71/19.93  thf('9', plain,
% 19.71/19.93      (![X0 : $i, X1 : $i]:
% 19.71/19.93         ((k5_xboole_0 @ X0 @ X1)
% 19.71/19.93           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 19.71/19.93      inference('cnf', [status(esa)], [d6_xboole_0])).
% 19.71/19.93  thf(t7_xboole_1, axiom,
% 19.71/19.93    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 19.71/19.93  thf('10', plain,
% 19.71/19.93      (![X8 : $i, X9 : $i]: (r1_tarski @ X8 @ (k2_xboole_0 @ X8 @ X9))),
% 19.71/19.93      inference('cnf', [status(esa)], [t7_xboole_1])).
% 19.71/19.93  thf('11', plain,
% 19.71/19.93      (![X15 : $i, X16 : $i]:
% 19.71/19.93         ((r1_tarski @ (k1_zfmisc_1 @ X15) @ (k1_zfmisc_1 @ X16))
% 19.71/19.93          | ~ (r1_tarski @ X15 @ X16))),
% 19.71/19.93      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 19.71/19.93  thf('12', plain,
% 19.71/19.93      (![X0 : $i, X1 : $i]:
% 19.71/19.93         (r1_tarski @ (k1_zfmisc_1 @ X1) @ 
% 19.71/19.93          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 19.71/19.93      inference('sup-', [status(thm)], ['10', '11'])).
% 19.71/19.93  thf('13', plain,
% 19.71/19.93      (![X0 : $i, X1 : $i]:
% 19.71/19.93         (r1_tarski @ (k1_zfmisc_1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 19.71/19.93          (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0)))),
% 19.71/19.93      inference('sup+', [status(thm)], ['9', '12'])).
% 19.71/19.93  thf(t8_xboole_1, axiom,
% 19.71/19.93    (![A:$i,B:$i,C:$i]:
% 19.71/19.93     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 19.71/19.93       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 19.71/19.93  thf('14', plain,
% 19.71/19.93      (![X10 : $i, X11 : $i, X12 : $i]:
% 19.71/19.93         (~ (r1_tarski @ X10 @ X11)
% 19.71/19.93          | ~ (r1_tarski @ X12 @ X11)
% 19.71/19.93          | (r1_tarski @ (k2_xboole_0 @ X10 @ X12) @ X11))),
% 19.71/19.93      inference('cnf', [status(esa)], [t8_xboole_1])).
% 19.71/19.93  thf('15', plain,
% 19.71/19.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.71/19.93         ((r1_tarski @ 
% 19.71/19.93           (k2_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ X1 @ X0)) @ X2) @ 
% 19.71/19.93           (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0)))
% 19.71/19.93          | ~ (r1_tarski @ X2 @ (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0))))),
% 19.71/19.93      inference('sup-', [status(thm)], ['13', '14'])).
% 19.71/19.93  thf('16', plain,
% 19.71/19.93      (![X0 : $i, X1 : $i]:
% 19.71/19.93         (r1_tarski @ 
% 19.71/19.93          (k2_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 19.71/19.93           (k1_zfmisc_1 @ (k4_xboole_0 @ X0 @ X1))) @ 
% 19.71/19.93          (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0)))),
% 19.71/19.93      inference('sup-', [status(thm)], ['8', '15'])).
% 19.71/19.93  thf('17', plain, ($false), inference('demod', [status(thm)], ['0', '16'])).
% 19.71/19.93  
% 19.71/19.93  % SZS output end Refutation
% 19.71/19.93  
% 19.71/19.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

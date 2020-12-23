%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yta7cGTVqB

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:49 EST 2020

% Result     : Theorem 5.71s
% Output     : Refutation 5.71s
% Verified   : 
% Statistics : Number of formulae       :   37 (  40 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :  282 ( 306 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf(t79_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('7',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X20 ) @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t109_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ ( k4_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ X2 ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('12',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('13',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X20 ) @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf(t110_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('16',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X11 @ X10 )
      | ( r1_tarski @ ( k5_xboole_0 @ X9 @ X11 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t110_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_tarski @ X2 @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ X2 ) ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','18'])).

thf('20',plain,(
    $false ),
    inference(demod,[status(thm)],['0','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yta7cGTVqB
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 13:44:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 5.71/5.93  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.71/5.93  % Solved by: fo/fo7.sh
% 5.71/5.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.71/5.93  % done 2206 iterations in 5.433s
% 5.71/5.93  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.71/5.93  % SZS output start Refutation
% 5.71/5.93  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 5.71/5.93  thf(sk_B_type, type, sk_B: $i).
% 5.71/5.93  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.71/5.93  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 5.71/5.93  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 5.71/5.93  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.71/5.93  thf(sk_A_type, type, sk_A: $i).
% 5.71/5.93  thf(t86_zfmisc_1, conjecture,
% 5.71/5.93    (![A:$i,B:$i]:
% 5.71/5.93     ( r1_tarski @
% 5.71/5.93       ( k2_xboole_0 @
% 5.71/5.93         ( k1_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) ) @ 
% 5.71/5.93         ( k1_zfmisc_1 @ ( k4_xboole_0 @ B @ A ) ) ) @ 
% 5.71/5.93       ( k1_zfmisc_1 @ ( k5_xboole_0 @ A @ B ) ) ))).
% 5.71/5.93  thf(zf_stmt_0, negated_conjecture,
% 5.71/5.93    (~( ![A:$i,B:$i]:
% 5.71/5.93        ( r1_tarski @
% 5.71/5.93          ( k2_xboole_0 @
% 5.71/5.93            ( k1_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) ) @ 
% 5.71/5.93            ( k1_zfmisc_1 @ ( k4_xboole_0 @ B @ A ) ) ) @ 
% 5.71/5.93          ( k1_zfmisc_1 @ ( k5_xboole_0 @ A @ B ) ) ) )),
% 5.71/5.93    inference('cnf.neg', [status(esa)], [t86_zfmisc_1])).
% 5.71/5.93  thf('0', plain,
% 5.71/5.93      (~ (r1_tarski @ 
% 5.71/5.93          (k2_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_B)) @ 
% 5.71/5.93           (k1_zfmisc_1 @ (k4_xboole_0 @ sk_B @ sk_A))) @ 
% 5.71/5.93          (k1_zfmisc_1 @ (k5_xboole_0 @ sk_A @ sk_B)))),
% 5.71/5.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.71/5.93  thf(t98_xboole_1, axiom,
% 5.71/5.93    (![A:$i,B:$i]:
% 5.71/5.93     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 5.71/5.93  thf('1', plain,
% 5.71/5.93      (![X14 : $i, X15 : $i]:
% 5.71/5.93         ((k2_xboole_0 @ X14 @ X15)
% 5.71/5.93           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 5.71/5.93      inference('cnf', [status(esa)], [t98_xboole_1])).
% 5.71/5.93  thf(commutativity_k5_xboole_0, axiom,
% 5.71/5.93    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 5.71/5.93  thf('2', plain,
% 5.71/5.93      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 5.71/5.93      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 5.71/5.93  thf(d6_xboole_0, axiom,
% 5.71/5.93    (![A:$i,B:$i]:
% 5.71/5.93     ( ( k5_xboole_0 @ A @ B ) =
% 5.71/5.93       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 5.71/5.93  thf('3', plain,
% 5.71/5.93      (![X2 : $i, X3 : $i]:
% 5.71/5.93         ((k5_xboole_0 @ X2 @ X3)
% 5.71/5.93           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 5.71/5.93      inference('cnf', [status(esa)], [d6_xboole_0])).
% 5.71/5.93  thf(t7_xboole_1, axiom,
% 5.71/5.93    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 5.71/5.93  thf('4', plain,
% 5.71/5.93      (![X12 : $i, X13 : $i]: (r1_tarski @ X12 @ (k2_xboole_0 @ X12 @ X13))),
% 5.71/5.93      inference('cnf', [status(esa)], [t7_xboole_1])).
% 5.71/5.93  thf('5', plain,
% 5.71/5.93      (![X0 : $i, X1 : $i]:
% 5.71/5.93         (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))),
% 5.71/5.93      inference('sup+', [status(thm)], ['3', '4'])).
% 5.71/5.93  thf('6', plain,
% 5.71/5.93      (![X0 : $i, X1 : $i]:
% 5.71/5.93         (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0))),
% 5.71/5.93      inference('sup+', [status(thm)], ['2', '5'])).
% 5.71/5.93  thf(t79_zfmisc_1, axiom,
% 5.71/5.93    (![A:$i,B:$i]:
% 5.71/5.93     ( ( r1_tarski @ A @ B ) =>
% 5.71/5.93       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 5.71/5.93  thf('7', plain,
% 5.71/5.93      (![X20 : $i, X21 : $i]:
% 5.71/5.93         ((r1_tarski @ (k1_zfmisc_1 @ X20) @ (k1_zfmisc_1 @ X21))
% 5.71/5.93          | ~ (r1_tarski @ X20 @ X21))),
% 5.71/5.93      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 5.71/5.93  thf('8', plain,
% 5.71/5.93      (![X0 : $i, X1 : $i]:
% 5.71/5.93         (r1_tarski @ (k1_zfmisc_1 @ (k4_xboole_0 @ X0 @ X1)) @ 
% 5.71/5.93          (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0)))),
% 5.71/5.93      inference('sup-', [status(thm)], ['6', '7'])).
% 5.71/5.93  thf(t109_xboole_1, axiom,
% 5.71/5.93    (![A:$i,B:$i,C:$i]:
% 5.71/5.93     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 5.71/5.93  thf('9', plain,
% 5.71/5.93      (![X6 : $i, X7 : $i, X8 : $i]:
% 5.71/5.93         (~ (r1_tarski @ X6 @ X7) | (r1_tarski @ (k4_xboole_0 @ X6 @ X8) @ X7))),
% 5.71/5.93      inference('cnf', [status(esa)], [t109_xboole_1])).
% 5.71/5.93  thf('10', plain,
% 5.71/5.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.71/5.93         (r1_tarski @ 
% 5.71/5.93          (k4_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ X0 @ X1)) @ X2) @ 
% 5.71/5.93          (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0)))),
% 5.71/5.93      inference('sup-', [status(thm)], ['8', '9'])).
% 5.71/5.93  thf('11', plain,
% 5.71/5.93      (![X2 : $i, X3 : $i]:
% 5.71/5.93         ((k5_xboole_0 @ X2 @ X3)
% 5.71/5.93           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 5.71/5.93      inference('cnf', [status(esa)], [d6_xboole_0])).
% 5.71/5.93  thf('12', plain,
% 5.71/5.93      (![X12 : $i, X13 : $i]: (r1_tarski @ X12 @ (k2_xboole_0 @ X12 @ X13))),
% 5.71/5.93      inference('cnf', [status(esa)], [t7_xboole_1])).
% 5.71/5.93  thf('13', plain,
% 5.71/5.93      (![X20 : $i, X21 : $i]:
% 5.71/5.93         ((r1_tarski @ (k1_zfmisc_1 @ X20) @ (k1_zfmisc_1 @ X21))
% 5.71/5.93          | ~ (r1_tarski @ X20 @ X21))),
% 5.71/5.93      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 5.71/5.93  thf('14', plain,
% 5.71/5.93      (![X0 : $i, X1 : $i]:
% 5.71/5.93         (r1_tarski @ (k1_zfmisc_1 @ X1) @ 
% 5.71/5.93          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 5.71/5.93      inference('sup-', [status(thm)], ['12', '13'])).
% 5.71/5.93  thf('15', plain,
% 5.71/5.93      (![X0 : $i, X1 : $i]:
% 5.71/5.93         (r1_tarski @ (k1_zfmisc_1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 5.71/5.93          (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0)))),
% 5.71/5.93      inference('sup+', [status(thm)], ['11', '14'])).
% 5.71/5.93  thf(t110_xboole_1, axiom,
% 5.71/5.93    (![A:$i,B:$i,C:$i]:
% 5.71/5.93     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 5.71/5.93       ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 5.71/5.93  thf('16', plain,
% 5.71/5.93      (![X9 : $i, X10 : $i, X11 : $i]:
% 5.71/5.93         (~ (r1_tarski @ X9 @ X10)
% 5.71/5.93          | ~ (r1_tarski @ X11 @ X10)
% 5.71/5.93          | (r1_tarski @ (k5_xboole_0 @ X9 @ X11) @ X10))),
% 5.71/5.93      inference('cnf', [status(esa)], [t110_xboole_1])).
% 5.71/5.93  thf('17', plain,
% 5.71/5.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.71/5.93         ((r1_tarski @ 
% 5.71/5.93           (k5_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ X1 @ X0)) @ X2) @ 
% 5.71/5.93           (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0)))
% 5.71/5.93          | ~ (r1_tarski @ X2 @ (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0))))),
% 5.71/5.93      inference('sup-', [status(thm)], ['15', '16'])).
% 5.71/5.93  thf('18', plain,
% 5.71/5.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.71/5.93         (r1_tarski @ 
% 5.71/5.93          (k5_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 5.71/5.93           (k4_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ X0 @ X1)) @ X2)) @ 
% 5.71/5.93          (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0)))),
% 5.71/5.93      inference('sup-', [status(thm)], ['10', '17'])).
% 5.71/5.93  thf('19', plain,
% 5.71/5.93      (![X0 : $i, X1 : $i]:
% 5.71/5.93         (r1_tarski @ 
% 5.71/5.93          (k2_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ X0 @ X1)) @ 
% 5.71/5.93           (k1_zfmisc_1 @ (k4_xboole_0 @ X1 @ X0))) @ 
% 5.71/5.93          (k1_zfmisc_1 @ (k5_xboole_0 @ X0 @ X1)))),
% 5.71/5.93      inference('sup+', [status(thm)], ['1', '18'])).
% 5.71/5.93  thf('20', plain, ($false), inference('demod', [status(thm)], ['0', '19'])).
% 5.71/5.93  
% 5.71/5.93  % SZS output end Refutation
% 5.71/5.93  
% 5.71/5.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

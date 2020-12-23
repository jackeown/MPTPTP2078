%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HM1YZ7BtLS

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:50 EST 2020

% Result     : Theorem 0.83s
% Output     : Refutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :   41 (  42 expanded)
%              Number of leaves         :   19 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :  301 ( 309 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X7 @ ( k2_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t34_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ( r1_tarski @ ( k4_xboole_0 @ X14 @ X13 ) @ ( k4_xboole_0 @ X14 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t107_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r1_tarski @ X3 @ ( k5_xboole_0 @ X4 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ ( k3_xboole_0 @ X4 @ X6 ) )
      | ~ ( r1_tarski @ X3 @ ( k2_xboole_0 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t107_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf(t79_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X22 ) @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( r1_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t96_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ ( k5_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t96_xboole_1])).

thf('15',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X22 ) @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( r1_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('17',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X17 @ X18 )
      | ~ ( r1_tarski @ X19 @ X18 )
      | ( r1_tarski @ ( k2_xboole_0 @ X17 @ X19 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_tarski @ X2 @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    $false ),
    inference(demod,[status(thm)],['0','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HM1YZ7BtLS
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:55:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.83/1.04  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.83/1.04  % Solved by: fo/fo7.sh
% 0.83/1.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.83/1.04  % done 413 iterations in 0.606s
% 0.83/1.04  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.83/1.04  % SZS output start Refutation
% 0.83/1.04  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.83/1.04  thf(sk_B_type, type, sk_B: $i).
% 0.83/1.04  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.83/1.04  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.83/1.04  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.83/1.04  thf(sk_A_type, type, sk_A: $i).
% 0.83/1.04  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.83/1.04  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.83/1.04  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.83/1.04  thf(t86_zfmisc_1, conjecture,
% 0.83/1.04    (![A:$i,B:$i]:
% 0.83/1.04     ( r1_tarski @
% 0.83/1.04       ( k2_xboole_0 @
% 0.83/1.04         ( k1_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) ) @ 
% 0.83/1.04         ( k1_zfmisc_1 @ ( k4_xboole_0 @ B @ A ) ) ) @ 
% 0.83/1.04       ( k1_zfmisc_1 @ ( k5_xboole_0 @ A @ B ) ) ))).
% 0.83/1.04  thf(zf_stmt_0, negated_conjecture,
% 0.83/1.04    (~( ![A:$i,B:$i]:
% 0.83/1.04        ( r1_tarski @
% 0.83/1.04          ( k2_xboole_0 @
% 0.83/1.04            ( k1_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) ) @ 
% 0.83/1.04            ( k1_zfmisc_1 @ ( k4_xboole_0 @ B @ A ) ) ) @ 
% 0.83/1.04          ( k1_zfmisc_1 @ ( k5_xboole_0 @ A @ B ) ) ) )),
% 0.83/1.04    inference('cnf.neg', [status(esa)], [t86_zfmisc_1])).
% 0.83/1.04  thf('0', plain,
% 0.83/1.04      (~ (r1_tarski @ 
% 0.83/1.04          (k2_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_B)) @ 
% 0.83/1.04           (k1_zfmisc_1 @ (k4_xboole_0 @ sk_B @ sk_A))) @ 
% 0.83/1.04          (k1_zfmisc_1 @ (k5_xboole_0 @ sk_A @ sk_B)))),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf(t36_xboole_1, axiom,
% 0.83/1.04    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.83/1.04  thf('1', plain,
% 0.83/1.04      (![X15 : $i, X16 : $i]: (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X15)),
% 0.83/1.04      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.83/1.04  thf(t10_xboole_1, axiom,
% 0.83/1.04    (![A:$i,B:$i,C:$i]:
% 0.83/1.04     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.83/1.04  thf('2', plain,
% 0.83/1.04      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.83/1.04         (~ (r1_tarski @ X7 @ X8) | (r1_tarski @ X7 @ (k2_xboole_0 @ X9 @ X8)))),
% 0.83/1.04      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.83/1.04  thf('3', plain,
% 0.83/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.04         (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X2 @ X0))),
% 0.83/1.04      inference('sup-', [status(thm)], ['1', '2'])).
% 0.83/1.04  thf(t17_xboole_1, axiom,
% 0.83/1.04    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.83/1.04  thf('4', plain,
% 0.83/1.04      (![X10 : $i, X11 : $i]: (r1_tarski @ (k3_xboole_0 @ X10 @ X11) @ X10)),
% 0.83/1.04      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.83/1.04  thf(t34_xboole_1, axiom,
% 0.83/1.04    (![A:$i,B:$i,C:$i]:
% 0.83/1.04     ( ( r1_tarski @ A @ B ) =>
% 0.83/1.04       ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ))).
% 0.83/1.04  thf('5', plain,
% 0.83/1.04      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.83/1.04         (~ (r1_tarski @ X12 @ X13)
% 0.83/1.04          | (r1_tarski @ (k4_xboole_0 @ X14 @ X13) @ (k4_xboole_0 @ X14 @ X12)))),
% 0.83/1.04      inference('cnf', [status(esa)], [t34_xboole_1])).
% 0.83/1.04  thf('6', plain,
% 0.83/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.04         (r1_tarski @ (k4_xboole_0 @ X2 @ X0) @ 
% 0.83/1.04          (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['4', '5'])).
% 0.83/1.04  thf(t106_xboole_1, axiom,
% 0.83/1.04    (![A:$i,B:$i,C:$i]:
% 0.83/1.04     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.83/1.04       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.83/1.04  thf('7', plain,
% 0.83/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.04         ((r1_xboole_0 @ X0 @ X2)
% 0.83/1.04          | ~ (r1_tarski @ X0 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.83/1.04      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.83/1.04  thf('8', plain,
% 0.83/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.04         (r1_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k3_xboole_0 @ X1 @ X0))),
% 0.83/1.04      inference('sup-', [status(thm)], ['6', '7'])).
% 0.83/1.04  thf(t107_xboole_1, axiom,
% 0.83/1.04    (![A:$i,B:$i,C:$i]:
% 0.83/1.04     ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.83/1.04       ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 0.83/1.04         ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 0.83/1.04  thf('9', plain,
% 0.83/1.04      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.83/1.04         ((r1_tarski @ X3 @ (k5_xboole_0 @ X4 @ X6))
% 0.83/1.04          | ~ (r1_xboole_0 @ X3 @ (k3_xboole_0 @ X4 @ X6))
% 0.83/1.04          | ~ (r1_tarski @ X3 @ (k2_xboole_0 @ X4 @ X6)))),
% 0.83/1.04      inference('cnf', [status(esa)], [t107_xboole_1])).
% 0.83/1.04  thf('10', plain,
% 0.83/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.04         (~ (r1_tarski @ (k4_xboole_0 @ X2 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 0.83/1.04          | (r1_tarski @ (k4_xboole_0 @ X2 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['8', '9'])).
% 0.83/1.04  thf('11', plain,
% 0.83/1.04      (![X0 : $i, X1 : $i]:
% 0.83/1.04         (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0))),
% 0.83/1.04      inference('sup-', [status(thm)], ['3', '10'])).
% 0.83/1.04  thf(t79_zfmisc_1, axiom,
% 0.83/1.04    (![A:$i,B:$i]:
% 0.83/1.04     ( ( r1_tarski @ A @ B ) =>
% 0.83/1.04       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.83/1.04  thf('12', plain,
% 0.83/1.04      (![X22 : $i, X23 : $i]:
% 0.83/1.04         ((r1_tarski @ (k1_zfmisc_1 @ X22) @ (k1_zfmisc_1 @ X23))
% 0.83/1.04          | ~ (r1_tarski @ X22 @ X23))),
% 0.83/1.04      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 0.83/1.04  thf('13', plain,
% 0.83/1.04      (![X0 : $i, X1 : $i]:
% 0.83/1.04         (r1_tarski @ (k1_zfmisc_1 @ (k4_xboole_0 @ X0 @ X1)) @ 
% 0.83/1.04          (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['11', '12'])).
% 0.83/1.04  thf(t96_xboole_1, axiom,
% 0.83/1.04    (![A:$i,B:$i]:
% 0.83/1.04     ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 0.83/1.04  thf('14', plain,
% 0.83/1.04      (![X20 : $i, X21 : $i]:
% 0.83/1.04         (r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ (k5_xboole_0 @ X20 @ X21))),
% 0.83/1.04      inference('cnf', [status(esa)], [t96_xboole_1])).
% 0.83/1.04  thf('15', plain,
% 0.83/1.04      (![X22 : $i, X23 : $i]:
% 0.83/1.04         ((r1_tarski @ (k1_zfmisc_1 @ X22) @ (k1_zfmisc_1 @ X23))
% 0.83/1.04          | ~ (r1_tarski @ X22 @ X23))),
% 0.83/1.04      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 0.83/1.04  thf('16', plain,
% 0.83/1.04      (![X0 : $i, X1 : $i]:
% 0.83/1.04         (r1_tarski @ (k1_zfmisc_1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 0.83/1.04          (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['14', '15'])).
% 0.83/1.04  thf(t8_xboole_1, axiom,
% 0.83/1.04    (![A:$i,B:$i,C:$i]:
% 0.83/1.04     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.83/1.04       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.83/1.04  thf('17', plain,
% 0.83/1.04      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.83/1.04         (~ (r1_tarski @ X17 @ X18)
% 0.83/1.04          | ~ (r1_tarski @ X19 @ X18)
% 0.83/1.04          | (r1_tarski @ (k2_xboole_0 @ X17 @ X19) @ X18))),
% 0.83/1.04      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.83/1.04  thf('18', plain,
% 0.83/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.04         ((r1_tarski @ 
% 0.83/1.04           (k2_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ X1 @ X0)) @ X2) @ 
% 0.83/1.04           (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0)))
% 0.83/1.04          | ~ (r1_tarski @ X2 @ (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0))))),
% 0.83/1.04      inference('sup-', [status(thm)], ['16', '17'])).
% 0.83/1.04  thf('19', plain,
% 0.83/1.04      (![X0 : $i, X1 : $i]:
% 0.83/1.04         (r1_tarski @ 
% 0.83/1.04          (k2_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 0.83/1.04           (k1_zfmisc_1 @ (k4_xboole_0 @ X0 @ X1))) @ 
% 0.83/1.04          (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['13', '18'])).
% 0.83/1.04  thf('20', plain, ($false), inference('demod', [status(thm)], ['0', '19'])).
% 0.83/1.04  
% 0.83/1.04  % SZS output end Refutation
% 0.83/1.04  
% 0.83/1.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BOKBCjE6sP

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:48 EST 2020

% Result     : Theorem 6.04s
% Output     : Refutation 6.04s
% Verified   : 
% Statistics : Number of formulae       :   43 (  53 expanded)
%              Number of leaves         :   17 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :  345 ( 419 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t79_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X25 ) @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( r1_tarski @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t108_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ ( k3_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k1_zfmisc_1 @ X1 ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t110_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('10',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_tarski @ X13 @ X12 )
      | ( r1_tarski @ ( k5_xboole_0 @ X11 @ X13 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t110_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_xboole_0 @ ( k1_zfmisc_1 @ X1 ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_tarski @ X2 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ ( k1_zfmisc_1 @ X1 ) @ ( k3_xboole_0 @ ( k1_zfmisc_1 @ X1 ) @ X2 ) ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ X1 ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ X2 ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','15'])).

thf('17',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_tarski @ X13 @ X12 )
      | ( r1_tarski @ ( k5_xboole_0 @ X11 @ X13 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t110_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_tarski @ X2 @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ X2 ) ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','22'])).

thf('24',plain,(
    $false ),
    inference(demod,[status(thm)],['0','23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BOKBCjE6sP
% 0.16/0.39  % Computer   : n025.cluster.edu
% 0.16/0.39  % Model      : x86_64 x86_64
% 0.16/0.39  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.39  % Memory     : 8042.1875MB
% 0.16/0.39  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.39  % CPULimit   : 60
% 0.16/0.39  % DateTime   : Tue Dec  1 17:29:51 EST 2020
% 0.16/0.39  % CPUTime    : 
% 0.16/0.39  % Running portfolio for 600 s
% 0.16/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.39  % Number of cores: 8
% 0.16/0.39  % Python version: Python 3.6.8
% 0.16/0.39  % Running in FO mode
% 6.04/6.26  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.04/6.26  % Solved by: fo/fo7.sh
% 6.04/6.26  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.04/6.26  % done 4364 iterations in 5.760s
% 6.04/6.26  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.04/6.26  % SZS output start Refutation
% 6.04/6.26  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 6.04/6.26  thf(sk_A_type, type, sk_A: $i).
% 6.04/6.26  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 6.04/6.26  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 6.04/6.26  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.04/6.26  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 6.04/6.26  thf(sk_B_type, type, sk_B: $i).
% 6.04/6.26  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.04/6.26  thf(t86_zfmisc_1, conjecture,
% 6.04/6.26    (![A:$i,B:$i]:
% 6.04/6.26     ( r1_tarski @
% 6.04/6.26       ( k2_xboole_0 @
% 6.04/6.26         ( k1_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) ) @ 
% 6.04/6.26         ( k1_zfmisc_1 @ ( k4_xboole_0 @ B @ A ) ) ) @ 
% 6.04/6.26       ( k1_zfmisc_1 @ ( k5_xboole_0 @ A @ B ) ) ))).
% 6.04/6.26  thf(zf_stmt_0, negated_conjecture,
% 6.04/6.26    (~( ![A:$i,B:$i]:
% 6.04/6.26        ( r1_tarski @
% 6.04/6.26          ( k2_xboole_0 @
% 6.04/6.26            ( k1_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) ) @ 
% 6.04/6.26            ( k1_zfmisc_1 @ ( k4_xboole_0 @ B @ A ) ) ) @ 
% 6.04/6.26          ( k1_zfmisc_1 @ ( k5_xboole_0 @ A @ B ) ) ) )),
% 6.04/6.26    inference('cnf.neg', [status(esa)], [t86_zfmisc_1])).
% 6.04/6.26  thf('0', plain,
% 6.04/6.26      (~ (r1_tarski @ 
% 6.04/6.26          (k2_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_B)) @ 
% 6.04/6.26           (k1_zfmisc_1 @ (k4_xboole_0 @ sk_B @ sk_A))) @ 
% 6.04/6.26          (k1_zfmisc_1 @ (k5_xboole_0 @ sk_A @ sk_B)))),
% 6.04/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.04/6.26  thf(t98_xboole_1, axiom,
% 6.04/6.26    (![A:$i,B:$i]:
% 6.04/6.26     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 6.04/6.26  thf('1', plain,
% 6.04/6.26      (![X16 : $i, X17 : $i]:
% 6.04/6.26         ((k2_xboole_0 @ X16 @ X17)
% 6.04/6.26           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 6.04/6.26      inference('cnf', [status(esa)], [t98_xboole_1])).
% 6.04/6.26  thf(commutativity_k5_xboole_0, axiom,
% 6.04/6.26    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 6.04/6.26  thf('2', plain,
% 6.04/6.26      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 6.04/6.26      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 6.04/6.26  thf(d6_xboole_0, axiom,
% 6.04/6.26    (![A:$i,B:$i]:
% 6.04/6.26     ( ( k5_xboole_0 @ A @ B ) =
% 6.04/6.26       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 6.04/6.26  thf('3', plain,
% 6.04/6.26      (![X4 : $i, X5 : $i]:
% 6.04/6.26         ((k5_xboole_0 @ X4 @ X5)
% 6.04/6.26           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 6.04/6.26      inference('cnf', [status(esa)], [d6_xboole_0])).
% 6.04/6.26  thf(t7_xboole_1, axiom,
% 6.04/6.26    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 6.04/6.26  thf('4', plain,
% 6.04/6.26      (![X14 : $i, X15 : $i]: (r1_tarski @ X14 @ (k2_xboole_0 @ X14 @ X15))),
% 6.04/6.26      inference('cnf', [status(esa)], [t7_xboole_1])).
% 6.04/6.26  thf(t79_zfmisc_1, axiom,
% 6.04/6.26    (![A:$i,B:$i]:
% 6.04/6.26     ( ( r1_tarski @ A @ B ) =>
% 6.04/6.26       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 6.04/6.26  thf('5', plain,
% 6.04/6.26      (![X25 : $i, X26 : $i]:
% 6.04/6.26         ((r1_tarski @ (k1_zfmisc_1 @ X25) @ (k1_zfmisc_1 @ X26))
% 6.04/6.26          | ~ (r1_tarski @ X25 @ X26))),
% 6.04/6.26      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 6.04/6.26  thf('6', plain,
% 6.04/6.26      (![X0 : $i, X1 : $i]:
% 6.04/6.26         (r1_tarski @ (k1_zfmisc_1 @ X1) @ 
% 6.04/6.26          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 6.04/6.26      inference('sup-', [status(thm)], ['4', '5'])).
% 6.04/6.26  thf(t108_xboole_1, axiom,
% 6.04/6.26    (![A:$i,B:$i,C:$i]:
% 6.04/6.26     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ))).
% 6.04/6.26  thf('7', plain,
% 6.04/6.26      (![X8 : $i, X9 : $i, X10 : $i]:
% 6.04/6.26         (~ (r1_tarski @ X8 @ X9) | (r1_tarski @ (k3_xboole_0 @ X8 @ X10) @ X9))),
% 6.04/6.26      inference('cnf', [status(esa)], [t108_xboole_1])).
% 6.04/6.26  thf('8', plain,
% 6.04/6.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.04/6.26         (r1_tarski @ (k3_xboole_0 @ (k1_zfmisc_1 @ X1) @ X2) @ 
% 6.04/6.26          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 6.04/6.26      inference('sup-', [status(thm)], ['6', '7'])).
% 6.04/6.26  thf('9', plain,
% 6.04/6.26      (![X0 : $i, X1 : $i]:
% 6.04/6.26         (r1_tarski @ (k1_zfmisc_1 @ X1) @ 
% 6.04/6.26          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 6.04/6.26      inference('sup-', [status(thm)], ['4', '5'])).
% 6.04/6.26  thf(t110_xboole_1, axiom,
% 6.04/6.26    (![A:$i,B:$i,C:$i]:
% 6.04/6.26     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 6.04/6.26       ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 6.04/6.26  thf('10', plain,
% 6.04/6.26      (![X11 : $i, X12 : $i, X13 : $i]:
% 6.04/6.26         (~ (r1_tarski @ X11 @ X12)
% 6.04/6.26          | ~ (r1_tarski @ X13 @ X12)
% 6.04/6.26          | (r1_tarski @ (k5_xboole_0 @ X11 @ X13) @ X12))),
% 6.04/6.26      inference('cnf', [status(esa)], [t110_xboole_1])).
% 6.04/6.26  thf('11', plain,
% 6.04/6.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.04/6.26         ((r1_tarski @ (k5_xboole_0 @ (k1_zfmisc_1 @ X1) @ X2) @ 
% 6.04/6.26           (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 6.04/6.26          | ~ (r1_tarski @ X2 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0))))),
% 6.04/6.26      inference('sup-', [status(thm)], ['9', '10'])).
% 6.04/6.26  thf('12', plain,
% 6.04/6.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.04/6.26         (r1_tarski @ 
% 6.04/6.26          (k5_xboole_0 @ (k1_zfmisc_1 @ X1) @ 
% 6.04/6.26           (k3_xboole_0 @ (k1_zfmisc_1 @ X1) @ X2)) @ 
% 6.04/6.26          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 6.04/6.26      inference('sup-', [status(thm)], ['8', '11'])).
% 6.04/6.26  thf(t100_xboole_1, axiom,
% 6.04/6.26    (![A:$i,B:$i]:
% 6.04/6.26     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 6.04/6.26  thf('13', plain,
% 6.04/6.26      (![X6 : $i, X7 : $i]:
% 6.04/6.26         ((k4_xboole_0 @ X6 @ X7)
% 6.04/6.26           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 6.04/6.26      inference('cnf', [status(esa)], [t100_xboole_1])).
% 6.04/6.26  thf('14', plain,
% 6.04/6.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.04/6.26         (r1_tarski @ (k4_xboole_0 @ (k1_zfmisc_1 @ X1) @ X2) @ 
% 6.04/6.26          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 6.04/6.26      inference('demod', [status(thm)], ['12', '13'])).
% 6.04/6.26  thf('15', plain,
% 6.04/6.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.04/6.26         (r1_tarski @ 
% 6.04/6.26          (k4_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ X1 @ X0)) @ X2) @ 
% 6.04/6.26          (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0)))),
% 6.04/6.26      inference('sup+', [status(thm)], ['3', '14'])).
% 6.04/6.26  thf('16', plain,
% 6.04/6.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.04/6.26         (r1_tarski @ 
% 6.04/6.26          (k4_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ X0 @ X1)) @ X2) @ 
% 6.04/6.26          (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0)))),
% 6.04/6.26      inference('sup+', [status(thm)], ['2', '15'])).
% 6.04/6.26  thf('17', plain,
% 6.04/6.26      (![X4 : $i, X5 : $i]:
% 6.04/6.26         ((k5_xboole_0 @ X4 @ X5)
% 6.04/6.26           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 6.04/6.26      inference('cnf', [status(esa)], [d6_xboole_0])).
% 6.04/6.26  thf('18', plain,
% 6.04/6.26      (![X0 : $i, X1 : $i]:
% 6.04/6.26         (r1_tarski @ (k1_zfmisc_1 @ X1) @ 
% 6.04/6.26          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 6.04/6.26      inference('sup-', [status(thm)], ['4', '5'])).
% 6.04/6.26  thf('19', plain,
% 6.04/6.26      (![X0 : $i, X1 : $i]:
% 6.04/6.26         (r1_tarski @ (k1_zfmisc_1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 6.04/6.26          (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0)))),
% 6.04/6.26      inference('sup+', [status(thm)], ['17', '18'])).
% 6.04/6.26  thf('20', plain,
% 6.04/6.26      (![X11 : $i, X12 : $i, X13 : $i]:
% 6.04/6.26         (~ (r1_tarski @ X11 @ X12)
% 6.04/6.26          | ~ (r1_tarski @ X13 @ X12)
% 6.04/6.26          | (r1_tarski @ (k5_xboole_0 @ X11 @ X13) @ X12))),
% 6.04/6.26      inference('cnf', [status(esa)], [t110_xboole_1])).
% 6.04/6.26  thf('21', plain,
% 6.04/6.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.04/6.26         ((r1_tarski @ 
% 6.04/6.26           (k5_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ X1 @ X0)) @ X2) @ 
% 6.04/6.26           (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0)))
% 6.04/6.26          | ~ (r1_tarski @ X2 @ (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0))))),
% 6.04/6.26      inference('sup-', [status(thm)], ['19', '20'])).
% 6.04/6.26  thf('22', plain,
% 6.04/6.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.04/6.26         (r1_tarski @ 
% 6.04/6.26          (k5_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 6.04/6.26           (k4_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ X0 @ X1)) @ X2)) @ 
% 6.04/6.26          (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0)))),
% 6.04/6.26      inference('sup-', [status(thm)], ['16', '21'])).
% 6.04/6.26  thf('23', plain,
% 6.04/6.26      (![X0 : $i, X1 : $i]:
% 6.04/6.26         (r1_tarski @ 
% 6.04/6.26          (k2_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ X0 @ X1)) @ 
% 6.04/6.26           (k1_zfmisc_1 @ (k4_xboole_0 @ X1 @ X0))) @ 
% 6.04/6.26          (k1_zfmisc_1 @ (k5_xboole_0 @ X0 @ X1)))),
% 6.04/6.26      inference('sup+', [status(thm)], ['1', '22'])).
% 6.04/6.26  thf('24', plain, ($false), inference('demod', [status(thm)], ['0', '23'])).
% 6.04/6.26  
% 6.04/6.26  % SZS output end Refutation
% 6.04/6.26  
% 6.04/6.26  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

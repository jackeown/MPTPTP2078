%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hwbft9B54K

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:49 EST 2020

% Result     : Theorem 1.05s
% Output     : Refutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :   36 (  47 expanded)
%              Number of leaves         :   16 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :  292 ( 383 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   12 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
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

thf(t96_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ ( k5_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t96_xboole_1])).

thf(t79_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('4',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X23 ) @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t108_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ ( k3_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t110_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X11 @ X10 )
      | ( r1_tarski @ ( k5_xboole_0 @ X9 @ X11 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t110_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_tarski @ X2 @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 ) ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ X2 ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_tarski @ X2 @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ X2 ) ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','16'])).

thf('18',plain,(
    $false ),
    inference(demod,[status(thm)],['0','17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hwbft9B54K
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:30:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.05/1.28  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.05/1.28  % Solved by: fo/fo7.sh
% 1.05/1.28  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.05/1.28  % done 1171 iterations in 0.819s
% 1.05/1.28  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.05/1.28  % SZS output start Refutation
% 1.05/1.28  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.05/1.28  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.05/1.28  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.05/1.28  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.05/1.28  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.05/1.28  thf(sk_A_type, type, sk_A: $i).
% 1.05/1.28  thf(sk_B_type, type, sk_B: $i).
% 1.05/1.28  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.05/1.28  thf(t86_zfmisc_1, conjecture,
% 1.05/1.28    (![A:$i,B:$i]:
% 1.05/1.28     ( r1_tarski @
% 1.05/1.28       ( k2_xboole_0 @
% 1.05/1.28         ( k1_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) ) @ 
% 1.05/1.28         ( k1_zfmisc_1 @ ( k4_xboole_0 @ B @ A ) ) ) @ 
% 1.05/1.28       ( k1_zfmisc_1 @ ( k5_xboole_0 @ A @ B ) ) ))).
% 1.05/1.28  thf(zf_stmt_0, negated_conjecture,
% 1.05/1.28    (~( ![A:$i,B:$i]:
% 1.05/1.28        ( r1_tarski @
% 1.05/1.28          ( k2_xboole_0 @
% 1.05/1.28            ( k1_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) ) @ 
% 1.05/1.28            ( k1_zfmisc_1 @ ( k4_xboole_0 @ B @ A ) ) ) @ 
% 1.05/1.28          ( k1_zfmisc_1 @ ( k5_xboole_0 @ A @ B ) ) ) )),
% 1.05/1.28    inference('cnf.neg', [status(esa)], [t86_zfmisc_1])).
% 1.05/1.28  thf('0', plain,
% 1.05/1.28      (~ (r1_tarski @ 
% 1.05/1.28          (k2_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_B)) @ 
% 1.05/1.28           (k1_zfmisc_1 @ (k4_xboole_0 @ sk_B @ sk_A))) @ 
% 1.05/1.28          (k1_zfmisc_1 @ (k5_xboole_0 @ sk_A @ sk_B)))),
% 1.05/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.28  thf(t98_xboole_1, axiom,
% 1.05/1.28    (![A:$i,B:$i]:
% 1.05/1.28     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.05/1.28  thf('1', plain,
% 1.05/1.28      (![X14 : $i, X15 : $i]:
% 1.05/1.28         ((k2_xboole_0 @ X14 @ X15)
% 1.05/1.28           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 1.05/1.28      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.05/1.28  thf(commutativity_k5_xboole_0, axiom,
% 1.05/1.28    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 1.05/1.28  thf('2', plain,
% 1.05/1.28      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.05/1.28      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.05/1.28  thf(t96_xboole_1, axiom,
% 1.05/1.28    (![A:$i,B:$i]:
% 1.05/1.28     ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 1.05/1.28  thf('3', plain,
% 1.05/1.28      (![X12 : $i, X13 : $i]:
% 1.05/1.28         (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ (k5_xboole_0 @ X12 @ X13))),
% 1.05/1.28      inference('cnf', [status(esa)], [t96_xboole_1])).
% 1.05/1.28  thf(t79_zfmisc_1, axiom,
% 1.05/1.28    (![A:$i,B:$i]:
% 1.05/1.28     ( ( r1_tarski @ A @ B ) =>
% 1.05/1.28       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 1.05/1.28  thf('4', plain,
% 1.05/1.28      (![X23 : $i, X24 : $i]:
% 1.05/1.28         ((r1_tarski @ (k1_zfmisc_1 @ X23) @ (k1_zfmisc_1 @ X24))
% 1.05/1.28          | ~ (r1_tarski @ X23 @ X24))),
% 1.05/1.28      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 1.05/1.28  thf('5', plain,
% 1.05/1.28      (![X0 : $i, X1 : $i]:
% 1.05/1.28         (r1_tarski @ (k1_zfmisc_1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 1.05/1.28          (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.05/1.28      inference('sup-', [status(thm)], ['3', '4'])).
% 1.05/1.28  thf(t108_xboole_1, axiom,
% 1.05/1.28    (![A:$i,B:$i,C:$i]:
% 1.05/1.28     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ))).
% 1.05/1.28  thf('6', plain,
% 1.05/1.28      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.05/1.28         (~ (r1_tarski @ X6 @ X7) | (r1_tarski @ (k3_xboole_0 @ X6 @ X8) @ X7))),
% 1.05/1.28      inference('cnf', [status(esa)], [t108_xboole_1])).
% 1.05/1.28  thf('7', plain,
% 1.05/1.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.28         (r1_tarski @ 
% 1.05/1.28          (k3_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ X1 @ X0)) @ X2) @ 
% 1.05/1.28          (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.05/1.28      inference('sup-', [status(thm)], ['5', '6'])).
% 1.05/1.28  thf('8', plain,
% 1.05/1.28      (![X0 : $i, X1 : $i]:
% 1.05/1.28         (r1_tarski @ (k1_zfmisc_1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 1.05/1.28          (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.05/1.28      inference('sup-', [status(thm)], ['3', '4'])).
% 1.05/1.28  thf(t110_xboole_1, axiom,
% 1.05/1.28    (![A:$i,B:$i,C:$i]:
% 1.05/1.28     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 1.05/1.28       ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 1.05/1.28  thf('9', plain,
% 1.05/1.28      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.05/1.28         (~ (r1_tarski @ X9 @ X10)
% 1.05/1.28          | ~ (r1_tarski @ X11 @ X10)
% 1.05/1.28          | (r1_tarski @ (k5_xboole_0 @ X9 @ X11) @ X10))),
% 1.05/1.28      inference('cnf', [status(esa)], [t110_xboole_1])).
% 1.05/1.28  thf('10', plain,
% 1.05/1.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.28         ((r1_tarski @ 
% 1.05/1.28           (k5_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ X1 @ X0)) @ X2) @ 
% 1.05/1.28           (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0)))
% 1.05/1.28          | ~ (r1_tarski @ X2 @ (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0))))),
% 1.05/1.28      inference('sup-', [status(thm)], ['8', '9'])).
% 1.05/1.28  thf('11', plain,
% 1.05/1.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.28         (r1_tarski @ 
% 1.05/1.28          (k5_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 1.05/1.28           (k3_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ X1 @ X0)) @ X2)) @ 
% 1.05/1.28          (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.05/1.28      inference('sup-', [status(thm)], ['7', '10'])).
% 1.05/1.28  thf(t100_xboole_1, axiom,
% 1.05/1.28    (![A:$i,B:$i]:
% 1.05/1.28     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.05/1.28  thf('12', plain,
% 1.05/1.28      (![X4 : $i, X5 : $i]:
% 1.05/1.28         ((k4_xboole_0 @ X4 @ X5)
% 1.05/1.28           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 1.05/1.28      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.05/1.28  thf('13', plain,
% 1.05/1.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.28         (r1_tarski @ 
% 1.05/1.28          (k4_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ X1 @ X0)) @ X2) @ 
% 1.05/1.28          (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.05/1.28      inference('demod', [status(thm)], ['11', '12'])).
% 1.05/1.28  thf('14', plain,
% 1.05/1.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.28         (r1_tarski @ 
% 1.05/1.28          (k4_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ X0 @ X1)) @ X2) @ 
% 1.05/1.28          (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.05/1.28      inference('sup+', [status(thm)], ['2', '13'])).
% 1.05/1.28  thf('15', plain,
% 1.05/1.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.28         ((r1_tarski @ 
% 1.05/1.28           (k5_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ X1 @ X0)) @ X2) @ 
% 1.05/1.28           (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0)))
% 1.05/1.28          | ~ (r1_tarski @ X2 @ (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0))))),
% 1.05/1.28      inference('sup-', [status(thm)], ['8', '9'])).
% 1.05/1.28  thf('16', plain,
% 1.05/1.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.28         (r1_tarski @ 
% 1.05/1.28          (k5_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 1.05/1.28           (k4_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ X0 @ X1)) @ X2)) @ 
% 1.05/1.28          (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.05/1.28      inference('sup-', [status(thm)], ['14', '15'])).
% 1.05/1.28  thf('17', plain,
% 1.05/1.28      (![X0 : $i, X1 : $i]:
% 1.05/1.28         (r1_tarski @ 
% 1.05/1.28          (k2_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ X0 @ X1)) @ 
% 1.05/1.28           (k1_zfmisc_1 @ (k4_xboole_0 @ X1 @ X0))) @ 
% 1.05/1.28          (k1_zfmisc_1 @ (k5_xboole_0 @ X0 @ X1)))),
% 1.05/1.28      inference('sup+', [status(thm)], ['1', '16'])).
% 1.05/1.28  thf('18', plain, ($false), inference('demod', [status(thm)], ['0', '17'])).
% 1.05/1.28  
% 1.05/1.28  % SZS output end Refutation
% 1.05/1.28  
% 1.05/1.29  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

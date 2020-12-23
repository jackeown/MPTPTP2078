%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.28goptbTNS

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:48 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   29 (  31 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    6
%              Number of atoms          :  198 ( 211 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t79_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X15 ) @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('8',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X15 ) @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ X1 ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_tarski @ X2 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','12'])).

thf('14',plain,(
    $false ),
    inference(demod,[status(thm)],['0','13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.28goptbTNS
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:16:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.32/1.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.32/1.48  % Solved by: fo/fo7.sh
% 1.32/1.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.32/1.48  % done 1531 iterations in 1.042s
% 1.32/1.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.32/1.48  % SZS output start Refutation
% 1.32/1.48  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.32/1.48  thf(sk_A_type, type, sk_A: $i).
% 1.32/1.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.32/1.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.32/1.48  thf(sk_B_type, type, sk_B: $i).
% 1.32/1.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.32/1.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.32/1.48  thf(t86_zfmisc_1, conjecture,
% 1.32/1.48    (![A:$i,B:$i]:
% 1.32/1.48     ( r1_tarski @
% 1.32/1.48       ( k2_xboole_0 @
% 1.32/1.48         ( k1_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) ) @ 
% 1.32/1.48         ( k1_zfmisc_1 @ ( k4_xboole_0 @ B @ A ) ) ) @ 
% 1.32/1.48       ( k1_zfmisc_1 @ ( k5_xboole_0 @ A @ B ) ) ))).
% 1.32/1.48  thf(zf_stmt_0, negated_conjecture,
% 1.32/1.48    (~( ![A:$i,B:$i]:
% 1.32/1.48        ( r1_tarski @
% 1.32/1.48          ( k2_xboole_0 @
% 1.32/1.48            ( k1_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) ) @ 
% 1.32/1.48            ( k1_zfmisc_1 @ ( k4_xboole_0 @ B @ A ) ) ) @ 
% 1.32/1.48          ( k1_zfmisc_1 @ ( k5_xboole_0 @ A @ B ) ) ) )),
% 1.32/1.48    inference('cnf.neg', [status(esa)], [t86_zfmisc_1])).
% 1.32/1.48  thf('0', plain,
% 1.32/1.48      (~ (r1_tarski @ 
% 1.32/1.48          (k2_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_B)) @ 
% 1.32/1.48           (k1_zfmisc_1 @ (k4_xboole_0 @ sk_B @ sk_A))) @ 
% 1.32/1.48          (k1_zfmisc_1 @ (k5_xboole_0 @ sk_A @ sk_B)))),
% 1.32/1.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.48  thf(d6_xboole_0, axiom,
% 1.32/1.48    (![A:$i,B:$i]:
% 1.32/1.48     ( ( k5_xboole_0 @ A @ B ) =
% 1.32/1.48       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.32/1.48  thf('1', plain,
% 1.32/1.48      (![X2 : $i, X3 : $i]:
% 1.32/1.48         ((k5_xboole_0 @ X2 @ X3)
% 1.32/1.48           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 1.32/1.48      inference('cnf', [status(esa)], [d6_xboole_0])).
% 1.32/1.48  thf(commutativity_k2_xboole_0, axiom,
% 1.32/1.48    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.32/1.48  thf('2', plain,
% 1.32/1.48      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.32/1.48      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.32/1.48  thf(t7_xboole_1, axiom,
% 1.32/1.48    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.32/1.48  thf('3', plain,
% 1.32/1.48      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 1.32/1.48      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.32/1.48  thf('4', plain,
% 1.32/1.48      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.32/1.48      inference('sup+', [status(thm)], ['2', '3'])).
% 1.32/1.48  thf(t79_zfmisc_1, axiom,
% 1.32/1.48    (![A:$i,B:$i]:
% 1.32/1.48     ( ( r1_tarski @ A @ B ) =>
% 1.32/1.48       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 1.32/1.48  thf('5', plain,
% 1.32/1.48      (![X15 : $i, X16 : $i]:
% 1.32/1.48         ((r1_tarski @ (k1_zfmisc_1 @ X15) @ (k1_zfmisc_1 @ X16))
% 1.32/1.48          | ~ (r1_tarski @ X15 @ X16))),
% 1.32/1.48      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 1.32/1.48  thf('6', plain,
% 1.32/1.48      (![X0 : $i, X1 : $i]:
% 1.32/1.48         (r1_tarski @ (k1_zfmisc_1 @ X0) @ 
% 1.32/1.48          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.32/1.48      inference('sup-', [status(thm)], ['4', '5'])).
% 1.32/1.48  thf('7', plain,
% 1.32/1.48      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 1.32/1.48      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.32/1.48  thf('8', plain,
% 1.32/1.48      (![X15 : $i, X16 : $i]:
% 1.32/1.48         ((r1_tarski @ (k1_zfmisc_1 @ X15) @ (k1_zfmisc_1 @ X16))
% 1.32/1.48          | ~ (r1_tarski @ X15 @ X16))),
% 1.32/1.48      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 1.32/1.48  thf('9', plain,
% 1.32/1.48      (![X0 : $i, X1 : $i]:
% 1.32/1.48         (r1_tarski @ (k1_zfmisc_1 @ X1) @ 
% 1.32/1.48          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.32/1.48      inference('sup-', [status(thm)], ['7', '8'])).
% 1.32/1.48  thf(t8_xboole_1, axiom,
% 1.32/1.48    (![A:$i,B:$i,C:$i]:
% 1.32/1.48     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 1.32/1.48       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.32/1.48  thf('10', plain,
% 1.32/1.48      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.32/1.48         (~ (r1_tarski @ X8 @ X9)
% 1.32/1.48          | ~ (r1_tarski @ X10 @ X9)
% 1.32/1.48          | (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 1.32/1.48      inference('cnf', [status(esa)], [t8_xboole_1])).
% 1.32/1.48  thf('11', plain,
% 1.32/1.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.32/1.48         ((r1_tarski @ (k2_xboole_0 @ (k1_zfmisc_1 @ X1) @ X2) @ 
% 1.32/1.48           (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 1.32/1.48          | ~ (r1_tarski @ X2 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0))))),
% 1.32/1.48      inference('sup-', [status(thm)], ['9', '10'])).
% 1.32/1.48  thf('12', plain,
% 1.32/1.48      (![X0 : $i, X1 : $i]:
% 1.32/1.48         (r1_tarski @ 
% 1.32/1.48          (k2_xboole_0 @ (k1_zfmisc_1 @ X1) @ (k1_zfmisc_1 @ X0)) @ 
% 1.32/1.48          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.32/1.48      inference('sup-', [status(thm)], ['6', '11'])).
% 1.32/1.48  thf('13', plain,
% 1.32/1.48      (![X0 : $i, X1 : $i]:
% 1.32/1.48         (r1_tarski @ 
% 1.32/1.48          (k2_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 1.32/1.48           (k1_zfmisc_1 @ (k4_xboole_0 @ X0 @ X1))) @ 
% 1.32/1.48          (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.32/1.48      inference('sup+', [status(thm)], ['1', '12'])).
% 1.32/1.48  thf('14', plain, ($false), inference('demod', [status(thm)], ['0', '13'])).
% 1.32/1.48  
% 1.32/1.48  % SZS output end Refutation
% 1.32/1.48  
% 1.32/1.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

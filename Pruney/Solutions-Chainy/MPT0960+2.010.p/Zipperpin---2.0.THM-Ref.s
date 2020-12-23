%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kZnA3anJ6K

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   29 (  29 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    6
%              Number of atoms          :  145 ( 145 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(t33_wellord2,conjecture,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t33_wellord2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_wellord2 @ sk_A ) @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t8_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A )
        = ( k1_wellord2 @ A ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X11 ) @ X10 )
        = ( k1_wellord2 @ X10 ) )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X0 )
      = ( k1_wellord2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d6_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k2_wellord1 @ A @ B )
          = ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ B @ B ) ) ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_wellord1 @ X7 @ X8 )
        = ( k3_xboole_0 @ X7 @ ( k2_zfmisc_1 @ X8 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d6_wellord1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_wellord1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','9'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('11',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    $false ),
    inference(demod,[status(thm)],['0','12'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kZnA3anJ6K
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:57:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 60 iterations in 0.035s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.21/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.48  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.21/0.48  thf(t33_wellord2, conjecture,
% 0.21/0.48    (![A:$i]: ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]: ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t33_wellord2])).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      (~ (r1_tarski @ (k1_wellord2 @ sk_A) @ (k2_zfmisc_1 @ sk_A @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(d10_xboole_0, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.48  thf('2', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.21/0.48      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.48  thf(t8_wellord2, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( r1_tarski @ A @ B ) =>
% 0.21/0.48       ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A ) = ( k1_wellord2 @ A ) ) ))).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X10 : $i, X11 : $i]:
% 0.21/0.48         (((k2_wellord1 @ (k1_wellord2 @ X11) @ X10) = (k1_wellord2 @ X10))
% 0.21/0.48          | ~ (r1_tarski @ X10 @ X11))),
% 0.21/0.48      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((k2_wellord1 @ (k1_wellord2 @ X0) @ X0) = (k1_wellord2 @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.48  thf(d6_wellord1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( k2_wellord1 @ A @ B ) =
% 0.21/0.48           ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ B @ B ) ) ) ) ))).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i]:
% 0.21/0.48         (((k2_wellord1 @ X7 @ X8)
% 0.21/0.48            = (k3_xboole_0 @ X7 @ (k2_zfmisc_1 @ X8 @ X8)))
% 0.21/0.48          | ~ (v1_relat_1 @ X7))),
% 0.21/0.48      inference('cnf', [status(esa)], [d6_wellord1])).
% 0.21/0.48  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.48    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.48      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.48  thf(t17_xboole_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 0.21/0.48      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.21/0.48      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r1_tarski @ (k2_wellord1 @ X1 @ X0) @ (k2_zfmisc_1 @ X0 @ X0))
% 0.21/0.48          | ~ (v1_relat_1 @ X1))),
% 0.21/0.48      inference('sup+', [status(thm)], ['5', '8'])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r1_tarski @ (k1_wellord2 @ X0) @ (k2_zfmisc_1 @ X0 @ X0))
% 0.21/0.48          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.21/0.48      inference('sup+', [status(thm)], ['4', '9'])).
% 0.21/0.48  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.21/0.48  thf('11', plain, (![X9 : $i]: (v1_relat_1 @ (k1_wellord2 @ X9))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (![X0 : $i]: (r1_tarski @ (k1_wellord2 @ X0) @ (k2_zfmisc_1 @ X0 @ X0))),
% 0.21/0.48      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.48  thf('13', plain, ($false), inference('demod', [status(thm)], ['0', '12'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3Sg1g77JqK

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:30 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   28 (  32 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    6
%              Number of atoms          :  181 ( 237 expanded)
%              Number of equality atoms :   17 (  21 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t26_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
        = ( k2_wellord1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X6 @ X7 ) @ X8 )
        = ( k2_wellord1 @ X6 @ ( k3_xboole_0 @ X7 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t26_wellord1])).

thf(t27_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
        = ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X9 @ X11 ) @ X10 )
        = ( k2_wellord1 @ ( k2_wellord1 @ X9 @ X10 ) @ X11 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t27_wellord1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_wellord1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k2_wellord1 @ ( k2_wellord1 @ X2 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k2_wellord1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k2_wellord1 @ ( k2_wellord1 @ X2 @ X0 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t29_wellord1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A )
          = ( k2_wellord1 @ C @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A )
            = ( k2_wellord1 @ C @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_wellord1])).

thf('4',plain,(
    ( k2_wellord1 @ ( k2_wellord1 @ sk_C @ sk_B ) @ sk_A )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( ( k2_wellord1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) )
     != ( k2_wellord1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('8',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) )
      = X2 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ( k2_wellord1 @ sk_C @ sk_A )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['5','10','11'])).

thf('13',plain,(
    $false ),
    inference(simplify,[status(thm)],['12'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3Sg1g77JqK
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:43:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 12 iterations in 0.018s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.22/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.48  thf(t26_wellord1, axiom,
% 0.22/0.48    (![A:$i,B:$i,C:$i]:
% 0.22/0.48     ( ( v1_relat_1 @ C ) =>
% 0.22/0.48       ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 0.22/0.48         ( k2_wellord1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.22/0.48  thf('0', plain,
% 0.22/0.48      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.48         (((k2_wellord1 @ (k2_wellord1 @ X6 @ X7) @ X8)
% 0.22/0.48            = (k2_wellord1 @ X6 @ (k3_xboole_0 @ X7 @ X8)))
% 0.22/0.48          | ~ (v1_relat_1 @ X6))),
% 0.22/0.48      inference('cnf', [status(esa)], [t26_wellord1])).
% 0.22/0.48  thf(t27_wellord1, axiom,
% 0.22/0.48    (![A:$i,B:$i,C:$i]:
% 0.22/0.48     ( ( v1_relat_1 @ C ) =>
% 0.22/0.48       ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 0.22/0.48         ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ))).
% 0.22/0.48  thf('1', plain,
% 0.22/0.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.48         (((k2_wellord1 @ (k2_wellord1 @ X9 @ X11) @ X10)
% 0.22/0.48            = (k2_wellord1 @ (k2_wellord1 @ X9 @ X10) @ X11))
% 0.22/0.48          | ~ (v1_relat_1 @ X9))),
% 0.22/0.48      inference('cnf', [status(esa)], [t27_wellord1])).
% 0.22/0.48  thf('2', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.48         (((k2_wellord1 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.22/0.48            = (k2_wellord1 @ (k2_wellord1 @ X2 @ X0) @ X1))
% 0.22/0.48          | ~ (v1_relat_1 @ X2)
% 0.22/0.48          | ~ (v1_relat_1 @ X2))),
% 0.22/0.48      inference('sup+', [status(thm)], ['0', '1'])).
% 0.22/0.48  thf('3', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.48         (~ (v1_relat_1 @ X2)
% 0.22/0.48          | ((k2_wellord1 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.22/0.48              = (k2_wellord1 @ (k2_wellord1 @ X2 @ X0) @ X1)))),
% 0.22/0.48      inference('simplify', [status(thm)], ['2'])).
% 0.22/0.48  thf(t29_wellord1, conjecture,
% 0.22/0.48    (![A:$i,B:$i,C:$i]:
% 0.22/0.48     ( ( v1_relat_1 @ C ) =>
% 0.22/0.48       ( ( r1_tarski @ A @ B ) =>
% 0.22/0.48         ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 0.22/0.48           ( k2_wellord1 @ C @ A ) ) ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.48        ( ( v1_relat_1 @ C ) =>
% 0.22/0.48          ( ( r1_tarski @ A @ B ) =>
% 0.22/0.48            ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 0.22/0.48              ( k2_wellord1 @ C @ A ) ) ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t29_wellord1])).
% 0.22/0.48  thf('4', plain,
% 0.22/0.48      (((k2_wellord1 @ (k2_wellord1 @ sk_C @ sk_B) @ sk_A)
% 0.22/0.48         != (k2_wellord1 @ sk_C @ sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('5', plain,
% 0.22/0.48      ((((k2_wellord1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B))
% 0.22/0.48          != (k2_wellord1 @ sk_C @ sk_A))
% 0.22/0.48        | ~ (v1_relat_1 @ sk_C))),
% 0.22/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.48  thf('6', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(t12_xboole_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.22/0.48  thf('7', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         (((k2_xboole_0 @ X1 @ X0) = (X0)) | ~ (r1_tarski @ X1 @ X0))),
% 0.22/0.48      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.22/0.48  thf('8', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.22/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.48  thf(t21_xboole_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.22/0.48  thf('9', plain,
% 0.22/0.48      (![X2 : $i, X3 : $i]:
% 0.22/0.48         ((k3_xboole_0 @ X2 @ (k2_xboole_0 @ X2 @ X3)) = (X2))),
% 0.22/0.48      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.22/0.48  thf('10', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.22/0.48      inference('sup+', [status(thm)], ['8', '9'])).
% 0.22/0.48  thf('11', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('12', plain,
% 0.22/0.48      (((k2_wellord1 @ sk_C @ sk_A) != (k2_wellord1 @ sk_C @ sk_A))),
% 0.22/0.48      inference('demod', [status(thm)], ['5', '10', '11'])).
% 0.22/0.48  thf('13', plain, ($false), inference('simplify', [status(thm)], ['12'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

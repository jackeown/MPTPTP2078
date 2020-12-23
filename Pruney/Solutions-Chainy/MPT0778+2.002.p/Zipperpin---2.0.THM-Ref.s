%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WpzFiHgf1I

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:24 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   21 (  26 expanded)
%              Number of leaves         :    9 (  12 expanded)
%              Depth                    :    7
%              Number of atoms          :  143 ( 208 expanded)
%              Number of equality atoms :   12 (  17 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t26_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
        = ( k2_wellord1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X2 @ X3 ) @ X4 )
        = ( k2_wellord1 @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t26_wellord1])).

thf('1',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X2 @ X3 ) @ X4 )
        = ( k2_wellord1 @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t26_wellord1])).

thf(t27_wellord1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
        = ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
          = ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_wellord1])).

thf('2',plain,(
    ( k2_wellord1 @ ( k2_wellord1 @ sk_C @ sk_A ) @ sk_B )
 != ( k2_wellord1 @ ( k2_wellord1 @ sk_C @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k2_wellord1 @ ( k2_wellord1 @ sk_C @ sk_A ) @ sk_B )
     != ( k2_wellord1 @ sk_C @ ( k3_xboole_0 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ( k2_wellord1 @ ( k2_wellord1 @ sk_C @ sk_A ) @ sk_B )
 != ( k2_wellord1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,
    ( ( ( k2_wellord1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) )
     != ( k2_wellord1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ( k2_wellord1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) )
 != ( k2_wellord1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    $false ),
    inference(simplify,[status(thm)],['9'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WpzFiHgf1I
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:32:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.46  % Solved by: fo/fo7.sh
% 0.22/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.46  % done 4 iterations in 0.007s
% 0.22/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.46  % SZS output start Refutation
% 0.22/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.46  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.22/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.46  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.46  thf(t26_wellord1, axiom,
% 0.22/0.46    (![A:$i,B:$i,C:$i]:
% 0.22/0.46     ( ( v1_relat_1 @ C ) =>
% 0.22/0.46       ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 0.22/0.46         ( k2_wellord1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.22/0.46  thf('0', plain,
% 0.22/0.46      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.46         (((k2_wellord1 @ (k2_wellord1 @ X2 @ X3) @ X4)
% 0.22/0.46            = (k2_wellord1 @ X2 @ (k3_xboole_0 @ X3 @ X4)))
% 0.22/0.46          | ~ (v1_relat_1 @ X2))),
% 0.22/0.46      inference('cnf', [status(esa)], [t26_wellord1])).
% 0.22/0.46  thf('1', plain,
% 0.22/0.46      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.47         (((k2_wellord1 @ (k2_wellord1 @ X2 @ X3) @ X4)
% 0.22/0.47            = (k2_wellord1 @ X2 @ (k3_xboole_0 @ X3 @ X4)))
% 0.22/0.47          | ~ (v1_relat_1 @ X2))),
% 0.22/0.47      inference('cnf', [status(esa)], [t26_wellord1])).
% 0.22/0.47  thf(t27_wellord1, conjecture,
% 0.22/0.47    (![A:$i,B:$i,C:$i]:
% 0.22/0.47     ( ( v1_relat_1 @ C ) =>
% 0.22/0.47       ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 0.22/0.47         ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ))).
% 0.22/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.47        ( ( v1_relat_1 @ C ) =>
% 0.22/0.47          ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 0.22/0.47            ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ) )),
% 0.22/0.47    inference('cnf.neg', [status(esa)], [t27_wellord1])).
% 0.22/0.47  thf('2', plain,
% 0.22/0.47      (((k2_wellord1 @ (k2_wellord1 @ sk_C @ sk_A) @ sk_B)
% 0.22/0.47         != (k2_wellord1 @ (k2_wellord1 @ sk_C @ sk_B) @ sk_A))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('3', plain,
% 0.22/0.47      ((((k2_wellord1 @ (k2_wellord1 @ sk_C @ sk_A) @ sk_B)
% 0.22/0.47          != (k2_wellord1 @ sk_C @ (k3_xboole_0 @ sk_B @ sk_A)))
% 0.22/0.47        | ~ (v1_relat_1 @ sk_C))),
% 0.22/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.47  thf(commutativity_k3_xboole_0, axiom,
% 0.22/0.47    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.22/0.47  thf('4', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.47      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.47  thf('5', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('6', plain,
% 0.22/0.47      (((k2_wellord1 @ (k2_wellord1 @ sk_C @ sk_A) @ sk_B)
% 0.22/0.47         != (k2_wellord1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.47      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.22/0.47  thf('7', plain,
% 0.22/0.47      ((((k2_wellord1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B))
% 0.22/0.47          != (k2_wellord1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B)))
% 0.22/0.47        | ~ (v1_relat_1 @ sk_C))),
% 0.22/0.47      inference('sup-', [status(thm)], ['0', '6'])).
% 0.22/0.47  thf('8', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('9', plain,
% 0.22/0.47      (((k2_wellord1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B))
% 0.22/0.47         != (k2_wellord1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.47      inference('demod', [status(thm)], ['7', '8'])).
% 0.22/0.47  thf('10', plain, ($false), inference('simplify', [status(thm)], ['9'])).
% 0.22/0.47  
% 0.22/0.47  % SZS output end Refutation
% 0.22/0.47  
% 0.22/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.u19QoalsiN

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   16 (  18 expanded)
%              Number of leaves         :    8 (   9 expanded)
%              Depth                    :    5
%              Number of atoms          :   88 ( 110 expanded)
%              Number of equality atoms :    9 (  11 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t26_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
        = ( k2_wellord1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X1 @ X2 ) @ X3 )
        = ( k2_wellord1 @ X1 @ ( k3_xboole_0 @ X2 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t26_wellord1])).

thf(t28_wellord1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ B @ A ) @ A )
        = ( k2_wellord1 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( k2_wellord1 @ ( k2_wellord1 @ B @ A ) @ A )
          = ( k2_wellord1 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_wellord1])).

thf('1',plain,(
    ( k2_wellord1 @ ( k2_wellord1 @ sk_B @ sk_A ) @ sk_A )
 != ( k2_wellord1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k2_wellord1 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_A ) )
     != ( k2_wellord1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('4',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ( k2_wellord1 @ sk_B @ sk_A )
 != ( k2_wellord1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    $false ),
    inference(simplify,[status(thm)],['5'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.u19QoalsiN
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:58:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.43  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.43  % Solved by: fo/fo7.sh
% 0.20/0.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.43  % done 3 iterations in 0.009s
% 0.20/0.43  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.43  % SZS output start Refutation
% 0.20/0.43  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.43  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.20/0.43  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.43  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.43  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.43  thf(t26_wellord1, axiom,
% 0.20/0.43    (![A:$i,B:$i,C:$i]:
% 0.20/0.43     ( ( v1_relat_1 @ C ) =>
% 0.20/0.43       ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 0.20/0.43         ( k2_wellord1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.20/0.43  thf('0', plain,
% 0.20/0.43      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.43         (((k2_wellord1 @ (k2_wellord1 @ X1 @ X2) @ X3)
% 0.20/0.43            = (k2_wellord1 @ X1 @ (k3_xboole_0 @ X2 @ X3)))
% 0.20/0.43          | ~ (v1_relat_1 @ X1))),
% 0.20/0.43      inference('cnf', [status(esa)], [t26_wellord1])).
% 0.20/0.43  thf(t28_wellord1, conjecture,
% 0.20/0.43    (![A:$i,B:$i]:
% 0.20/0.43     ( ( v1_relat_1 @ B ) =>
% 0.20/0.43       ( ( k2_wellord1 @ ( k2_wellord1 @ B @ A ) @ A ) =
% 0.20/0.43         ( k2_wellord1 @ B @ A ) ) ))).
% 0.20/0.43  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.43    (~( ![A:$i,B:$i]:
% 0.20/0.43        ( ( v1_relat_1 @ B ) =>
% 0.20/0.43          ( ( k2_wellord1 @ ( k2_wellord1 @ B @ A ) @ A ) =
% 0.20/0.43            ( k2_wellord1 @ B @ A ) ) ) )),
% 0.20/0.43    inference('cnf.neg', [status(esa)], [t28_wellord1])).
% 0.20/0.43  thf('1', plain,
% 0.20/0.43      (((k2_wellord1 @ (k2_wellord1 @ sk_B @ sk_A) @ sk_A)
% 0.20/0.43         != (k2_wellord1 @ sk_B @ sk_A))),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf('2', plain,
% 0.20/0.43      ((((k2_wellord1 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_A))
% 0.20/0.43          != (k2_wellord1 @ sk_B @ sk_A))
% 0.20/0.43        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.43      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.43  thf(idempotence_k3_xboole_0, axiom,
% 0.20/0.43    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.20/0.43  thf('3', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.43      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.20/0.43  thf('4', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf('5', plain,
% 0.20/0.43      (((k2_wellord1 @ sk_B @ sk_A) != (k2_wellord1 @ sk_B @ sk_A))),
% 0.20/0.43      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.20/0.43  thf('6', plain, ($false), inference('simplify', [status(thm)], ['5'])).
% 0.20/0.43  
% 0.20/0.43  % SZS output end Refutation
% 0.20/0.43  
% 0.20/0.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JdY74aKPmr

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   24 (  28 expanded)
%              Number of leaves         :   11 (  13 expanded)
%              Depth                    :    6
%              Number of atoms          :  162 ( 218 expanded)
%              Number of equality atoms :   14 (  18 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t27_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
        = ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X5 @ X7 ) @ X6 )
        = ( k2_wellord1 @ ( k2_wellord1 @ X5 @ X6 ) @ X7 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t27_wellord1])).

thf(t26_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
        = ( k2_wellord1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X2 @ X3 ) @ X4 )
        = ( k2_wellord1 @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t26_wellord1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X2 @ X1 ) @ X0 )
        = ( k2_wellord1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k2_wellord1 @ ( k2_wellord1 @ X2 @ X1 ) @ X0 )
        = ( k2_wellord1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
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

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('8',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ( k2_wellord1 @ sk_C @ sk_A )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['5','8','9'])).

thf('11',plain,(
    $false ),
    inference(simplify,[status(thm)],['10'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JdY74aKPmr
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:32:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 7 iterations in 0.013s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.46  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.46  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.46  thf(t27_wellord1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ( v1_relat_1 @ C ) =>
% 0.21/0.46       ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 0.21/0.46         ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ))).
% 0.21/0.46  thf('0', plain,
% 0.21/0.46      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.46         (((k2_wellord1 @ (k2_wellord1 @ X5 @ X7) @ X6)
% 0.21/0.46            = (k2_wellord1 @ (k2_wellord1 @ X5 @ X6) @ X7))
% 0.21/0.46          | ~ (v1_relat_1 @ X5))),
% 0.21/0.46      inference('cnf', [status(esa)], [t27_wellord1])).
% 0.21/0.46  thf(t26_wellord1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ( v1_relat_1 @ C ) =>
% 0.21/0.46       ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 0.21/0.46         ( k2_wellord1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.21/0.46  thf('1', plain,
% 0.21/0.46      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.46         (((k2_wellord1 @ (k2_wellord1 @ X2 @ X3) @ X4)
% 0.21/0.46            = (k2_wellord1 @ X2 @ (k3_xboole_0 @ X3 @ X4)))
% 0.21/0.46          | ~ (v1_relat_1 @ X2))),
% 0.21/0.46      inference('cnf', [status(esa)], [t26_wellord1])).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.46         (((k2_wellord1 @ (k2_wellord1 @ X2 @ X1) @ X0)
% 0.21/0.46            = (k2_wellord1 @ X2 @ (k3_xboole_0 @ X0 @ X1)))
% 0.21/0.46          | ~ (v1_relat_1 @ X2)
% 0.21/0.46          | ~ (v1_relat_1 @ X2))),
% 0.21/0.46      inference('sup+', [status(thm)], ['0', '1'])).
% 0.21/0.46  thf('3', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.46         (~ (v1_relat_1 @ X2)
% 0.21/0.46          | ((k2_wellord1 @ (k2_wellord1 @ X2 @ X1) @ X0)
% 0.21/0.46              = (k2_wellord1 @ X2 @ (k3_xboole_0 @ X0 @ X1))))),
% 0.21/0.46      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.46  thf(t29_wellord1, conjecture,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ( v1_relat_1 @ C ) =>
% 0.21/0.46       ( ( r1_tarski @ A @ B ) =>
% 0.21/0.46         ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 0.21/0.46           ( k2_wellord1 @ C @ A ) ) ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.46        ( ( v1_relat_1 @ C ) =>
% 0.21/0.46          ( ( r1_tarski @ A @ B ) =>
% 0.21/0.46            ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 0.21/0.46              ( k2_wellord1 @ C @ A ) ) ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t29_wellord1])).
% 0.21/0.46  thf('4', plain,
% 0.21/0.46      (((k2_wellord1 @ (k2_wellord1 @ sk_C @ sk_B) @ sk_A)
% 0.21/0.46         != (k2_wellord1 @ sk_C @ sk_A))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('5', plain,
% 0.21/0.46      ((((k2_wellord1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B))
% 0.21/0.46          != (k2_wellord1 @ sk_C @ sk_A))
% 0.21/0.46        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.46      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.46  thf('6', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t28_xboole_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.46  thf('7', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.21/0.46      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.46  thf('8', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.21/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.46  thf('9', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('10', plain,
% 0.21/0.46      (((k2_wellord1 @ sk_C @ sk_A) != (k2_wellord1 @ sk_C @ sk_A))),
% 0.21/0.46      inference('demod', [status(thm)], ['5', '8', '9'])).
% 0.21/0.46  thf('11', plain, ($false), inference('simplify', [status(thm)], ['10'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

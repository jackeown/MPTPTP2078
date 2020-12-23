%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SXHqIO7hDC

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:26 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   23 (  27 expanded)
%              Number of leaves         :   11 (  13 expanded)
%              Depth                    :    6
%              Number of atoms          :  127 ( 183 expanded)
%              Number of equality atoms :   13 (  17 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t26_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
        = ( k2_wellord1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X4 @ X5 ) @ X6 )
        = ( k2_wellord1 @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t26_wellord1])).

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

thf('1',plain,(
    ( k2_wellord1 @ ( k2_wellord1 @ sk_C @ sk_B ) @ sk_A )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k2_wellord1 @ sk_C @ ( k3_xboole_0 @ sk_B @ sk_A ) )
     != ( k2_wellord1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = X2 )
      | ~ ( r1_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('7',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ( k2_wellord1 @ sk_C @ sk_A )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['2','7','8'])).

thf('10',plain,(
    $false ),
    inference(simplify,[status(thm)],['9'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SXHqIO7hDC
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:49:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.45  % Solved by: fo/fo7.sh
% 0.20/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.45  % done 7 iterations in 0.008s
% 0.20/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.45  % SZS output start Refutation
% 0.20/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.45  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.45  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.20/0.45  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.45  thf(t26_wellord1, axiom,
% 0.20/0.45    (![A:$i,B:$i,C:$i]:
% 0.20/0.45     ( ( v1_relat_1 @ C ) =>
% 0.20/0.45       ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 0.20/0.45         ( k2_wellord1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.20/0.45  thf('0', plain,
% 0.20/0.45      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.45         (((k2_wellord1 @ (k2_wellord1 @ X4 @ X5) @ X6)
% 0.20/0.45            = (k2_wellord1 @ X4 @ (k3_xboole_0 @ X5 @ X6)))
% 0.20/0.45          | ~ (v1_relat_1 @ X4))),
% 0.20/0.45      inference('cnf', [status(esa)], [t26_wellord1])).
% 0.20/0.45  thf(t29_wellord1, conjecture,
% 0.20/0.45    (![A:$i,B:$i,C:$i]:
% 0.20/0.45     ( ( v1_relat_1 @ C ) =>
% 0.20/0.45       ( ( r1_tarski @ A @ B ) =>
% 0.20/0.45         ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 0.20/0.45           ( k2_wellord1 @ C @ A ) ) ) ))).
% 0.20/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.45    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.45        ( ( v1_relat_1 @ C ) =>
% 0.20/0.45          ( ( r1_tarski @ A @ B ) =>
% 0.20/0.45            ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 0.20/0.45              ( k2_wellord1 @ C @ A ) ) ) ) )),
% 0.20/0.45    inference('cnf.neg', [status(esa)], [t29_wellord1])).
% 0.20/0.45  thf('1', plain,
% 0.20/0.45      (((k2_wellord1 @ (k2_wellord1 @ sk_C @ sk_B) @ sk_A)
% 0.20/0.45         != (k2_wellord1 @ sk_C @ sk_A))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('2', plain,
% 0.20/0.45      ((((k2_wellord1 @ sk_C @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.20/0.45          != (k2_wellord1 @ sk_C @ sk_A))
% 0.20/0.45        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.45      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.45  thf('3', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf(t28_xboole_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.45  thf('4', plain,
% 0.20/0.45      (![X2 : $i, X3 : $i]:
% 0.20/0.45         (((k3_xboole_0 @ X2 @ X3) = (X2)) | ~ (r1_tarski @ X2 @ X3))),
% 0.20/0.45      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.45  thf('5', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.20/0.45      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.45  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.45    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.45  thf('6', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.45      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.45  thf('7', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.20/0.45      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.45  thf('8', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('9', plain,
% 0.20/0.45      (((k2_wellord1 @ sk_C @ sk_A) != (k2_wellord1 @ sk_C @ sk_A))),
% 0.20/0.45      inference('demod', [status(thm)], ['2', '7', '8'])).
% 0.20/0.45  thf('10', plain, ($false), inference('simplify', [status(thm)], ['9'])).
% 0.20/0.45  
% 0.20/0.45  % SZS output end Refutation
% 0.20/0.45  
% 0.20/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

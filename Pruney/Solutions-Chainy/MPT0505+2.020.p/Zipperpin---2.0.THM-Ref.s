%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AFBNhfOhOE

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:20 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   39 (  45 expanded)
%              Number of leaves         :   15 (  19 expanded)
%              Depth                    :   10
%              Number of atoms          :  240 ( 310 expanded)
%              Number of equality atoms :   19 (  25 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t103_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k7_relat_1 @ C @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A )
            = ( k7_relat_1 @ C @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t103_relat_1])).

thf('4',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ ( k3_xboole_0 @ X4 @ X6 ) @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t26_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('9',plain,
    ( ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_A )
    | ( ( k3_xboole_0 @ sk_B @ sk_A )
      = sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t31_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ ( k2_xboole_0 @ B @ C ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ ( k3_xboole_0 @ X9 @ X11 ) ) @ ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t31_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['9','14'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('16',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) @ X14 )
        = ( k7_relat_1 @ X12 @ ( k3_xboole_0 @ X13 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ sk_B ) @ sk_A )
        = ( k7_relat_1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
 != ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( k7_relat_1 @ sk_C @ sk_A )
     != ( k7_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ( k7_relat_1 @ sk_C @ sk_A )
 != ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    $false ),
    inference(simplify,[status(thm)],['21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AFBNhfOhOE
% 0.14/0.37  % Computer   : n017.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 13:17:31 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.59/0.77  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.77  % Solved by: fo/fo7.sh
% 0.59/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.77  % done 392 iterations in 0.324s
% 0.59/0.77  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.77  % SZS output start Refutation
% 0.59/0.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.77  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.77  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.59/0.77  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.59/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.77  thf(sk_C_type, type, sk_C: $i).
% 0.59/0.77  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.59/0.77  thf(d10_xboole_0, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.59/0.77  thf('0', plain,
% 0.59/0.77      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.59/0.77      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.77  thf('1', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.59/0.77      inference('simplify', [status(thm)], ['0'])).
% 0.59/0.77  thf(t28_xboole_1, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.59/0.77  thf('2', plain,
% 0.59/0.77      (![X7 : $i, X8 : $i]:
% 0.59/0.77         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.59/0.77      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.59/0.77  thf('3', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.59/0.77      inference('sup-', [status(thm)], ['1', '2'])).
% 0.59/0.77  thf(t103_relat_1, conjecture,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( ( v1_relat_1 @ C ) =>
% 0.59/0.77       ( ( r1_tarski @ A @ B ) =>
% 0.59/0.77         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k7_relat_1 @ C @ A ) ) ) ))).
% 0.59/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.77    (~( ![A:$i,B:$i,C:$i]:
% 0.59/0.77        ( ( v1_relat_1 @ C ) =>
% 0.59/0.77          ( ( r1_tarski @ A @ B ) =>
% 0.59/0.77            ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A ) =
% 0.59/0.77              ( k7_relat_1 @ C @ A ) ) ) ) )),
% 0.59/0.77    inference('cnf.neg', [status(esa)], [t103_relat_1])).
% 0.59/0.77  thf('4', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf(t26_xboole_1, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( ( r1_tarski @ A @ B ) =>
% 0.59/0.77       ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.59/0.77  thf('5', plain,
% 0.59/0.77      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.59/0.77         (~ (r1_tarski @ X4 @ X5)
% 0.59/0.77          | (r1_tarski @ (k3_xboole_0 @ X4 @ X6) @ (k3_xboole_0 @ X5 @ X6)))),
% 0.59/0.77      inference('cnf', [status(esa)], [t26_xboole_1])).
% 0.59/0.77  thf('6', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ (k3_xboole_0 @ sk_B @ X0))),
% 0.59/0.77      inference('sup-', [status(thm)], ['4', '5'])).
% 0.59/0.77  thf('7', plain, ((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A))),
% 0.59/0.77      inference('sup+', [status(thm)], ['3', '6'])).
% 0.59/0.77  thf('8', plain,
% 0.59/0.77      (![X1 : $i, X3 : $i]:
% 0.59/0.77         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.59/0.77      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.77  thf('9', plain,
% 0.59/0.77      ((~ (r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_A)
% 0.59/0.77        | ((k3_xboole_0 @ sk_B @ sk_A) = (sk_A)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['7', '8'])).
% 0.59/0.77  thf(idempotence_k2_xboole_0, axiom,
% 0.59/0.77    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.59/0.77  thf('10', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.59/0.77      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.59/0.77  thf(t31_xboole_1, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( r1_tarski @
% 0.59/0.77       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ 
% 0.59/0.77       ( k2_xboole_0 @ B @ C ) ))).
% 0.59/0.77  thf('11', plain,
% 0.59/0.77      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.59/0.77         (r1_tarski @ 
% 0.59/0.77          (k2_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ (k3_xboole_0 @ X9 @ X11)) @ 
% 0.59/0.77          (k2_xboole_0 @ X10 @ X11))),
% 0.59/0.77      inference('cnf', [status(esa)], [t31_xboole_1])).
% 0.59/0.77  thf('12', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['10', '11'])).
% 0.59/0.77  thf('13', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.59/0.77      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.59/0.77  thf('14', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.59/0.77      inference('demod', [status(thm)], ['12', '13'])).
% 0.59/0.77  thf('15', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.59/0.77      inference('demod', [status(thm)], ['9', '14'])).
% 0.59/0.77  thf(t100_relat_1, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( ( v1_relat_1 @ C ) =>
% 0.59/0.77       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.59/0.77         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.59/0.77  thf('16', plain,
% 0.59/0.77      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.59/0.77         (((k7_relat_1 @ (k7_relat_1 @ X12 @ X13) @ X14)
% 0.59/0.77            = (k7_relat_1 @ X12 @ (k3_xboole_0 @ X13 @ X14)))
% 0.59/0.77          | ~ (v1_relat_1 @ X12))),
% 0.59/0.77      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.59/0.77  thf('17', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (((k7_relat_1 @ (k7_relat_1 @ X0 @ sk_B) @ sk_A)
% 0.59/0.77            = (k7_relat_1 @ X0 @ sk_A))
% 0.59/0.77          | ~ (v1_relat_1 @ X0))),
% 0.59/0.77      inference('sup+', [status(thm)], ['15', '16'])).
% 0.59/0.77  thf('18', plain,
% 0.59/0.77      (((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A)
% 0.59/0.77         != (k7_relat_1 @ sk_C @ sk_A))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('19', plain,
% 0.59/0.77      ((((k7_relat_1 @ sk_C @ sk_A) != (k7_relat_1 @ sk_C @ sk_A))
% 0.59/0.77        | ~ (v1_relat_1 @ sk_C))),
% 0.59/0.77      inference('sup-', [status(thm)], ['17', '18'])).
% 0.59/0.77  thf('20', plain, ((v1_relat_1 @ sk_C)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('21', plain,
% 0.59/0.77      (((k7_relat_1 @ sk_C @ sk_A) != (k7_relat_1 @ sk_C @ sk_A))),
% 0.59/0.77      inference('demod', [status(thm)], ['19', '20'])).
% 0.59/0.77  thf('22', plain, ($false), inference('simplify', [status(thm)], ['21'])).
% 0.59/0.77  
% 0.59/0.77  % SZS output end Refutation
% 0.59/0.77  
% 0.59/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

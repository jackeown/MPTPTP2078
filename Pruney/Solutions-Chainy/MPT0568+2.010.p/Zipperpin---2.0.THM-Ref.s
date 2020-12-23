%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EJiE2GK2EI

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:49 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   45 (  46 expanded)
%              Number of leaves         :   22 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :  190 ( 192 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('0',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_xboole_0 @ X10 )
      | ~ ( v1_xboole_0 @ X11 )
      | ( X10 = X11 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf(t172_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k10_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t172_relat_1])).

thf('1',plain,(
    ( k10_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k10_relat_1 @ k1_xboole_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k10_relat_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('4',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('5',plain,(
    ~ ( v1_xboole_0 @ ( k10_relat_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference('simplify_reflect+',[status(thm)],['3','4'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('6',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('7',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X13 @ X14 ) @ ( k1_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('11',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('12',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','12'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('14',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      = ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('16',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('18',plain,(
    ! [X9: $i] :
      ( r1_xboole_0 @ X9 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','19'])).

thf('21',plain,(
    $false ),
    inference(demod,[status(thm)],['5','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EJiE2GK2EI
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:54:06 EST 2020
% 0.22/0.35  % CPUTime    : 
% 0.22/0.35  % Running portfolio for 600 s
% 0.22/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.22/0.35  % Number of cores: 8
% 0.22/0.36  % Python version: Python 3.6.8
% 0.22/0.36  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 51 iterations in 0.044s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.51  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.22/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.51  thf(t8_boole, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.22/0.51  thf('0', plain,
% 0.22/0.51      (![X10 : $i, X11 : $i]:
% 0.22/0.51         (~ (v1_xboole_0 @ X10) | ~ (v1_xboole_0 @ X11) | ((X10) = (X11)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t8_boole])).
% 0.22/0.51  thf(t172_relat_1, conjecture,
% 0.22/0.51    (![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.51    (~( ![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t172_relat_1])).
% 0.22/0.51  thf('1', plain, (((k10_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('2', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (((X0) != (k1_xboole_0))
% 0.22/0.51          | ~ (v1_xboole_0 @ (k10_relat_1 @ k1_xboole_0 @ sk_A))
% 0.22/0.51          | ~ (v1_xboole_0 @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.51  thf('3', plain,
% 0.22/0.51      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.22/0.51        | ~ (v1_xboole_0 @ (k10_relat_1 @ k1_xboole_0 @ sk_A)))),
% 0.22/0.51      inference('simplify', [status(thm)], ['2'])).
% 0.22/0.51  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.22/0.51  thf('4', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.51      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.51  thf('5', plain, (~ (v1_xboole_0 @ (k10_relat_1 @ k1_xboole_0 @ sk_A))),
% 0.22/0.51      inference('simplify_reflect+', [status(thm)], ['3', '4'])).
% 0.22/0.51  thf(d1_xboole_0, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.51  thf('6', plain,
% 0.22/0.51      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.22/0.51      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.51  thf(t60_relat_1, axiom,
% 0.22/0.51    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.22/0.51     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.51  thf('7', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.51      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.51  thf(t167_relat_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( v1_relat_1 @ B ) =>
% 0.22/0.51       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.22/0.51  thf('8', plain,
% 0.22/0.51      (![X13 : $i, X14 : $i]:
% 0.22/0.51         ((r1_tarski @ (k10_relat_1 @ X13 @ X14) @ (k1_relat_1 @ X13))
% 0.22/0.51          | ~ (v1_relat_1 @ X13))),
% 0.22/0.51      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.22/0.51  thf('9', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((r1_tarski @ (k10_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.22/0.51          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.22/0.51      inference('sup+', [status(thm)], ['7', '8'])).
% 0.22/0.51  thf('10', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.51      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.51  thf(cc1_relat_1, axiom,
% 0.22/0.51    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.22/0.51  thf('11', plain, (![X12 : $i]: ((v1_relat_1 @ X12) | ~ (v1_xboole_0 @ X12))),
% 0.22/0.51      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.22/0.51  thf('12', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.22/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.51  thf('13', plain,
% 0.22/0.51      (![X0 : $i]: (r1_tarski @ (k10_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)),
% 0.22/0.51      inference('demod', [status(thm)], ['9', '12'])).
% 0.22/0.51  thf(t28_xboole_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.51  thf('14', plain,
% 0.22/0.51      (![X7 : $i, X8 : $i]:
% 0.22/0.51         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.22/0.51      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.22/0.51  thf('15', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((k3_xboole_0 @ (k10_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.22/0.51           = (k10_relat_1 @ k1_xboole_0 @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.51  thf(t4_xboole_0, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.51            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.51       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.22/0.51            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.22/0.51  thf('16', plain,
% 0.22/0.51      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.22/0.51          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.22/0.51      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.22/0.51  thf('17', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X1 @ (k10_relat_1 @ k1_xboole_0 @ X0))
% 0.22/0.51          | ~ (r1_xboole_0 @ (k10_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.51  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.22/0.51  thf('18', plain, (![X9 : $i]: (r1_xboole_0 @ X9 @ k1_xboole_0)),
% 0.22/0.51      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.22/0.51  thf('19', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         ~ (r2_hidden @ X1 @ (k10_relat_1 @ k1_xboole_0 @ X0))),
% 0.22/0.51      inference('demod', [status(thm)], ['17', '18'])).
% 0.22/0.51  thf('20', plain,
% 0.22/0.51      (![X0 : $i]: (v1_xboole_0 @ (k10_relat_1 @ k1_xboole_0 @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['6', '19'])).
% 0.22/0.51  thf('21', plain, ($false), inference('demod', [status(thm)], ['5', '20'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.22/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

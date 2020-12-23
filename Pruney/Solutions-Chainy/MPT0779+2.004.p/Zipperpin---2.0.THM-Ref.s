%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1k9FjxHVi8

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:24 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   41 (  46 expanded)
%              Number of leaves         :   19 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :  241 ( 291 expanded)
%              Number of equality atoms :   26 (  33 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t26_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
        = ( k2_wellord1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X36 @ X37 ) @ X38 )
        = ( k2_wellord1 @ X36 @ ( k3_xboole_0 @ X37 @ X38 ) ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t26_wellord1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X27 @ X28 ) )
      = ( k3_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X36 @ X37 ) @ X38 )
        = ( k2_wellord1 @ X36 @ ( k1_setfam_1 @ ( k2_tarski @ X37 @ X38 ) ) ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

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

thf('3',plain,(
    ( k2_wellord1 @ ( k2_wellord1 @ sk_B @ sk_A ) @ sk_A )
 != ( k2_wellord1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( ( k2_wellord1 @ sk_B @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_A ) ) )
     != ( k2_wellord1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('5',plain,(
    ! [X30: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('6',plain,(
    ! [X31: $i] :
      ( ( ( k5_relat_1 @ X31 @ ( k6_relat_1 @ ( k2_relat_1 @ X31 ) ) )
        = X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X32: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ ( k6_relat_1 @ X34 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf('11',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X27 @ X28 ) )
      = ( k3_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('12',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ ( k6_relat_1 @ X34 ) )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X34 @ X35 ) ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X29: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X29: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( X0
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ( k2_wellord1 @ sk_B @ sk_A )
 != ( k2_wellord1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['4','17','18'])).

thf('20',plain,(
    $false ),
    inference(simplify,[status(thm)],['19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1k9FjxHVi8
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:39:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 19 iterations in 0.014s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.22/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.50  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.50  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.22/0.50  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.22/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.50  thf(t26_wellord1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ C ) =>
% 0.22/0.50       ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 0.22/0.50         ( k2_wellord1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.22/0.50         (((k2_wellord1 @ (k2_wellord1 @ X36 @ X37) @ X38)
% 0.22/0.50            = (k2_wellord1 @ X36 @ (k3_xboole_0 @ X37 @ X38)))
% 0.22/0.50          | ~ (v1_relat_1 @ X36))),
% 0.22/0.50      inference('cnf', [status(esa)], [t26_wellord1])).
% 0.22/0.50  thf(t12_setfam_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      (![X27 : $i, X28 : $i]:
% 0.22/0.50         ((k1_setfam_1 @ (k2_tarski @ X27 @ X28)) = (k3_xboole_0 @ X27 @ X28))),
% 0.22/0.50      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.22/0.50         (((k2_wellord1 @ (k2_wellord1 @ X36 @ X37) @ X38)
% 0.22/0.50            = (k2_wellord1 @ X36 @ (k1_setfam_1 @ (k2_tarski @ X37 @ X38))))
% 0.22/0.50          | ~ (v1_relat_1 @ X36))),
% 0.22/0.50      inference('demod', [status(thm)], ['0', '1'])).
% 0.22/0.50  thf(t28_wellord1, conjecture,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ B ) =>
% 0.22/0.50       ( ( k2_wellord1 @ ( k2_wellord1 @ B @ A ) @ A ) =
% 0.22/0.50         ( k2_wellord1 @ B @ A ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i,B:$i]:
% 0.22/0.50        ( ( v1_relat_1 @ B ) =>
% 0.22/0.50          ( ( k2_wellord1 @ ( k2_wellord1 @ B @ A ) @ A ) =
% 0.22/0.50            ( k2_wellord1 @ B @ A ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t28_wellord1])).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      (((k2_wellord1 @ (k2_wellord1 @ sk_B @ sk_A) @ sk_A)
% 0.22/0.50         != (k2_wellord1 @ sk_B @ sk_A))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      ((((k2_wellord1 @ sk_B @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_A)))
% 0.22/0.50          != (k2_wellord1 @ sk_B @ sk_A))
% 0.22/0.50        | ~ (v1_relat_1 @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.50  thf(t71_relat_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.22/0.50       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.22/0.50  thf('5', plain, (![X30 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X30)) = (X30))),
% 0.22/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.50  thf(t80_relat_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ A ) =>
% 0.22/0.50       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      (![X31 : $i]:
% 0.22/0.50         (((k5_relat_1 @ X31 @ (k6_relat_1 @ (k2_relat_1 @ X31))) = (X31))
% 0.22/0.50          | ~ (v1_relat_1 @ X31))),
% 0.22/0.50      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.22/0.50            = (k6_relat_1 @ X0))
% 0.22/0.50          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.22/0.50      inference('sup+', [status(thm)], ['5', '6'])).
% 0.22/0.50  thf(fc3_funct_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.22/0.50       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.22/0.50  thf('8', plain, (![X32 : $i]: (v1_relat_1 @ (k6_relat_1 @ X32))),
% 0.22/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.22/0.50           = (k6_relat_1 @ X0))),
% 0.22/0.50      inference('demod', [status(thm)], ['7', '8'])).
% 0.22/0.50  thf(t43_funct_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.22/0.50       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      (![X34 : $i, X35 : $i]:
% 0.22/0.50         ((k5_relat_1 @ (k6_relat_1 @ X35) @ (k6_relat_1 @ X34))
% 0.22/0.50           = (k6_relat_1 @ (k3_xboole_0 @ X34 @ X35)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      (![X27 : $i, X28 : $i]:
% 0.22/0.50         ((k1_setfam_1 @ (k2_tarski @ X27 @ X28)) = (k3_xboole_0 @ X27 @ X28))),
% 0.22/0.50      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      (![X34 : $i, X35 : $i]:
% 0.22/0.50         ((k5_relat_1 @ (k6_relat_1 @ X35) @ (k6_relat_1 @ X34))
% 0.22/0.50           = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X34 @ X35))))),
% 0.22/0.50      inference('demod', [status(thm)], ['10', '11'])).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X0)))
% 0.22/0.50           = (k6_relat_1 @ X0))),
% 0.22/0.50      inference('demod', [status(thm)], ['9', '12'])).
% 0.22/0.50  thf('14', plain, (![X29 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X29)) = (X29))),
% 0.22/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((k1_relat_1 @ (k6_relat_1 @ X0))
% 0.22/0.50           = (k1_setfam_1 @ (k2_tarski @ X0 @ X0)))),
% 0.22/0.50      inference('sup+', [status(thm)], ['13', '14'])).
% 0.22/0.50  thf('16', plain, (![X29 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X29)) = (X29))),
% 0.22/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.50  thf('17', plain,
% 0.22/0.50      (![X0 : $i]: ((X0) = (k1_setfam_1 @ (k2_tarski @ X0 @ X0)))),
% 0.22/0.50      inference('demod', [status(thm)], ['15', '16'])).
% 0.22/0.50  thf('18', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('19', plain,
% 0.22/0.50      (((k2_wellord1 @ sk_B @ sk_A) != (k2_wellord1 @ sk_B @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['4', '17', '18'])).
% 0.22/0.50  thf('20', plain, ($false), inference('simplify', [status(thm)], ['19'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

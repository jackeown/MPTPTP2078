%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7eyzCJ6tDf

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:37 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   41 (  47 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :  262 ( 351 expanded)
%              Number of equality atoms :   19 (  25 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('0',plain,(
    ! [X74: $i,X75: $i,X76: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X75 @ X74 ) @ X76 )
        = ( k3_xboole_0 @ X74 @ ( k10_relat_1 @ X75 @ X76 ) ) )
      | ~ ( v1_relat_1 @ X75 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t175_funct_2,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
         => ( ( k10_relat_1 @ A @ C )
            = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i,C: $i] :
            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
           => ( ( k10_relat_1 @ A @ C )
              = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t175_funct_2])).

thf('1',plain,(
    ( k10_relat_1 @ sk_A @ sk_C_1 )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k10_relat_1 @ sk_A @ sk_C_1 )
     != ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('4',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_tarski @ X16 @ X18 )
      | ( r1_tarski @ X16 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C_1 ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C_1 ) @ ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,
    ( ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) @ ( k10_relat_1 @ sk_A @ sk_C_1 ) )
    | ( ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C_1 ) )
      = ( k10_relat_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('11',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_tarski @ X21 @ X20 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X49 @ X50 ) )
      = ( k3_xboole_0 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X49 @ X50 ) )
      = ( k3_xboole_0 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('16',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C_1 ) )
    = ( k10_relat_1 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['10','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ( k10_relat_1 @ sk_A @ sk_C_1 )
 != ( k10_relat_1 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','18','19'])).

thf('21',plain,(
    $false ),
    inference(simplify,[status(thm)],['20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7eyzCJ6tDf
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:57:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.47/0.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.67  % Solved by: fo/fo7.sh
% 0.47/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.67  % done 353 iterations in 0.208s
% 0.47/0.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.67  % SZS output start Refutation
% 0.47/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.67  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.47/0.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.67  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.47/0.67  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.47/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.67  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.47/0.67  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.47/0.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.67  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.47/0.67  thf(t139_funct_1, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( v1_relat_1 @ C ) =>
% 0.47/0.67       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.47/0.67         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.47/0.67  thf('0', plain,
% 0.47/0.67      (![X74 : $i, X75 : $i, X76 : $i]:
% 0.47/0.67         (((k10_relat_1 @ (k7_relat_1 @ X75 @ X74) @ X76)
% 0.47/0.67            = (k3_xboole_0 @ X74 @ (k10_relat_1 @ X75 @ X76)))
% 0.47/0.67          | ~ (v1_relat_1 @ X75))),
% 0.47/0.67      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.47/0.67  thf(t175_funct_2, conjecture,
% 0.47/0.67    (![A:$i]:
% 0.47/0.67     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.67       ( ![B:$i,C:$i]:
% 0.47/0.67         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.47/0.67           ( ( k10_relat_1 @ A @ C ) =
% 0.47/0.67             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.47/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.67    (~( ![A:$i]:
% 0.47/0.67        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.67          ( ![B:$i,C:$i]:
% 0.47/0.67            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.47/0.67              ( ( k10_relat_1 @ A @ C ) =
% 0.47/0.67                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 0.47/0.67    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 0.47/0.67  thf('1', plain,
% 0.47/0.67      (((k10_relat_1 @ sk_A @ sk_C_1)
% 0.47/0.67         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C_1))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('2', plain,
% 0.47/0.67      ((((k10_relat_1 @ sk_A @ sk_C_1)
% 0.47/0.67          != (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C_1)))
% 0.47/0.67        | ~ (v1_relat_1 @ sk_A))),
% 0.47/0.67      inference('sup-', [status(thm)], ['0', '1'])).
% 0.47/0.67  thf(d10_xboole_0, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.47/0.67  thf('3', plain,
% 0.47/0.67      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 0.47/0.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.67  thf('4', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.47/0.67      inference('simplify', [status(thm)], ['3'])).
% 0.47/0.67  thf('5', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C_1) @ sk_B)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(t19_xboole_1, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.47/0.67       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.47/0.67  thf('6', plain,
% 0.47/0.67      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.47/0.67         (~ (r1_tarski @ X16 @ X17)
% 0.47/0.67          | ~ (r1_tarski @ X16 @ X18)
% 0.47/0.67          | (r1_tarski @ X16 @ (k3_xboole_0 @ X17 @ X18)))),
% 0.47/0.67      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.47/0.67  thf('7', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C_1) @ 
% 0.47/0.67           (k3_xboole_0 @ sk_B @ X0))
% 0.47/0.67          | ~ (r1_tarski @ (k10_relat_1 @ sk_A @ sk_C_1) @ X0))),
% 0.47/0.67      inference('sup-', [status(thm)], ['5', '6'])).
% 0.47/0.67  thf('8', plain,
% 0.47/0.67      ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C_1) @ 
% 0.47/0.67        (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C_1)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['4', '7'])).
% 0.47/0.67  thf('9', plain,
% 0.47/0.67      (![X6 : $i, X8 : $i]:
% 0.47/0.67         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 0.47/0.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.67  thf('10', plain,
% 0.47/0.67      ((~ (r1_tarski @ (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C_1)) @ 
% 0.47/0.67           (k10_relat_1 @ sk_A @ sk_C_1))
% 0.47/0.67        | ((k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C_1))
% 0.47/0.67            = (k10_relat_1 @ sk_A @ sk_C_1)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['8', '9'])).
% 0.47/0.67  thf(commutativity_k2_tarski, axiom,
% 0.47/0.67    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.47/0.67  thf('11', plain,
% 0.47/0.67      (![X20 : $i, X21 : $i]:
% 0.47/0.67         ((k2_tarski @ X21 @ X20) = (k2_tarski @ X20 @ X21))),
% 0.47/0.67      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.47/0.67  thf(t12_setfam_1, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.47/0.67  thf('12', plain,
% 0.47/0.67      (![X49 : $i, X50 : $i]:
% 0.47/0.67         ((k1_setfam_1 @ (k2_tarski @ X49 @ X50)) = (k3_xboole_0 @ X49 @ X50))),
% 0.47/0.67      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.47/0.67  thf('13', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.47/0.67      inference('sup+', [status(thm)], ['11', '12'])).
% 0.47/0.67  thf('14', plain,
% 0.47/0.67      (![X49 : $i, X50 : $i]:
% 0.47/0.67         ((k1_setfam_1 @ (k2_tarski @ X49 @ X50)) = (k3_xboole_0 @ X49 @ X50))),
% 0.47/0.67      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.47/0.67  thf('15', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.47/0.67      inference('sup+', [status(thm)], ['13', '14'])).
% 0.47/0.67  thf(t17_xboole_1, axiom,
% 0.47/0.67    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.47/0.67  thf('16', plain,
% 0.47/0.67      (![X14 : $i, X15 : $i]: (r1_tarski @ (k3_xboole_0 @ X14 @ X15) @ X14)),
% 0.47/0.67      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.47/0.67  thf('17', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.47/0.67      inference('sup+', [status(thm)], ['15', '16'])).
% 0.47/0.67  thf('18', plain,
% 0.47/0.67      (((k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C_1))
% 0.47/0.67         = (k10_relat_1 @ sk_A @ sk_C_1))),
% 0.47/0.67      inference('demod', [status(thm)], ['10', '17'])).
% 0.47/0.67  thf('19', plain, ((v1_relat_1 @ sk_A)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('20', plain,
% 0.47/0.67      (((k10_relat_1 @ sk_A @ sk_C_1) != (k10_relat_1 @ sk_A @ sk_C_1))),
% 0.47/0.67      inference('demod', [status(thm)], ['2', '18', '19'])).
% 0.47/0.67  thf('21', plain, ($false), inference('simplify', [status(thm)], ['20'])).
% 0.47/0.67  
% 0.47/0.67  % SZS output end Refutation
% 0.47/0.67  
% 0.47/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

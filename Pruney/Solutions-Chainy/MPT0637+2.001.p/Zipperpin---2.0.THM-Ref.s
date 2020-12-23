%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CnOa6rP51A

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:55 EST 2020

% Result     : Theorem 2.32s
% Output     : Refutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   51 (  68 expanded)
%              Number of leaves         :   19 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :  351 ( 463 expanded)
%              Number of equality atoms :   31 (  40 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_3_type,type,(
    sk_A_3: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k8_relat_1 @ X29 @ X28 )
        = ( k5_relat_1 @ X28 @ ( k6_relat_1 @ X29 ) ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t43_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_funct_1])).

thf('1',plain,(
    ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A_3 ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A_3 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k8_relat_1 @ sk_A_3 @ ( k6_relat_1 @ sk_B ) )
     != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A_3 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('4',plain,(
    ( k8_relat_1 @ sk_A_3 @ ( k6_relat_1 @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A_3 @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k8_relat_1 @ X29 @ X28 )
        = ( k5_relat_1 @ X28 @ ( k6_relat_1 @ X29 ) ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('7',plain,(
    ! [X40: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X40 ) )
      = X40 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('8',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X45 ) @ X46 )
      | ( ( k5_relat_1 @ X45 @ ( k6_relat_1 @ X46 ) )
        = X45 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['5','12'])).

thf('14',plain,(
    ! [X39: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X39 ) )
      = X39 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t192_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('15',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k7_relat_1 @ X32 @ X33 )
        = ( k7_relat_1 @ X32 @ ( k3_xboole_0 @ ( k1_relat_1 @ X32 ) @ X33 ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k8_relat_1 @ X29 @ X28 )
        = ( k5_relat_1 @ X28 @ ( k6_relat_1 @ X29 ) ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('20',plain,(
    ! [X48: $i,X49: $i] :
      ( ( ( k7_relat_1 @ X49 @ X48 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X48 ) @ X49 ) )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('23',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['18','24','25'])).

thf('27',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','26','27'])).

thf('29',plain,(
    ( k8_relat_1 @ sk_A_3 @ ( k6_relat_1 @ sk_B ) )
 != ( k8_relat_1 @ sk_A_3 @ ( k6_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','28'])).

thf('30',plain,(
    $false ),
    inference(simplify,[status(thm)],['29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CnOa6rP51A
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 13:51:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 2.32/2.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.32/2.58  % Solved by: fo/fo7.sh
% 2.32/2.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.32/2.58  % done 3088 iterations in 2.109s
% 2.32/2.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.32/2.58  % SZS output start Refutation
% 2.32/2.58  thf(sk_A_3_type, type, sk_A_3: $i).
% 2.32/2.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.32/2.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.32/2.58  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.32/2.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.32/2.58  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 2.32/2.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.32/2.58  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 2.32/2.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.32/2.58  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.32/2.58  thf(sk_B_type, type, sk_B: $i).
% 2.32/2.58  thf(t123_relat_1, axiom,
% 2.32/2.58    (![A:$i,B:$i]:
% 2.32/2.58     ( ( v1_relat_1 @ B ) =>
% 2.32/2.58       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 2.32/2.58  thf('0', plain,
% 2.32/2.58      (![X28 : $i, X29 : $i]:
% 2.32/2.58         (((k8_relat_1 @ X29 @ X28) = (k5_relat_1 @ X28 @ (k6_relat_1 @ X29)))
% 2.32/2.58          | ~ (v1_relat_1 @ X28))),
% 2.32/2.58      inference('cnf', [status(esa)], [t123_relat_1])).
% 2.32/2.58  thf(t43_funct_1, conjecture,
% 2.32/2.58    (![A:$i,B:$i]:
% 2.32/2.58     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 2.32/2.58       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.32/2.58  thf(zf_stmt_0, negated_conjecture,
% 2.32/2.58    (~( ![A:$i,B:$i]:
% 2.32/2.58        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 2.32/2.58          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 2.32/2.58    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 2.32/2.58  thf('1', plain,
% 2.32/2.58      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A_3))
% 2.32/2.58         != (k6_relat_1 @ (k3_xboole_0 @ sk_A_3 @ sk_B)))),
% 2.32/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.58  thf('2', plain,
% 2.32/2.58      ((((k8_relat_1 @ sk_A_3 @ (k6_relat_1 @ sk_B))
% 2.32/2.58          != (k6_relat_1 @ (k3_xboole_0 @ sk_A_3 @ sk_B)))
% 2.32/2.58        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 2.32/2.58      inference('sup-', [status(thm)], ['0', '1'])).
% 2.32/2.58  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 2.32/2.58  thf('3', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 2.32/2.58      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.32/2.58  thf('4', plain,
% 2.32/2.58      (((k8_relat_1 @ sk_A_3 @ (k6_relat_1 @ sk_B))
% 2.32/2.58         != (k6_relat_1 @ (k3_xboole_0 @ sk_A_3 @ sk_B)))),
% 2.32/2.58      inference('demod', [status(thm)], ['2', '3'])).
% 2.32/2.58  thf('5', plain,
% 2.32/2.58      (![X28 : $i, X29 : $i]:
% 2.32/2.58         (((k8_relat_1 @ X29 @ X28) = (k5_relat_1 @ X28 @ (k6_relat_1 @ X29)))
% 2.32/2.58          | ~ (v1_relat_1 @ X28))),
% 2.32/2.58      inference('cnf', [status(esa)], [t123_relat_1])).
% 2.32/2.58  thf(t17_xboole_1, axiom,
% 2.32/2.58    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 2.32/2.58  thf('6', plain,
% 2.32/2.58      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 2.32/2.58      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.32/2.58  thf(t71_relat_1, axiom,
% 2.32/2.58    (![A:$i]:
% 2.32/2.58     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 2.32/2.58       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 2.32/2.58  thf('7', plain, (![X40 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X40)) = (X40))),
% 2.32/2.58      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.32/2.58  thf(t79_relat_1, axiom,
% 2.32/2.58    (![A:$i,B:$i]:
% 2.32/2.58     ( ( v1_relat_1 @ B ) =>
% 2.32/2.58       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 2.32/2.58         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 2.32/2.58  thf('8', plain,
% 2.32/2.58      (![X45 : $i, X46 : $i]:
% 2.32/2.58         (~ (r1_tarski @ (k2_relat_1 @ X45) @ X46)
% 2.32/2.58          | ((k5_relat_1 @ X45 @ (k6_relat_1 @ X46)) = (X45))
% 2.32/2.58          | ~ (v1_relat_1 @ X45))),
% 2.32/2.58      inference('cnf', [status(esa)], [t79_relat_1])).
% 2.32/2.58  thf('9', plain,
% 2.32/2.58      (![X0 : $i, X1 : $i]:
% 2.32/2.58         (~ (r1_tarski @ X0 @ X1)
% 2.32/2.58          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.32/2.58          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 2.32/2.58              = (k6_relat_1 @ X0)))),
% 2.32/2.58      inference('sup-', [status(thm)], ['7', '8'])).
% 2.32/2.58  thf('10', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 2.32/2.58      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.32/2.58  thf('11', plain,
% 2.32/2.58      (![X0 : $i, X1 : $i]:
% 2.32/2.58         (~ (r1_tarski @ X0 @ X1)
% 2.32/2.58          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 2.32/2.58              = (k6_relat_1 @ X0)))),
% 2.32/2.58      inference('demod', [status(thm)], ['9', '10'])).
% 2.32/2.58  thf('12', plain,
% 2.32/2.58      (![X0 : $i, X1 : $i]:
% 2.32/2.58         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 2.32/2.58           (k6_relat_1 @ X0)) = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.32/2.58      inference('sup-', [status(thm)], ['6', '11'])).
% 2.32/2.58  thf('13', plain,
% 2.32/2.58      (![X0 : $i, X1 : $i]:
% 2.32/2.58         (((k8_relat_1 @ X1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 2.32/2.58            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 2.32/2.58          | ~ (v1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 2.32/2.58      inference('sup+', [status(thm)], ['5', '12'])).
% 2.32/2.58  thf('14', plain, (![X39 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X39)) = (X39))),
% 2.32/2.58      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.32/2.58  thf(t192_relat_1, axiom,
% 2.32/2.58    (![A:$i,B:$i]:
% 2.32/2.58     ( ( v1_relat_1 @ B ) =>
% 2.32/2.58       ( ( k7_relat_1 @ B @ A ) =
% 2.32/2.58         ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 2.32/2.58  thf('15', plain,
% 2.32/2.58      (![X32 : $i, X33 : $i]:
% 2.32/2.58         (((k7_relat_1 @ X32 @ X33)
% 2.32/2.58            = (k7_relat_1 @ X32 @ (k3_xboole_0 @ (k1_relat_1 @ X32) @ X33)))
% 2.32/2.58          | ~ (v1_relat_1 @ X32))),
% 2.32/2.58      inference('cnf', [status(esa)], [t192_relat_1])).
% 2.32/2.58  thf('16', plain,
% 2.32/2.58      (![X0 : $i, X1 : $i]:
% 2.32/2.58         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 2.32/2.58            = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))
% 2.32/2.58          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.32/2.58      inference('sup+', [status(thm)], ['14', '15'])).
% 2.32/2.58  thf('17', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 2.32/2.58      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.32/2.58  thf('18', plain,
% 2.32/2.58      (![X0 : $i, X1 : $i]:
% 2.32/2.58         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 2.32/2.58           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 2.32/2.58      inference('demod', [status(thm)], ['16', '17'])).
% 2.32/2.58  thf('19', plain,
% 2.32/2.58      (![X28 : $i, X29 : $i]:
% 2.32/2.58         (((k8_relat_1 @ X29 @ X28) = (k5_relat_1 @ X28 @ (k6_relat_1 @ X29)))
% 2.32/2.58          | ~ (v1_relat_1 @ X28))),
% 2.32/2.58      inference('cnf', [status(esa)], [t123_relat_1])).
% 2.32/2.58  thf(t94_relat_1, axiom,
% 2.32/2.58    (![A:$i,B:$i]:
% 2.32/2.58     ( ( v1_relat_1 @ B ) =>
% 2.32/2.58       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 2.32/2.58  thf('20', plain,
% 2.32/2.58      (![X48 : $i, X49 : $i]:
% 2.32/2.58         (((k7_relat_1 @ X49 @ X48) = (k5_relat_1 @ (k6_relat_1 @ X48) @ X49))
% 2.32/2.58          | ~ (v1_relat_1 @ X49))),
% 2.32/2.58      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.32/2.58  thf('21', plain,
% 2.32/2.58      (![X0 : $i, X1 : $i]:
% 2.32/2.58         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 2.32/2.58            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 2.32/2.58          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.32/2.58          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 2.32/2.58      inference('sup+', [status(thm)], ['19', '20'])).
% 2.32/2.58  thf('22', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 2.32/2.58      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.32/2.58  thf('23', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 2.32/2.58      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.32/2.58  thf('24', plain,
% 2.32/2.58      (![X0 : $i, X1 : $i]:
% 2.32/2.58         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 2.32/2.58           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 2.32/2.58      inference('demod', [status(thm)], ['21', '22', '23'])).
% 2.32/2.58  thf('25', plain,
% 2.32/2.58      (![X0 : $i, X1 : $i]:
% 2.32/2.58         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 2.32/2.58           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 2.32/2.58      inference('demod', [status(thm)], ['21', '22', '23'])).
% 2.32/2.58  thf('26', plain,
% 2.32/2.58      (![X0 : $i, X1 : $i]:
% 2.32/2.58         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 2.32/2.58           = (k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))))),
% 2.32/2.58      inference('demod', [status(thm)], ['18', '24', '25'])).
% 2.32/2.58  thf('27', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 2.32/2.58      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 2.32/2.58  thf('28', plain,
% 2.32/2.58      (![X0 : $i, X1 : $i]:
% 2.32/2.58         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 2.32/2.58           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.32/2.58      inference('demod', [status(thm)], ['13', '26', '27'])).
% 2.32/2.58  thf('29', plain,
% 2.32/2.58      (((k8_relat_1 @ sk_A_3 @ (k6_relat_1 @ sk_B))
% 2.32/2.58         != (k8_relat_1 @ sk_A_3 @ (k6_relat_1 @ sk_B)))),
% 2.32/2.58      inference('demod', [status(thm)], ['4', '28'])).
% 2.32/2.58  thf('30', plain, ($false), inference('simplify', [status(thm)], ['29'])).
% 2.32/2.58  
% 2.32/2.58  % SZS output end Refutation
% 2.32/2.58  
% 2.32/2.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

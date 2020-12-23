%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3fjmxYjRz9

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:58 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   59 (  86 expanded)
%              Number of leaves         :   21 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :  403 ( 615 expanded)
%              Number of equality atoms :   37 (  51 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k8_relat_1 @ X19 @ X18 )
        = ( k5_relat_1 @ X18 @ ( k6_relat_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
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
    ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
     != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('4',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('6',plain,(
    ! [X26: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('7',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X20 ) @ X21 )
      | ( ( k8_relat_1 @ X21 @ X20 )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) @ X15 )
        = ( k7_relat_1 @ X13 @ ( k3_xboole_0 @ X14 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('13',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k8_relat_1 @ X19 @ X18 )
        = ( k5_relat_1 @ X18 @ ( k6_relat_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('14',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k7_relat_1 @ X29 @ X28 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X28 ) @ X29 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('17',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 )
        = ( k8_relat_1 @ X2 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['12','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('21',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relat_1 @ ( k8_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 )
      = ( k8_relat_1 @ X2 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k8_relat_1 @ X19 @ X18 )
        = ( k5_relat_1 @ X18 @ ( k6_relat_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('24',plain,(
    ! [X26: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('25',plain,(
    ! [X27: $i] :
      ( ( ( k5_relat_1 @ X27 @ ( k6_relat_1 @ ( k2_relat_1 @ X27 ) ) )
        = X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','28'])).

thf('30',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['11','22','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) )
 != ( k8_relat_1 @ sk_A @ ( k6_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','34'])).

thf('36',plain,(
    $false ),
    inference(simplify,[status(thm)],['35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3fjmxYjRz9
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:43:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.62  % Solved by: fo/fo7.sh
% 0.37/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.62  % done 241 iterations in 0.146s
% 0.37/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.62  % SZS output start Refutation
% 0.37/0.62  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.37/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.62  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.37/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.62  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.37/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.62  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.37/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.62  thf(t123_relat_1, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( v1_relat_1 @ B ) =>
% 0.37/0.62       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.37/0.62  thf('0', plain,
% 0.37/0.62      (![X18 : $i, X19 : $i]:
% 0.37/0.62         (((k8_relat_1 @ X19 @ X18) = (k5_relat_1 @ X18 @ (k6_relat_1 @ X19)))
% 0.37/0.62          | ~ (v1_relat_1 @ X18))),
% 0.37/0.62      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.37/0.62  thf(t43_funct_1, conjecture,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.37/0.62       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.62    (~( ![A:$i,B:$i]:
% 0.37/0.62        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.37/0.62          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.37/0.62    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 0.37/0.62  thf('1', plain,
% 0.37/0.62      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.37/0.62         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('2', plain,
% 0.37/0.62      ((((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.37/0.62          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 0.37/0.62        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['0', '1'])).
% 0.37/0.62  thf(fc3_funct_1, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.37/0.62       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.37/0.62  thf('3', plain, (![X30 : $i]: (v1_relat_1 @ (k6_relat_1 @ X30))),
% 0.37/0.62      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.37/0.62  thf('4', plain,
% 0.37/0.62      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.37/0.62         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.37/0.62      inference('demod', [status(thm)], ['2', '3'])).
% 0.37/0.62  thf(t17_xboole_1, axiom,
% 0.37/0.62    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.37/0.62  thf('5', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.37/0.62      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.37/0.62  thf(t71_relat_1, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.37/0.62       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.37/0.62  thf('6', plain, (![X26 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 0.37/0.62      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.37/0.62  thf(t125_relat_1, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( v1_relat_1 @ B ) =>
% 0.37/0.62       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.37/0.62         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.37/0.62  thf('7', plain,
% 0.37/0.62      (![X20 : $i, X21 : $i]:
% 0.37/0.62         (~ (r1_tarski @ (k2_relat_1 @ X20) @ X21)
% 0.37/0.62          | ((k8_relat_1 @ X21 @ X20) = (X20))
% 0.37/0.62          | ~ (v1_relat_1 @ X20))),
% 0.37/0.62      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.37/0.62  thf('8', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         (~ (r1_tarski @ X0 @ X1)
% 0.37/0.62          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.37/0.62          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.62  thf('9', plain, (![X30 : $i]: (v1_relat_1 @ (k6_relat_1 @ X30))),
% 0.37/0.62      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.37/0.62  thf('10', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         (~ (r1_tarski @ X0 @ X1)
% 0.37/0.62          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0)))),
% 0.37/0.62      inference('demod', [status(thm)], ['8', '9'])).
% 0.37/0.62  thf('11', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         ((k8_relat_1 @ X0 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 0.37/0.62           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['5', '10'])).
% 0.37/0.62  thf(t100_relat_1, axiom,
% 0.37/0.62    (![A:$i,B:$i,C:$i]:
% 0.37/0.62     ( ( v1_relat_1 @ C ) =>
% 0.37/0.62       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.37/0.62         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.37/0.62  thf('12', plain,
% 0.37/0.62      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.37/0.62         (((k7_relat_1 @ (k7_relat_1 @ X13 @ X14) @ X15)
% 0.37/0.62            = (k7_relat_1 @ X13 @ (k3_xboole_0 @ X14 @ X15)))
% 0.37/0.62          | ~ (v1_relat_1 @ X13))),
% 0.37/0.62      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.37/0.62  thf('13', plain,
% 0.37/0.62      (![X18 : $i, X19 : $i]:
% 0.37/0.62         (((k8_relat_1 @ X19 @ X18) = (k5_relat_1 @ X18 @ (k6_relat_1 @ X19)))
% 0.37/0.62          | ~ (v1_relat_1 @ X18))),
% 0.37/0.62      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.37/0.62  thf(t94_relat_1, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( v1_relat_1 @ B ) =>
% 0.37/0.62       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.37/0.62  thf('14', plain,
% 0.37/0.62      (![X28 : $i, X29 : $i]:
% 0.37/0.62         (((k7_relat_1 @ X29 @ X28) = (k5_relat_1 @ (k6_relat_1 @ X28) @ X29))
% 0.37/0.62          | ~ (v1_relat_1 @ X29))),
% 0.37/0.62      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.37/0.62  thf('15', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.37/0.62            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.37/0.62          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.37/0.62          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.37/0.62      inference('sup+', [status(thm)], ['13', '14'])).
% 0.37/0.62  thf('16', plain, (![X30 : $i]: (v1_relat_1 @ (k6_relat_1 @ X30))),
% 0.37/0.62      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.37/0.62  thf('17', plain, (![X30 : $i]: (v1_relat_1 @ (k6_relat_1 @ X30))),
% 0.37/0.62      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.37/0.62  thf('18', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.37/0.62           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.37/0.62      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.37/0.62  thf('19', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.62         (((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0)
% 0.37/0.62            = (k8_relat_1 @ X2 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))
% 0.37/0.62          | ~ (v1_relat_1 @ (k6_relat_1 @ X2)))),
% 0.37/0.62      inference('sup+', [status(thm)], ['12', '18'])).
% 0.37/0.62  thf('20', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.37/0.62           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.37/0.62      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.37/0.62  thf('21', plain, (![X30 : $i]: (v1_relat_1 @ (k6_relat_1 @ X30))),
% 0.37/0.62      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.37/0.62  thf('22', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.62         ((k7_relat_1 @ (k8_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0)
% 0.37/0.62           = (k8_relat_1 @ X2 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.37/0.62      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.37/0.62  thf('23', plain,
% 0.37/0.62      (![X18 : $i, X19 : $i]:
% 0.37/0.62         (((k8_relat_1 @ X19 @ X18) = (k5_relat_1 @ X18 @ (k6_relat_1 @ X19)))
% 0.37/0.62          | ~ (v1_relat_1 @ X18))),
% 0.37/0.62      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.37/0.62  thf('24', plain, (![X26 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 0.37/0.62      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.37/0.62  thf(t80_relat_1, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( v1_relat_1 @ A ) =>
% 0.37/0.62       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.37/0.62  thf('25', plain,
% 0.37/0.62      (![X27 : $i]:
% 0.37/0.62         (((k5_relat_1 @ X27 @ (k6_relat_1 @ (k2_relat_1 @ X27))) = (X27))
% 0.37/0.62          | ~ (v1_relat_1 @ X27))),
% 0.37/0.62      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.37/0.62  thf('26', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.37/0.62            = (k6_relat_1 @ X0))
% 0.37/0.62          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.37/0.62      inference('sup+', [status(thm)], ['24', '25'])).
% 0.37/0.62  thf('27', plain, (![X30 : $i]: (v1_relat_1 @ (k6_relat_1 @ X30))),
% 0.37/0.62      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.37/0.62  thf('28', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))
% 0.37/0.62           = (k6_relat_1 @ X0))),
% 0.37/0.62      inference('demod', [status(thm)], ['26', '27'])).
% 0.37/0.62  thf('29', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))
% 0.37/0.62          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.37/0.62      inference('sup+', [status(thm)], ['23', '28'])).
% 0.37/0.62  thf('30', plain, (![X30 : $i]: (v1_relat_1 @ (k6_relat_1 @ X30))),
% 0.37/0.62      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.37/0.62  thf('31', plain,
% 0.37/0.62      (![X0 : $i]: ((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 0.37/0.62      inference('demod', [status(thm)], ['29', '30'])).
% 0.37/0.62  thf('32', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.37/0.62           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.37/0.62      inference('demod', [status(thm)], ['11', '22', '31'])).
% 0.37/0.62  thf('33', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.37/0.62           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.37/0.62      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.37/0.62  thf('34', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.37/0.62           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.37/0.62      inference('demod', [status(thm)], ['32', '33'])).
% 0.37/0.62  thf('35', plain,
% 0.37/0.62      (((k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B))
% 0.37/0.62         != (k8_relat_1 @ sk_A @ (k6_relat_1 @ sk_B)))),
% 0.37/0.62      inference('demod', [status(thm)], ['4', '34'])).
% 0.37/0.62  thf('36', plain, ($false), inference('simplify', [status(thm)], ['35'])).
% 0.37/0.62  
% 0.37/0.62  % SZS output end Refutation
% 0.37/0.62  
% 0.37/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

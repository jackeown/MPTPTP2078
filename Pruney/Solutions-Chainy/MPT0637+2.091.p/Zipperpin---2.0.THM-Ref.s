%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Fu07gzhG8i

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:09 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   48 (  54 expanded)
%              Number of leaves         :   20 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :  318 ( 383 expanded)
%              Number of equality atoms :   27 (  28 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k7_relat_1 @ X23 @ X22 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X22 ) @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

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
    ( ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
     != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc24_relat_1,axiom,(
    ! [A: $i] :
      ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('4',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X25: $i] :
      ( v4_relat_1 @ ( k6_relat_1 @ X25 ) @ X25 ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X16
        = ( k7_relat_1 @ X16 @ X17 ) )
      | ~ ( v4_relat_1 @ X16 @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k6_relat_1 @ X0 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k6_relat_1 @ X0 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('10',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) @ X15 )
        = ( k7_relat_1 @ X13 @ ( k3_xboole_0 @ X14 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('13',plain,(
    ! [X19: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('14',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X20 ) @ X21 )
      | ( ( k5_relat_1 @ X20 @ ( k6_relat_1 @ X21 ) )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k7_relat_1 @ X23 @ X22 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X22 ) @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['11','22','23'])).

thf('25',plain,(
    ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','24'])).

thf('26',plain,(
    $false ),
    inference(simplify,[status(thm)],['25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Fu07gzhG8i
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:46:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.47  % Solved by: fo/fo7.sh
% 0.22/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.47  % done 22 iterations in 0.016s
% 0.22/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.47  % SZS output start Refutation
% 0.22/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.47  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.47  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.22/0.47  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.22/0.47  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.22/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.47  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.47  thf(t94_relat_1, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( v1_relat_1 @ B ) =>
% 0.22/0.47       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.22/0.47  thf('0', plain,
% 0.22/0.47      (![X22 : $i, X23 : $i]:
% 0.22/0.47         (((k7_relat_1 @ X23 @ X22) = (k5_relat_1 @ (k6_relat_1 @ X22) @ X23))
% 0.22/0.47          | ~ (v1_relat_1 @ X23))),
% 0.22/0.47      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.22/0.47  thf(t43_funct_1, conjecture,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.22/0.47       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.47    (~( ![A:$i,B:$i]:
% 0.22/0.47        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.22/0.47          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.22/0.47    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 0.22/0.47  thf('1', plain,
% 0.22/0.47      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.22/0.47         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('2', plain,
% 0.22/0.47      ((((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.22/0.47          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 0.22/0.47        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.47  thf(fc24_relat_1, axiom,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.22/0.47       ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.22/0.47       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.22/0.47  thf('3', plain, (![X24 : $i]: (v1_relat_1 @ (k6_relat_1 @ X24))),
% 0.22/0.47      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.22/0.47  thf('4', plain,
% 0.22/0.47      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.22/0.47         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.47      inference('demod', [status(thm)], ['2', '3'])).
% 0.22/0.47  thf('5', plain, (![X25 : $i]: (v4_relat_1 @ (k6_relat_1 @ X25) @ X25)),
% 0.22/0.47      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.22/0.47  thf(t209_relat_1, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.22/0.47       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.22/0.47  thf('6', plain,
% 0.22/0.47      (![X16 : $i, X17 : $i]:
% 0.22/0.47         (((X16) = (k7_relat_1 @ X16 @ X17))
% 0.22/0.47          | ~ (v4_relat_1 @ X16 @ X17)
% 0.22/0.47          | ~ (v1_relat_1 @ X16))),
% 0.22/0.47      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.22/0.47  thf('7', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.22/0.47          | ((k6_relat_1 @ X0) = (k7_relat_1 @ (k6_relat_1 @ X0) @ X0)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.47  thf('8', plain, (![X24 : $i]: (v1_relat_1 @ (k6_relat_1 @ X24))),
% 0.22/0.47      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.22/0.47  thf('9', plain,
% 0.22/0.47      (![X0 : $i]: ((k6_relat_1 @ X0) = (k7_relat_1 @ (k6_relat_1 @ X0) @ X0))),
% 0.22/0.47      inference('demod', [status(thm)], ['7', '8'])).
% 0.22/0.47  thf(t100_relat_1, axiom,
% 0.22/0.47    (![A:$i,B:$i,C:$i]:
% 0.22/0.47     ( ( v1_relat_1 @ C ) =>
% 0.22/0.47       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.22/0.47         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.22/0.47  thf('10', plain,
% 0.22/0.47      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.47         (((k7_relat_1 @ (k7_relat_1 @ X13 @ X14) @ X15)
% 0.22/0.47            = (k7_relat_1 @ X13 @ (k3_xboole_0 @ X14 @ X15)))
% 0.22/0.47          | ~ (v1_relat_1 @ X13))),
% 0.22/0.47      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.22/0.47  thf('11', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i]:
% 0.22/0.47         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.22/0.47            = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))
% 0.22/0.47          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.22/0.47      inference('sup+', [status(thm)], ['9', '10'])).
% 0.22/0.47  thf(t17_xboole_1, axiom,
% 0.22/0.47    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.22/0.47  thf('12', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.22/0.47      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.22/0.47  thf(t71_relat_1, axiom,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.22/0.47       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.22/0.47  thf('13', plain, (![X19 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X19)) = (X19))),
% 0.22/0.47      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.47  thf(t79_relat_1, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( v1_relat_1 @ B ) =>
% 0.22/0.47       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.22/0.47         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.22/0.47  thf('14', plain,
% 0.22/0.47      (![X20 : $i, X21 : $i]:
% 0.22/0.47         (~ (r1_tarski @ (k2_relat_1 @ X20) @ X21)
% 0.22/0.47          | ((k5_relat_1 @ X20 @ (k6_relat_1 @ X21)) = (X20))
% 0.22/0.47          | ~ (v1_relat_1 @ X20))),
% 0.22/0.47      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.22/0.47  thf('15', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i]:
% 0.22/0.47         (~ (r1_tarski @ X0 @ X1)
% 0.22/0.47          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.22/0.47          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.22/0.47              = (k6_relat_1 @ X0)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.47  thf('16', plain, (![X24 : $i]: (v1_relat_1 @ (k6_relat_1 @ X24))),
% 0.22/0.47      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.22/0.47  thf('17', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i]:
% 0.22/0.47         (~ (r1_tarski @ X0 @ X1)
% 0.22/0.47          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.22/0.47              = (k6_relat_1 @ X0)))),
% 0.22/0.47      inference('demod', [status(thm)], ['15', '16'])).
% 0.22/0.47  thf('18', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i]:
% 0.22/0.47         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.22/0.47           (k6_relat_1 @ X0)) = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['12', '17'])).
% 0.22/0.47  thf('19', plain,
% 0.22/0.47      (![X22 : $i, X23 : $i]:
% 0.22/0.47         (((k7_relat_1 @ X23 @ X22) = (k5_relat_1 @ (k6_relat_1 @ X22) @ X23))
% 0.22/0.47          | ~ (v1_relat_1 @ X23))),
% 0.22/0.47      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.22/0.47  thf('20', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i]:
% 0.22/0.47         (((k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 0.22/0.47            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.22/0.47          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.22/0.47      inference('sup+', [status(thm)], ['18', '19'])).
% 0.22/0.47  thf('21', plain, (![X24 : $i]: (v1_relat_1 @ (k6_relat_1 @ X24))),
% 0.22/0.47      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.22/0.47  thf('22', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i]:
% 0.22/0.47         ((k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 0.22/0.47           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.22/0.47      inference('demod', [status(thm)], ['20', '21'])).
% 0.22/0.47  thf('23', plain, (![X24 : $i]: (v1_relat_1 @ (k6_relat_1 @ X24))),
% 0.22/0.47      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.22/0.47  thf('24', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i]:
% 0.22/0.47         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.22/0.47           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.22/0.47      inference('demod', [status(thm)], ['11', '22', '23'])).
% 0.22/0.47  thf('25', plain,
% 0.22/0.47      (((k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B))
% 0.22/0.47         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.47      inference('demod', [status(thm)], ['4', '24'])).
% 0.22/0.47  thf('26', plain, ($false), inference('simplify', [status(thm)], ['25'])).
% 0.22/0.47  
% 0.22/0.47  % SZS output end Refutation
% 0.22/0.47  
% 0.22/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

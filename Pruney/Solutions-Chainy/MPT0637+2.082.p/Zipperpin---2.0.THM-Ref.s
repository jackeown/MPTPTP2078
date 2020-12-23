%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2FKCEHBXYU

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   47 (  53 expanded)
%              Number of leaves         :   18 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :  318 ( 350 expanded)
%              Number of equality atoms :   29 (  32 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k7_relat_1 @ X18 @ X17 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X17 ) @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
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

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('4',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('5',plain,(
    ! [X13: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('6',plain,(
    ! [X19: $i] :
      ( ( ( k7_relat_1 @ X19 @ ( k1_relat_1 @ X19 ) )
        = X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) @ X12 )
        = ( k7_relat_1 @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('15',plain,(
    ! [X14: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('16',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ( ( k5_relat_1 @ X15 @ ( k6_relat_1 @ X16 ) )
        = X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k7_relat_1 @ X18 @ X17 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X17 ) @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','24'])).

thf('26',plain,(
    ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','25'])).

thf('27',plain,(
    $false ),
    inference(simplify,[status(thm)],['26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2FKCEHBXYU
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:31:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 29 iterations in 0.018s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.47  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.47  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.47  thf(t94_relat_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ B ) =>
% 0.21/0.47       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      (![X17 : $i, X18 : $i]:
% 0.21/0.47         (((k7_relat_1 @ X18 @ X17) = (k5_relat_1 @ (k6_relat_1 @ X17) @ X18))
% 0.21/0.47          | ~ (v1_relat_1 @ X18))),
% 0.21/0.47      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.21/0.47  thf(t43_funct_1, conjecture,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.21/0.47       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i]:
% 0.21/0.47        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.21/0.47          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.21/0.47         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      ((((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.21/0.47          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 0.21/0.47        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.47  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.21/0.47  thf('3', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.21/0.47         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.47      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.47  thf(t71_relat_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.21/0.47       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.47  thf('5', plain, (![X13 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X13)) = (X13))),
% 0.21/0.47      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.47  thf(t98_relat_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ A ) =>
% 0.21/0.47       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X19 : $i]:
% 0.21/0.47         (((k7_relat_1 @ X19 @ (k1_relat_1 @ X19)) = (X19))
% 0.21/0.47          | ~ (v1_relat_1 @ X19))),
% 0.21/0.47      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))
% 0.21/0.47          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.47      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.47  thf('8', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.21/0.47      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.47  thf(t100_relat_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ C ) =>
% 0.21/0.47       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.21/0.47         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.47         (((k7_relat_1 @ (k7_relat_1 @ X10 @ X11) @ X12)
% 0.21/0.47            = (k7_relat_1 @ X10 @ (k3_xboole_0 @ X11 @ X12)))
% 0.21/0.47          | ~ (v1_relat_1 @ X10))),
% 0.21/0.47      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.21/0.47            = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))
% 0.21/0.47          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.47      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.47  thf('12', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.21/0.47           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.21/0.47      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.47  thf(t17_xboole_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.21/0.47      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.21/0.47  thf('15', plain, (![X14 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X14)) = (X14))),
% 0.21/0.47      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.47  thf(t79_relat_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ B ) =>
% 0.21/0.47       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.21/0.47         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      (![X15 : $i, X16 : $i]:
% 0.21/0.47         (~ (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 0.21/0.47          | ((k5_relat_1 @ X15 @ (k6_relat_1 @ X16)) = (X15))
% 0.21/0.47          | ~ (v1_relat_1 @ X15))),
% 0.21/0.47      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.47          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.21/0.47          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.21/0.47              = (k6_relat_1 @ X0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.47  thf('18', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.47          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.21/0.47              = (k6_relat_1 @ X0)))),
% 0.21/0.47      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.21/0.47           (k6_relat_1 @ X0)) = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['14', '19'])).
% 0.21/0.47  thf('21', plain,
% 0.21/0.47      (![X17 : $i, X18 : $i]:
% 0.21/0.47         (((k7_relat_1 @ X18 @ X17) = (k5_relat_1 @ (k6_relat_1 @ X17) @ X18))
% 0.21/0.47          | ~ (v1_relat_1 @ X18))),
% 0.21/0.47      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.21/0.47  thf('22', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (((k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.47            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.21/0.47          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.21/0.47      inference('sup+', [status(thm)], ['20', '21'])).
% 0.21/0.47  thf('23', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.47  thf('24', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.47           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.47      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.47  thf('25', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.21/0.47           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.47      inference('sup+', [status(thm)], ['13', '24'])).
% 0.21/0.47  thf('26', plain,
% 0.21/0.47      (((k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B))
% 0.21/0.47         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.47      inference('demod', [status(thm)], ['4', '25'])).
% 0.21/0.47  thf('27', plain, ($false), inference('simplify', [status(thm)], ['26'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

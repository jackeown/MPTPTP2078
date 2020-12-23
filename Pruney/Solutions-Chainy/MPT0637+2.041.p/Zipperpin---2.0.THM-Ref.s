%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QA5pMHLmJi

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:01 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :   54 (  79 expanded)
%              Number of leaves         :   21 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :  390 ( 578 expanded)
%              Number of equality atoms :   35 (  51 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t43_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_funct_1])).

thf('0',plain,(
    ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('1',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k7_relat_1 @ X24 @ X23 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X23 ) @ X24 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t72_relat_1,axiom,(
    ! [A: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X18: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X18 ) )
      = ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('3',plain,(
    ! [X18: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X18 ) )
      = ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X14 ) @ ( k4_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('6',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','7'])).

thf('9',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf('12',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','13'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('16',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('17',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X19 ) @ X20 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X20 ) @ X19 )
        = X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('23',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t192_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('24',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k7_relat_1 @ X12 @ X13 )
        = ( k7_relat_1 @ X12 @ ( k3_xboole_0 @ ( k1_relat_1 @ X12 ) @ X13 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['21','22','27'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('30',plain,(
    ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','28','29'])).

thf('31',plain,(
    $false ),
    inference(simplify,[status(thm)],['30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QA5pMHLmJi
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:56:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.55/0.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.55/0.73  % Solved by: fo/fo7.sh
% 0.55/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.73  % done 290 iterations in 0.230s
% 0.55/0.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.55/0.73  % SZS output start Refutation
% 0.55/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.55/0.73  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.55/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.73  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.55/0.73  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.55/0.73  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.55/0.73  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.55/0.73  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.55/0.73  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.55/0.73  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.55/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.73  thf(t43_funct_1, conjecture,
% 0.55/0.73    (![A:$i,B:$i]:
% 0.55/0.73     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.55/0.73       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.55/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.73    (~( ![A:$i,B:$i]:
% 0.55/0.73        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.55/0.73          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.55/0.73    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 0.55/0.73  thf('0', plain,
% 0.55/0.73      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.55/0.73         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf(t94_relat_1, axiom,
% 0.55/0.73    (![A:$i,B:$i]:
% 0.55/0.73     ( ( v1_relat_1 @ B ) =>
% 0.55/0.73       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.55/0.73  thf('1', plain,
% 0.55/0.73      (![X23 : $i, X24 : $i]:
% 0.55/0.73         (((k7_relat_1 @ X24 @ X23) = (k5_relat_1 @ (k6_relat_1 @ X23) @ X24))
% 0.55/0.73          | ~ (v1_relat_1 @ X24))),
% 0.55/0.73      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.55/0.73  thf(t72_relat_1, axiom,
% 0.55/0.73    (![A:$i]: ( ( k4_relat_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.55/0.73  thf('2', plain,
% 0.55/0.73      (![X18 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X18)) = (k6_relat_1 @ X18))),
% 0.55/0.73      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.55/0.73  thf('3', plain,
% 0.55/0.73      (![X18 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X18)) = (k6_relat_1 @ X18))),
% 0.55/0.73      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.55/0.73  thf(t54_relat_1, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( v1_relat_1 @ A ) =>
% 0.55/0.73       ( ![B:$i]:
% 0.55/0.73         ( ( v1_relat_1 @ B ) =>
% 0.55/0.73           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.55/0.73             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 0.55/0.73  thf('4', plain,
% 0.55/0.73      (![X14 : $i, X15 : $i]:
% 0.55/0.73         (~ (v1_relat_1 @ X14)
% 0.55/0.73          | ((k4_relat_1 @ (k5_relat_1 @ X15 @ X14))
% 0.55/0.73              = (k5_relat_1 @ (k4_relat_1 @ X14) @ (k4_relat_1 @ X15)))
% 0.55/0.73          | ~ (v1_relat_1 @ X15))),
% 0.55/0.73      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.55/0.73  thf('5', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i]:
% 0.55/0.73         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.55/0.73            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.55/0.73          | ~ (v1_relat_1 @ X1)
% 0.55/0.73          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.55/0.73      inference('sup+', [status(thm)], ['3', '4'])).
% 0.55/0.73  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.55/0.73  thf('6', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.55/0.73      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.55/0.73  thf('7', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i]:
% 0.55/0.73         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.55/0.73            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.55/0.73          | ~ (v1_relat_1 @ X1))),
% 0.55/0.73      inference('demod', [status(thm)], ['5', '6'])).
% 0.55/0.73  thf('8', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i]:
% 0.55/0.73         (((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))
% 0.55/0.73            = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 0.55/0.73          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.55/0.73      inference('sup+', [status(thm)], ['2', '7'])).
% 0.55/0.73  thf('9', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.55/0.73      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.55/0.73  thf('10', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i]:
% 0.55/0.73         ((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))
% 0.55/0.73           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.55/0.73      inference('demod', [status(thm)], ['8', '9'])).
% 0.55/0.73  thf('11', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i]:
% 0.55/0.73         (((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.55/0.73            = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 0.55/0.73          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.55/0.73      inference('sup+', [status(thm)], ['1', '10'])).
% 0.55/0.73  thf('12', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.55/0.73      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.55/0.73  thf('13', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i]:
% 0.55/0.73         ((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.55/0.73           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.55/0.73      inference('demod', [status(thm)], ['11', '12'])).
% 0.55/0.73  thf('14', plain,
% 0.55/0.73      (((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ sk_B) @ sk_A))
% 0.55/0.73         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.55/0.73      inference('demod', [status(thm)], ['0', '13'])).
% 0.55/0.73  thf(t17_xboole_1, axiom,
% 0.55/0.73    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.55/0.73  thf('15', plain,
% 0.55/0.73      (![X2 : $i, X3 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X3) @ X2)),
% 0.55/0.73      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.55/0.73  thf(t71_relat_1, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.55/0.73       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.55/0.73  thf('16', plain, (![X16 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X16)) = (X16))),
% 0.55/0.73      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.55/0.73  thf(t77_relat_1, axiom,
% 0.55/0.73    (![A:$i,B:$i]:
% 0.55/0.73     ( ( v1_relat_1 @ B ) =>
% 0.55/0.73       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.55/0.73         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 0.55/0.73  thf('17', plain,
% 0.55/0.73      (![X19 : $i, X20 : $i]:
% 0.55/0.73         (~ (r1_tarski @ (k1_relat_1 @ X19) @ X20)
% 0.55/0.73          | ((k5_relat_1 @ (k6_relat_1 @ X20) @ X19) = (X19))
% 0.55/0.73          | ~ (v1_relat_1 @ X19))),
% 0.55/0.73      inference('cnf', [status(esa)], [t77_relat_1])).
% 0.55/0.73  thf('18', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i]:
% 0.55/0.73         (~ (r1_tarski @ X0 @ X1)
% 0.55/0.73          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.55/0.73          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 0.55/0.73              = (k6_relat_1 @ X0)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['16', '17'])).
% 0.55/0.73  thf('19', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.55/0.73      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.55/0.73  thf('20', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i]:
% 0.55/0.73         (~ (r1_tarski @ X0 @ X1)
% 0.55/0.73          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 0.55/0.73              = (k6_relat_1 @ X0)))),
% 0.55/0.73      inference('demod', [status(thm)], ['18', '19'])).
% 0.55/0.73  thf('21', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i]:
% 0.55/0.73         ((k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.55/0.73           (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 0.55/0.73           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['15', '20'])).
% 0.55/0.73  thf('22', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i]:
% 0.55/0.73         ((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.55/0.73           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.55/0.73      inference('demod', [status(thm)], ['11', '12'])).
% 0.55/0.73  thf('23', plain, (![X16 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X16)) = (X16))),
% 0.55/0.73      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.55/0.73  thf(t192_relat_1, axiom,
% 0.55/0.73    (![A:$i,B:$i]:
% 0.55/0.73     ( ( v1_relat_1 @ B ) =>
% 0.55/0.73       ( ( k7_relat_1 @ B @ A ) =
% 0.55/0.73         ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 0.55/0.73  thf('24', plain,
% 0.55/0.73      (![X12 : $i, X13 : $i]:
% 0.55/0.73         (((k7_relat_1 @ X12 @ X13)
% 0.55/0.73            = (k7_relat_1 @ X12 @ (k3_xboole_0 @ (k1_relat_1 @ X12) @ X13)))
% 0.55/0.73          | ~ (v1_relat_1 @ X12))),
% 0.55/0.73      inference('cnf', [status(esa)], [t192_relat_1])).
% 0.55/0.73  thf('25', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i]:
% 0.55/0.73         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.55/0.73            = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))
% 0.55/0.73          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.55/0.73      inference('sup+', [status(thm)], ['23', '24'])).
% 0.55/0.73  thf('26', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.55/0.73      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.55/0.73  thf('27', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i]:
% 0.55/0.73         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.55/0.73           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.55/0.73      inference('demod', [status(thm)], ['25', '26'])).
% 0.55/0.73  thf('28', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i]:
% 0.55/0.73         ((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.55/0.73           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.55/0.73      inference('demod', [status(thm)], ['21', '22', '27'])).
% 0.55/0.73  thf(commutativity_k3_xboole_0, axiom,
% 0.55/0.73    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.55/0.73  thf('29', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.55/0.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.55/0.73  thf('30', plain,
% 0.55/0.73      (((k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B))
% 0.55/0.73         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.55/0.73      inference('demod', [status(thm)], ['14', '28', '29'])).
% 0.55/0.73  thf('31', plain, ($false), inference('simplify', [status(thm)], ['30'])).
% 0.55/0.73  
% 0.55/0.73  % SZS output end Refutation
% 0.55/0.73  
% 0.55/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

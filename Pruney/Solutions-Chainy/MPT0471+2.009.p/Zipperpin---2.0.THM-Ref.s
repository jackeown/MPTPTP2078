%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XulceCZycl

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   44 (  47 expanded)
%              Number of leaves         :   20 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :  191 ( 213 expanded)
%              Number of equality atoms :   28 (  32 expanded)
%              Maximal formula depth    :    7 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('0',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X8: $i] :
      ( ( ( k3_relat_1 @ X8 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X8 ) @ ( k2_relat_1 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('3',plain,
    ( ( ( k3_relat_1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('5',plain,(
    ! [X2: $i] :
      ( ( k4_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X2: $i] :
      ( ( k4_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ ( k4_xboole_0 @ X3 @ X4 ) )
      = ( k3_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X1: $i] :
      ( ( k3_xboole_0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( k3_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4','7','16'])).

thf(t63_relat_1,conjecture,
    ( ( k3_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf(zf_stmt_0,negated_conjecture,(
    ( k3_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('cnf.neg',[status(esa)],[t63_relat_1])).

thf('18',plain,(
    ( k3_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','19'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('21',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('22',plain,(
    $false ),
    inference(demod,[status(thm)],['20','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XulceCZycl
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:53:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 20 iterations in 0.013s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.21/0.47  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.47  thf(cc1_relat_1, axiom,
% 0.21/0.47    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.21/0.47  thf('0', plain, (![X7 : $i]: ((v1_relat_1 @ X7) | ~ (v1_xboole_0 @ X7))),
% 0.21/0.47      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.21/0.47  thf(t60_relat_1, axiom,
% 0.21/0.47    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.47     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.47  thf('1', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.47  thf(d6_relat_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ A ) =>
% 0.21/0.47       ( ( k3_relat_1 @ A ) =
% 0.21/0.47         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X8 : $i]:
% 0.21/0.47         (((k3_relat_1 @ X8)
% 0.21/0.47            = (k2_xboole_0 @ (k1_relat_1 @ X8) @ (k2_relat_1 @ X8)))
% 0.21/0.47          | ~ (v1_relat_1 @ X8))),
% 0.21/0.47      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      ((((k3_relat_1 @ k1_xboole_0)
% 0.21/0.47          = (k2_xboole_0 @ k1_xboole_0 @ (k2_relat_1 @ k1_xboole_0)))
% 0.21/0.47        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.21/0.47      inference('sup+', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf('4', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.47  thf(t3_boole, axiom,
% 0.21/0.47    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.47  thf('5', plain, (![X2 : $i]: ((k4_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.21/0.47      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.47  thf(t98_xboole_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X5 : $i, X6 : $i]:
% 0.21/0.47         ((k2_xboole_0 @ X5 @ X6)
% 0.21/0.47           = (k5_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.21/0.47      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.47  thf('8', plain, (![X2 : $i]: ((k4_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.21/0.47      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.47  thf(t48_xboole_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (![X3 : $i, X4 : $i]:
% 0.21/0.47         ((k4_xboole_0 @ X3 @ (k4_xboole_0 @ X3 @ X4))
% 0.21/0.47           = (k3_xboole_0 @ X3 @ X4))),
% 0.21/0.47      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.47      inference('sup+', [status(thm)], ['8', '9'])).
% 0.21/0.47  thf(t2_boole, axiom,
% 0.21/0.47    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X1 : $i]: ((k3_xboole_0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.47  thf('12', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.47      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (![X5 : $i, X6 : $i]:
% 0.21/0.47         ((k2_xboole_0 @ X5 @ X6)
% 0.21/0.47           = (k5_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.47      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.47  thf(idempotence_k2_xboole_0, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.21/0.47  thf('15', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.21/0.47  thf('16', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.47      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      ((((k3_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.21/0.47        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.21/0.47      inference('demod', [status(thm)], ['3', '4', '7', '16'])).
% 0.21/0.47  thf(t63_relat_1, conjecture,
% 0.21/0.47    (( k3_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (( k3_relat_1 @ k1_xboole_0 ) != ( k1_xboole_0 )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t63_relat_1])).
% 0.21/0.47  thf('18', plain, (((k3_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('19', plain, (~ (v1_relat_1 @ k1_xboole_0)),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 0.21/0.47  thf('20', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.47      inference('sup-', [status(thm)], ['0', '19'])).
% 0.21/0.47  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.47  thf('21', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.47      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.47  thf('22', plain, ($false), inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

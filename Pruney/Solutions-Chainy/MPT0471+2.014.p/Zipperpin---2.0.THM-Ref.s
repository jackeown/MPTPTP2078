%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.q59KAAQbTm

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   33 (  34 expanded)
%              Number of leaves         :   17 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :  125 ( 133 expanded)
%              Number of equality atoms :   18 (  20 expanded)
%              Maximal formula depth    :    7 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
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
    ! [X5: $i] :
      ( ( ( k3_relat_1 @ X5 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X5 ) @ ( k2_relat_1 @ X5 ) ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
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
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X1: $i] :
      ( ( k5_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('9',plain,
    ( ( ( k3_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4','7','8'])).

thf(t63_relat_1,conjecture,
    ( ( k3_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf(zf_stmt_0,negated_conjecture,(
    ( k3_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('cnf.neg',[status(esa)],[t63_relat_1])).

thf('10',plain,(
    ( k3_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('13',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('14',plain,(
    $false ),
    inference(demod,[status(thm)],['12','13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.q59KAAQbTm
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:33:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.43  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.43  % Solved by: fo/fo7.sh
% 0.21/0.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.43  % done 10 iterations in 0.008s
% 0.21/0.43  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.43  % SZS output start Refutation
% 0.21/0.43  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.21/0.43  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.43  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.43  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.43  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.43  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.43  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.43  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.43  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.43  thf(cc1_relat_1, axiom,
% 0.21/0.43    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.21/0.43  thf('0', plain, (![X4 : $i]: ((v1_relat_1 @ X4) | ~ (v1_xboole_0 @ X4))),
% 0.21/0.43      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.21/0.43  thf(t60_relat_1, axiom,
% 0.21/0.43    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.43     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.43  thf('1', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.43      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.43  thf(d6_relat_1, axiom,
% 0.21/0.43    (![A:$i]:
% 0.21/0.43     ( ( v1_relat_1 @ A ) =>
% 0.21/0.43       ( ( k3_relat_1 @ A ) =
% 0.21/0.43         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.21/0.43  thf('2', plain,
% 0.21/0.43      (![X5 : $i]:
% 0.21/0.43         (((k3_relat_1 @ X5)
% 0.21/0.43            = (k2_xboole_0 @ (k1_relat_1 @ X5) @ (k2_relat_1 @ X5)))
% 0.21/0.43          | ~ (v1_relat_1 @ X5))),
% 0.21/0.43      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.21/0.43  thf('3', plain,
% 0.21/0.43      ((((k3_relat_1 @ k1_xboole_0)
% 0.21/0.43          = (k2_xboole_0 @ k1_xboole_0 @ (k2_relat_1 @ k1_xboole_0)))
% 0.21/0.43        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.21/0.43      inference('sup+', [status(thm)], ['1', '2'])).
% 0.21/0.43  thf('4', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.43      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.43  thf(t3_boole, axiom,
% 0.21/0.43    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.43  thf('5', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.43      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.43  thf(t98_xboole_1, axiom,
% 0.21/0.43    (![A:$i,B:$i]:
% 0.21/0.43     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.21/0.43  thf('6', plain,
% 0.21/0.43      (![X2 : $i, X3 : $i]:
% 0.21/0.43         ((k2_xboole_0 @ X2 @ X3)
% 0.21/0.43           = (k5_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2)))),
% 0.21/0.43      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.21/0.43  thf('7', plain,
% 0.21/0.43      (![X0 : $i]:
% 0.21/0.43         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.21/0.43      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.43  thf(t5_boole, axiom,
% 0.21/0.43    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.43  thf('8', plain, (![X1 : $i]: ((k5_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.21/0.43      inference('cnf', [status(esa)], [t5_boole])).
% 0.21/0.43  thf('9', plain,
% 0.21/0.43      ((((k3_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.21/0.43        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.21/0.43      inference('demod', [status(thm)], ['3', '4', '7', '8'])).
% 0.21/0.43  thf(t63_relat_1, conjecture,
% 0.21/0.43    (( k3_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.21/0.43  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.43    (( k3_relat_1 @ k1_xboole_0 ) != ( k1_xboole_0 )),
% 0.21/0.43    inference('cnf.neg', [status(esa)], [t63_relat_1])).
% 0.21/0.43  thf('10', plain, (((k3_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.43  thf('11', plain, (~ (v1_relat_1 @ k1_xboole_0)),
% 0.21/0.43      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.21/0.43  thf('12', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.43      inference('sup-', [status(thm)], ['0', '11'])).
% 0.21/0.43  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.43  thf('13', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.43      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.43  thf('14', plain, ($false), inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.43  
% 0.21/0.43  % SZS output end Refutation
% 0.21/0.43  
% 0.21/0.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

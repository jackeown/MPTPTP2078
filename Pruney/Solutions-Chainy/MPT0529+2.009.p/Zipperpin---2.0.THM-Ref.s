%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3aLam7e1kD

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   31 (  35 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :    9
%              Number of atoms          :  202 ( 258 expanded)
%              Number of equality atoms :   14 (  18 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t129_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) )
          = ( k8_relat_1 @ A @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) )
            = ( k8_relat_1 @ A @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t129_relat_1])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t108_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['0','3'])).

thf(t119_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X8 @ X7 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X7 ) @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X9 ) @ X10 )
      | ( ( k8_relat_1 @ X10 @ X9 )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) )
      | ( ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X0 @ X1 ) )
        = ( k8_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ X0 ) )
        = ( k8_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ X0 ) )
        = ( k8_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
 != ( k8_relat_1 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( k8_relat_1 @ sk_A @ sk_C )
     != ( k8_relat_1 @ sk_A @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ( k8_relat_1 @ sk_A @ sk_C )
 != ( k8_relat_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    $false ),
    inference(simplify,[status(thm)],['14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3aLam7e1kD
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:28:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 30 iterations in 0.021s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.47  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.21/0.47  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.47      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.47  thf(t129_relat_1, conjecture,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ C ) =>
% 0.21/0.47       ( ( r1_tarski @ A @ B ) =>
% 0.21/0.47         ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) = ( k8_relat_1 @ A @ C ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.47        ( ( v1_relat_1 @ C ) =>
% 0.21/0.47          ( ( r1_tarski @ A @ B ) =>
% 0.21/0.47            ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) =
% 0.21/0.47              ( k8_relat_1 @ A @ C ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t129_relat_1])).
% 0.21/0.47  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t108_xboole_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.47         (~ (r1_tarski @ X2 @ X3) | (r1_tarski @ (k3_xboole_0 @ X2 @ X4) @ X3))),
% 0.21/0.47      inference('cnf', [status(esa)], [t108_xboole_1])).
% 0.21/0.47  thf('3', plain, (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ sk_B)),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf('4', plain, (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ sk_B)),
% 0.21/0.47      inference('sup+', [status(thm)], ['0', '3'])).
% 0.21/0.47  thf(t119_relat_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ B ) =>
% 0.21/0.47       ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) =
% 0.21/0.47         ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X7 : $i, X8 : $i]:
% 0.21/0.47         (((k2_relat_1 @ (k8_relat_1 @ X8 @ X7))
% 0.21/0.47            = (k3_xboole_0 @ (k2_relat_1 @ X7) @ X8))
% 0.21/0.47          | ~ (v1_relat_1 @ X7))),
% 0.21/0.47      inference('cnf', [status(esa)], [t119_relat_1])).
% 0.21/0.47  thf(t125_relat_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ B ) =>
% 0.21/0.47       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.21/0.47         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X9 : $i, X10 : $i]:
% 0.21/0.47         (~ (r1_tarski @ (k2_relat_1 @ X9) @ X10)
% 0.21/0.47          | ((k8_relat_1 @ X10 @ X9) = (X9))
% 0.21/0.47          | ~ (v1_relat_1 @ X9))),
% 0.21/0.47      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         (~ (r1_tarski @ (k3_xboole_0 @ (k2_relat_1 @ X1) @ X0) @ X2)
% 0.21/0.47          | ~ (v1_relat_1 @ X1)
% 0.21/0.47          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ X1))
% 0.21/0.47          | ((k8_relat_1 @ X2 @ (k8_relat_1 @ X0 @ X1))
% 0.21/0.47              = (k8_relat_1 @ X0 @ X1)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ X0))
% 0.21/0.47            = (k8_relat_1 @ sk_A @ X0))
% 0.21/0.47          | ~ (v1_relat_1 @ (k8_relat_1 @ sk_A @ X0))
% 0.21/0.47          | ~ (v1_relat_1 @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['4', '7'])).
% 0.21/0.47  thf(dt_k8_relat_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (![X5 : $i, X6 : $i]:
% 0.21/0.47         ((v1_relat_1 @ (k8_relat_1 @ X5 @ X6)) | ~ (v1_relat_1 @ X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ X0)
% 0.21/0.47          | ((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ X0))
% 0.21/0.47              = (k8_relat_1 @ sk_A @ X0)))),
% 0.21/0.47      inference('clc', [status(thm)], ['8', '9'])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ sk_C))
% 0.21/0.47         != (k8_relat_1 @ sk_A @ sk_C))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      ((((k8_relat_1 @ sk_A @ sk_C) != (k8_relat_1 @ sk_A @ sk_C))
% 0.21/0.47        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.47  thf('13', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (((k8_relat_1 @ sk_A @ sk_C) != (k8_relat_1 @ sk_A @ sk_C))),
% 0.21/0.47      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.47  thf('15', plain, ($false), inference('simplify', [status(thm)], ['14'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

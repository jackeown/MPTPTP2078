%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.h8hCdIB7dX

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 (  44 expanded)
%              Number of leaves         :   17 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :  187 ( 271 expanded)
%              Number of equality atoms :   22 (  34 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t174_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( A != k1_xboole_0 )
          & ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
          & ( ( k10_relat_1 @ B @ A )
            = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ~ ( ( A != k1_xboole_0 )
            & ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
            & ( ( k10_relat_1 @ B @ A )
              = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t174_relat_1])).

thf('0',plain,
    ( ( k10_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t173_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k10_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k10_relat_1 @ X10 @ X11 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t173_relat_1])).

thf('2',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X5 @ X6 )
      | ( r1_xboole_0 @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_xboole_0 @ sk_A @ sk_A ),
    inference('sup-',[status(thm)],['5','8'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('11',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    k1_xboole_0 = sk_A ),
    inference(demod,[status(thm)],['11','16'])).

thf('18',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.h8hCdIB7dX
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:03:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 21 iterations in 0.013s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.47  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(t174_relat_1, conjecture,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ B ) =>
% 0.21/0.47       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.47            ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) & 
% 0.21/0.47            ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i]:
% 0.21/0.47        ( ( v1_relat_1 @ B ) =>
% 0.21/0.47          ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.47               ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) & 
% 0.21/0.47               ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t174_relat_1])).
% 0.21/0.47  thf('0', plain, (((k10_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t173_relat_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ B ) =>
% 0.21/0.47       ( ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.47         ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (![X10 : $i, X11 : $i]:
% 0.21/0.47         (((k10_relat_1 @ X10 @ X11) != (k1_xboole_0))
% 0.21/0.47          | (r1_xboole_0 @ (k2_relat_1 @ X10) @ X11)
% 0.21/0.47          | ~ (v1_relat_1 @ X10))),
% 0.21/0.47      inference('cnf', [status(esa)], [t173_relat_1])).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.47        | ~ (v1_relat_1 @ sk_B)
% 0.21/0.47        | (r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.47  thf('3', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.47        | (r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.47  thf('5', plain, ((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)),
% 0.21/0.47      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.47  thf('6', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t63_xboole_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.21/0.47       ( r1_xboole_0 @ A @ C ) ))).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.47         (~ (r1_tarski @ X4 @ X5)
% 0.21/0.47          | ~ (r1_xboole_0 @ X5 @ X6)
% 0.21/0.47          | (r1_xboole_0 @ X4 @ X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r1_xboole_0 @ sk_A @ X0)
% 0.21/0.47          | ~ (r1_xboole_0 @ (k2_relat_1 @ sk_B) @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.47  thf('9', plain, ((r1_xboole_0 @ sk_A @ sk_A)),
% 0.21/0.47      inference('sup-', [status(thm)], ['5', '8'])).
% 0.21/0.47  thf(t83_xboole_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (![X7 : $i, X8 : $i]:
% 0.21/0.47         (((k4_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_xboole_0 @ X7 @ X8))),
% 0.21/0.47      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.47  thf('11', plain, (((k4_xboole_0 @ sk_A @ sk_A) = (sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.47  thf(t3_boole, axiom,
% 0.21/0.47    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.47  thf('12', plain, (![X1 : $i]: ((k4_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.21/0.47      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.47  thf(t48_xboole_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (![X2 : $i, X3 : $i]:
% 0.21/0.47         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 0.21/0.47           = (k3_xboole_0 @ X2 @ X3))),
% 0.21/0.47      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.47      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.47  thf(t2_boole, axiom,
% 0.21/0.47    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.47  thf('16', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.47      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.47  thf('17', plain, (((k1_xboole_0) = (sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['11', '16'])).
% 0.21/0.47  thf('18', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('19', plain, ($false),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ETnqdCDGrm

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:32 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   32 (  34 expanded)
%              Number of leaves         :   14 (  15 expanded)
%              Depth                    :    9
%              Number of atoms          :  244 ( 268 expanded)
%              Number of equality atoms :   19 (  21 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X37 @ X38 ) @ X39 )
        = ( k7_relat_1 @ X37 @ ( k3_xboole_0 @ X38 @ X39 ) ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('2',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X40 @ X41 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X40 ) @ X41 ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('3',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X42 ) @ X43 )
      | ( ( k7_relat_1 @ X42 @ X43 )
        = X42 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v1_relat_1 @ X35 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
        = ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X0 @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t192_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( k7_relat_1 @ B @ A )
          = ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t192_relat_1])).

thf('10',plain,(
    ( k7_relat_1 @ sk_B @ sk_A )
 != ( k7_relat_1 @ sk_B @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('12',plain,(
    ( k7_relat_1 @ sk_B @ sk_A )
 != ( k7_relat_1 @ sk_B @ ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
     != ( k7_relat_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ( k7_relat_1 @ sk_B @ sk_A )
 != ( k7_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    $false ),
    inference(simplify,[status(thm)],['15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ETnqdCDGrm
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:16:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.43/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.62  % Solved by: fo/fo7.sh
% 0.43/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.62  % done 149 iterations in 0.167s
% 0.43/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.62  % SZS output start Refutation
% 0.43/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.43/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.43/0.62  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.43/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.43/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.43/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.43/0.62  thf(t100_relat_1, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i]:
% 0.43/0.62     ( ( v1_relat_1 @ C ) =>
% 0.43/0.62       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.43/0.62         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.43/0.62  thf('0', plain,
% 0.43/0.62      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.43/0.62         (((k7_relat_1 @ (k7_relat_1 @ X37 @ X38) @ X39)
% 0.43/0.62            = (k7_relat_1 @ X37 @ (k3_xboole_0 @ X38 @ X39)))
% 0.43/0.62          | ~ (v1_relat_1 @ X37))),
% 0.43/0.62      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.43/0.62  thf(t17_xboole_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.43/0.62  thf('1', plain,
% 0.43/0.62      (![X2 : $i, X3 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X3) @ X2)),
% 0.43/0.62      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.43/0.62  thf(t90_relat_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( v1_relat_1 @ B ) =>
% 0.43/0.62       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.43/0.62         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.43/0.62  thf('2', plain,
% 0.43/0.62      (![X40 : $i, X41 : $i]:
% 0.43/0.62         (((k1_relat_1 @ (k7_relat_1 @ X40 @ X41))
% 0.43/0.62            = (k3_xboole_0 @ (k1_relat_1 @ X40) @ X41))
% 0.43/0.62          | ~ (v1_relat_1 @ X40))),
% 0.43/0.62      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.43/0.62  thf(t97_relat_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( v1_relat_1 @ B ) =>
% 0.43/0.62       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.43/0.62         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.43/0.62  thf('3', plain,
% 0.43/0.62      (![X42 : $i, X43 : $i]:
% 0.43/0.62         (~ (r1_tarski @ (k1_relat_1 @ X42) @ X43)
% 0.43/0.62          | ((k7_relat_1 @ X42 @ X43) = (X42))
% 0.43/0.62          | ~ (v1_relat_1 @ X42))),
% 0.43/0.62      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.43/0.62  thf('4', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.62         (~ (r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) @ X2)
% 0.43/0.62          | ~ (v1_relat_1 @ X1)
% 0.43/0.62          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.43/0.62          | ((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 0.43/0.62              = (k7_relat_1 @ X1 @ X0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['2', '3'])).
% 0.43/0.62  thf('5', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (((k7_relat_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.43/0.62            = (k7_relat_1 @ X0 @ X1))
% 0.43/0.62          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.43/0.62          | ~ (v1_relat_1 @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['1', '4'])).
% 0.43/0.62  thf(dt_k7_relat_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.43/0.62  thf('6', plain,
% 0.43/0.62      (![X35 : $i, X36 : $i]:
% 0.43/0.62         (~ (v1_relat_1 @ X35) | (v1_relat_1 @ (k7_relat_1 @ X35 @ X36)))),
% 0.43/0.62      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.43/0.62  thf('7', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (~ (v1_relat_1 @ X0)
% 0.43/0.62          | ((k7_relat_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.43/0.62              = (k7_relat_1 @ X0 @ X1)))),
% 0.43/0.62      inference('clc', [status(thm)], ['5', '6'])).
% 0.43/0.62  thf('8', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (((k7_relat_1 @ X0 @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)))
% 0.43/0.62            = (k7_relat_1 @ X0 @ X1))
% 0.43/0.62          | ~ (v1_relat_1 @ X0)
% 0.43/0.62          | ~ (v1_relat_1 @ X0))),
% 0.43/0.62      inference('sup+', [status(thm)], ['0', '7'])).
% 0.43/0.62  thf('9', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (~ (v1_relat_1 @ X0)
% 0.43/0.62          | ((k7_relat_1 @ X0 @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)))
% 0.43/0.62              = (k7_relat_1 @ X0 @ X1)))),
% 0.43/0.62      inference('simplify', [status(thm)], ['8'])).
% 0.43/0.62  thf(t192_relat_1, conjecture,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( v1_relat_1 @ B ) =>
% 0.43/0.62       ( ( k7_relat_1 @ B @ A ) =
% 0.43/0.62         ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 0.43/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.62    (~( ![A:$i,B:$i]:
% 0.43/0.62        ( ( v1_relat_1 @ B ) =>
% 0.43/0.62          ( ( k7_relat_1 @ B @ A ) =
% 0.43/0.62            ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )),
% 0.43/0.62    inference('cnf.neg', [status(esa)], [t192_relat_1])).
% 0.43/0.62  thf('10', plain,
% 0.43/0.62      (((k7_relat_1 @ sk_B @ sk_A)
% 0.43/0.62         != (k7_relat_1 @ sk_B @ (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(commutativity_k3_xboole_0, axiom,
% 0.43/0.62    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.43/0.62  thf('11', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.43/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.43/0.62  thf('12', plain,
% 0.43/0.62      (((k7_relat_1 @ sk_B @ sk_A)
% 0.43/0.62         != (k7_relat_1 @ sk_B @ (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.43/0.62      inference('demod', [status(thm)], ['10', '11'])).
% 0.43/0.62  thf('13', plain,
% 0.43/0.62      ((((k7_relat_1 @ sk_B @ sk_A) != (k7_relat_1 @ sk_B @ sk_A))
% 0.43/0.62        | ~ (v1_relat_1 @ sk_B))),
% 0.43/0.62      inference('sup-', [status(thm)], ['9', '12'])).
% 0.43/0.62  thf('14', plain, ((v1_relat_1 @ sk_B)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('15', plain,
% 0.43/0.62      (((k7_relat_1 @ sk_B @ sk_A) != (k7_relat_1 @ sk_B @ sk_A))),
% 0.43/0.62      inference('demod', [status(thm)], ['13', '14'])).
% 0.43/0.62  thf('16', plain, ($false), inference('simplify', [status(thm)], ['15'])).
% 0.43/0.62  
% 0.43/0.62  % SZS output end Refutation
% 0.43/0.62  
% 0.47/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

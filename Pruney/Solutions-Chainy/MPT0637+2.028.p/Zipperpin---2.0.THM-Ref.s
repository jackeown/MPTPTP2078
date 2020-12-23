%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zDNoYHygSm

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:59 EST 2020

% Result     : Theorem 2.92s
% Output     : Refutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :   43 (  48 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :  277 ( 330 expanded)
%              Number of equality atoms :   24 (  27 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X76: $i,X77: $i] :
      ( ( ( k7_relat_1 @ X77 @ X76 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X76 ) @ X77 ) )
      | ~ ( v1_relat_1 @ X77 ) ) ),
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
    ! [X78: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X78 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('4',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X76: $i,X77: $i] :
      ( ( ( k7_relat_1 @ X77 @ X76 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X76 ) @ X77 ) )
      | ~ ( v1_relat_1 @ X77 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('6',plain,(
    ! [X28: $i,X29: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X28 @ X29 ) @ X28 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('7',plain,(
    ! [X73: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X73 ) )
      = X73 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('8',plain,(
    ! [X74: $i,X75: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X74 ) @ X75 )
      | ( ( k5_relat_1 @ X74 @ ( k6_relat_1 @ X75 ) )
        = X74 )
      | ~ ( v1_relat_1 @ X74 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X78: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X78 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

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
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','12'])).

thf('14',plain,(
    ! [X72: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X72 ) )
      = X72 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t192_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('15',plain,(
    ! [X70: $i,X71: $i] :
      ( ( ( k7_relat_1 @ X70 @ X71 )
        = ( k7_relat_1 @ X70 @ ( k3_xboole_0 @ ( k1_relat_1 @ X70 ) @ X71 ) ) )
      | ~ ( v1_relat_1 @ X70 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X78: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X78 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X78: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X78 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','18','19'])).

thf('21',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['4','20'])).

thf('22',plain,(
    $false ),
    inference(simplify,[status(thm)],['21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zDNoYHygSm
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:18:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.92/3.11  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.92/3.11  % Solved by: fo/fo7.sh
% 2.92/3.11  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.92/3.11  % done 2926 iterations in 2.656s
% 2.92/3.11  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.92/3.11  % SZS output start Refutation
% 2.92/3.11  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.92/3.11  thf(sk_B_type, type, sk_B: $i).
% 2.92/3.11  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.92/3.11  thf(sk_A_type, type, sk_A: $i).
% 2.92/3.11  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.92/3.11  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 2.92/3.11  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.92/3.11  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.92/3.11  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.92/3.11  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.92/3.11  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.92/3.11  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.92/3.11  thf(t94_relat_1, axiom,
% 2.92/3.11    (![A:$i,B:$i]:
% 2.92/3.11     ( ( v1_relat_1 @ B ) =>
% 2.92/3.11       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 2.92/3.11  thf('0', plain,
% 2.92/3.11      (![X76 : $i, X77 : $i]:
% 2.92/3.11         (((k7_relat_1 @ X77 @ X76) = (k5_relat_1 @ (k6_relat_1 @ X76) @ X77))
% 2.92/3.11          | ~ (v1_relat_1 @ X77))),
% 2.92/3.11      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.92/3.11  thf(t43_funct_1, conjecture,
% 2.92/3.11    (![A:$i,B:$i]:
% 2.92/3.11     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 2.92/3.11       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.92/3.11  thf(zf_stmt_0, negated_conjecture,
% 2.92/3.11    (~( ![A:$i,B:$i]:
% 2.92/3.11        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 2.92/3.11          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 2.92/3.11    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 2.92/3.11  thf('1', plain,
% 2.92/3.11      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 2.92/3.11         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 2.92/3.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.92/3.11  thf('2', plain,
% 2.92/3.11      ((((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 2.92/3.11          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 2.92/3.11        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 2.92/3.11      inference('sup-', [status(thm)], ['0', '1'])).
% 2.92/3.11  thf(fc24_relat_1, axiom,
% 2.92/3.11    (![A:$i]:
% 2.92/3.11     ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 2.92/3.11       ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 2.92/3.11       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 2.92/3.11  thf('3', plain, (![X78 : $i]: (v1_relat_1 @ (k6_relat_1 @ X78))),
% 2.92/3.11      inference('cnf', [status(esa)], [fc24_relat_1])).
% 2.92/3.11  thf('4', plain,
% 2.92/3.11      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 2.92/3.11         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 2.92/3.11      inference('demod', [status(thm)], ['2', '3'])).
% 2.92/3.11  thf('5', plain,
% 2.92/3.11      (![X76 : $i, X77 : $i]:
% 2.92/3.11         (((k7_relat_1 @ X77 @ X76) = (k5_relat_1 @ (k6_relat_1 @ X76) @ X77))
% 2.92/3.11          | ~ (v1_relat_1 @ X77))),
% 2.92/3.11      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.92/3.11  thf(t17_xboole_1, axiom,
% 2.92/3.11    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 2.92/3.11  thf('6', plain,
% 2.92/3.11      (![X28 : $i, X29 : $i]: (r1_tarski @ (k3_xboole_0 @ X28 @ X29) @ X28)),
% 2.92/3.11      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.92/3.11  thf(t71_relat_1, axiom,
% 2.92/3.11    (![A:$i]:
% 2.92/3.11     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 2.92/3.11       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 2.92/3.11  thf('7', plain, (![X73 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X73)) = (X73))),
% 2.92/3.11      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.92/3.11  thf(t79_relat_1, axiom,
% 2.92/3.11    (![A:$i,B:$i]:
% 2.92/3.11     ( ( v1_relat_1 @ B ) =>
% 2.92/3.11       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 2.92/3.11         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 2.92/3.11  thf('8', plain,
% 2.92/3.11      (![X74 : $i, X75 : $i]:
% 2.92/3.11         (~ (r1_tarski @ (k2_relat_1 @ X74) @ X75)
% 2.92/3.11          | ((k5_relat_1 @ X74 @ (k6_relat_1 @ X75)) = (X74))
% 2.92/3.11          | ~ (v1_relat_1 @ X74))),
% 2.92/3.11      inference('cnf', [status(esa)], [t79_relat_1])).
% 2.92/3.11  thf('9', plain,
% 2.92/3.11      (![X0 : $i, X1 : $i]:
% 2.92/3.11         (~ (r1_tarski @ X0 @ X1)
% 2.92/3.11          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.92/3.11          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 2.92/3.11              = (k6_relat_1 @ X0)))),
% 2.92/3.11      inference('sup-', [status(thm)], ['7', '8'])).
% 2.92/3.11  thf('10', plain, (![X78 : $i]: (v1_relat_1 @ (k6_relat_1 @ X78))),
% 2.92/3.11      inference('cnf', [status(esa)], [fc24_relat_1])).
% 2.92/3.11  thf('11', plain,
% 2.92/3.11      (![X0 : $i, X1 : $i]:
% 2.92/3.11         (~ (r1_tarski @ X0 @ X1)
% 2.92/3.11          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 2.92/3.11              = (k6_relat_1 @ X0)))),
% 2.92/3.11      inference('demod', [status(thm)], ['9', '10'])).
% 2.92/3.11  thf('12', plain,
% 2.92/3.11      (![X0 : $i, X1 : $i]:
% 2.92/3.11         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 2.92/3.11           (k6_relat_1 @ X0)) = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.92/3.11      inference('sup-', [status(thm)], ['6', '11'])).
% 2.92/3.11  thf('13', plain,
% 2.92/3.11      (![X0 : $i, X1 : $i]:
% 2.92/3.11         (((k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 2.92/3.11            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 2.92/3.11          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 2.92/3.11      inference('sup+', [status(thm)], ['5', '12'])).
% 2.92/3.11  thf('14', plain, (![X72 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X72)) = (X72))),
% 2.92/3.11      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.92/3.11  thf(t192_relat_1, axiom,
% 2.92/3.11    (![A:$i,B:$i]:
% 2.92/3.11     ( ( v1_relat_1 @ B ) =>
% 2.92/3.11       ( ( k7_relat_1 @ B @ A ) =
% 2.92/3.11         ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 2.92/3.11  thf('15', plain,
% 2.92/3.11      (![X70 : $i, X71 : $i]:
% 2.92/3.11         (((k7_relat_1 @ X70 @ X71)
% 2.92/3.11            = (k7_relat_1 @ X70 @ (k3_xboole_0 @ (k1_relat_1 @ X70) @ X71)))
% 2.92/3.11          | ~ (v1_relat_1 @ X70))),
% 2.92/3.11      inference('cnf', [status(esa)], [t192_relat_1])).
% 2.92/3.11  thf('16', plain,
% 2.92/3.11      (![X0 : $i, X1 : $i]:
% 2.92/3.11         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 2.92/3.11            = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))
% 2.92/3.11          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.92/3.11      inference('sup+', [status(thm)], ['14', '15'])).
% 2.92/3.11  thf('17', plain, (![X78 : $i]: (v1_relat_1 @ (k6_relat_1 @ X78))),
% 2.92/3.11      inference('cnf', [status(esa)], [fc24_relat_1])).
% 2.92/3.11  thf('18', plain,
% 2.92/3.11      (![X0 : $i, X1 : $i]:
% 2.92/3.11         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 2.92/3.11           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 2.92/3.11      inference('demod', [status(thm)], ['16', '17'])).
% 2.92/3.11  thf('19', plain, (![X78 : $i]: (v1_relat_1 @ (k6_relat_1 @ X78))),
% 2.92/3.11      inference('cnf', [status(esa)], [fc24_relat_1])).
% 2.92/3.11  thf('20', plain,
% 2.92/3.11      (![X0 : $i, X1 : $i]:
% 2.92/3.11         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 2.92/3.11           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.92/3.11      inference('demod', [status(thm)], ['13', '18', '19'])).
% 2.92/3.11  thf('21', plain,
% 2.92/3.11      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 2.92/3.11         != (k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 2.92/3.11      inference('demod', [status(thm)], ['4', '20'])).
% 2.92/3.11  thf('22', plain, ($false), inference('simplify', [status(thm)], ['21'])).
% 2.92/3.11  
% 2.92/3.11  % SZS output end Refutation
% 2.92/3.11  
% 2.92/3.12  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

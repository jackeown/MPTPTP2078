%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vGGgDJTl3R

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:10 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   42 (  47 expanded)
%              Number of leaves         :   18 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :  272 ( 310 expanded)
%              Number of equality atoms :   24 (  27 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    ! [X12: $i,X13: $i] :
      ( ( ( k7_relat_1 @ X13 @ X12 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X12 ) @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
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

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('4',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k7_relat_1 @ X13 @ X12 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X12 ) @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('7',plain,(
    ! [X9: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X10 ) @ X11 )
      | ( ( k5_relat_1 @ X10 @ ( k6_relat_1 @ X11 ) )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

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
    ! [X8: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X8 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t192_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('15',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k7_relat_1 @ X6 @ X7 )
        = ( k7_relat_1 @ X6 @ ( k3_xboole_0 @ ( k1_relat_1 @ X6 ) @ X7 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t192_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

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
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vGGgDJTl3R
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:33:10 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.44  % Solved by: fo/fo7.sh
% 0.19/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.44  % done 23 iterations in 0.016s
% 0.19/0.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.44  % SZS output start Refutation
% 0.19/0.44  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.19/0.44  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.44  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.44  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.44  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.44  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.44  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.44  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.44  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.19/0.44  thf(t94_relat_1, axiom,
% 0.19/0.44    (![A:$i,B:$i]:
% 0.19/0.44     ( ( v1_relat_1 @ B ) =>
% 0.19/0.44       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.19/0.44  thf('0', plain,
% 0.19/0.44      (![X12 : $i, X13 : $i]:
% 0.19/0.44         (((k7_relat_1 @ X13 @ X12) = (k5_relat_1 @ (k6_relat_1 @ X12) @ X13))
% 0.19/0.44          | ~ (v1_relat_1 @ X13))),
% 0.19/0.44      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.19/0.44  thf(t43_funct_1, conjecture,
% 0.19/0.44    (![A:$i,B:$i]:
% 0.19/0.44     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.19/0.44       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.19/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.44    (~( ![A:$i,B:$i]:
% 0.19/0.44        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.19/0.44          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.19/0.44    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 0.19/0.44  thf('1', plain,
% 0.19/0.44      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.19/0.44         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf('2', plain,
% 0.19/0.44      ((((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.19/0.44          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 0.19/0.44        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.19/0.44      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.44  thf(fc3_funct_1, axiom,
% 0.19/0.44    (![A:$i]:
% 0.19/0.44     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.19/0.44       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.19/0.44  thf('3', plain, (![X14 : $i]: (v1_relat_1 @ (k6_relat_1 @ X14))),
% 0.19/0.44      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.44  thf('4', plain,
% 0.19/0.44      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.19/0.44         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.19/0.44      inference('demod', [status(thm)], ['2', '3'])).
% 0.19/0.44  thf('5', plain,
% 0.19/0.44      (![X12 : $i, X13 : $i]:
% 0.19/0.44         (((k7_relat_1 @ X13 @ X12) = (k5_relat_1 @ (k6_relat_1 @ X12) @ X13))
% 0.19/0.44          | ~ (v1_relat_1 @ X13))),
% 0.19/0.44      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.19/0.44  thf(t17_xboole_1, axiom,
% 0.19/0.44    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.19/0.44  thf('6', plain,
% 0.19/0.44      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.19/0.44      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.19/0.44  thf(t71_relat_1, axiom,
% 0.19/0.44    (![A:$i]:
% 0.19/0.44     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.19/0.44       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.19/0.44  thf('7', plain, (![X9 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X9)) = (X9))),
% 0.19/0.44      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.44  thf(t79_relat_1, axiom,
% 0.19/0.44    (![A:$i,B:$i]:
% 0.19/0.44     ( ( v1_relat_1 @ B ) =>
% 0.19/0.44       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.19/0.44         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.19/0.44  thf('8', plain,
% 0.19/0.44      (![X10 : $i, X11 : $i]:
% 0.19/0.44         (~ (r1_tarski @ (k2_relat_1 @ X10) @ X11)
% 0.19/0.44          | ((k5_relat_1 @ X10 @ (k6_relat_1 @ X11)) = (X10))
% 0.19/0.44          | ~ (v1_relat_1 @ X10))),
% 0.19/0.44      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.19/0.44  thf('9', plain,
% 0.19/0.44      (![X0 : $i, X1 : $i]:
% 0.19/0.44         (~ (r1_tarski @ X0 @ X1)
% 0.19/0.44          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.19/0.44          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.19/0.44              = (k6_relat_1 @ X0)))),
% 0.19/0.44      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.44  thf('10', plain, (![X14 : $i]: (v1_relat_1 @ (k6_relat_1 @ X14))),
% 0.19/0.44      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.44  thf('11', plain,
% 0.19/0.44      (![X0 : $i, X1 : $i]:
% 0.19/0.44         (~ (r1_tarski @ X0 @ X1)
% 0.19/0.44          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.19/0.44              = (k6_relat_1 @ X0)))),
% 0.19/0.44      inference('demod', [status(thm)], ['9', '10'])).
% 0.19/0.44  thf('12', plain,
% 0.19/0.44      (![X0 : $i, X1 : $i]:
% 0.19/0.44         ((k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.19/0.44           (k6_relat_1 @ X0)) = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.19/0.44      inference('sup-', [status(thm)], ['6', '11'])).
% 0.19/0.44  thf('13', plain,
% 0.19/0.44      (![X0 : $i, X1 : $i]:
% 0.19/0.44         (((k7_relat_1 @ (k6_relat_1 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 0.19/0.44            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.19/0.44          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.19/0.44      inference('sup+', [status(thm)], ['5', '12'])).
% 0.19/0.44  thf('14', plain, (![X8 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X8)) = (X8))),
% 0.19/0.44      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.44  thf(t192_relat_1, axiom,
% 0.19/0.44    (![A:$i,B:$i]:
% 0.19/0.44     ( ( v1_relat_1 @ B ) =>
% 0.19/0.44       ( ( k7_relat_1 @ B @ A ) =
% 0.19/0.44         ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 0.19/0.44  thf('15', plain,
% 0.19/0.44      (![X6 : $i, X7 : $i]:
% 0.19/0.44         (((k7_relat_1 @ X6 @ X7)
% 0.19/0.44            = (k7_relat_1 @ X6 @ (k3_xboole_0 @ (k1_relat_1 @ X6) @ X7)))
% 0.19/0.44          | ~ (v1_relat_1 @ X6))),
% 0.19/0.44      inference('cnf', [status(esa)], [t192_relat_1])).
% 0.19/0.44  thf('16', plain,
% 0.19/0.44      (![X0 : $i, X1 : $i]:
% 0.19/0.44         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.19/0.44            = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))
% 0.19/0.44          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.19/0.44      inference('sup+', [status(thm)], ['14', '15'])).
% 0.19/0.44  thf('17', plain, (![X14 : $i]: (v1_relat_1 @ (k6_relat_1 @ X14))),
% 0.19/0.44      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.44  thf('18', plain,
% 0.19/0.44      (![X0 : $i, X1 : $i]:
% 0.19/0.44         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.19/0.44           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.19/0.44      inference('demod', [status(thm)], ['16', '17'])).
% 0.19/0.44  thf('19', plain, (![X14 : $i]: (v1_relat_1 @ (k6_relat_1 @ X14))),
% 0.19/0.44      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.44  thf('20', plain,
% 0.19/0.44      (![X0 : $i, X1 : $i]:
% 0.19/0.44         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.19/0.44           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.19/0.44      inference('demod', [status(thm)], ['13', '18', '19'])).
% 0.19/0.44  thf('21', plain,
% 0.19/0.44      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.19/0.44         != (k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 0.19/0.44      inference('demod', [status(thm)], ['4', '20'])).
% 0.19/0.44  thf('22', plain, ($false), inference('simplify', [status(thm)], ['21'])).
% 0.19/0.44  
% 0.19/0.44  % SZS output end Refutation
% 0.19/0.44  
% 0.19/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

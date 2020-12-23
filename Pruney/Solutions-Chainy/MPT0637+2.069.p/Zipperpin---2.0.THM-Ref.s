%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Gx1MfuZurp

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   55 (  65 expanded)
%              Number of leaves         :   21 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :  364 ( 440 expanded)
%              Number of equality atoms :   33 (  39 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k7_relat_1 @ X37 @ X36 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X36 ) @ X37 ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
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
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('4',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) @ X15 )
        = ( k7_relat_1 @ X13 @ ( k3_xboole_0 @ X14 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

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
    ! [X33: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X33 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('8',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X22 ) @ X23 )
      | ( ( k8_relat_1 @ X23 @ X22 )
        = X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('12',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k8_relat_1 @ X19 @ X18 )
        = ( k5_relat_1 @ X18 @ ( k6_relat_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('13',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k7_relat_1 @ X37 @ X36 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X36 ) @ X37 ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('16',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X1 ) @ X0 )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','19'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('21',plain,(
    ! [X35: $i] :
      ( ( ( k5_relat_1 @ X35 @ ( k6_relat_1 @ ( k2_relat_1 @ X35 ) ) )
        = X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('22',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k7_relat_1 @ X37 @ X36 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X36 ) @ X37 ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X33: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X33 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('25',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('26',plain,(
    ! [X33: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X33 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('27',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24','25','26','27'])).

thf('29',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','28','29'])).

thf('31',plain,(
    ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['4','30'])).

thf('32',plain,(
    $false ),
    inference(simplify,[status(thm)],['31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Gx1MfuZurp
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:23:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 74 iterations in 0.051s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.50  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.50  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.50  thf(t94_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ B ) =>
% 0.20/0.50       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      (![X36 : $i, X37 : $i]:
% 0.20/0.50         (((k7_relat_1 @ X37 @ X36) = (k5_relat_1 @ (k6_relat_1 @ X36) @ X37))
% 0.20/0.50          | ~ (v1_relat_1 @ X37))),
% 0.20/0.50      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.20/0.50  thf(t43_funct_1, conjecture,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.20/0.50       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i]:
% 0.20/0.50        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.20/0.50          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.20/0.50         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      ((((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.20/0.50          != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))
% 0.20/0.50        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.50  thf(fc3_funct_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.20/0.50       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.20/0.50  thf('3', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.20/0.50         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.50  thf(t100_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ C ) =>
% 0.20/0.50       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.20/0.50         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.50         (((k7_relat_1 @ (k7_relat_1 @ X13 @ X14) @ X15)
% 0.20/0.50            = (k7_relat_1 @ X13 @ (k3_xboole_0 @ X14 @ X15)))
% 0.20/0.50          | ~ (v1_relat_1 @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.20/0.50  thf(t17_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.20/0.50      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.20/0.50  thf(t71_relat_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.20/0.50       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.50  thf('7', plain, (![X33 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X33)) = (X33))),
% 0.20/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.50  thf(t125_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ B ) =>
% 0.20/0.50       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.20/0.50         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X22 : $i, X23 : $i]:
% 0.20/0.50         (~ (r1_tarski @ (k2_relat_1 @ X22) @ X23)
% 0.20/0.50          | ((k8_relat_1 @ X23 @ X22) = (X22))
% 0.20/0.50          | ~ (v1_relat_1 @ X22))),
% 0.20/0.50      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (r1_tarski @ X0 @ X1)
% 0.20/0.50          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.20/0.50          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.50  thf('10', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (r1_tarski @ X0 @ X1)
% 0.20/0.50          | ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.50  thf(t123_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ B ) =>
% 0.20/0.50       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X18 : $i, X19 : $i]:
% 0.20/0.50         (((k8_relat_1 @ X19 @ X18) = (k5_relat_1 @ X18 @ (k6_relat_1 @ X19)))
% 0.20/0.50          | ~ (v1_relat_1 @ X18))),
% 0.20/0.50      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X36 : $i, X37 : $i]:
% 0.20/0.50         (((k7_relat_1 @ X37 @ X36) = (k5_relat_1 @ (k6_relat_1 @ X36) @ X37))
% 0.20/0.50          | ~ (v1_relat_1 @ X37))),
% 0.20/0.50      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.20/0.50            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.20/0.50          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.20/0.50          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['12', '13'])).
% 0.20/0.50  thf('15', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.50  thf('16', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.20/0.50           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (r1_tarski @ X0 @ X1)
% 0.20/0.50          | ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0) = (k6_relat_1 @ X0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['11', '17'])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 0.20/0.50           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['6', '18'])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((k7_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X1) @ X0)
% 0.20/0.50            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.20/0.50          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['5', '19'])).
% 0.20/0.50  thf(t80_relat_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ A ) =>
% 0.20/0.50       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (![X35 : $i]:
% 0.20/0.50         (((k5_relat_1 @ X35 @ (k6_relat_1 @ (k2_relat_1 @ X35))) = (X35))
% 0.20/0.50          | ~ (v1_relat_1 @ X35))),
% 0.20/0.50      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (![X36 : $i, X37 : $i]:
% 0.20/0.50         (((k7_relat_1 @ X37 @ X36) = (k5_relat_1 @ (k6_relat_1 @ X36) @ X37))
% 0.20/0.50          | ~ (v1_relat_1 @ X37))),
% 0.20/0.50      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k7_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0))) @ X0)
% 0.20/0.50            = (k6_relat_1 @ X0))
% 0.20/0.50          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.20/0.50          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0)))))),
% 0.20/0.50      inference('sup+', [status(thm)], ['21', '22'])).
% 0.20/0.50  thf('24', plain, (![X33 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X33)) = (X33))),
% 0.20/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.50  thf('25', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.50  thf('26', plain, (![X33 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X33)) = (X33))),
% 0.20/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.50  thf('27', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['23', '24', '25', '26', '27'])).
% 0.20/0.50  thf('29', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.20/0.50           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['20', '28', '29'])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.20/0.50         != (k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['4', '30'])).
% 0.20/0.50  thf('32', plain, ($false), inference('simplify', [status(thm)], ['31'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

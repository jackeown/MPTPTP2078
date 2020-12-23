%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xh7iqmuJBv

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   37 (  44 expanded)
%              Number of leaves         :   14 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :  321 ( 406 expanded)
%              Number of equality atoms :   26 (  33 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('0',plain,(
    ! [X40: $i] :
      ( ( ( k7_relat_1 @ X40 @ ( k1_relat_1 @ X40 ) )
        = X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X33 @ X34 ) @ X35 )
        = ( k7_relat_1 @ X33 @ ( k3_xboole_0 @ X34 @ X35 ) ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X0 @ X1 )
        = ( k7_relat_1 @ X0 @ ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ X1 )
        = ( k7_relat_1 @ X0 @ ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t212_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('4',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k1_relat_1 @ ( k6_subset_1 @ X36 @ ( k7_relat_1 @ X36 @ X37 ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ X36 ) @ X37 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t212_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k6_subset_1 @ X29 @ X30 )
      = ( k4_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('6',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k6_subset_1 @ X29 @ X30 )
      = ( k4_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('7',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k1_relat_1 @ ( k4_xboole_0 @ X36 @ ( k7_relat_1 @ X36 @ X37 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X36 ) @ X37 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k4_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k4_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('10',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X38 @ X39 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X38 ) @ X39 ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t213_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k6_subset_1 @ ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) )
        = ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( k6_subset_1 @ ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) )
          = ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t213_relat_1])).

thf('11',plain,(
    ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
 != ( k1_relat_1 @ ( k6_subset_1 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k6_subset_1 @ X29 @ X30 )
      = ( k4_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('13',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k6_subset_1 @ X29 @ X30 )
      = ( k4_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('14',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
     != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
     != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    $false ),
    inference(simplify,[status(thm)],['20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xh7iqmuJBv
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:15:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 45 iterations in 0.048s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.20/0.54  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.54  thf(t98_relat_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( v1_relat_1 @ A ) =>
% 0.20/0.54       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.54  thf('0', plain,
% 0.20/0.54      (![X40 : $i]:
% 0.20/0.54         (((k7_relat_1 @ X40 @ (k1_relat_1 @ X40)) = (X40))
% 0.20/0.54          | ~ (v1_relat_1 @ X40))),
% 0.20/0.54      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.20/0.54  thf(t100_relat_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( v1_relat_1 @ C ) =>
% 0.20/0.54       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.20/0.54         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.20/0.54  thf('1', plain,
% 0.20/0.54      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.20/0.54         (((k7_relat_1 @ (k7_relat_1 @ X33 @ X34) @ X35)
% 0.20/0.54            = (k7_relat_1 @ X33 @ (k3_xboole_0 @ X34 @ X35)))
% 0.20/0.54          | ~ (v1_relat_1 @ X33))),
% 0.20/0.54      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.20/0.54  thf('2', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (((k7_relat_1 @ X0 @ X1)
% 0.20/0.54            = (k7_relat_1 @ X0 @ (k3_xboole_0 @ (k1_relat_1 @ X0) @ X1)))
% 0.20/0.54          | ~ (v1_relat_1 @ X0)
% 0.20/0.54          | ~ (v1_relat_1 @ X0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['0', '1'])).
% 0.20/0.54  thf('3', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (v1_relat_1 @ X0)
% 0.20/0.54          | ((k7_relat_1 @ X0 @ X1)
% 0.20/0.54              = (k7_relat_1 @ X0 @ (k3_xboole_0 @ (k1_relat_1 @ X0) @ X1))))),
% 0.20/0.54      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.54  thf(t212_relat_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( v1_relat_1 @ B ) =>
% 0.20/0.54       ( ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.20/0.54         ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.54  thf('4', plain,
% 0.20/0.54      (![X36 : $i, X37 : $i]:
% 0.20/0.54         (((k1_relat_1 @ (k6_subset_1 @ X36 @ (k7_relat_1 @ X36 @ X37)))
% 0.20/0.54            = (k6_subset_1 @ (k1_relat_1 @ X36) @ X37))
% 0.20/0.54          | ~ (v1_relat_1 @ X36))),
% 0.20/0.54      inference('cnf', [status(esa)], [t212_relat_1])).
% 0.20/0.54  thf(redefinition_k6_subset_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.20/0.54  thf('5', plain,
% 0.20/0.54      (![X29 : $i, X30 : $i]:
% 0.20/0.54         ((k6_subset_1 @ X29 @ X30) = (k4_xboole_0 @ X29 @ X30))),
% 0.20/0.54      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.54  thf('6', plain,
% 0.20/0.54      (![X29 : $i, X30 : $i]:
% 0.20/0.54         ((k6_subset_1 @ X29 @ X30) = (k4_xboole_0 @ X29 @ X30))),
% 0.20/0.54      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.54  thf('7', plain,
% 0.20/0.54      (![X36 : $i, X37 : $i]:
% 0.20/0.54         (((k1_relat_1 @ (k4_xboole_0 @ X36 @ (k7_relat_1 @ X36 @ X37)))
% 0.20/0.54            = (k4_xboole_0 @ (k1_relat_1 @ X36) @ X37))
% 0.20/0.54          | ~ (v1_relat_1 @ X36))),
% 0.20/0.54      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.20/0.54  thf('8', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (((k1_relat_1 @ (k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 0.20/0.54            = (k4_xboole_0 @ (k1_relat_1 @ X1) @ 
% 0.20/0.54               (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))
% 0.20/0.54          | ~ (v1_relat_1 @ X1)
% 0.20/0.54          | ~ (v1_relat_1 @ X1))),
% 0.20/0.54      inference('sup+', [status(thm)], ['3', '7'])).
% 0.20/0.54  thf('9', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (v1_relat_1 @ X1)
% 0.20/0.54          | ((k1_relat_1 @ (k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 0.20/0.54              = (k4_xboole_0 @ (k1_relat_1 @ X1) @ 
% 0.20/0.54                 (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))))),
% 0.20/0.54      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.54  thf(t90_relat_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( v1_relat_1 @ B ) =>
% 0.20/0.54       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.20/0.54         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.54  thf('10', plain,
% 0.20/0.54      (![X38 : $i, X39 : $i]:
% 0.20/0.54         (((k1_relat_1 @ (k7_relat_1 @ X38 @ X39))
% 0.20/0.54            = (k3_xboole_0 @ (k1_relat_1 @ X38) @ X39))
% 0.20/0.54          | ~ (v1_relat_1 @ X38))),
% 0.20/0.54      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.20/0.54  thf(t213_relat_1, conjecture,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( v1_relat_1 @ B ) =>
% 0.20/0.54       ( ( k6_subset_1 @
% 0.20/0.54           ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.20/0.54         ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i,B:$i]:
% 0.20/0.54        ( ( v1_relat_1 @ B ) =>
% 0.20/0.54          ( ( k6_subset_1 @
% 0.20/0.54              ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.20/0.54            ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t213_relat_1])).
% 0.20/0.54  thf('11', plain,
% 0.20/0.54      (((k6_subset_1 @ (k1_relat_1 @ sk_B) @ 
% 0.20/0.54         (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.20/0.54         != (k1_relat_1 @ (k6_subset_1 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      (![X29 : $i, X30 : $i]:
% 0.20/0.54         ((k6_subset_1 @ X29 @ X30) = (k4_xboole_0 @ X29 @ X30))),
% 0.20/0.54      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.54  thf('13', plain,
% 0.20/0.54      (![X29 : $i, X30 : $i]:
% 0.20/0.54         ((k6_subset_1 @ X29 @ X30) = (k4_xboole_0 @ X29 @ X30))),
% 0.20/0.54      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.54  thf('14', plain,
% 0.20/0.54      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.20/0.54         (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.20/0.54         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.20/0.54      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.20/0.54  thf('15', plain,
% 0.20/0.54      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.20/0.54          (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.20/0.54          != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.20/0.54        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['10', '14'])).
% 0.20/0.54  thf('16', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('17', plain,
% 0.20/0.54      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.20/0.54         (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.20/0.54         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.20/0.54      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.54  thf('18', plain,
% 0.20/0.54      ((((k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.20/0.54          != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.20/0.54        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['9', '17'])).
% 0.20/0.54  thf('19', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('20', plain,
% 0.20/0.54      (((k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.20/0.54         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.20/0.54      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.54  thf('21', plain, ($false), inference('simplify', [status(thm)], ['20'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.37/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zz5fytlwSM

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:01 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   48 (  58 expanded)
%              Number of leaves         :   18 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :  350 ( 458 expanded)
%              Number of equality atoms :   33 (  43 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t212_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('0',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k1_relat_1 @ ( k6_subset_1 @ X13 @ ( k7_relat_1 @ X13 @ X14 ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ X13 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t212_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k1_relat_1 @ ( k4_xboole_0 @ X13 @ ( k7_relat_1 @ X13 @ X14 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X13 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('4',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X15 @ X16 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X15 ) @ X16 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
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

thf('5',plain,(
    ( k6_subset_1 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
 != ( k1_relat_1 @ ( k6_subset_1 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('7',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('8',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
     != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('11',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('14',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('15',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','18'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
 != ( k1_relat_1 @ ( k4_xboole_0 @ sk_B @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['12','23'])).

thf('25',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
     != ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['3','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
 != ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    $false ),
    inference(simplify,[status(thm)],['27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zz5fytlwSM
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:48:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.54  % Solved by: fo/fo7.sh
% 0.19/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.54  % done 126 iterations in 0.093s
% 0.19/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.54  % SZS output start Refutation
% 0.19/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.54  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.54  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.19/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.54  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.19/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.54  thf(t212_relat_1, axiom,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( v1_relat_1 @ B ) =>
% 0.19/0.54       ( ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.19/0.54         ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.19/0.54  thf('0', plain,
% 0.19/0.54      (![X13 : $i, X14 : $i]:
% 0.19/0.54         (((k1_relat_1 @ (k6_subset_1 @ X13 @ (k7_relat_1 @ X13 @ X14)))
% 0.19/0.54            = (k6_subset_1 @ (k1_relat_1 @ X13) @ X14))
% 0.19/0.54          | ~ (v1_relat_1 @ X13))),
% 0.19/0.54      inference('cnf', [status(esa)], [t212_relat_1])).
% 0.19/0.54  thf(redefinition_k6_subset_1, axiom,
% 0.19/0.54    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.19/0.54  thf('1', plain,
% 0.19/0.54      (![X11 : $i, X12 : $i]:
% 0.19/0.54         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.19/0.54      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.19/0.54  thf('2', plain,
% 0.19/0.54      (![X11 : $i, X12 : $i]:
% 0.19/0.54         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.19/0.54      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.19/0.54  thf('3', plain,
% 0.19/0.54      (![X13 : $i, X14 : $i]:
% 0.19/0.54         (((k1_relat_1 @ (k4_xboole_0 @ X13 @ (k7_relat_1 @ X13 @ X14)))
% 0.19/0.54            = (k4_xboole_0 @ (k1_relat_1 @ X13) @ X14))
% 0.19/0.54          | ~ (v1_relat_1 @ X13))),
% 0.19/0.54      inference('demod', [status(thm)], ['0', '1', '2'])).
% 0.19/0.54  thf(t90_relat_1, axiom,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( v1_relat_1 @ B ) =>
% 0.19/0.54       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.19/0.54         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.19/0.54  thf('4', plain,
% 0.19/0.54      (![X15 : $i, X16 : $i]:
% 0.19/0.54         (((k1_relat_1 @ (k7_relat_1 @ X15 @ X16))
% 0.19/0.54            = (k3_xboole_0 @ (k1_relat_1 @ X15) @ X16))
% 0.19/0.54          | ~ (v1_relat_1 @ X15))),
% 0.19/0.54      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.19/0.54  thf(t213_relat_1, conjecture,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( v1_relat_1 @ B ) =>
% 0.19/0.54       ( ( k6_subset_1 @
% 0.19/0.54           ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.19/0.54         ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ))).
% 0.19/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.54    (~( ![A:$i,B:$i]:
% 0.19/0.54        ( ( v1_relat_1 @ B ) =>
% 0.19/0.54          ( ( k6_subset_1 @
% 0.19/0.54              ( k1_relat_1 @ B ) @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.19/0.54            ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) ) ) )),
% 0.19/0.54    inference('cnf.neg', [status(esa)], [t213_relat_1])).
% 0.19/0.54  thf('5', plain,
% 0.19/0.54      (((k6_subset_1 @ (k1_relat_1 @ sk_B) @ 
% 0.19/0.54         (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.19/0.54         != (k1_relat_1 @ (k6_subset_1 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('6', plain,
% 0.19/0.54      (![X11 : $i, X12 : $i]:
% 0.19/0.54         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.19/0.54      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.19/0.54  thf('7', plain,
% 0.19/0.54      (![X11 : $i, X12 : $i]:
% 0.19/0.54         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.19/0.54      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.19/0.54  thf('8', plain,
% 0.19/0.54      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.19/0.54         (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.19/0.54         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.19/0.54      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.19/0.54  thf('9', plain,
% 0.19/0.54      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.19/0.54          (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.19/0.54          != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.19/0.54        | ~ (v1_relat_1 @ sk_B))),
% 0.19/0.54      inference('sup-', [status(thm)], ['4', '8'])).
% 0.19/0.54  thf(commutativity_k3_xboole_0, axiom,
% 0.19/0.54    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.19/0.54  thf('10', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.54  thf('11', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('12', plain,
% 0.19/0.54      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.19/0.54         (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.19/0.54         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.19/0.54      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.19/0.54  thf('13', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.54  thf(t17_xboole_1, axiom,
% 0.19/0.54    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.19/0.54  thf('14', plain,
% 0.19/0.54      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 0.19/0.54      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.19/0.54  thf(t28_xboole_1, axiom,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.54  thf('15', plain,
% 0.19/0.54      (![X9 : $i, X10 : $i]:
% 0.19/0.54         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.19/0.54      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.54  thf('16', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i]:
% 0.19/0.54         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 0.19/0.54           = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.54      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.54  thf('17', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.54  thf('18', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i]:
% 0.19/0.54         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.19/0.54           = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.54      inference('demod', [status(thm)], ['16', '17'])).
% 0.19/0.54  thf('19', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i]:
% 0.19/0.54         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.19/0.54           = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.54      inference('sup+', [status(thm)], ['13', '18'])).
% 0.19/0.54  thf(t100_xboole_1, axiom,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.19/0.54  thf('20', plain,
% 0.19/0.54      (![X2 : $i, X3 : $i]:
% 0.19/0.54         ((k4_xboole_0 @ X2 @ X3)
% 0.19/0.54           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.19/0.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.19/0.54  thf('21', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i]:
% 0.19/0.54         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 0.19/0.54           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.19/0.54      inference('sup+', [status(thm)], ['19', '20'])).
% 0.19/0.54  thf('22', plain,
% 0.19/0.54      (![X2 : $i, X3 : $i]:
% 0.19/0.54         ((k4_xboole_0 @ X2 @ X3)
% 0.19/0.54           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.19/0.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.19/0.54  thf('23', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i]:
% 0.19/0.54         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 0.19/0.54           = (k4_xboole_0 @ X1 @ X0))),
% 0.19/0.54      inference('demod', [status(thm)], ['21', '22'])).
% 0.19/0.54  thf('24', plain,
% 0.19/0.54      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.19/0.54         != (k1_relat_1 @ (k4_xboole_0 @ sk_B @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.19/0.54      inference('demod', [status(thm)], ['12', '23'])).
% 0.19/0.54  thf('25', plain,
% 0.19/0.54      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.19/0.54          != (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.19/0.54        | ~ (v1_relat_1 @ sk_B))),
% 0.19/0.54      inference('sup-', [status(thm)], ['3', '24'])).
% 0.19/0.54  thf('26', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('27', plain,
% 0.19/0.54      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.19/0.54         != (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.19/0.54      inference('demod', [status(thm)], ['25', '26'])).
% 0.19/0.54  thf('28', plain, ($false), inference('simplify', [status(thm)], ['27'])).
% 0.19/0.54  
% 0.19/0.54  % SZS output end Refutation
% 0.19/0.54  
% 0.37/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

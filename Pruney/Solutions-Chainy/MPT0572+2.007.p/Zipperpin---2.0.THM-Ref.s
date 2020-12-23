%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ibQQReSRhq

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:15 EST 2020

% Result     : Theorem 7.39s
% Output     : Refutation 7.39s
% Verified   : 
% Statistics : Number of formulae       :   36 (  46 expanded)
%              Number of leaves         :   15 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :  267 ( 363 expanded)
%              Number of equality atoms :   10 (  15 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('0',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t175_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k10_relat_1 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ X11 @ X12 ) @ ( k10_relat_1 @ X11 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t175_relat_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ X0 ) @ ( k10_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k10_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['2','7'])).

thf('9',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ X0 ) @ ( k10_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k10_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X4 @ X6 )
      | ( r1_tarski @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ ( k3_xboole_0 @ ( k10_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ~ ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k10_relat_1 @ X1 @ X2 ) @ ( k10_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k10_relat_1 @ X1 @ X2 ) @ ( k10_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t176_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( r1_tarski @ ( k10_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( r1_tarski @ ( k10_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t176_relat_1])).

thf('16',plain,(
    ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['17','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ibQQReSRhq
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:42:46 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 7.39/7.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 7.39/7.58  % Solved by: fo/fo7.sh
% 7.39/7.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.39/7.58  % done 3720 iterations in 7.100s
% 7.39/7.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 7.39/7.58  % SZS output start Refutation
% 7.39/7.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 7.39/7.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.39/7.58  thf(sk_B_type, type, sk_B: $i).
% 7.39/7.58  thf(sk_A_type, type, sk_A: $i).
% 7.39/7.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 7.39/7.58  thf(sk_C_type, type, sk_C: $i).
% 7.39/7.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 7.39/7.58  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 7.39/7.58  thf(commutativity_k3_xboole_0, axiom,
% 7.39/7.58    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 7.39/7.58  thf('0', plain,
% 7.39/7.58      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 7.39/7.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 7.39/7.58  thf(t22_xboole_1, axiom,
% 7.39/7.58    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 7.39/7.58  thf('1', plain,
% 7.39/7.58      (![X7 : $i, X8 : $i]:
% 7.39/7.58         ((k2_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)) = (X7))),
% 7.39/7.58      inference('cnf', [status(esa)], [t22_xboole_1])).
% 7.39/7.58  thf('2', plain,
% 7.39/7.58      (![X0 : $i, X1 : $i]:
% 7.39/7.58         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 7.39/7.58      inference('sup+', [status(thm)], ['0', '1'])).
% 7.39/7.58  thf(t175_relat_1, axiom,
% 7.39/7.58    (![A:$i,B:$i,C:$i]:
% 7.39/7.58     ( ( v1_relat_1 @ C ) =>
% 7.39/7.58       ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 7.39/7.58         ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 7.39/7.58  thf('3', plain,
% 7.39/7.58      (![X11 : $i, X12 : $i, X13 : $i]:
% 7.39/7.58         (((k10_relat_1 @ X11 @ (k2_xboole_0 @ X12 @ X13))
% 7.39/7.58            = (k2_xboole_0 @ (k10_relat_1 @ X11 @ X12) @ 
% 7.39/7.58               (k10_relat_1 @ X11 @ X13)))
% 7.39/7.58          | ~ (v1_relat_1 @ X11))),
% 7.39/7.58      inference('cnf', [status(esa)], [t175_relat_1])).
% 7.39/7.58  thf(commutativity_k2_xboole_0, axiom,
% 7.39/7.58    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 7.39/7.58  thf('4', plain,
% 7.39/7.58      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 7.39/7.58      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 7.39/7.58  thf(t7_xboole_1, axiom,
% 7.39/7.58    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 7.39/7.58  thf('5', plain,
% 7.39/7.58      (![X9 : $i, X10 : $i]: (r1_tarski @ X9 @ (k2_xboole_0 @ X9 @ X10))),
% 7.39/7.58      inference('cnf', [status(esa)], [t7_xboole_1])).
% 7.39/7.58  thf('6', plain,
% 7.39/7.58      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 7.39/7.58      inference('sup+', [status(thm)], ['4', '5'])).
% 7.39/7.58  thf('7', plain,
% 7.39/7.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.39/7.58         ((r1_tarski @ (k10_relat_1 @ X2 @ X0) @ 
% 7.39/7.58           (k10_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 7.39/7.58          | ~ (v1_relat_1 @ X2))),
% 7.39/7.58      inference('sup+', [status(thm)], ['3', '6'])).
% 7.39/7.58  thf('8', plain,
% 7.39/7.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.39/7.58         ((r1_tarski @ (k10_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 7.39/7.58           (k10_relat_1 @ X2 @ X0))
% 7.39/7.58          | ~ (v1_relat_1 @ X2))),
% 7.39/7.58      inference('sup+', [status(thm)], ['2', '7'])).
% 7.39/7.58  thf('9', plain,
% 7.39/7.58      (![X7 : $i, X8 : $i]:
% 7.39/7.58         ((k2_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)) = (X7))),
% 7.39/7.58      inference('cnf', [status(esa)], [t22_xboole_1])).
% 7.39/7.58  thf('10', plain,
% 7.39/7.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.39/7.58         ((r1_tarski @ (k10_relat_1 @ X2 @ X0) @ 
% 7.39/7.58           (k10_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 7.39/7.58          | ~ (v1_relat_1 @ X2))),
% 7.39/7.58      inference('sup+', [status(thm)], ['3', '6'])).
% 7.39/7.58  thf('11', plain,
% 7.39/7.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.39/7.58         ((r1_tarski @ (k10_relat_1 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 7.39/7.58           (k10_relat_1 @ X2 @ X0))
% 7.39/7.58          | ~ (v1_relat_1 @ X2))),
% 7.39/7.58      inference('sup+', [status(thm)], ['9', '10'])).
% 7.39/7.58  thf(t19_xboole_1, axiom,
% 7.39/7.58    (![A:$i,B:$i,C:$i]:
% 7.39/7.58     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 7.39/7.58       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 7.39/7.58  thf('12', plain,
% 7.39/7.58      (![X4 : $i, X5 : $i, X6 : $i]:
% 7.39/7.58         (~ (r1_tarski @ X4 @ X5)
% 7.39/7.58          | ~ (r1_tarski @ X4 @ X6)
% 7.39/7.58          | (r1_tarski @ X4 @ (k3_xboole_0 @ X5 @ X6)))),
% 7.39/7.58      inference('cnf', [status(esa)], [t19_xboole_1])).
% 7.39/7.58  thf('13', plain,
% 7.39/7.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.39/7.58         (~ (v1_relat_1 @ X1)
% 7.39/7.59          | (r1_tarski @ (k10_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ 
% 7.39/7.59             (k3_xboole_0 @ (k10_relat_1 @ X1 @ X0) @ X3))
% 7.39/7.59          | ~ (r1_tarski @ (k10_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ X3))),
% 7.39/7.59      inference('sup-', [status(thm)], ['11', '12'])).
% 7.39/7.59  thf('14', plain,
% 7.39/7.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.39/7.59         (~ (v1_relat_1 @ X1)
% 7.39/7.59          | (r1_tarski @ (k10_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 7.39/7.59             (k3_xboole_0 @ (k10_relat_1 @ X1 @ X2) @ (k10_relat_1 @ X1 @ X0)))
% 7.39/7.59          | ~ (v1_relat_1 @ X1))),
% 7.39/7.59      inference('sup-', [status(thm)], ['8', '13'])).
% 7.39/7.59  thf('15', plain,
% 7.39/7.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.39/7.59         ((r1_tarski @ (k10_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 7.39/7.59           (k3_xboole_0 @ (k10_relat_1 @ X1 @ X2) @ (k10_relat_1 @ X1 @ X0)))
% 7.39/7.59          | ~ (v1_relat_1 @ X1))),
% 7.39/7.59      inference('simplify', [status(thm)], ['14'])).
% 7.39/7.59  thf(t176_relat_1, conjecture,
% 7.39/7.59    (![A:$i,B:$i,C:$i]:
% 7.39/7.59     ( ( v1_relat_1 @ C ) =>
% 7.39/7.59       ( r1_tarski @
% 7.39/7.59         ( k10_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 7.39/7.59         ( k3_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 7.39/7.59  thf(zf_stmt_0, negated_conjecture,
% 7.39/7.59    (~( ![A:$i,B:$i,C:$i]:
% 7.39/7.59        ( ( v1_relat_1 @ C ) =>
% 7.39/7.59          ( r1_tarski @
% 7.39/7.59            ( k10_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 7.39/7.59            ( k3_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )),
% 7.39/7.59    inference('cnf.neg', [status(esa)], [t176_relat_1])).
% 7.39/7.59  thf('16', plain,
% 7.39/7.59      (~ (r1_tarski @ (k10_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 7.39/7.59          (k3_xboole_0 @ (k10_relat_1 @ sk_C @ sk_A) @ 
% 7.39/7.59           (k10_relat_1 @ sk_C @ sk_B)))),
% 7.39/7.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.39/7.59  thf('17', plain, (~ (v1_relat_1 @ sk_C)),
% 7.39/7.59      inference('sup-', [status(thm)], ['15', '16'])).
% 7.39/7.59  thf('18', plain, ((v1_relat_1 @ sk_C)),
% 7.39/7.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.39/7.59  thf('19', plain, ($false), inference('demod', [status(thm)], ['17', '18'])).
% 7.39/7.59  
% 7.39/7.59  % SZS output end Refutation
% 7.39/7.59  
% 7.39/7.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

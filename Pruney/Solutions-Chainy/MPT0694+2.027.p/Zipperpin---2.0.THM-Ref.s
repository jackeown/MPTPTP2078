%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Z0hEvlcIxO

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   43 (  52 expanded)
%              Number of leaves         :   16 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :  373 ( 486 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t154_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X10 @ X11 ) @ ( k9_relat_1 @ X10 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t154_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t148_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k9_relat_1 @ X14 @ ( k10_relat_1 @ X14 @ X13 ) )
        = ( k3_xboole_0 @ X13 @ ( k9_relat_1 @ X14 @ ( k1_relat_1 @ X14 ) ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf('7',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X10 @ X11 ) @ ( k9_relat_1 @ X10 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t154_relat_1])).

thf('12',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k9_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('14',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X7 )
      | ( r1_tarski @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) ) ) @ ( k3_xboole_0 @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','17'])).

thf(t149_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t149_funct_1])).

thf('19',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C @ sk_B ) ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C @ sk_B ) ) ) @ ( k3_xboole_0 @ sk_B @ ( k9_relat_1 @ sk_C @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    $false ),
    inference(demod,[status(thm)],['22','23','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Z0hEvlcIxO
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:08:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.56  % Solved by: fo/fo7.sh
% 0.20/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.56  % done 115 iterations in 0.107s
% 0.20/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.56  % SZS output start Refutation
% 0.20/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.56  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.56  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.56  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.56    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.56  thf('0', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.56  thf(t154_relat_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( v1_relat_1 @ C ) =>
% 0.20/0.56       ( r1_tarski @
% 0.20/0.56         ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.20/0.56         ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.20/0.56  thf('1', plain,
% 0.20/0.56      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.56         ((r1_tarski @ (k9_relat_1 @ X10 @ (k3_xboole_0 @ X11 @ X12)) @ 
% 0.20/0.56           (k3_xboole_0 @ (k9_relat_1 @ X10 @ X11) @ (k9_relat_1 @ X10 @ X12)))
% 0.20/0.56          | ~ (v1_relat_1 @ X10))),
% 0.20/0.56      inference('cnf', [status(esa)], [t154_relat_1])).
% 0.20/0.56  thf('2', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.56  thf(t18_xboole_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 0.20/0.56  thf('3', plain,
% 0.20/0.56      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.56         ((r1_tarski @ X2 @ X3) | ~ (r1_tarski @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t18_xboole_1])).
% 0.20/0.56  thf('4', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.56         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.56  thf('5', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.56         (~ (v1_relat_1 @ X1)
% 0.20/0.56          | (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 0.20/0.56             (k9_relat_1 @ X1 @ X0)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['1', '4'])).
% 0.20/0.56  thf(t148_funct_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.56       ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 0.20/0.56         ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ))).
% 0.20/0.56  thf('6', plain,
% 0.20/0.56      (![X13 : $i, X14 : $i]:
% 0.20/0.56         (((k9_relat_1 @ X14 @ (k10_relat_1 @ X14 @ X13))
% 0.20/0.56            = (k3_xboole_0 @ X13 @ (k9_relat_1 @ X14 @ (k1_relat_1 @ X14))))
% 0.20/0.56          | ~ (v1_funct_1 @ X14)
% 0.20/0.56          | ~ (v1_relat_1 @ X14))),
% 0.20/0.56      inference('cnf', [status(esa)], [t148_funct_1])).
% 0.20/0.56  thf('7', plain,
% 0.20/0.56      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.56         ((r1_tarski @ X2 @ X3) | ~ (r1_tarski @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t18_xboole_1])).
% 0.20/0.56  thf('8', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.56         (~ (r1_tarski @ X2 @ (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0)))
% 0.20/0.56          | ~ (v1_relat_1 @ X1)
% 0.20/0.56          | ~ (v1_funct_1 @ X1)
% 0.20/0.56          | (r1_tarski @ X2 @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.56  thf('9', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.56         (~ (v1_relat_1 @ X1)
% 0.20/0.56          | (r1_tarski @ 
% 0.20/0.56             (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))) @ 
% 0.20/0.56             X0)
% 0.20/0.56          | ~ (v1_funct_1 @ X1)
% 0.20/0.56          | ~ (v1_relat_1 @ X1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['5', '8'])).
% 0.20/0.56  thf('10', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.56         (~ (v1_funct_1 @ X1)
% 0.20/0.56          | (r1_tarski @ 
% 0.20/0.56             (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))) @ 
% 0.20/0.56             X0)
% 0.20/0.56          | ~ (v1_relat_1 @ X1))),
% 0.20/0.56      inference('simplify', [status(thm)], ['9'])).
% 0.20/0.56  thf('11', plain,
% 0.20/0.56      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.56         ((r1_tarski @ (k9_relat_1 @ X10 @ (k3_xboole_0 @ X11 @ X12)) @ 
% 0.20/0.56           (k3_xboole_0 @ (k9_relat_1 @ X10 @ X11) @ (k9_relat_1 @ X10 @ X12)))
% 0.20/0.56          | ~ (v1_relat_1 @ X10))),
% 0.20/0.56      inference('cnf', [status(esa)], [t154_relat_1])).
% 0.20/0.56  thf('12', plain,
% 0.20/0.56      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.56         ((r1_tarski @ X2 @ X3) | ~ (r1_tarski @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t18_xboole_1])).
% 0.20/0.56  thf('13', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.56         (~ (v1_relat_1 @ X1)
% 0.20/0.56          | (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 0.20/0.56             (k9_relat_1 @ X1 @ X2)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.56  thf(t19_xboole_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.20/0.56       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.20/0.56  thf('14', plain,
% 0.20/0.56      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.56         (~ (r1_tarski @ X5 @ X6)
% 0.20/0.56          | ~ (r1_tarski @ X5 @ X7)
% 0.20/0.56          | (r1_tarski @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.20/0.56  thf('15', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.56         (~ (v1_relat_1 @ X1)
% 0.20/0.56          | (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ 
% 0.20/0.56             (k3_xboole_0 @ (k9_relat_1 @ X1 @ X0) @ X3))
% 0.20/0.56          | ~ (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ X3))),
% 0.20/0.56      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.56  thf('16', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.56         (~ (v1_relat_1 @ X1)
% 0.20/0.56          | ~ (v1_funct_1 @ X1)
% 0.20/0.56          | (r1_tarski @ 
% 0.20/0.56             (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))) @ 
% 0.20/0.56             (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ X0))
% 0.20/0.56          | ~ (v1_relat_1 @ X1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['10', '15'])).
% 0.20/0.56  thf('17', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.56         ((r1_tarski @ 
% 0.20/0.56           (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))) @ 
% 0.20/0.56           (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ X0))
% 0.20/0.56          | ~ (v1_funct_1 @ X1)
% 0.20/0.56          | ~ (v1_relat_1 @ X1))),
% 0.20/0.56      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.56  thf('18', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.56         ((r1_tarski @ 
% 0.20/0.56           (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ X2))) @ 
% 0.20/0.56           (k3_xboole_0 @ X2 @ (k9_relat_1 @ X1 @ X0)))
% 0.20/0.56          | ~ (v1_relat_1 @ X1)
% 0.20/0.56          | ~ (v1_funct_1 @ X1))),
% 0.20/0.56      inference('sup+', [status(thm)], ['0', '17'])).
% 0.20/0.56  thf(t149_funct_1, conjecture,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.56       ( r1_tarski @
% 0.20/0.56         ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) @ 
% 0.20/0.56         ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ))).
% 0.20/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.56        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.56          ( r1_tarski @
% 0.20/0.56            ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) @ 
% 0.20/0.56            ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ) )),
% 0.20/0.56    inference('cnf.neg', [status(esa)], [t149_funct_1])).
% 0.20/0.56  thf('19', plain,
% 0.20/0.56      (~ (r1_tarski @ 
% 0.20/0.56          (k9_relat_1 @ sk_C @ 
% 0.20/0.56           (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_C @ sk_B))) @ 
% 0.20/0.56          (k3_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ sk_B))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('20', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.56  thf('21', plain,
% 0.20/0.56      (~ (r1_tarski @ 
% 0.20/0.56          (k9_relat_1 @ sk_C @ 
% 0.20/0.56           (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_C @ sk_B))) @ 
% 0.20/0.56          (k3_xboole_0 @ sk_B @ (k9_relat_1 @ sk_C @ sk_A)))),
% 0.20/0.56      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.56  thf('22', plain, ((~ (v1_funct_1 @ sk_C) | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.56      inference('sup-', [status(thm)], ['18', '21'])).
% 0.20/0.56  thf('23', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('24', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('25', plain, ($false),
% 0.20/0.56      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.20/0.56  
% 0.20/0.56  % SZS output end Refutation
% 0.20/0.56  
% 0.20/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

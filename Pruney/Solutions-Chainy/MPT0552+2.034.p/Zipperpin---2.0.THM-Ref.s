%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Bt4ziSEKhg

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:27 EST 2020

% Result     : Theorem 5.63s
% Output     : Refutation 5.63s
% Verified   : 
% Statistics : Number of formulae       :   42 (  63 expanded)
%              Number of leaves         :   17 (  25 expanded)
%              Depth                    :   12
%              Number of atoms          :  349 ( 579 expanded)
%              Number of equality atoms :    8 (  16 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X19 @ X20 ) )
        = ( k9_relat_1 @ X19 @ X20 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t103_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k7_relat_1 @ C @ A ) ) ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X16 @ X17 )
      | ~ ( v1_relat_1 @ X18 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X18 @ X17 ) @ X16 )
        = ( k7_relat_1 @ X18 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t103_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
        = ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X19 @ X20 ) )
        = ( k9_relat_1 @ X19 @ X20 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t99_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k2_relat_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) ) @ ( k2_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t99_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ ( k9_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ ( k9_relat_1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['0','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X4 @ X6 )
      | ( r1_tarski @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(t154_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t154_relat_1])).

thf('20',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['21','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Bt4ziSEKhg
% 0.13/0.36  % Computer   : n004.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 11:46:09 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 5.63/5.88  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.63/5.88  % Solved by: fo/fo7.sh
% 5.63/5.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.63/5.88  % done 2467 iterations in 5.448s
% 5.63/5.88  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.63/5.88  % SZS output start Refutation
% 5.63/5.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.63/5.88  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 5.63/5.88  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.63/5.88  thf(sk_C_type, type, sk_C: $i).
% 5.63/5.88  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 5.63/5.88  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 5.63/5.88  thf(sk_B_type, type, sk_B: $i).
% 5.63/5.88  thf(sk_A_type, type, sk_A: $i).
% 5.63/5.88  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 5.63/5.88  thf(commutativity_k3_xboole_0, axiom,
% 5.63/5.88    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 5.63/5.88  thf('0', plain,
% 5.63/5.88      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.63/5.88      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.63/5.88  thf(t148_relat_1, axiom,
% 5.63/5.88    (![A:$i,B:$i]:
% 5.63/5.88     ( ( v1_relat_1 @ B ) =>
% 5.63/5.88       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 5.63/5.88  thf('1', plain,
% 5.63/5.88      (![X19 : $i, X20 : $i]:
% 5.63/5.88         (((k2_relat_1 @ (k7_relat_1 @ X19 @ X20)) = (k9_relat_1 @ X19 @ X20))
% 5.63/5.88          | ~ (v1_relat_1 @ X19))),
% 5.63/5.88      inference('cnf', [status(esa)], [t148_relat_1])).
% 5.63/5.88  thf(t17_xboole_1, axiom,
% 5.63/5.88    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 5.63/5.88  thf('2', plain,
% 5.63/5.88      (![X2 : $i, X3 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X3) @ X2)),
% 5.63/5.88      inference('cnf', [status(esa)], [t17_xboole_1])).
% 5.63/5.88  thf(t103_relat_1, axiom,
% 5.63/5.88    (![A:$i,B:$i,C:$i]:
% 5.63/5.88     ( ( v1_relat_1 @ C ) =>
% 5.63/5.88       ( ( r1_tarski @ A @ B ) =>
% 5.63/5.88         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k7_relat_1 @ C @ A ) ) ) ))).
% 5.63/5.88  thf('3', plain,
% 5.63/5.88      (![X16 : $i, X17 : $i, X18 : $i]:
% 5.63/5.88         (~ (r1_tarski @ X16 @ X17)
% 5.63/5.88          | ~ (v1_relat_1 @ X18)
% 5.63/5.88          | ((k7_relat_1 @ (k7_relat_1 @ X18 @ X17) @ X16)
% 5.63/5.88              = (k7_relat_1 @ X18 @ X16)))),
% 5.63/5.88      inference('cnf', [status(esa)], [t103_relat_1])).
% 5.63/5.88  thf('4', plain,
% 5.63/5.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.63/5.88         (((k7_relat_1 @ (k7_relat_1 @ X2 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 5.63/5.88            = (k7_relat_1 @ X2 @ (k3_xboole_0 @ X0 @ X1)))
% 5.63/5.88          | ~ (v1_relat_1 @ X2))),
% 5.63/5.88      inference('sup-', [status(thm)], ['2', '3'])).
% 5.63/5.88  thf('5', plain,
% 5.63/5.88      (![X19 : $i, X20 : $i]:
% 5.63/5.88         (((k2_relat_1 @ (k7_relat_1 @ X19 @ X20)) = (k9_relat_1 @ X19 @ X20))
% 5.63/5.88          | ~ (v1_relat_1 @ X19))),
% 5.63/5.88      inference('cnf', [status(esa)], [t148_relat_1])).
% 5.63/5.88  thf(t99_relat_1, axiom,
% 5.63/5.88    (![A:$i,B:$i]:
% 5.63/5.88     ( ( v1_relat_1 @ B ) =>
% 5.63/5.88       ( r1_tarski @
% 5.63/5.88         ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k2_relat_1 @ B ) ) ))).
% 5.63/5.88  thf('6', plain,
% 5.63/5.88      (![X21 : $i, X22 : $i]:
% 5.63/5.88         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X21 @ X22)) @ 
% 5.63/5.88           (k2_relat_1 @ X21))
% 5.63/5.88          | ~ (v1_relat_1 @ X21))),
% 5.63/5.88      inference('cnf', [status(esa)], [t99_relat_1])).
% 5.63/5.88  thf('7', plain,
% 5.63/5.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.63/5.88         ((r1_tarski @ 
% 5.63/5.88           (k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)) @ 
% 5.63/5.88           (k9_relat_1 @ X1 @ X0))
% 5.63/5.88          | ~ (v1_relat_1 @ X1)
% 5.63/5.88          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 5.63/5.88      inference('sup+', [status(thm)], ['5', '6'])).
% 5.63/5.88  thf(dt_k7_relat_1, axiom,
% 5.63/5.88    (![A:$i,B:$i]:
% 5.63/5.88     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 5.63/5.88  thf('8', plain,
% 5.63/5.88      (![X14 : $i, X15 : $i]:
% 5.63/5.88         (~ (v1_relat_1 @ X14) | (v1_relat_1 @ (k7_relat_1 @ X14 @ X15)))),
% 5.63/5.88      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 5.63/5.88  thf('9', plain,
% 5.63/5.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.63/5.88         (~ (v1_relat_1 @ X1)
% 5.63/5.88          | (r1_tarski @ 
% 5.63/5.88             (k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)) @ 
% 5.63/5.88             (k9_relat_1 @ X1 @ X0)))),
% 5.63/5.88      inference('clc', [status(thm)], ['7', '8'])).
% 5.63/5.88  thf('10', plain,
% 5.63/5.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.63/5.88         ((r1_tarski @ 
% 5.63/5.88           (k2_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0))) @ 
% 5.63/5.88           (k9_relat_1 @ X2 @ X1))
% 5.63/5.88          | ~ (v1_relat_1 @ X2)
% 5.63/5.88          | ~ (v1_relat_1 @ X2))),
% 5.63/5.88      inference('sup+', [status(thm)], ['4', '9'])).
% 5.63/5.88  thf('11', plain,
% 5.63/5.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.63/5.88         (~ (v1_relat_1 @ X2)
% 5.63/5.88          | (r1_tarski @ 
% 5.63/5.88             (k2_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0))) @ 
% 5.63/5.88             (k9_relat_1 @ X2 @ X1)))),
% 5.63/5.88      inference('simplify', [status(thm)], ['10'])).
% 5.63/5.88  thf('12', plain,
% 5.63/5.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.63/5.88         ((r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 5.63/5.88           (k9_relat_1 @ X2 @ X1))
% 5.63/5.88          | ~ (v1_relat_1 @ X2)
% 5.63/5.88          | ~ (v1_relat_1 @ X2))),
% 5.63/5.88      inference('sup+', [status(thm)], ['1', '11'])).
% 5.63/5.88  thf('13', plain,
% 5.63/5.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.63/5.88         (~ (v1_relat_1 @ X2)
% 5.63/5.88          | (r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 5.63/5.88             (k9_relat_1 @ X2 @ X1)))),
% 5.63/5.88      inference('simplify', [status(thm)], ['12'])).
% 5.63/5.88  thf('14', plain,
% 5.63/5.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.63/5.88         ((r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 5.63/5.88           (k9_relat_1 @ X2 @ X0))
% 5.63/5.88          | ~ (v1_relat_1 @ X2))),
% 5.63/5.88      inference('sup+', [status(thm)], ['0', '13'])).
% 5.63/5.88  thf('15', plain,
% 5.63/5.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.63/5.88         (~ (v1_relat_1 @ X2)
% 5.63/5.88          | (r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 5.63/5.88             (k9_relat_1 @ X2 @ X1)))),
% 5.63/5.88      inference('simplify', [status(thm)], ['12'])).
% 5.63/5.88  thf(t19_xboole_1, axiom,
% 5.63/5.88    (![A:$i,B:$i,C:$i]:
% 5.63/5.88     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 5.63/5.88       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 5.63/5.88  thf('16', plain,
% 5.63/5.88      (![X4 : $i, X5 : $i, X6 : $i]:
% 5.63/5.88         (~ (r1_tarski @ X4 @ X5)
% 5.63/5.88          | ~ (r1_tarski @ X4 @ X6)
% 5.63/5.88          | (r1_tarski @ X4 @ (k3_xboole_0 @ X5 @ X6)))),
% 5.63/5.88      inference('cnf', [status(esa)], [t19_xboole_1])).
% 5.63/5.88  thf('17', plain,
% 5.63/5.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.63/5.88         (~ (v1_relat_1 @ X1)
% 5.63/5.88          | (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ 
% 5.63/5.88             (k3_xboole_0 @ (k9_relat_1 @ X1 @ X0) @ X3))
% 5.63/5.88          | ~ (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ X3))),
% 5.63/5.88      inference('sup-', [status(thm)], ['15', '16'])).
% 5.63/5.88  thf('18', plain,
% 5.63/5.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.63/5.88         (~ (v1_relat_1 @ X1)
% 5.63/5.88          | (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 5.63/5.88             (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ (k9_relat_1 @ X1 @ X0)))
% 5.63/5.88          | ~ (v1_relat_1 @ X1))),
% 5.63/5.88      inference('sup-', [status(thm)], ['14', '17'])).
% 5.63/5.88  thf('19', plain,
% 5.63/5.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.63/5.88         ((r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 5.63/5.88           (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ (k9_relat_1 @ X1 @ X0)))
% 5.63/5.88          | ~ (v1_relat_1 @ X1))),
% 5.63/5.88      inference('simplify', [status(thm)], ['18'])).
% 5.63/5.88  thf(t154_relat_1, conjecture,
% 5.63/5.88    (![A:$i,B:$i,C:$i]:
% 5.63/5.88     ( ( v1_relat_1 @ C ) =>
% 5.63/5.88       ( r1_tarski @
% 5.63/5.88         ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 5.63/5.88         ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 5.63/5.88  thf(zf_stmt_0, negated_conjecture,
% 5.63/5.88    (~( ![A:$i,B:$i,C:$i]:
% 5.63/5.88        ( ( v1_relat_1 @ C ) =>
% 5.63/5.88          ( r1_tarski @
% 5.63/5.88            ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 5.63/5.88            ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )),
% 5.63/5.88    inference('cnf.neg', [status(esa)], [t154_relat_1])).
% 5.63/5.88  thf('20', plain,
% 5.63/5.88      (~ (r1_tarski @ (k9_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 5.63/5.88          (k3_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ 
% 5.63/5.88           (k9_relat_1 @ sk_C @ sk_B)))),
% 5.63/5.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.63/5.88  thf('21', plain, (~ (v1_relat_1 @ sk_C)),
% 5.63/5.88      inference('sup-', [status(thm)], ['19', '20'])).
% 5.63/5.88  thf('22', plain, ((v1_relat_1 @ sk_C)),
% 5.63/5.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.63/5.88  thf('23', plain, ($false), inference('demod', [status(thm)], ['21', '22'])).
% 5.63/5.88  
% 5.63/5.88  % SZS output end Refutation
% 5.63/5.88  
% 5.63/5.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

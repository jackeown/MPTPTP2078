%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jQXvMcuIhM

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:06 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   36 (  39 expanded)
%              Number of leaves         :   17 (  19 expanded)
%              Depth                    :   10
%              Number of atoms          :  278 ( 318 expanded)
%              Number of equality atoms :   20 (  23 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t140_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k8_relat_1 @ A @ C ) @ B )
        = ( k8_relat_1 @ A @ ( k7_relat_1 @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X8 @ X9 ) @ X10 )
        = ( k8_relat_1 @ X8 @ ( k7_relat_1 @ X9 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t140_relat_1])).

thf(t119_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X7 @ X6 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X6 ) @ X7 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ ( k8_relat_1 @ X2 @ X1 ) @ X0 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ ( k8_relat_1 @ X2 @ X1 ) @ X0 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 ) ) ) ),
    inference(clc,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) @ X0 )
        = ( k9_relat_1 @ ( k8_relat_1 @ X0 @ X2 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k3_xboole_0 @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) @ X0 )
        = ( k9_relat_1 @ ( k8_relat_1 @ X0 @ X2 ) @ X1 ) ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k9_relat_1 @ ( k8_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k9_relat_1 @ ( k8_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t126_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k9_relat_1 @ ( k8_relat_1 @ A @ C ) @ B )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( k9_relat_1 @ ( k8_relat_1 @ A @ C ) @ B )
          = ( k3_xboole_0 @ A @ ( k9_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t126_funct_1])).

thf('12',plain,(
    ( k9_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C ) @ sk_B )
 != ( k3_xboole_0 @ sk_A @ ( k9_relat_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_B ) @ sk_A )
     != ( k3_xboole_0 @ sk_A @ ( k9_relat_1 @ sk_C @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('15',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ( k3_xboole_0 @ sk_A @ ( k9_relat_1 @ sk_C @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ ( k9_relat_1 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    $false ),
    inference(simplify,[status(thm)],['16'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.16/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jQXvMcuIhM
% 0.16/0.38  % Computer   : n019.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 10:44:53 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.23/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.46  % Solved by: fo/fo7.sh
% 0.23/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.46  % done 14 iterations in 0.010s
% 0.23/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.46  % SZS output start Refutation
% 0.23/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.23/0.46  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.23/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.46  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.23/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.46  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.23/0.46  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.23/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.23/0.46  thf(t148_relat_1, axiom,
% 0.23/0.46    (![A:$i,B:$i]:
% 0.23/0.46     ( ( v1_relat_1 @ B ) =>
% 0.23/0.46       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.23/0.46  thf('0', plain,
% 0.23/0.46      (![X11 : $i, X12 : $i]:
% 0.23/0.46         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 0.23/0.46          | ~ (v1_relat_1 @ X11))),
% 0.23/0.46      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.23/0.46  thf(t140_relat_1, axiom,
% 0.23/0.46    (![A:$i,B:$i,C:$i]:
% 0.23/0.46     ( ( v1_relat_1 @ C ) =>
% 0.23/0.46       ( ( k7_relat_1 @ ( k8_relat_1 @ A @ C ) @ B ) =
% 0.23/0.46         ( k8_relat_1 @ A @ ( k7_relat_1 @ C @ B ) ) ) ))).
% 0.23/0.46  thf('1', plain,
% 0.23/0.46      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.23/0.46         (((k7_relat_1 @ (k8_relat_1 @ X8 @ X9) @ X10)
% 0.23/0.46            = (k8_relat_1 @ X8 @ (k7_relat_1 @ X9 @ X10)))
% 0.23/0.46          | ~ (v1_relat_1 @ X9))),
% 0.23/0.46      inference('cnf', [status(esa)], [t140_relat_1])).
% 0.23/0.46  thf(t119_relat_1, axiom,
% 0.23/0.46    (![A:$i,B:$i]:
% 0.23/0.46     ( ( v1_relat_1 @ B ) =>
% 0.23/0.46       ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) =
% 0.23/0.46         ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.23/0.46  thf('2', plain,
% 0.23/0.46      (![X6 : $i, X7 : $i]:
% 0.23/0.46         (((k2_relat_1 @ (k8_relat_1 @ X7 @ X6))
% 0.23/0.46            = (k3_xboole_0 @ (k2_relat_1 @ X6) @ X7))
% 0.23/0.46          | ~ (v1_relat_1 @ X6))),
% 0.23/0.46      inference('cnf', [status(esa)], [t119_relat_1])).
% 0.23/0.46  thf('3', plain,
% 0.23/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.46         (((k2_relat_1 @ (k7_relat_1 @ (k8_relat_1 @ X2 @ X1) @ X0))
% 0.23/0.46            = (k3_xboole_0 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2))
% 0.23/0.46          | ~ (v1_relat_1 @ X1)
% 0.23/0.46          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.23/0.46      inference('sup+', [status(thm)], ['1', '2'])).
% 0.23/0.46  thf(dt_k7_relat_1, axiom,
% 0.23/0.46    (![A:$i,B:$i]:
% 0.23/0.46     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.23/0.46  thf('4', plain,
% 0.23/0.46      (![X2 : $i, X3 : $i]:
% 0.23/0.46         (~ (v1_relat_1 @ X2) | (v1_relat_1 @ (k7_relat_1 @ X2 @ X3)))),
% 0.23/0.46      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.23/0.46  thf('5', plain,
% 0.23/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.46         (~ (v1_relat_1 @ X1)
% 0.23/0.46          | ((k2_relat_1 @ (k7_relat_1 @ (k8_relat_1 @ X2 @ X1) @ X0))
% 0.23/0.46              = (k3_xboole_0 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2)))),
% 0.23/0.46      inference('clc', [status(thm)], ['3', '4'])).
% 0.23/0.46  thf('6', plain,
% 0.23/0.46      (![X11 : $i, X12 : $i]:
% 0.23/0.46         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 0.23/0.46          | ~ (v1_relat_1 @ X11))),
% 0.23/0.46      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.23/0.46  thf('7', plain,
% 0.23/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.46         (((k3_xboole_0 @ (k2_relat_1 @ (k7_relat_1 @ X2 @ X1)) @ X0)
% 0.23/0.46            = (k9_relat_1 @ (k8_relat_1 @ X0 @ X2) @ X1))
% 0.23/0.46          | ~ (v1_relat_1 @ X2)
% 0.23/0.46          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ X2)))),
% 0.23/0.46      inference('sup+', [status(thm)], ['5', '6'])).
% 0.23/0.46  thf(dt_k8_relat_1, axiom,
% 0.23/0.46    (![A:$i,B:$i]:
% 0.23/0.46     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 0.23/0.46  thf('8', plain,
% 0.23/0.46      (![X4 : $i, X5 : $i]:
% 0.23/0.46         ((v1_relat_1 @ (k8_relat_1 @ X4 @ X5)) | ~ (v1_relat_1 @ X5))),
% 0.23/0.46      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.23/0.46  thf('9', plain,
% 0.23/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.46         (~ (v1_relat_1 @ X2)
% 0.23/0.46          | ((k3_xboole_0 @ (k2_relat_1 @ (k7_relat_1 @ X2 @ X1)) @ X0)
% 0.23/0.46              = (k9_relat_1 @ (k8_relat_1 @ X0 @ X2) @ X1)))),
% 0.23/0.46      inference('clc', [status(thm)], ['7', '8'])).
% 0.23/0.46  thf('10', plain,
% 0.23/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.46         (((k3_xboole_0 @ (k9_relat_1 @ X1 @ X0) @ X2)
% 0.23/0.46            = (k9_relat_1 @ (k8_relat_1 @ X2 @ X1) @ X0))
% 0.23/0.46          | ~ (v1_relat_1 @ X1)
% 0.23/0.46          | ~ (v1_relat_1 @ X1))),
% 0.23/0.46      inference('sup+', [status(thm)], ['0', '9'])).
% 0.23/0.46  thf('11', plain,
% 0.23/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.46         (~ (v1_relat_1 @ X1)
% 0.23/0.46          | ((k3_xboole_0 @ (k9_relat_1 @ X1 @ X0) @ X2)
% 0.23/0.46              = (k9_relat_1 @ (k8_relat_1 @ X2 @ X1) @ X0)))),
% 0.23/0.46      inference('simplify', [status(thm)], ['10'])).
% 0.23/0.46  thf(t126_funct_1, conjecture,
% 0.23/0.46    (![A:$i,B:$i,C:$i]:
% 0.23/0.46     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.23/0.46       ( ( k9_relat_1 @ ( k8_relat_1 @ A @ C ) @ B ) =
% 0.23/0.46         ( k3_xboole_0 @ A @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.23/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.46    (~( ![A:$i,B:$i,C:$i]:
% 0.23/0.46        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.23/0.46          ( ( k9_relat_1 @ ( k8_relat_1 @ A @ C ) @ B ) =
% 0.23/0.46            ( k3_xboole_0 @ A @ ( k9_relat_1 @ C @ B ) ) ) ) )),
% 0.23/0.46    inference('cnf.neg', [status(esa)], [t126_funct_1])).
% 0.23/0.46  thf('12', plain,
% 0.23/0.46      (((k9_relat_1 @ (k8_relat_1 @ sk_A @ sk_C) @ sk_B)
% 0.23/0.46         != (k3_xboole_0 @ sk_A @ (k9_relat_1 @ sk_C @ sk_B)))),
% 0.23/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.46  thf('13', plain,
% 0.23/0.46      ((((k3_xboole_0 @ (k9_relat_1 @ sk_C @ sk_B) @ sk_A)
% 0.23/0.46          != (k3_xboole_0 @ sk_A @ (k9_relat_1 @ sk_C @ sk_B)))
% 0.23/0.46        | ~ (v1_relat_1 @ sk_C))),
% 0.23/0.46      inference('sup-', [status(thm)], ['11', '12'])).
% 0.23/0.46  thf(commutativity_k3_xboole_0, axiom,
% 0.23/0.46    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.23/0.46  thf('14', plain,
% 0.23/0.46      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.23/0.46      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.23/0.46  thf('15', plain, ((v1_relat_1 @ sk_C)),
% 0.23/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.46  thf('16', plain,
% 0.23/0.46      (((k3_xboole_0 @ sk_A @ (k9_relat_1 @ sk_C @ sk_B))
% 0.23/0.46         != (k3_xboole_0 @ sk_A @ (k9_relat_1 @ sk_C @ sk_B)))),
% 0.23/0.46      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.23/0.46  thf('17', plain, ($false), inference('simplify', [status(thm)], ['16'])).
% 0.23/0.46  
% 0.23/0.46  % SZS output end Refutation
% 0.23/0.46  
% 0.23/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

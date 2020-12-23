%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GcWiHg3rxX

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:06 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   38 (  43 expanded)
%              Number of leaves         :   17 (  20 expanded)
%              Depth                    :   11
%              Number of atoms          :  312 ( 382 expanded)
%              Number of equality atoms :   21 (  26 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

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

thf(fc8_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf(t140_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k8_relat_1 @ A @ C ) @ B )
        = ( k8_relat_1 @ A @ ( k7_relat_1 @ C @ B ) ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X8 @ X9 ) @ X10 )
        = ( k8_relat_1 @ X8 @ ( k7_relat_1 @ X9 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t140_relat_1])).

thf('3',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k8_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k8_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf(t119_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X7 @ X6 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X6 ) @ X7 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_relat_1 @ ( k8_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k3_xboole_0 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ ( k8_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k3_xboole_0 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_relat_1 @ ( k8_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k3_xboole_0 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_relat_1 @ ( k8_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ ( k8_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

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

thf('13',plain,(
    ( k9_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C ) @ sk_B )
 != ( k3_xboole_0 @ sk_A @ ( k9_relat_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_B ) @ sk_A )
     != ( k3_xboole_0 @ sk_A @ ( k9_relat_1 @ sk_C @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('16',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ( k3_xboole_0 @ sk_A @ ( k9_relat_1 @ sk_C @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ ( k9_relat_1 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','15','16','17'])).

thf('19',plain,(
    $false ),
    inference(simplify,[status(thm)],['18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GcWiHg3rxX
% 0.15/0.37  % Computer   : n013.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 20:29:55 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.22/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.46  % Solved by: fo/fo7.sh
% 0.22/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.46  % done 17 iterations in 0.011s
% 0.22/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.46  % SZS output start Refutation
% 0.22/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.46  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.46  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.46  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.22/0.46  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.22/0.46  thf(t148_relat_1, axiom,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( v1_relat_1 @ B ) =>
% 0.22/0.46       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.22/0.46  thf('0', plain,
% 0.22/0.46      (![X11 : $i, X12 : $i]:
% 0.22/0.46         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 0.22/0.46          | ~ (v1_relat_1 @ X11))),
% 0.22/0.46      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.22/0.46  thf(fc8_funct_1, axiom,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.46       ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) & 
% 0.22/0.46         ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 0.22/0.46  thf('1', plain,
% 0.22/0.46      (![X13 : $i, X14 : $i]:
% 0.22/0.46         (~ (v1_funct_1 @ X13)
% 0.22/0.46          | ~ (v1_relat_1 @ X13)
% 0.22/0.46          | (v1_relat_1 @ (k7_relat_1 @ X13 @ X14)))),
% 0.22/0.46      inference('cnf', [status(esa)], [fc8_funct_1])).
% 0.22/0.46  thf(t140_relat_1, axiom,
% 0.22/0.46    (![A:$i,B:$i,C:$i]:
% 0.22/0.46     ( ( v1_relat_1 @ C ) =>
% 0.22/0.46       ( ( k7_relat_1 @ ( k8_relat_1 @ A @ C ) @ B ) =
% 0.22/0.46         ( k8_relat_1 @ A @ ( k7_relat_1 @ C @ B ) ) ) ))).
% 0.22/0.46  thf('2', plain,
% 0.22/0.46      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.46         (((k7_relat_1 @ (k8_relat_1 @ X8 @ X9) @ X10)
% 0.22/0.46            = (k8_relat_1 @ X8 @ (k7_relat_1 @ X9 @ X10)))
% 0.22/0.46          | ~ (v1_relat_1 @ X9))),
% 0.22/0.46      inference('cnf', [status(esa)], [t140_relat_1])).
% 0.22/0.46  thf('3', plain,
% 0.22/0.46      (![X11 : $i, X12 : $i]:
% 0.22/0.46         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 0.22/0.46          | ~ (v1_relat_1 @ X11))),
% 0.22/0.46      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.22/0.46  thf('4', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.46         (((k2_relat_1 @ (k8_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0)))
% 0.22/0.46            = (k9_relat_1 @ (k8_relat_1 @ X2 @ X1) @ X0))
% 0.22/0.46          | ~ (v1_relat_1 @ X1)
% 0.22/0.46          | ~ (v1_relat_1 @ (k8_relat_1 @ X2 @ X1)))),
% 0.22/0.46      inference('sup+', [status(thm)], ['2', '3'])).
% 0.22/0.46  thf(dt_k8_relat_1, axiom,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 0.22/0.46  thf('5', plain,
% 0.22/0.46      (![X4 : $i, X5 : $i]:
% 0.22/0.46         ((v1_relat_1 @ (k8_relat_1 @ X4 @ X5)) | ~ (v1_relat_1 @ X5))),
% 0.22/0.46      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.22/0.46  thf('6', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.46         (~ (v1_relat_1 @ X1)
% 0.22/0.46          | ((k2_relat_1 @ (k8_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0)))
% 0.22/0.46              = (k9_relat_1 @ (k8_relat_1 @ X2 @ X1) @ X0)))),
% 0.22/0.46      inference('clc', [status(thm)], ['4', '5'])).
% 0.22/0.46  thf(t119_relat_1, axiom,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( v1_relat_1 @ B ) =>
% 0.22/0.46       ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) =
% 0.22/0.46         ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.46  thf('7', plain,
% 0.22/0.46      (![X6 : $i, X7 : $i]:
% 0.22/0.46         (((k2_relat_1 @ (k8_relat_1 @ X7 @ X6))
% 0.22/0.46            = (k3_xboole_0 @ (k2_relat_1 @ X6) @ X7))
% 0.22/0.46          | ~ (v1_relat_1 @ X6))),
% 0.22/0.46      inference('cnf', [status(esa)], [t119_relat_1])).
% 0.22/0.46  thf('8', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.46         (((k9_relat_1 @ (k8_relat_1 @ X2 @ X1) @ X0)
% 0.22/0.46            = (k3_xboole_0 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2))
% 0.22/0.46          | ~ (v1_relat_1 @ X1)
% 0.22/0.46          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.22/0.46      inference('sup+', [status(thm)], ['6', '7'])).
% 0.22/0.46  thf('9', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.46         (~ (v1_relat_1 @ X1)
% 0.22/0.46          | ~ (v1_funct_1 @ X1)
% 0.22/0.46          | ~ (v1_relat_1 @ X1)
% 0.22/0.46          | ((k9_relat_1 @ (k8_relat_1 @ X2 @ X1) @ X0)
% 0.22/0.46              = (k3_xboole_0 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2)))),
% 0.22/0.46      inference('sup-', [status(thm)], ['1', '8'])).
% 0.22/0.46  thf('10', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.46         (((k9_relat_1 @ (k8_relat_1 @ X2 @ X1) @ X0)
% 0.22/0.46            = (k3_xboole_0 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2))
% 0.22/0.46          | ~ (v1_funct_1 @ X1)
% 0.22/0.46          | ~ (v1_relat_1 @ X1))),
% 0.22/0.46      inference('simplify', [status(thm)], ['9'])).
% 0.22/0.46  thf('11', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.46         (((k9_relat_1 @ (k8_relat_1 @ X2 @ X1) @ X0)
% 0.22/0.46            = (k3_xboole_0 @ (k9_relat_1 @ X1 @ X0) @ X2))
% 0.22/0.46          | ~ (v1_relat_1 @ X1)
% 0.22/0.46          | ~ (v1_relat_1 @ X1)
% 0.22/0.46          | ~ (v1_funct_1 @ X1))),
% 0.22/0.46      inference('sup+', [status(thm)], ['0', '10'])).
% 0.22/0.46  thf('12', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.46         (~ (v1_funct_1 @ X1)
% 0.22/0.46          | ~ (v1_relat_1 @ X1)
% 0.22/0.46          | ((k9_relat_1 @ (k8_relat_1 @ X2 @ X1) @ X0)
% 0.22/0.46              = (k3_xboole_0 @ (k9_relat_1 @ X1 @ X0) @ X2)))),
% 0.22/0.46      inference('simplify', [status(thm)], ['11'])).
% 0.22/0.46  thf(t126_funct_1, conjecture,
% 0.22/0.46    (![A:$i,B:$i,C:$i]:
% 0.22/0.46     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.46       ( ( k9_relat_1 @ ( k8_relat_1 @ A @ C ) @ B ) =
% 0.22/0.46         ( k3_xboole_0 @ A @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.22/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.46    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.46        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.46          ( ( k9_relat_1 @ ( k8_relat_1 @ A @ C ) @ B ) =
% 0.22/0.46            ( k3_xboole_0 @ A @ ( k9_relat_1 @ C @ B ) ) ) ) )),
% 0.22/0.46    inference('cnf.neg', [status(esa)], [t126_funct_1])).
% 0.22/0.46  thf('13', plain,
% 0.22/0.46      (((k9_relat_1 @ (k8_relat_1 @ sk_A @ sk_C) @ sk_B)
% 0.22/0.46         != (k3_xboole_0 @ sk_A @ (k9_relat_1 @ sk_C @ sk_B)))),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('14', plain,
% 0.22/0.46      ((((k3_xboole_0 @ (k9_relat_1 @ sk_C @ sk_B) @ sk_A)
% 0.22/0.46          != (k3_xboole_0 @ sk_A @ (k9_relat_1 @ sk_C @ sk_B)))
% 0.22/0.46        | ~ (v1_relat_1 @ sk_C)
% 0.22/0.46        | ~ (v1_funct_1 @ sk_C))),
% 0.22/0.46      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.46  thf(commutativity_k3_xboole_0, axiom,
% 0.22/0.46    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.22/0.46  thf('15', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.46      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.46  thf('16', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('18', plain,
% 0.22/0.46      (((k3_xboole_0 @ sk_A @ (k9_relat_1 @ sk_C @ sk_B))
% 0.22/0.46         != (k3_xboole_0 @ sk_A @ (k9_relat_1 @ sk_C @ sk_B)))),
% 0.22/0.46      inference('demod', [status(thm)], ['14', '15', '16', '17'])).
% 0.22/0.46  thf('19', plain, ($false), inference('simplify', [status(thm)], ['18'])).
% 0.22/0.46  
% 0.22/0.46  % SZS output end Refutation
% 0.22/0.46  
% 0.22/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VDCtFX2dVq

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   29 (  32 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    9
%              Number of atoms          :  223 ( 259 expanded)
%              Number of equality atoms :   15 (  18 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k8_relat_1 @ X7 @ X6 )
        = ( k5_relat_1 @ X6 @ ( k6_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k8_relat_1 @ X7 @ X6 )
        = ( k5_relat_1 @ X6 @ ( k6_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t112_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ X4 @ X3 ) @ X5 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) @ X3 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t112_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X2 ) ) @ X0 )
        = ( k8_relat_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('4',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X2 ) ) @ X0 )
        = ( k8_relat_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X2 ) ) @ X0 )
        = ( k8_relat_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k8_relat_1 @ X1 @ ( k7_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k8_relat_1 @ X1 @ ( k7_relat_1 @ X0 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t140_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k8_relat_1 @ A @ C ) @ B )
        = ( k8_relat_1 @ A @ ( k7_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( k7_relat_1 @ ( k8_relat_1 @ A @ C ) @ B )
          = ( k8_relat_1 @ A @ ( k7_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t140_relat_1])).

thf('10',plain,(
    ( k7_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C ) @ sk_B )
 != ( k8_relat_1 @ sk_A @ ( k7_relat_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( k7_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C ) @ sk_B )
     != ( k7_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C ) @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ( k7_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C ) @ sk_B )
 != ( k7_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    $false ),
    inference(simplify,[status(thm)],['13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VDCtFX2dVq
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:26:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 7 iterations in 0.011s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.46  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.46  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.46  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.20/0.46  thf(t123_relat_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( v1_relat_1 @ B ) =>
% 0.20/0.46       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.20/0.46  thf('0', plain,
% 0.20/0.46      (![X6 : $i, X7 : $i]:
% 0.20/0.46         (((k8_relat_1 @ X7 @ X6) = (k5_relat_1 @ X6 @ (k6_relat_1 @ X7)))
% 0.20/0.46          | ~ (v1_relat_1 @ X6))),
% 0.20/0.46      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      (![X6 : $i, X7 : $i]:
% 0.20/0.46         (((k8_relat_1 @ X7 @ X6) = (k5_relat_1 @ X6 @ (k6_relat_1 @ X7)))
% 0.20/0.46          | ~ (v1_relat_1 @ X6))),
% 0.20/0.46      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.20/0.46  thf(t112_relat_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( v1_relat_1 @ B ) =>
% 0.20/0.46       ( ![C:$i]:
% 0.20/0.46         ( ( v1_relat_1 @ C ) =>
% 0.20/0.46           ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.20/0.46             ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) ))).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.46         (~ (v1_relat_1 @ X3)
% 0.20/0.46          | ((k7_relat_1 @ (k5_relat_1 @ X4 @ X3) @ X5)
% 0.20/0.46              = (k5_relat_1 @ (k7_relat_1 @ X4 @ X5) @ X3))
% 0.20/0.46          | ~ (v1_relat_1 @ X4))),
% 0.20/0.46      inference('cnf', [status(esa)], [t112_relat_1])).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.46         (((k7_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X2)) @ X0)
% 0.20/0.46            = (k8_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0)))
% 0.20/0.46          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.20/0.46          | ~ (v1_relat_1 @ X1)
% 0.20/0.46          | ~ (v1_relat_1 @ (k6_relat_1 @ X2)))),
% 0.20/0.46      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.46  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.20/0.46  thf('4', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 0.20/0.46      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.46         (((k7_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X2)) @ X0)
% 0.20/0.46            = (k8_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0)))
% 0.20/0.46          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.20/0.46          | ~ (v1_relat_1 @ X1))),
% 0.20/0.46      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.46  thf(dt_k7_relat_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      (![X1 : $i, X2 : $i]:
% 0.20/0.46         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X2)))),
% 0.20/0.46      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.46         (~ (v1_relat_1 @ X1)
% 0.20/0.46          | ((k7_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X2)) @ X0)
% 0.20/0.46              = (k8_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0))))),
% 0.20/0.46      inference('clc', [status(thm)], ['5', '6'])).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.46         (((k7_relat_1 @ (k8_relat_1 @ X1 @ X0) @ X2)
% 0.20/0.46            = (k8_relat_1 @ X1 @ (k7_relat_1 @ X0 @ X2)))
% 0.20/0.46          | ~ (v1_relat_1 @ X0)
% 0.20/0.46          | ~ (v1_relat_1 @ X0))),
% 0.20/0.46      inference('sup+', [status(thm)], ['0', '7'])).
% 0.20/0.46  thf('9', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.46         (~ (v1_relat_1 @ X0)
% 0.20/0.46          | ((k7_relat_1 @ (k8_relat_1 @ X1 @ X0) @ X2)
% 0.20/0.46              = (k8_relat_1 @ X1 @ (k7_relat_1 @ X0 @ X2))))),
% 0.20/0.46      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.46  thf(t140_relat_1, conjecture,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( v1_relat_1 @ C ) =>
% 0.20/0.46       ( ( k7_relat_1 @ ( k8_relat_1 @ A @ C ) @ B ) =
% 0.20/0.46         ( k8_relat_1 @ A @ ( k7_relat_1 @ C @ B ) ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.46        ( ( v1_relat_1 @ C ) =>
% 0.20/0.46          ( ( k7_relat_1 @ ( k8_relat_1 @ A @ C ) @ B ) =
% 0.20/0.46            ( k8_relat_1 @ A @ ( k7_relat_1 @ C @ B ) ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t140_relat_1])).
% 0.20/0.46  thf('10', plain,
% 0.20/0.46      (((k7_relat_1 @ (k8_relat_1 @ sk_A @ sk_C) @ sk_B)
% 0.20/0.46         != (k8_relat_1 @ sk_A @ (k7_relat_1 @ sk_C @ sk_B)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      ((((k7_relat_1 @ (k8_relat_1 @ sk_A @ sk_C) @ sk_B)
% 0.20/0.46          != (k7_relat_1 @ (k8_relat_1 @ sk_A @ sk_C) @ sk_B))
% 0.20/0.46        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.46      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.46  thf('12', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('13', plain,
% 0.20/0.46      (((k7_relat_1 @ (k8_relat_1 @ sk_A @ sk_C) @ sk_B)
% 0.20/0.46         != (k7_relat_1 @ (k8_relat_1 @ sk_A @ sk_C) @ sk_B))),
% 0.20/0.46      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.46  thf('14', plain, ($false), inference('simplify', [status(thm)], ['13'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

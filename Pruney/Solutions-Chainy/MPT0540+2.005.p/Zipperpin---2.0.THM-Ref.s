%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vxNjs3vP6D

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   40 (  45 expanded)
%              Number of leaves         :   15 (  19 expanded)
%              Depth                    :   14
%              Number of atoms          :  360 ( 409 expanded)
%              Number of equality atoms :   23 (  27 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k8_relat_1 @ X6 @ X5 )
        = ( k5_relat_1 @ X5 @ ( k6_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k7_relat_1 @ X11 @ X10 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X10 ) @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k5_relat_1 @ X8 @ ( k5_relat_1 @ X7 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
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
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X0 @ X2 ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k8_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['0','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X0 @ X2 ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k8_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X0 @ X2 ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k8_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k7_relat_1 @ X11 @ X10 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X10 ) @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X0 @ X2 ) @ X1 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X3: $i,X4: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X3 @ X4 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k7_relat_1 @ ( k8_relat_1 @ X0 @ X2 ) @ X1 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k8_relat_1 @ X6 @ X5 )
        = ( k5_relat_1 @ X5 @ ( k6_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k7_relat_1 @ ( k8_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k8_relat_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k7_relat_1 @ ( k8_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['16','17'])).

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

thf('19',plain,(
    ( k7_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C ) @ sk_B )
 != ( k8_relat_1 @ sk_A @ ( k7_relat_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( k7_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C ) @ sk_B )
     != ( k7_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C ) @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ( k7_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C ) @ sk_B )
 != ( k7_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    $false ),
    inference(simplify,[status(thm)],['22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vxNjs3vP6D
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:31:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.20/0.34  % Python version: Python 3.6.8
% 0.20/0.34  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 33 iterations in 0.056s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.50  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.50  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.50  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(t123_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ B ) =>
% 0.20/0.50       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      (![X5 : $i, X6 : $i]:
% 0.20/0.50         (((k8_relat_1 @ X6 @ X5) = (k5_relat_1 @ X5 @ (k6_relat_1 @ X6)))
% 0.20/0.50          | ~ (v1_relat_1 @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.20/0.50  thf(t94_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ B ) =>
% 0.20/0.50       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (![X10 : $i, X11 : $i]:
% 0.20/0.50         (((k7_relat_1 @ X11 @ X10) = (k5_relat_1 @ (k6_relat_1 @ X10) @ X11))
% 0.20/0.50          | ~ (v1_relat_1 @ X11))),
% 0.20/0.50      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.20/0.50  thf(t55_relat_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( v1_relat_1 @ B ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( v1_relat_1 @ C ) =>
% 0.20/0.50               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.20/0.50                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X7)
% 0.20/0.50          | ((k5_relat_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 0.20/0.50              = (k5_relat_1 @ X8 @ (k5_relat_1 @ X7 @ X9)))
% 0.20/0.50          | ~ (v1_relat_1 @ X9)
% 0.20/0.50          | ~ (v1_relat_1 @ X8))),
% 0.20/0.50      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 0.20/0.50            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 0.20/0.50          | ~ (v1_relat_1 @ X1)
% 0.20/0.50          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.20/0.50          | ~ (v1_relat_1 @ X2)
% 0.20/0.50          | ~ (v1_relat_1 @ X1))),
% 0.20/0.50      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.50  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.20/0.50  thf('4', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 0.20/0.50            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 0.20/0.50          | ~ (v1_relat_1 @ X1)
% 0.20/0.50          | ~ (v1_relat_1 @ X2)
% 0.20/0.50          | ~ (v1_relat_1 @ X1))),
% 0.20/0.50      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X2)
% 0.20/0.50          | ~ (v1_relat_1 @ X1)
% 0.20/0.50          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 0.20/0.50              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 0.20/0.50      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (((k5_relat_1 @ (k7_relat_1 @ X0 @ X2) @ (k6_relat_1 @ X1))
% 0.20/0.50            = (k5_relat_1 @ (k6_relat_1 @ X2) @ (k8_relat_1 @ X1 @ X0)))
% 0.20/0.50          | ~ (v1_relat_1 @ X0)
% 0.20/0.50          | ~ (v1_relat_1 @ X0)
% 0.20/0.50          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['0', '6'])).
% 0.20/0.50  thf('8', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (((k5_relat_1 @ (k7_relat_1 @ X0 @ X2) @ (k6_relat_1 @ X1))
% 0.20/0.50            = (k5_relat_1 @ (k6_relat_1 @ X2) @ (k8_relat_1 @ X1 @ X0)))
% 0.20/0.50          | ~ (v1_relat_1 @ X0)
% 0.20/0.50          | ~ (v1_relat_1 @ X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X0)
% 0.20/0.50          | ((k5_relat_1 @ (k7_relat_1 @ X0 @ X2) @ (k6_relat_1 @ X1))
% 0.20/0.50              = (k5_relat_1 @ (k6_relat_1 @ X2) @ (k8_relat_1 @ X1 @ X0))))),
% 0.20/0.50      inference('simplify', [status(thm)], ['9'])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X10 : $i, X11 : $i]:
% 0.20/0.50         (((k7_relat_1 @ X11 @ X10) = (k5_relat_1 @ (k6_relat_1 @ X10) @ X11))
% 0.20/0.50          | ~ (v1_relat_1 @ X11))),
% 0.20/0.50      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (((k7_relat_1 @ (k8_relat_1 @ X0 @ X2) @ X1)
% 0.20/0.50            = (k5_relat_1 @ (k7_relat_1 @ X2 @ X1) @ (k6_relat_1 @ X0)))
% 0.20/0.50          | ~ (v1_relat_1 @ X2)
% 0.20/0.50          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ X2)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['10', '11'])).
% 0.20/0.50  thf(dt_k8_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X3 : $i, X4 : $i]:
% 0.20/0.50         ((v1_relat_1 @ (k8_relat_1 @ X3 @ X4)) | ~ (v1_relat_1 @ X4))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X2)
% 0.20/0.50          | ((k7_relat_1 @ (k8_relat_1 @ X0 @ X2) @ X1)
% 0.20/0.50              = (k5_relat_1 @ (k7_relat_1 @ X2 @ X1) @ (k6_relat_1 @ X0))))),
% 0.20/0.50      inference('clc', [status(thm)], ['12', '13'])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (![X5 : $i, X6 : $i]:
% 0.20/0.50         (((k8_relat_1 @ X6 @ X5) = (k5_relat_1 @ X5 @ (k6_relat_1 @ X6)))
% 0.20/0.50          | ~ (v1_relat_1 @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (((k8_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0))
% 0.20/0.50            = (k7_relat_1 @ (k8_relat_1 @ X2 @ X1) @ X0))
% 0.20/0.50          | ~ (v1_relat_1 @ X1)
% 0.20/0.50          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['14', '15'])).
% 0.20/0.50  thf(dt_k7_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (![X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X2)))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X1)
% 0.20/0.50          | ((k8_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0))
% 0.20/0.50              = (k7_relat_1 @ (k8_relat_1 @ X2 @ X1) @ X0)))),
% 0.20/0.50      inference('clc', [status(thm)], ['16', '17'])).
% 0.20/0.50  thf(t140_relat_1, conjecture,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ C ) =>
% 0.20/0.50       ( ( k7_relat_1 @ ( k8_relat_1 @ A @ C ) @ B ) =
% 0.20/0.50         ( k8_relat_1 @ A @ ( k7_relat_1 @ C @ B ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.50        ( ( v1_relat_1 @ C ) =>
% 0.20/0.50          ( ( k7_relat_1 @ ( k8_relat_1 @ A @ C ) @ B ) =
% 0.20/0.50            ( k8_relat_1 @ A @ ( k7_relat_1 @ C @ B ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t140_relat_1])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (((k7_relat_1 @ (k8_relat_1 @ sk_A @ sk_C) @ sk_B)
% 0.20/0.50         != (k8_relat_1 @ sk_A @ (k7_relat_1 @ sk_C @ sk_B)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      ((((k7_relat_1 @ (k8_relat_1 @ sk_A @ sk_C) @ sk_B)
% 0.20/0.50          != (k7_relat_1 @ (k8_relat_1 @ sk_A @ sk_C) @ sk_B))
% 0.20/0.50        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.50  thf('21', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (((k7_relat_1 @ (k8_relat_1 @ sk_A @ sk_C) @ sk_B)
% 0.20/0.50         != (k7_relat_1 @ (k8_relat_1 @ sk_A @ sk_C) @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.50  thf('23', plain, ($false), inference('simplify', [status(thm)], ['22'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

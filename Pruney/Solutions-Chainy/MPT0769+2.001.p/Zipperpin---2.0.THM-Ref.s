%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0xb1vqJ4eS

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:22 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   33 (  36 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :   11
%              Number of atoms          :  255 ( 287 expanded)
%              Number of equality atoms :   19 (  22 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(t17_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_wellord1 @ B @ A )
        = ( k7_relat_1 @ ( k8_relat_1 @ A @ B ) @ A ) ) ) )).

thf('0',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_wellord1 @ X9 @ X8 )
        = ( k7_relat_1 @ ( k8_relat_1 @ X8 @ X9 ) @ X8 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t17_wellord1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k7_relat_1 @ X7 @ X6 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X6 ) @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k7_relat_1 @ X7 @ X6 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X6 ) @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t139_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k8_relat_1 @ A @ ( k5_relat_1 @ B @ C ) )
            = ( k5_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( ( k8_relat_1 @ X5 @ ( k5_relat_1 @ X4 @ X3 ) )
        = ( k5_relat_1 @ X4 @ ( k8_relat_1 @ X5 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t139_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k7_relat_1 @ ( k8_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('5',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k7_relat_1 @ ( k8_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X1: $i,X2: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k8_relat_1 @ X2 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k7_relat_1 @ ( k8_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k7_relat_1 @ ( k8_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k8_relat_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k7_relat_1 @ ( k8_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k2_wellord1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k8_relat_1 @ X0 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k2_wellord1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t18_wellord1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_wellord1 @ B @ A )
        = ( k8_relat_1 @ A @ ( k7_relat_1 @ B @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( k2_wellord1 @ B @ A )
          = ( k8_relat_1 @ A @ ( k7_relat_1 @ B @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_wellord1])).

thf('13',plain,(
    ( k2_wellord1 @ sk_B @ sk_A )
 != ( k8_relat_1 @ sk_A @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k2_wellord1 @ sk_B @ sk_A )
     != ( k2_wellord1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ( k2_wellord1 @ sk_B @ sk_A )
 != ( k2_wellord1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    $false ),
    inference(simplify,[status(thm)],['16'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0xb1vqJ4eS
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 13:45:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.22/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.47  % Solved by: fo/fo7.sh
% 0.22/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.47  % done 9 iterations in 0.014s
% 0.22/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.47  % SZS output start Refutation
% 0.22/0.47  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.22/0.47  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.22/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.47  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.22/0.47  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.22/0.47  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.47  thf(t17_wellord1, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( v1_relat_1 @ B ) =>
% 0.22/0.47       ( ( k2_wellord1 @ B @ A ) = ( k7_relat_1 @ ( k8_relat_1 @ A @ B ) @ A ) ) ))).
% 0.22/0.47  thf('0', plain,
% 0.22/0.47      (![X8 : $i, X9 : $i]:
% 0.22/0.47         (((k2_wellord1 @ X9 @ X8) = (k7_relat_1 @ (k8_relat_1 @ X8 @ X9) @ X8))
% 0.22/0.47          | ~ (v1_relat_1 @ X9))),
% 0.22/0.47      inference('cnf', [status(esa)], [t17_wellord1])).
% 0.22/0.47  thf(t94_relat_1, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( v1_relat_1 @ B ) =>
% 0.22/0.47       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.22/0.47  thf('1', plain,
% 0.22/0.47      (![X6 : $i, X7 : $i]:
% 0.22/0.47         (((k7_relat_1 @ X7 @ X6) = (k5_relat_1 @ (k6_relat_1 @ X6) @ X7))
% 0.22/0.47          | ~ (v1_relat_1 @ X7))),
% 0.22/0.47      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.22/0.47  thf('2', plain,
% 0.22/0.47      (![X6 : $i, X7 : $i]:
% 0.22/0.47         (((k7_relat_1 @ X7 @ X6) = (k5_relat_1 @ (k6_relat_1 @ X6) @ X7))
% 0.22/0.47          | ~ (v1_relat_1 @ X7))),
% 0.22/0.47      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.22/0.47  thf(t139_relat_1, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( v1_relat_1 @ B ) =>
% 0.22/0.47       ( ![C:$i]:
% 0.22/0.47         ( ( v1_relat_1 @ C ) =>
% 0.22/0.47           ( ( k8_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) =
% 0.22/0.47             ( k5_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) ) ) ) ))).
% 0.22/0.47  thf('3', plain,
% 0.22/0.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.47         (~ (v1_relat_1 @ X3)
% 0.22/0.47          | ((k8_relat_1 @ X5 @ (k5_relat_1 @ X4 @ X3))
% 0.22/0.47              = (k5_relat_1 @ X4 @ (k8_relat_1 @ X5 @ X3)))
% 0.22/0.47          | ~ (v1_relat_1 @ X4))),
% 0.22/0.47      inference('cnf', [status(esa)], [t139_relat_1])).
% 0.22/0.47  thf('4', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.47         (((k8_relat_1 @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.22/0.47            = (k7_relat_1 @ (k8_relat_1 @ X2 @ X1) @ X0))
% 0.22/0.47          | ~ (v1_relat_1 @ (k8_relat_1 @ X2 @ X1))
% 0.22/0.47          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.22/0.47          | ~ (v1_relat_1 @ X1))),
% 0.22/0.47      inference('sup+', [status(thm)], ['2', '3'])).
% 0.22/0.47  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.22/0.47  thf('5', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 0.22/0.47      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.47  thf('6', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.47         (((k8_relat_1 @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.22/0.47            = (k7_relat_1 @ (k8_relat_1 @ X2 @ X1) @ X0))
% 0.22/0.47          | ~ (v1_relat_1 @ (k8_relat_1 @ X2 @ X1))
% 0.22/0.47          | ~ (v1_relat_1 @ X1))),
% 0.22/0.47      inference('demod', [status(thm)], ['4', '5'])).
% 0.22/0.47  thf(dt_k8_relat_1, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 0.22/0.47  thf('7', plain,
% 0.22/0.47      (![X1 : $i, X2 : $i]:
% 0.22/0.47         ((v1_relat_1 @ (k8_relat_1 @ X1 @ X2)) | ~ (v1_relat_1 @ X2))),
% 0.22/0.47      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.22/0.47  thf('8', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.47         (~ (v1_relat_1 @ X1)
% 0.22/0.47          | ((k8_relat_1 @ X2 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.22/0.47              = (k7_relat_1 @ (k8_relat_1 @ X2 @ X1) @ X0)))),
% 0.22/0.47      inference('clc', [status(thm)], ['6', '7'])).
% 0.22/0.47  thf('9', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.47         (((k8_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0))
% 0.22/0.47            = (k7_relat_1 @ (k8_relat_1 @ X2 @ X1) @ X0))
% 0.22/0.47          | ~ (v1_relat_1 @ X1)
% 0.22/0.47          | ~ (v1_relat_1 @ X1))),
% 0.22/0.47      inference('sup+', [status(thm)], ['1', '8'])).
% 0.22/0.47  thf('10', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.47         (~ (v1_relat_1 @ X1)
% 0.22/0.47          | ((k8_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0))
% 0.22/0.47              = (k7_relat_1 @ (k8_relat_1 @ X2 @ X1) @ X0)))),
% 0.22/0.47      inference('simplify', [status(thm)], ['9'])).
% 0.22/0.47  thf('11', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i]:
% 0.22/0.47         (((k8_relat_1 @ X0 @ (k7_relat_1 @ X1 @ X0)) = (k2_wellord1 @ X1 @ X0))
% 0.22/0.47          | ~ (v1_relat_1 @ X1)
% 0.22/0.47          | ~ (v1_relat_1 @ X1))),
% 0.22/0.47      inference('sup+', [status(thm)], ['0', '10'])).
% 0.22/0.47  thf('12', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i]:
% 0.22/0.47         (~ (v1_relat_1 @ X1)
% 0.22/0.47          | ((k8_relat_1 @ X0 @ (k7_relat_1 @ X1 @ X0))
% 0.22/0.47              = (k2_wellord1 @ X1 @ X0)))),
% 0.22/0.47      inference('simplify', [status(thm)], ['11'])).
% 0.22/0.47  thf(t18_wellord1, conjecture,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( v1_relat_1 @ B ) =>
% 0.22/0.47       ( ( k2_wellord1 @ B @ A ) = ( k8_relat_1 @ A @ ( k7_relat_1 @ B @ A ) ) ) ))).
% 0.22/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.47    (~( ![A:$i,B:$i]:
% 0.22/0.47        ( ( v1_relat_1 @ B ) =>
% 0.22/0.47          ( ( k2_wellord1 @ B @ A ) =
% 0.22/0.47            ( k8_relat_1 @ A @ ( k7_relat_1 @ B @ A ) ) ) ) )),
% 0.22/0.47    inference('cnf.neg', [status(esa)], [t18_wellord1])).
% 0.22/0.47  thf('13', plain,
% 0.22/0.47      (((k2_wellord1 @ sk_B @ sk_A)
% 0.22/0.47         != (k8_relat_1 @ sk_A @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('14', plain,
% 0.22/0.47      ((((k2_wellord1 @ sk_B @ sk_A) != (k2_wellord1 @ sk_B @ sk_A))
% 0.22/0.47        | ~ (v1_relat_1 @ sk_B))),
% 0.22/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.47  thf('15', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('16', plain,
% 0.22/0.47      (((k2_wellord1 @ sk_B @ sk_A) != (k2_wellord1 @ sk_B @ sk_A))),
% 0.22/0.47      inference('demod', [status(thm)], ['14', '15'])).
% 0.22/0.47  thf('17', plain, ($false), inference('simplify', [status(thm)], ['16'])).
% 0.22/0.47  
% 0.22/0.47  % SZS output end Refutation
% 0.22/0.47  
% 0.22/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

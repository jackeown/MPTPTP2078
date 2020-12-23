%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WZWLTWlvTU

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   48 (  55 expanded)
%              Number of leaves         :   15 (  21 expanded)
%              Depth                    :   17
%              Number of atoms          :  496 ( 551 expanded)
%              Number of equality atoms :   33 (  37 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k8_relat_1 @ X10 @ X9 )
        = ( k5_relat_1 @ X9 @ ( k6_relat_1 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t112_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) @ X8 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) @ X6 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t112_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k7_relat_1 @ X18 @ X17 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X17 ) @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t139_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k8_relat_1 @ A @ ( k5_relat_1 @ B @ C ) )
            = ( k5_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) ) ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( ( k8_relat_1 @ X13 @ ( k5_relat_1 @ X12 @ X11 ) )
        = ( k5_relat_1 @ X12 @ ( k8_relat_1 @ X13 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t139_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('5',plain,(
    ! [X5: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k8_relat_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k8_relat_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k8_relat_1 @ X2 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k8_relat_1 @ X10 @ X9 )
        = ( k5_relat_1 @ X9 @ ( k6_relat_1 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('9',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k7_relat_1 @ X18 @ X17 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X17 ) @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
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

thf('10',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) @ X16 )
        = ( k5_relat_1 @ X15 @ ( k5_relat_1 @ X14 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X5: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X0 @ X2 ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k8_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['8','14'])).

thf('16',plain,(
    ! [X5: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X0 @ X2 ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k8_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X0 @ X2 ) @ ( k6_relat_1 @ X1 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k8_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k6_relat_1 @ X2 ) )
        = ( k8_relat_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k6_relat_1 @ X2 ) )
        = ( k8_relat_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k7_relat_1 @ X2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','20'])).

thf('22',plain,(
    ! [X5: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k7_relat_1 @ X2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k7_relat_1 @ X2 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k8_relat_1 @ X1 @ ( k7_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k8_relat_1 @ X1 @ ( k7_relat_1 @ X0 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

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

thf('27',plain,(
    ( k7_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C_1 ) @ sk_B )
 != ( k8_relat_1 @ sk_A @ ( k7_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( ( k7_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C_1 ) @ sk_B )
     != ( k7_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C_1 ) @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ( k7_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C_1 ) @ sk_B )
 != ( k7_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    $false ),
    inference(simplify,[status(thm)],['30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WZWLTWlvTU
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:55:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 53 iterations in 0.072s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.52  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.52  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(t123_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ B ) =>
% 0.21/0.52       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      (![X9 : $i, X10 : $i]:
% 0.21/0.52         (((k8_relat_1 @ X10 @ X9) = (k5_relat_1 @ X9 @ (k6_relat_1 @ X10)))
% 0.21/0.52          | ~ (v1_relat_1 @ X9))),
% 0.21/0.52      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.21/0.52  thf(t112_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ B ) =>
% 0.21/0.52       ( ![C:$i]:
% 0.21/0.52         ( ( v1_relat_1 @ C ) =>
% 0.21/0.52           ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.21/0.52             ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) ))).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X6)
% 0.21/0.52          | ((k7_relat_1 @ (k5_relat_1 @ X7 @ X6) @ X8)
% 0.21/0.52              = (k5_relat_1 @ (k7_relat_1 @ X7 @ X8) @ X6))
% 0.21/0.52          | ~ (v1_relat_1 @ X7))),
% 0.21/0.52      inference('cnf', [status(esa)], [t112_relat_1])).
% 0.21/0.52  thf(t94_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ B ) =>
% 0.21/0.52       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (![X17 : $i, X18 : $i]:
% 0.21/0.52         (((k7_relat_1 @ X18 @ X17) = (k5_relat_1 @ (k6_relat_1 @ X17) @ X18))
% 0.21/0.52          | ~ (v1_relat_1 @ X18))),
% 0.21/0.52      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.21/0.52  thf(t139_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ B ) =>
% 0.21/0.52       ( ![C:$i]:
% 0.21/0.52         ( ( v1_relat_1 @ C ) =>
% 0.21/0.52           ( ( k8_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) =
% 0.21/0.52             ( k5_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) ) ) ) ))).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X11)
% 0.21/0.52          | ((k8_relat_1 @ X13 @ (k5_relat_1 @ X12 @ X11))
% 0.21/0.52              = (k5_relat_1 @ X12 @ (k8_relat_1 @ X13 @ X11)))
% 0.21/0.52          | ~ (v1_relat_1 @ X12))),
% 0.21/0.52      inference('cnf', [status(esa)], [t139_relat_1])).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (((k8_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0))
% 0.21/0.52            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k8_relat_1 @ X2 @ X1)))
% 0.21/0.52          | ~ (v1_relat_1 @ X1)
% 0.21/0.52          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.21/0.52          | ~ (v1_relat_1 @ X1))),
% 0.21/0.52      inference('sup+', [status(thm)], ['2', '3'])).
% 0.21/0.52  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.21/0.52  thf('5', plain, (![X5 : $i]: (v1_relat_1 @ (k6_relat_1 @ X5))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (((k8_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0))
% 0.21/0.52            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k8_relat_1 @ X2 @ X1)))
% 0.21/0.52          | ~ (v1_relat_1 @ X1)
% 0.21/0.52          | ~ (v1_relat_1 @ X1))),
% 0.21/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X1)
% 0.21/0.52          | ((k8_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0))
% 0.21/0.52              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k8_relat_1 @ X2 @ X1))))),
% 0.21/0.52      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X9 : $i, X10 : $i]:
% 0.21/0.52         (((k8_relat_1 @ X10 @ X9) = (k5_relat_1 @ X9 @ (k6_relat_1 @ X10)))
% 0.21/0.52          | ~ (v1_relat_1 @ X9))),
% 0.21/0.52      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      (![X17 : $i, X18 : $i]:
% 0.21/0.52         (((k7_relat_1 @ X18 @ X17) = (k5_relat_1 @ (k6_relat_1 @ X17) @ X18))
% 0.21/0.52          | ~ (v1_relat_1 @ X18))),
% 0.21/0.52      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.21/0.52  thf(t55_relat_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( v1_relat_1 @ B ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( v1_relat_1 @ C ) =>
% 0.21/0.52               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.21/0.52                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X14)
% 0.21/0.52          | ((k5_relat_1 @ (k5_relat_1 @ X15 @ X14) @ X16)
% 0.21/0.52              = (k5_relat_1 @ X15 @ (k5_relat_1 @ X14 @ X16)))
% 0.21/0.52          | ~ (v1_relat_1 @ X16)
% 0.21/0.52          | ~ (v1_relat_1 @ X15))),
% 0.21/0.52      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 0.21/0.52            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 0.21/0.52          | ~ (v1_relat_1 @ X1)
% 0.21/0.52          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.21/0.52          | ~ (v1_relat_1 @ X2)
% 0.21/0.52          | ~ (v1_relat_1 @ X1))),
% 0.21/0.52      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.52  thf('12', plain, (![X5 : $i]: (v1_relat_1 @ (k6_relat_1 @ X5))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 0.21/0.52            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 0.21/0.52          | ~ (v1_relat_1 @ X1)
% 0.21/0.52          | ~ (v1_relat_1 @ X2)
% 0.21/0.52          | ~ (v1_relat_1 @ X1))),
% 0.21/0.52      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X2)
% 0.21/0.52          | ~ (v1_relat_1 @ X1)
% 0.21/0.52          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 0.21/0.52              = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 0.21/0.52      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (((k5_relat_1 @ (k7_relat_1 @ X0 @ X2) @ (k6_relat_1 @ X1))
% 0.21/0.52            = (k5_relat_1 @ (k6_relat_1 @ X2) @ (k8_relat_1 @ X1 @ X0)))
% 0.21/0.52          | ~ (v1_relat_1 @ X0)
% 0.21/0.52          | ~ (v1_relat_1 @ X0)
% 0.21/0.52          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['8', '14'])).
% 0.21/0.52  thf('16', plain, (![X5 : $i]: (v1_relat_1 @ (k6_relat_1 @ X5))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (((k5_relat_1 @ (k7_relat_1 @ X0 @ X2) @ (k6_relat_1 @ X1))
% 0.21/0.52            = (k5_relat_1 @ (k6_relat_1 @ X2) @ (k8_relat_1 @ X1 @ X0)))
% 0.21/0.52          | ~ (v1_relat_1 @ X0)
% 0.21/0.52          | ~ (v1_relat_1 @ X0))),
% 0.21/0.52      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X0)
% 0.21/0.52          | ((k5_relat_1 @ (k7_relat_1 @ X0 @ X2) @ (k6_relat_1 @ X1))
% 0.21/0.52              = (k5_relat_1 @ (k6_relat_1 @ X2) @ (k8_relat_1 @ X1 @ X0))))),
% 0.21/0.52      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k6_relat_1 @ X2))
% 0.21/0.52            = (k8_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0)))
% 0.21/0.52          | ~ (v1_relat_1 @ X1)
% 0.21/0.52          | ~ (v1_relat_1 @ X1))),
% 0.21/0.52      inference('sup+', [status(thm)], ['7', '18'])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X1)
% 0.21/0.52          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k6_relat_1 @ X2))
% 0.21/0.52              = (k8_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0))))),
% 0.21/0.52      inference('simplify', [status(thm)], ['19'])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (((k7_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0)
% 0.21/0.52            = (k8_relat_1 @ X1 @ (k7_relat_1 @ X2 @ X0)))
% 0.21/0.52          | ~ (v1_relat_1 @ X2)
% 0.21/0.52          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.21/0.52          | ~ (v1_relat_1 @ X2))),
% 0.21/0.52      inference('sup+', [status(thm)], ['1', '20'])).
% 0.21/0.52  thf('22', plain, (![X5 : $i]: (v1_relat_1 @ (k6_relat_1 @ X5))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (((k7_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0)
% 0.21/0.52            = (k8_relat_1 @ X1 @ (k7_relat_1 @ X2 @ X0)))
% 0.21/0.52          | ~ (v1_relat_1 @ X2)
% 0.21/0.52          | ~ (v1_relat_1 @ X2))),
% 0.21/0.52      inference('demod', [status(thm)], ['21', '22'])).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X2)
% 0.21/0.52          | ((k7_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0)
% 0.21/0.52              = (k8_relat_1 @ X1 @ (k7_relat_1 @ X2 @ X0))))),
% 0.21/0.52      inference('simplify', [status(thm)], ['23'])).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (((k7_relat_1 @ (k8_relat_1 @ X1 @ X0) @ X2)
% 0.21/0.52            = (k8_relat_1 @ X1 @ (k7_relat_1 @ X0 @ X2)))
% 0.21/0.52          | ~ (v1_relat_1 @ X0)
% 0.21/0.52          | ~ (v1_relat_1 @ X0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['0', '24'])).
% 0.21/0.52  thf('26', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X0)
% 0.21/0.52          | ((k7_relat_1 @ (k8_relat_1 @ X1 @ X0) @ X2)
% 0.21/0.52              = (k8_relat_1 @ X1 @ (k7_relat_1 @ X0 @ X2))))),
% 0.21/0.52      inference('simplify', [status(thm)], ['25'])).
% 0.21/0.52  thf(t140_relat_1, conjecture,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ C ) =>
% 0.21/0.52       ( ( k7_relat_1 @ ( k8_relat_1 @ A @ C ) @ B ) =
% 0.21/0.52         ( k8_relat_1 @ A @ ( k7_relat_1 @ C @ B ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.52        ( ( v1_relat_1 @ C ) =>
% 0.21/0.52          ( ( k7_relat_1 @ ( k8_relat_1 @ A @ C ) @ B ) =
% 0.21/0.52            ( k8_relat_1 @ A @ ( k7_relat_1 @ C @ B ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t140_relat_1])).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      (((k7_relat_1 @ (k8_relat_1 @ sk_A @ sk_C_1) @ sk_B)
% 0.21/0.52         != (k8_relat_1 @ sk_A @ (k7_relat_1 @ sk_C_1 @ sk_B)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('28', plain,
% 0.21/0.52      ((((k7_relat_1 @ (k8_relat_1 @ sk_A @ sk_C_1) @ sk_B)
% 0.21/0.52          != (k7_relat_1 @ (k8_relat_1 @ sk_A @ sk_C_1) @ sk_B))
% 0.21/0.52        | ~ (v1_relat_1 @ sk_C_1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.52  thf('29', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('30', plain,
% 0.21/0.52      (((k7_relat_1 @ (k8_relat_1 @ sk_A @ sk_C_1) @ sk_B)
% 0.21/0.52         != (k7_relat_1 @ (k8_relat_1 @ sk_A @ sk_C_1) @ sk_B))),
% 0.21/0.52      inference('demod', [status(thm)], ['28', '29'])).
% 0.21/0.52  thf('31', plain, ($false), inference('simplify', [status(thm)], ['30'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.37/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

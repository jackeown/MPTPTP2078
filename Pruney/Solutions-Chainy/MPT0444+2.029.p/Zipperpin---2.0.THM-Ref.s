%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6uoUtqYKxi

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:49 EST 2020

% Result     : Theorem 1.19s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :   48 (  88 expanded)
%              Number of leaves         :   16 (  33 expanded)
%              Depth                    :   13
%              Number of atoms          :  343 ( 680 expanded)
%              Number of equality atoms :    9 (  24 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t31_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ ( k2_xboole_0 @ B @ C ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ ( k3_xboole_0 @ X10 @ X12 ) ) @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t31_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X7 @ X9 )
      | ( r1_tarski @ X7 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X2 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','10'])).

thf('12',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','10'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('17',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( r1_tarski @ ( k2_relat_1 @ X17 ) @ ( k2_relat_1 @ X16 ) )
      | ~ ( r1_tarski @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('23',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X7 @ X9 )
      | ( r1_tarski @ X7 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ X0 ) @ X2 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf(t27_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_relat_1])).

thf('26',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['27','28','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6uoUtqYKxi
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:47:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.19/1.38  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.19/1.38  % Solved by: fo/fo7.sh
% 1.19/1.38  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.19/1.38  % done 1555 iterations in 0.931s
% 1.19/1.38  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.19/1.38  % SZS output start Refutation
% 1.19/1.38  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.19/1.38  thf(sk_B_type, type, sk_B: $i).
% 1.19/1.38  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.19/1.38  thf(sk_A_type, type, sk_A: $i).
% 1.19/1.38  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.19/1.38  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.19/1.38  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.19/1.38  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.19/1.38  thf(t17_xboole_1, axiom,
% 1.19/1.38    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.19/1.38  thf('0', plain,
% 1.19/1.38      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 1.19/1.38      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.19/1.38  thf(d10_xboole_0, axiom,
% 1.19/1.38    (![A:$i,B:$i]:
% 1.19/1.38     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.19/1.38  thf('1', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.19/1.38      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.19/1.38  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.19/1.38      inference('simplify', [status(thm)], ['1'])).
% 1.19/1.38  thf(t12_xboole_1, axiom,
% 1.19/1.38    (![A:$i,B:$i]:
% 1.19/1.38     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.19/1.38  thf('3', plain,
% 1.19/1.38      (![X3 : $i, X4 : $i]:
% 1.19/1.38         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 1.19/1.38      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.19/1.38  thf('4', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 1.19/1.38      inference('sup-', [status(thm)], ['2', '3'])).
% 1.19/1.38  thf(t31_xboole_1, axiom,
% 1.19/1.38    (![A:$i,B:$i,C:$i]:
% 1.19/1.38     ( r1_tarski @
% 1.19/1.38       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ 
% 1.19/1.38       ( k2_xboole_0 @ B @ C ) ))).
% 1.19/1.38  thf('5', plain,
% 1.19/1.38      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.19/1.38         (r1_tarski @ 
% 1.19/1.38          (k2_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ (k3_xboole_0 @ X10 @ X12)) @ 
% 1.19/1.38          (k2_xboole_0 @ X11 @ X12))),
% 1.19/1.38      inference('cnf', [status(esa)], [t31_xboole_1])).
% 1.19/1.38  thf('6', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i]:
% 1.19/1.38         (r1_tarski @ 
% 1.19/1.38          (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)) @ 
% 1.19/1.38          X0)),
% 1.19/1.38      inference('sup+', [status(thm)], ['4', '5'])).
% 1.19/1.38  thf('7', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 1.19/1.38      inference('sup-', [status(thm)], ['2', '3'])).
% 1.19/1.38  thf('8', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.19/1.38      inference('demod', [status(thm)], ['6', '7'])).
% 1.19/1.38  thf(t19_xboole_1, axiom,
% 1.19/1.38    (![A:$i,B:$i,C:$i]:
% 1.19/1.38     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 1.19/1.38       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 1.19/1.38  thf('9', plain,
% 1.19/1.38      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.19/1.38         (~ (r1_tarski @ X7 @ X8)
% 1.19/1.38          | ~ (r1_tarski @ X7 @ X9)
% 1.19/1.38          | (r1_tarski @ X7 @ (k3_xboole_0 @ X8 @ X9)))),
% 1.19/1.38      inference('cnf', [status(esa)], [t19_xboole_1])).
% 1.19/1.38  thf('10', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.19/1.38         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X2))
% 1.19/1.38          | ~ (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 1.19/1.38      inference('sup-', [status(thm)], ['8', '9'])).
% 1.19/1.38  thf('11', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i]:
% 1.19/1.38         (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0))),
% 1.19/1.38      inference('sup-', [status(thm)], ['0', '10'])).
% 1.19/1.38  thf('12', plain,
% 1.19/1.38      (![X0 : $i, X2 : $i]:
% 1.19/1.38         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.19/1.38      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.19/1.38  thf('13', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i]:
% 1.19/1.38         (~ (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 1.19/1.38          | ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1)))),
% 1.19/1.38      inference('sup-', [status(thm)], ['11', '12'])).
% 1.19/1.38  thf('14', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i]:
% 1.19/1.38         (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0))),
% 1.19/1.38      inference('sup-', [status(thm)], ['0', '10'])).
% 1.19/1.38  thf('15', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.19/1.38      inference('demod', [status(thm)], ['13', '14'])).
% 1.19/1.38  thf('16', plain,
% 1.19/1.38      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 1.19/1.38      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.19/1.38  thf(t25_relat_1, axiom,
% 1.19/1.38    (![A:$i]:
% 1.19/1.38     ( ( v1_relat_1 @ A ) =>
% 1.19/1.38       ( ![B:$i]:
% 1.19/1.38         ( ( v1_relat_1 @ B ) =>
% 1.19/1.38           ( ( r1_tarski @ A @ B ) =>
% 1.19/1.38             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 1.19/1.38               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 1.19/1.38  thf('17', plain,
% 1.19/1.38      (![X16 : $i, X17 : $i]:
% 1.19/1.38         (~ (v1_relat_1 @ X16)
% 1.19/1.38          | (r1_tarski @ (k2_relat_1 @ X17) @ (k2_relat_1 @ X16))
% 1.19/1.38          | ~ (r1_tarski @ X17 @ X16)
% 1.19/1.38          | ~ (v1_relat_1 @ X17))),
% 1.19/1.38      inference('cnf', [status(esa)], [t25_relat_1])).
% 1.19/1.38  thf('18', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i]:
% 1.19/1.38         (~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 1.19/1.38          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 1.19/1.38             (k2_relat_1 @ X0))
% 1.19/1.38          | ~ (v1_relat_1 @ X0))),
% 1.19/1.38      inference('sup-', [status(thm)], ['16', '17'])).
% 1.19/1.38  thf(fc1_relat_1, axiom,
% 1.19/1.38    (![A:$i,B:$i]:
% 1.19/1.38     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.19/1.38  thf('19', plain,
% 1.19/1.38      (![X13 : $i, X14 : $i]:
% 1.19/1.38         (~ (v1_relat_1 @ X13) | (v1_relat_1 @ (k3_xboole_0 @ X13 @ X14)))),
% 1.19/1.38      inference('cnf', [status(esa)], [fc1_relat_1])).
% 1.19/1.38  thf('20', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i]:
% 1.19/1.38         (~ (v1_relat_1 @ X0)
% 1.19/1.38          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 1.19/1.38             (k2_relat_1 @ X0)))),
% 1.19/1.38      inference('clc', [status(thm)], ['18', '19'])).
% 1.19/1.38  thf('21', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i]:
% 1.19/1.38         ((r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 1.19/1.38           (k2_relat_1 @ X0))
% 1.19/1.38          | ~ (v1_relat_1 @ X0))),
% 1.19/1.38      inference('sup+', [status(thm)], ['15', '20'])).
% 1.19/1.38  thf('22', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i]:
% 1.19/1.38         (~ (v1_relat_1 @ X0)
% 1.19/1.38          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 1.19/1.38             (k2_relat_1 @ X0)))),
% 1.19/1.38      inference('clc', [status(thm)], ['18', '19'])).
% 1.19/1.38  thf('23', plain,
% 1.19/1.38      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.19/1.38         (~ (r1_tarski @ X7 @ X8)
% 1.19/1.38          | ~ (r1_tarski @ X7 @ X9)
% 1.19/1.38          | (r1_tarski @ X7 @ (k3_xboole_0 @ X8 @ X9)))),
% 1.19/1.38      inference('cnf', [status(esa)], [t19_xboole_1])).
% 1.19/1.38  thf('24', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.19/1.38         (~ (v1_relat_1 @ X0)
% 1.19/1.38          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 1.19/1.38             (k3_xboole_0 @ (k2_relat_1 @ X0) @ X2))
% 1.19/1.38          | ~ (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X2))),
% 1.19/1.38      inference('sup-', [status(thm)], ['22', '23'])).
% 1.19/1.38  thf('25', plain,
% 1.19/1.38      (![X0 : $i, X1 : $i]:
% 1.19/1.38         (~ (v1_relat_1 @ X0)
% 1.19/1.38          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 1.19/1.38             (k3_xboole_0 @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0)))
% 1.19/1.38          | ~ (v1_relat_1 @ X1))),
% 1.19/1.38      inference('sup-', [status(thm)], ['21', '24'])).
% 1.19/1.38  thf(t27_relat_1, conjecture,
% 1.19/1.38    (![A:$i]:
% 1.19/1.38     ( ( v1_relat_1 @ A ) =>
% 1.19/1.38       ( ![B:$i]:
% 1.19/1.38         ( ( v1_relat_1 @ B ) =>
% 1.19/1.38           ( r1_tarski @
% 1.19/1.38             ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 1.19/1.38             ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 1.19/1.38  thf(zf_stmt_0, negated_conjecture,
% 1.19/1.38    (~( ![A:$i]:
% 1.19/1.38        ( ( v1_relat_1 @ A ) =>
% 1.19/1.38          ( ![B:$i]:
% 1.19/1.38            ( ( v1_relat_1 @ B ) =>
% 1.19/1.38              ( r1_tarski @
% 1.19/1.38                ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 1.19/1.38                ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )),
% 1.19/1.38    inference('cnf.neg', [status(esa)], [t27_relat_1])).
% 1.19/1.38  thf('26', plain,
% 1.19/1.38      (~ (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 1.19/1.38          (k3_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B)))),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('27', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 1.19/1.38      inference('sup-', [status(thm)], ['25', '26'])).
% 1.19/1.38  thf('28', plain, ((v1_relat_1 @ sk_A)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('29', plain, ((v1_relat_1 @ sk_B)),
% 1.19/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.38  thf('30', plain, ($false),
% 1.19/1.38      inference('demod', [status(thm)], ['27', '28', '29'])).
% 1.19/1.38  
% 1.19/1.38  % SZS output end Refutation
% 1.19/1.38  
% 1.19/1.39  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

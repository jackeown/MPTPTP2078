%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KHyzsnx3NG

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:37 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   47 (  54 expanded)
%              Number of leaves         :   18 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :  379 ( 452 expanded)
%              Number of equality atoms :   14 (  16 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(t145_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k9_relat_1 @ B @ A )
        = ( k9_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k9_relat_1 @ X5 @ X6 )
        = ( k9_relat_1 @ X5 @ ( k3_xboole_0 @ ( k1_relat_1 @ X5 ) @ X6 ) ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t145_relat_1])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X14 ) @ X15 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X3 ) @ X4 )
        = ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t156_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( v1_relat_1 @ X11 )
      | ( r1_tarski @ ( k9_relat_1 @ X11 @ X9 ) @ ( k9_relat_1 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ X3 @ ( k3_xboole_0 @ ( k1_relat_1 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ ( k9_relat_1 @ X3 @ X0 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['0','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k9_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('14',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X3 ) @ X4 )
        = ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k9_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t161_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) @ ( k9_relat_1 @ C @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) @ ( k9_relat_1 @ C @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t161_relat_1])).

thf('21',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k9_relat_1 @ sk_C @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['12','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['25','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KHyzsnx3NG
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:40:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.39/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.57  % Solved by: fo/fo7.sh
% 0.39/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.57  % done 113 iterations in 0.127s
% 0.39/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.57  % SZS output start Refutation
% 0.39/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.57  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.39/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.39/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.57  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.39/0.57  thf(t145_relat_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ B ) =>
% 0.39/0.57       ( ( k9_relat_1 @ B @ A ) =
% 0.39/0.57         ( k9_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 0.39/0.57  thf('0', plain,
% 0.39/0.57      (![X5 : $i, X6 : $i]:
% 0.39/0.57         (((k9_relat_1 @ X5 @ X6)
% 0.39/0.57            = (k9_relat_1 @ X5 @ (k3_xboole_0 @ (k1_relat_1 @ X5) @ X6)))
% 0.39/0.57          | ~ (v1_relat_1 @ X5))),
% 0.39/0.57      inference('cnf', [status(esa)], [t145_relat_1])).
% 0.39/0.57  thf(t90_relat_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ B ) =>
% 0.39/0.57       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.39/0.57         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.39/0.57  thf('1', plain,
% 0.39/0.57      (![X14 : $i, X15 : $i]:
% 0.39/0.57         (((k1_relat_1 @ (k7_relat_1 @ X14 @ X15))
% 0.39/0.57            = (k3_xboole_0 @ (k1_relat_1 @ X14) @ X15))
% 0.39/0.57          | ~ (v1_relat_1 @ X14))),
% 0.39/0.57      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.39/0.57  thf(t100_relat_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ C ) =>
% 0.39/0.57       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.39/0.57         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.39/0.57  thf('2', plain,
% 0.39/0.57      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.39/0.57         (((k7_relat_1 @ (k7_relat_1 @ X2 @ X3) @ X4)
% 0.39/0.57            = (k7_relat_1 @ X2 @ (k3_xboole_0 @ X3 @ X4)))
% 0.39/0.57          | ~ (v1_relat_1 @ X2))),
% 0.39/0.57      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.39/0.57  thf(t87_relat_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ B ) =>
% 0.39/0.57       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.39/0.57  thf('3', plain,
% 0.39/0.57      (![X12 : $i, X13 : $i]:
% 0.39/0.57         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X12 @ X13)) @ X13)
% 0.39/0.57          | ~ (v1_relat_1 @ X12))),
% 0.39/0.57      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.39/0.57  thf('4', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         ((r1_tarski @ 
% 0.39/0.57           (k1_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0))) @ X0)
% 0.39/0.57          | ~ (v1_relat_1 @ X2)
% 0.39/0.57          | ~ (v1_relat_1 @ (k7_relat_1 @ X2 @ X1)))),
% 0.39/0.57      inference('sup+', [status(thm)], ['2', '3'])).
% 0.39/0.57  thf(dt_k7_relat_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.39/0.57  thf('5', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k7_relat_1 @ X0 @ X1)))),
% 0.39/0.57      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.39/0.57  thf('6', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         (~ (v1_relat_1 @ X2)
% 0.39/0.57          | (r1_tarski @ 
% 0.39/0.57             (k1_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0))) @ X0))),
% 0.39/0.57      inference('clc', [status(thm)], ['4', '5'])).
% 0.39/0.57  thf('7', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         ((r1_tarski @ 
% 0.39/0.57           (k3_xboole_0 @ (k1_relat_1 @ X2) @ (k3_xboole_0 @ X1 @ X0)) @ X0)
% 0.39/0.57          | ~ (v1_relat_1 @ X2)
% 0.39/0.57          | ~ (v1_relat_1 @ X2))),
% 0.39/0.57      inference('sup+', [status(thm)], ['1', '6'])).
% 0.39/0.57  thf('8', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         (~ (v1_relat_1 @ X2)
% 0.39/0.57          | (r1_tarski @ 
% 0.39/0.57             (k3_xboole_0 @ (k1_relat_1 @ X2) @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.39/0.57      inference('simplify', [status(thm)], ['7'])).
% 0.39/0.57  thf(t156_relat_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ C ) =>
% 0.39/0.57       ( ( r1_tarski @ A @ B ) =>
% 0.39/0.57         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.39/0.57  thf('9', plain,
% 0.39/0.57      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.39/0.57         (~ (r1_tarski @ X9 @ X10)
% 0.39/0.57          | ~ (v1_relat_1 @ X11)
% 0.39/0.57          | (r1_tarski @ (k9_relat_1 @ X11 @ X9) @ (k9_relat_1 @ X11 @ X10)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t156_relat_1])).
% 0.39/0.57  thf('10', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.57         (~ (v1_relat_1 @ X2)
% 0.39/0.57          | (r1_tarski @ 
% 0.39/0.57             (k9_relat_1 @ X3 @ 
% 0.39/0.57              (k3_xboole_0 @ (k1_relat_1 @ X2) @ (k3_xboole_0 @ X1 @ X0))) @ 
% 0.39/0.57             (k9_relat_1 @ X3 @ X0))
% 0.39/0.57          | ~ (v1_relat_1 @ X3))),
% 0.39/0.57      inference('sup-', [status(thm)], ['8', '9'])).
% 0.39/0.57  thf('11', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         ((r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.39/0.57           (k9_relat_1 @ X2 @ X0))
% 0.39/0.57          | ~ (v1_relat_1 @ X2)
% 0.39/0.57          | ~ (v1_relat_1 @ X2)
% 0.39/0.57          | ~ (v1_relat_1 @ X2))),
% 0.39/0.57      inference('sup+', [status(thm)], ['0', '10'])).
% 0.39/0.57  thf('12', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         (~ (v1_relat_1 @ X2)
% 0.39/0.57          | (r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.39/0.57             (k9_relat_1 @ X2 @ X0)))),
% 0.39/0.57      inference('simplify', [status(thm)], ['11'])).
% 0.39/0.57  thf(t148_relat_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ B ) =>
% 0.39/0.57       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.39/0.57  thf('13', plain,
% 0.39/0.57      (![X7 : $i, X8 : $i]:
% 0.39/0.57         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 0.39/0.57          | ~ (v1_relat_1 @ X7))),
% 0.39/0.57      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.39/0.57  thf('14', plain,
% 0.39/0.57      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.39/0.57         (((k7_relat_1 @ (k7_relat_1 @ X2 @ X3) @ X4)
% 0.39/0.57            = (k7_relat_1 @ X2 @ (k3_xboole_0 @ X3 @ X4)))
% 0.39/0.57          | ~ (v1_relat_1 @ X2))),
% 0.39/0.57      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.39/0.57  thf('15', plain,
% 0.39/0.57      (![X7 : $i, X8 : $i]:
% 0.39/0.57         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 0.39/0.57          | ~ (v1_relat_1 @ X7))),
% 0.39/0.57      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.39/0.57  thf('16', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         (((k2_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.39/0.57            = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 0.39/0.57          | ~ (v1_relat_1 @ X2)
% 0.39/0.57          | ~ (v1_relat_1 @ (k7_relat_1 @ X2 @ X1)))),
% 0.39/0.57      inference('sup+', [status(thm)], ['14', '15'])).
% 0.39/0.57  thf('17', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k7_relat_1 @ X0 @ X1)))),
% 0.39/0.57      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.39/0.57  thf('18', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         (~ (v1_relat_1 @ X2)
% 0.39/0.57          | ((k2_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.39/0.57              = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)))),
% 0.39/0.57      inference('clc', [status(thm)], ['16', '17'])).
% 0.39/0.57  thf('19', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         (((k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.39/0.57            = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 0.39/0.57          | ~ (v1_relat_1 @ X2)
% 0.39/0.57          | ~ (v1_relat_1 @ X2))),
% 0.39/0.57      inference('sup+', [status(thm)], ['13', '18'])).
% 0.39/0.57  thf('20', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         (~ (v1_relat_1 @ X2)
% 0.39/0.57          | ((k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.39/0.57              = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)))),
% 0.39/0.57      inference('simplify', [status(thm)], ['19'])).
% 0.39/0.57  thf(t161_relat_1, conjecture,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ C ) =>
% 0.39/0.57       ( r1_tarski @
% 0.39/0.57         ( k9_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) @ ( k9_relat_1 @ C @ B ) ) ))).
% 0.39/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.39/0.57        ( ( v1_relat_1 @ C ) =>
% 0.39/0.57          ( r1_tarski @
% 0.39/0.57            ( k9_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) @ 
% 0.39/0.57            ( k9_relat_1 @ C @ B ) ) ) )),
% 0.39/0.57    inference('cnf.neg', [status(esa)], [t161_relat_1])).
% 0.39/0.57  thf('21', plain,
% 0.39/0.57      (~ (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B) @ 
% 0.39/0.57          (k9_relat_1 @ sk_C @ sk_B))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('22', plain,
% 0.39/0.57      ((~ (r1_tarski @ (k9_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 0.39/0.57           (k9_relat_1 @ sk_C @ sk_B))
% 0.39/0.57        | ~ (v1_relat_1 @ sk_C))),
% 0.39/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.39/0.57  thf('23', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('24', plain,
% 0.39/0.57      (~ (r1_tarski @ (k9_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 0.39/0.57          (k9_relat_1 @ sk_C @ sk_B))),
% 0.39/0.57      inference('demod', [status(thm)], ['22', '23'])).
% 0.39/0.57  thf('25', plain, (~ (v1_relat_1 @ sk_C)),
% 0.39/0.57      inference('sup-', [status(thm)], ['12', '24'])).
% 0.39/0.57  thf('26', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('27', plain, ($false), inference('demod', [status(thm)], ['25', '26'])).
% 0.39/0.57  
% 0.39/0.57  % SZS output end Refutation
% 0.39/0.57  
% 0.39/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

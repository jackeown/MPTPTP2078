%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FbOpHnuVQ3

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:29 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   60 (  73 expanded)
%              Number of leaves         :   20 (  28 expanded)
%              Depth                    :   18
%              Number of atoms          :  488 ( 656 expanded)
%              Number of equality atoms :   30 (  42 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t18_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_wellord1 @ B @ A )
        = ( k8_relat_1 @ A @ ( k7_relat_1 @ B @ A ) ) ) ) )).

thf('0',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_wellord1 @ X19 @ X18 )
        = ( k8_relat_1 @ X18 @ ( k7_relat_1 @ X19 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t18_wellord1])).

thf('1',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_wellord1 @ X19 @ X18 )
        = ( k8_relat_1 @ X18 @ ( k7_relat_1 @ X19 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t18_wellord1])).

thf(t29_wellord1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A )
          = ( k2_wellord1 @ C @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A )
            = ( k2_wellord1 @ C @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_wellord1])).

thf('2',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t129_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) )
          = ( k8_relat_1 @ A @ C ) ) ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( ( k8_relat_1 @ X8 @ ( k8_relat_1 @ X7 @ X9 ) )
        = ( k8_relat_1 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t129_relat_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ X0 ) )
        = ( k8_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) )
        = ( k8_relat_1 @ sk_A @ ( k7_relat_1 @ X0 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) )
        = ( k8_relat_1 @ sk_A @ ( k7_relat_1 @ X0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf(t27_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
        = ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ) )).

thf('8',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X20 @ X22 ) @ X21 )
        = ( k2_wellord1 @ ( k2_wellord1 @ X20 @ X21 ) @ X22 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t27_wellord1])).

thf('9',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t17_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_wellord1 @ B @ A )
        = ( k7_relat_1 @ ( k8_relat_1 @ A @ B ) @ A ) ) ) )).

thf('10',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_wellord1 @ X17 @ X16 )
        = ( k7_relat_1 @ ( k8_relat_1 @ X16 @ X17 ) @ X16 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t17_wellord1])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('18',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ( ( k7_relat_1 @ X12 @ X13 )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) )
      | ( ( k7_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
        = ( k2_wellord1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(dt_k2_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k2_wellord1 @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
        = ( k2_wellord1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_wellord1 @ X19 @ X18 )
        = ( k8_relat_1 @ X18 @ ( k7_relat_1 @ X19 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t18_wellord1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
        = ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
        = ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_B ) @ sk_A )
        = ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_B ) @ sk_A )
        = ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ( k2_wellord1 @ ( k2_wellord1 @ sk_C @ sk_B ) @ sk_A )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ sk_C @ sk_A ) )
     != ( k2_wellord1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ sk_C @ sk_A ) )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k8_relat_1 @ sk_A @ ( k7_relat_1 @ sk_C @ sk_A ) )
     != ( k2_wellord1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ( k8_relat_1 @ sk_A @ ( k7_relat_1 @ sk_C @ sk_A ) )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k2_wellord1 @ sk_C @ sk_A )
     != ( k2_wellord1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ( k2_wellord1 @ sk_C @ sk_A )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    $false ),
    inference(simplify,[status(thm)],['37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FbOpHnuVQ3
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:13:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 114 iterations in 0.097s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.55  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.20/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.55  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.55  thf(t18_wellord1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ B ) =>
% 0.20/0.55       ( ( k2_wellord1 @ B @ A ) = ( k8_relat_1 @ A @ ( k7_relat_1 @ B @ A ) ) ) ))).
% 0.20/0.55  thf('0', plain,
% 0.20/0.55      (![X18 : $i, X19 : $i]:
% 0.20/0.55         (((k2_wellord1 @ X19 @ X18)
% 0.20/0.55            = (k8_relat_1 @ X18 @ (k7_relat_1 @ X19 @ X18)))
% 0.20/0.55          | ~ (v1_relat_1 @ X19))),
% 0.20/0.55      inference('cnf', [status(esa)], [t18_wellord1])).
% 0.20/0.55  thf('1', plain,
% 0.20/0.55      (![X18 : $i, X19 : $i]:
% 0.20/0.55         (((k2_wellord1 @ X19 @ X18)
% 0.20/0.55            = (k8_relat_1 @ X18 @ (k7_relat_1 @ X19 @ X18)))
% 0.20/0.55          | ~ (v1_relat_1 @ X19))),
% 0.20/0.55      inference('cnf', [status(esa)], [t18_wellord1])).
% 0.20/0.55  thf(t29_wellord1, conjecture,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ C ) =>
% 0.20/0.55       ( ( r1_tarski @ A @ B ) =>
% 0.20/0.55         ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 0.20/0.55           ( k2_wellord1 @ C @ A ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.55        ( ( v1_relat_1 @ C ) =>
% 0.20/0.55          ( ( r1_tarski @ A @ B ) =>
% 0.20/0.55            ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 0.20/0.55              ( k2_wellord1 @ C @ A ) ) ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t29_wellord1])).
% 0.20/0.55  thf('2', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(t129_relat_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ C ) =>
% 0.20/0.55       ( ( r1_tarski @ A @ B ) =>
% 0.20/0.55         ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) = ( k8_relat_1 @ A @ C ) ) ) ))).
% 0.20/0.55  thf('3', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.55         (~ (r1_tarski @ X7 @ X8)
% 0.20/0.55          | ~ (v1_relat_1 @ X9)
% 0.20/0.55          | ((k8_relat_1 @ X8 @ (k8_relat_1 @ X7 @ X9))
% 0.20/0.55              = (k8_relat_1 @ X7 @ X9)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t129_relat_1])).
% 0.20/0.55  thf('4', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ X0))
% 0.20/0.55            = (k8_relat_1 @ sk_A @ X0))
% 0.20/0.55          | ~ (v1_relat_1 @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.55  thf('5', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A))
% 0.20/0.55            = (k8_relat_1 @ sk_A @ (k7_relat_1 @ X0 @ sk_A)))
% 0.20/0.55          | ~ (v1_relat_1 @ X0)
% 0.20/0.55          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ sk_A)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['1', '4'])).
% 0.20/0.55  thf(dt_k7_relat_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.20/0.55  thf('6', plain,
% 0.20/0.55      (![X3 : $i, X4 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X3) | (v1_relat_1 @ (k7_relat_1 @ X3 @ X4)))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.20/0.55  thf('7', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X0)
% 0.20/0.55          | ((k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A))
% 0.20/0.55              = (k8_relat_1 @ sk_A @ (k7_relat_1 @ X0 @ sk_A))))),
% 0.20/0.55      inference('clc', [status(thm)], ['5', '6'])).
% 0.20/0.55  thf(t27_wellord1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ C ) =>
% 0.20/0.55       ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 0.20/0.55         ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ))).
% 0.20/0.55  thf('8', plain,
% 0.20/0.55      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.55         (((k2_wellord1 @ (k2_wellord1 @ X20 @ X22) @ X21)
% 0.20/0.55            = (k2_wellord1 @ (k2_wellord1 @ X20 @ X21) @ X22))
% 0.20/0.55          | ~ (v1_relat_1 @ X20))),
% 0.20/0.55      inference('cnf', [status(esa)], [t27_wellord1])).
% 0.20/0.55  thf('9', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(t17_wellord1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ B ) =>
% 0.20/0.55       ( ( k2_wellord1 @ B @ A ) = ( k7_relat_1 @ ( k8_relat_1 @ A @ B ) @ A ) ) ))).
% 0.20/0.55  thf('10', plain,
% 0.20/0.55      (![X16 : $i, X17 : $i]:
% 0.20/0.55         (((k2_wellord1 @ X17 @ X16)
% 0.20/0.55            = (k7_relat_1 @ (k8_relat_1 @ X16 @ X17) @ X16))
% 0.20/0.55          | ~ (v1_relat_1 @ X17))),
% 0.20/0.55      inference('cnf', [status(esa)], [t17_wellord1])).
% 0.20/0.55  thf(t87_relat_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ B ) =>
% 0.20/0.55       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.20/0.55  thf('11', plain,
% 0.20/0.55      (![X10 : $i, X11 : $i]:
% 0.20/0.55         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X10 @ X11)) @ X11)
% 0.20/0.55          | ~ (v1_relat_1 @ X10))),
% 0.20/0.55      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.20/0.55  thf('12', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((r1_tarski @ (k1_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X0)
% 0.20/0.55          | ~ (v1_relat_1 @ X1)
% 0.20/0.55          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ X1)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['10', '11'])).
% 0.20/0.55  thf(dt_k8_relat_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 0.20/0.55  thf('13', plain,
% 0.20/0.55      (![X5 : $i, X6 : $i]:
% 0.20/0.55         ((v1_relat_1 @ (k8_relat_1 @ X5 @ X6)) | ~ (v1_relat_1 @ X6))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.20/0.55  thf('14', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X1)
% 0.20/0.55          | (r1_tarski @ (k1_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X0))),
% 0.20/0.55      inference('clc', [status(thm)], ['12', '13'])).
% 0.20/0.55  thf(t1_xboole_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.20/0.55       ( r1_tarski @ A @ C ) ))).
% 0.20/0.55  thf('15', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         (~ (r1_tarski @ X0 @ X1)
% 0.20/0.55          | ~ (r1_tarski @ X1 @ X2)
% 0.20/0.55          | (r1_tarski @ X0 @ X2))),
% 0.20/0.55      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.20/0.55  thf('16', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X1)
% 0.20/0.55          | (r1_tarski @ (k1_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X2)
% 0.20/0.55          | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.55      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.55  thf('17', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((r1_tarski @ (k1_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B)
% 0.20/0.55          | ~ (v1_relat_1 @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['9', '16'])).
% 0.20/0.55  thf(t97_relat_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ B ) =>
% 0.20/0.55       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.20/0.55         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.20/0.55  thf('18', plain,
% 0.20/0.55      (![X12 : $i, X13 : $i]:
% 0.20/0.55         (~ (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 0.20/0.55          | ((k7_relat_1 @ X12 @ X13) = (X12))
% 0.20/0.55          | ~ (v1_relat_1 @ X12))),
% 0.20/0.55      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.20/0.55  thf('19', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X0)
% 0.20/0.55          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A))
% 0.20/0.55          | ((k7_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)
% 0.20/0.55              = (k2_wellord1 @ X0 @ sk_A)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.55  thf(dt_k2_wellord1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k2_wellord1 @ A @ B ) ) ))).
% 0.20/0.55  thf('20', plain,
% 0.20/0.55      (![X14 : $i, X15 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X14) | (v1_relat_1 @ (k2_wellord1 @ X14 @ X15)))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.20/0.55  thf('21', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k7_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)
% 0.20/0.55            = (k2_wellord1 @ X0 @ sk_A))
% 0.20/0.55          | ~ (v1_relat_1 @ X0))),
% 0.20/0.55      inference('clc', [status(thm)], ['19', '20'])).
% 0.20/0.55  thf('22', plain,
% 0.20/0.55      (![X18 : $i, X19 : $i]:
% 0.20/0.55         (((k2_wellord1 @ X19 @ X18)
% 0.20/0.55            = (k8_relat_1 @ X18 @ (k7_relat_1 @ X19 @ X18)))
% 0.20/0.55          | ~ (v1_relat_1 @ X19))),
% 0.20/0.55      inference('cnf', [status(esa)], [t18_wellord1])).
% 0.20/0.55  thf('23', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)
% 0.20/0.55            = (k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A)))
% 0.20/0.55          | ~ (v1_relat_1 @ X0)
% 0.20/0.55          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['21', '22'])).
% 0.20/0.55  thf('24', plain,
% 0.20/0.55      (![X14 : $i, X15 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X14) | (v1_relat_1 @ (k2_wellord1 @ X14 @ X15)))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.20/0.55  thf('25', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X0)
% 0.20/0.55          | ((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)
% 0.20/0.55              = (k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A))))),
% 0.20/0.55      inference('clc', [status(thm)], ['23', '24'])).
% 0.20/0.55  thf('26', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_B) @ sk_A)
% 0.20/0.55            = (k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A)))
% 0.20/0.55          | ~ (v1_relat_1 @ X0)
% 0.20/0.55          | ~ (v1_relat_1 @ X0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['8', '25'])).
% 0.20/0.55  thf('27', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X0)
% 0.20/0.55          | ((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_B) @ sk_A)
% 0.20/0.55              = (k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A))))),
% 0.20/0.55      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.55  thf('28', plain,
% 0.20/0.55      (((k2_wellord1 @ (k2_wellord1 @ sk_C @ sk_B) @ sk_A)
% 0.20/0.55         != (k2_wellord1 @ sk_C @ sk_A))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('29', plain,
% 0.20/0.55      ((((k8_relat_1 @ sk_B @ (k2_wellord1 @ sk_C @ sk_A))
% 0.20/0.55          != (k2_wellord1 @ sk_C @ sk_A))
% 0.20/0.55        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.55      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.55  thf('30', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('31', plain,
% 0.20/0.55      (((k8_relat_1 @ sk_B @ (k2_wellord1 @ sk_C @ sk_A))
% 0.20/0.55         != (k2_wellord1 @ sk_C @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.55  thf('32', plain,
% 0.20/0.55      ((((k8_relat_1 @ sk_A @ (k7_relat_1 @ sk_C @ sk_A))
% 0.20/0.55          != (k2_wellord1 @ sk_C @ sk_A))
% 0.20/0.55        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.55      inference('sup-', [status(thm)], ['7', '31'])).
% 0.20/0.55  thf('33', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('34', plain,
% 0.20/0.55      (((k8_relat_1 @ sk_A @ (k7_relat_1 @ sk_C @ sk_A))
% 0.20/0.55         != (k2_wellord1 @ sk_C @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.55  thf('35', plain,
% 0.20/0.55      ((((k2_wellord1 @ sk_C @ sk_A) != (k2_wellord1 @ sk_C @ sk_A))
% 0.20/0.55        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.55      inference('sup-', [status(thm)], ['0', '34'])).
% 0.20/0.55  thf('36', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('37', plain,
% 0.20/0.55      (((k2_wellord1 @ sk_C @ sk_A) != (k2_wellord1 @ sk_C @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.55  thf('38', plain, ($false), inference('simplify', [status(thm)], ['37'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

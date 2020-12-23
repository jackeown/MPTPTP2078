%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lfpA1CCV26

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:29 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   64 (  76 expanded)
%              Number of leaves         :   22 (  30 expanded)
%              Depth                    :   16
%              Number of atoms          :  504 ( 648 expanded)
%              Number of equality atoms :   26 (  35 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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

thf('0',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t17_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_wellord1 @ B @ A )
        = ( k7_relat_1 @ ( k8_relat_1 @ A @ B ) @ A ) ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k2_wellord1 @ X18 @ X17 )
        = ( k7_relat_1 @ ( k8_relat_1 @ X17 @ X18 ) @ X17 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t17_wellord1])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['3','4'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('9',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ( ( k7_relat_1 @ X13 @ X14 )
        = X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) )
      | ( ( k7_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
        = ( k2_wellord1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(dt_k2_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k2_wellord1 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
        = ( k2_wellord1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf(t27_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
        = ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ) )).

thf('13',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X21 @ X23 ) @ X22 )
        = ( k2_wellord1 @ ( k2_wellord1 @ X21 @ X22 ) @ X23 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t27_wellord1])).

thf('14',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t18_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_wellord1 @ B @ A )
        = ( k8_relat_1 @ A @ ( k7_relat_1 @ B @ A ) ) ) ) )).

thf('15',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k2_wellord1 @ X20 @ X19 )
        = ( k8_relat_1 @ X19 @ ( k7_relat_1 @ X20 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t18_wellord1])).

thf(t116_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ A ) ) )).

thf('16',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X7 @ X8 ) ) @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t116_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('23',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X9 ) @ X10 )
      | ( ( k8_relat_1 @ X10 @ X9 )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) )
      | ( ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) )
        = ( k2_wellord1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) )
        = ( k2_wellord1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k2_wellord1 @ X18 @ X17 )
        = ( k7_relat_1 @ ( k8_relat_1 @ X17 @ X18 ) @ X17 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t17_wellord1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
        = ( k7_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
        = ( k7_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_B ) @ sk_A )
        = ( k7_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_B ) @ sk_A )
        = ( k7_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ( k2_wellord1 @ ( k2_wellord1 @ sk_C @ sk_B ) @ sk_A )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( ( k7_relat_1 @ ( k2_wellord1 @ sk_C @ sk_A ) @ sk_B )
     != ( k2_wellord1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ( k7_relat_1 @ ( k2_wellord1 @ sk_C @ sk_A ) @ sk_B )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k2_wellord1 @ sk_C @ sk_A )
     != ( k2_wellord1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['12','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ( k2_wellord1 @ sk_C @ sk_A )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    $false ),
    inference(simplify,[status(thm)],['39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lfpA1CCV26
% 0.12/0.32  % Computer   : n004.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 14:51:24 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.35/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.52  % Solved by: fo/fo7.sh
% 0.35/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.52  % done 69 iterations in 0.088s
% 0.35/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.52  % SZS output start Refutation
% 0.35/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.52  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.35/0.52  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.35/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.35/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.52  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.35/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.35/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.52  thf(t29_wellord1, conjecture,
% 0.35/0.52    (![A:$i,B:$i,C:$i]:
% 0.35/0.52     ( ( v1_relat_1 @ C ) =>
% 0.35/0.52       ( ( r1_tarski @ A @ B ) =>
% 0.35/0.52         ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 0.35/0.52           ( k2_wellord1 @ C @ A ) ) ) ))).
% 0.35/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.35/0.52        ( ( v1_relat_1 @ C ) =>
% 0.35/0.52          ( ( r1_tarski @ A @ B ) =>
% 0.35/0.52            ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 0.35/0.52              ( k2_wellord1 @ C @ A ) ) ) ) )),
% 0.35/0.52    inference('cnf.neg', [status(esa)], [t29_wellord1])).
% 0.35/0.52  thf('0', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf(t17_wellord1, axiom,
% 0.35/0.52    (![A:$i,B:$i]:
% 0.35/0.52     ( ( v1_relat_1 @ B ) =>
% 0.35/0.52       ( ( k2_wellord1 @ B @ A ) = ( k7_relat_1 @ ( k8_relat_1 @ A @ B ) @ A ) ) ))).
% 0.35/0.52  thf('1', plain,
% 0.35/0.52      (![X17 : $i, X18 : $i]:
% 0.35/0.52         (((k2_wellord1 @ X18 @ X17)
% 0.35/0.52            = (k7_relat_1 @ (k8_relat_1 @ X17 @ X18) @ X17))
% 0.35/0.52          | ~ (v1_relat_1 @ X18))),
% 0.35/0.52      inference('cnf', [status(esa)], [t17_wellord1])).
% 0.35/0.52  thf(t87_relat_1, axiom,
% 0.35/0.52    (![A:$i,B:$i]:
% 0.35/0.52     ( ( v1_relat_1 @ B ) =>
% 0.35/0.52       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.35/0.52  thf('2', plain,
% 0.35/0.52      (![X11 : $i, X12 : $i]:
% 0.35/0.52         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X11 @ X12)) @ X12)
% 0.35/0.52          | ~ (v1_relat_1 @ X11))),
% 0.35/0.52      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.35/0.52  thf('3', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i]:
% 0.35/0.52         ((r1_tarski @ (k1_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X0)
% 0.35/0.52          | ~ (v1_relat_1 @ X1)
% 0.35/0.52          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ X1)))),
% 0.35/0.52      inference('sup+', [status(thm)], ['1', '2'])).
% 0.35/0.52  thf(dt_k8_relat_1, axiom,
% 0.35/0.52    (![A:$i,B:$i]:
% 0.35/0.52     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 0.35/0.52  thf('4', plain,
% 0.35/0.52      (![X5 : $i, X6 : $i]:
% 0.35/0.52         ((v1_relat_1 @ (k8_relat_1 @ X5 @ X6)) | ~ (v1_relat_1 @ X6))),
% 0.35/0.52      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.35/0.52  thf('5', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i]:
% 0.35/0.52         (~ (v1_relat_1 @ X1)
% 0.35/0.52          | (r1_tarski @ (k1_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X0))),
% 0.35/0.52      inference('clc', [status(thm)], ['3', '4'])).
% 0.35/0.52  thf(t1_xboole_1, axiom,
% 0.35/0.52    (![A:$i,B:$i,C:$i]:
% 0.35/0.52     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.35/0.52       ( r1_tarski @ A @ C ) ))).
% 0.35/0.52  thf('6', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.52         (~ (r1_tarski @ X0 @ X1)
% 0.35/0.52          | ~ (r1_tarski @ X1 @ X2)
% 0.35/0.52          | (r1_tarski @ X0 @ X2))),
% 0.35/0.52      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.35/0.52  thf('7', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.52         (~ (v1_relat_1 @ X1)
% 0.35/0.52          | (r1_tarski @ (k1_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X2)
% 0.35/0.52          | ~ (r1_tarski @ X0 @ X2))),
% 0.35/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.35/0.52  thf('8', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         ((r1_tarski @ (k1_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B)
% 0.35/0.52          | ~ (v1_relat_1 @ X0))),
% 0.35/0.52      inference('sup-', [status(thm)], ['0', '7'])).
% 0.35/0.52  thf(t97_relat_1, axiom,
% 0.35/0.52    (![A:$i,B:$i]:
% 0.35/0.52     ( ( v1_relat_1 @ B ) =>
% 0.35/0.52       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.35/0.52         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.35/0.52  thf('9', plain,
% 0.35/0.52      (![X13 : $i, X14 : $i]:
% 0.35/0.52         (~ (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 0.35/0.52          | ((k7_relat_1 @ X13 @ X14) = (X13))
% 0.35/0.52          | ~ (v1_relat_1 @ X13))),
% 0.35/0.52      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.35/0.52  thf('10', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         (~ (v1_relat_1 @ X0)
% 0.35/0.52          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A))
% 0.35/0.52          | ((k7_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)
% 0.35/0.52              = (k2_wellord1 @ X0 @ sk_A)))),
% 0.35/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.35/0.52  thf(dt_k2_wellord1, axiom,
% 0.35/0.52    (![A:$i,B:$i]:
% 0.35/0.52     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k2_wellord1 @ A @ B ) ) ))).
% 0.35/0.52  thf('11', plain,
% 0.35/0.52      (![X15 : $i, X16 : $i]:
% 0.35/0.52         (~ (v1_relat_1 @ X15) | (v1_relat_1 @ (k2_wellord1 @ X15 @ X16)))),
% 0.35/0.52      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.35/0.52  thf('12', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         (((k7_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)
% 0.35/0.52            = (k2_wellord1 @ X0 @ sk_A))
% 0.35/0.52          | ~ (v1_relat_1 @ X0))),
% 0.35/0.52      inference('clc', [status(thm)], ['10', '11'])).
% 0.35/0.52  thf(t27_wellord1, axiom,
% 0.35/0.52    (![A:$i,B:$i,C:$i]:
% 0.35/0.52     ( ( v1_relat_1 @ C ) =>
% 0.35/0.52       ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 0.35/0.52         ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ))).
% 0.35/0.52  thf('13', plain,
% 0.35/0.52      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.35/0.52         (((k2_wellord1 @ (k2_wellord1 @ X21 @ X23) @ X22)
% 0.35/0.52            = (k2_wellord1 @ (k2_wellord1 @ X21 @ X22) @ X23))
% 0.35/0.52          | ~ (v1_relat_1 @ X21))),
% 0.35/0.53      inference('cnf', [status(esa)], [t27_wellord1])).
% 0.35/0.53  thf('14', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(t18_wellord1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( v1_relat_1 @ B ) =>
% 0.35/0.53       ( ( k2_wellord1 @ B @ A ) = ( k8_relat_1 @ A @ ( k7_relat_1 @ B @ A ) ) ) ))).
% 0.35/0.53  thf('15', plain,
% 0.35/0.53      (![X19 : $i, X20 : $i]:
% 0.35/0.53         (((k2_wellord1 @ X20 @ X19)
% 0.35/0.53            = (k8_relat_1 @ X19 @ (k7_relat_1 @ X20 @ X19)))
% 0.35/0.53          | ~ (v1_relat_1 @ X20))),
% 0.35/0.53      inference('cnf', [status(esa)], [t18_wellord1])).
% 0.35/0.53  thf(t116_relat_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( v1_relat_1 @ B ) =>
% 0.35/0.53       ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ A ) ))).
% 0.35/0.53  thf('16', plain,
% 0.35/0.53      (![X7 : $i, X8 : $i]:
% 0.35/0.53         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X7 @ X8)) @ X7)
% 0.35/0.53          | ~ (v1_relat_1 @ X8))),
% 0.35/0.53      inference('cnf', [status(esa)], [t116_relat_1])).
% 0.35/0.53  thf('17', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         ((r1_tarski @ (k2_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X0)
% 0.35/0.53          | ~ (v1_relat_1 @ X1)
% 0.35/0.53          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.35/0.53      inference('sup+', [status(thm)], ['15', '16'])).
% 0.35/0.53  thf(dt_k7_relat_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.35/0.53  thf('18', plain,
% 0.35/0.53      (![X3 : $i, X4 : $i]:
% 0.35/0.53         (~ (v1_relat_1 @ X3) | (v1_relat_1 @ (k7_relat_1 @ X3 @ X4)))),
% 0.35/0.53      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.35/0.53  thf('19', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         (~ (v1_relat_1 @ X1)
% 0.35/0.53          | (r1_tarski @ (k2_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X0))),
% 0.35/0.53      inference('clc', [status(thm)], ['17', '18'])).
% 0.35/0.53  thf('20', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.53         (~ (r1_tarski @ X0 @ X1)
% 0.35/0.53          | ~ (r1_tarski @ X1 @ X2)
% 0.35/0.53          | (r1_tarski @ X0 @ X2))),
% 0.35/0.53      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.35/0.53  thf('21', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.53         (~ (v1_relat_1 @ X1)
% 0.35/0.53          | (r1_tarski @ (k2_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X2)
% 0.35/0.53          | ~ (r1_tarski @ X0 @ X2))),
% 0.35/0.53      inference('sup-', [status(thm)], ['19', '20'])).
% 0.35/0.53  thf('22', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((r1_tarski @ (k2_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B)
% 0.35/0.53          | ~ (v1_relat_1 @ X0))),
% 0.35/0.53      inference('sup-', [status(thm)], ['14', '21'])).
% 0.35/0.53  thf(t125_relat_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( v1_relat_1 @ B ) =>
% 0.35/0.53       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.35/0.53         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.35/0.53  thf('23', plain,
% 0.35/0.53      (![X9 : $i, X10 : $i]:
% 0.35/0.53         (~ (r1_tarski @ (k2_relat_1 @ X9) @ X10)
% 0.35/0.53          | ((k8_relat_1 @ X10 @ X9) = (X9))
% 0.35/0.53          | ~ (v1_relat_1 @ X9))),
% 0.35/0.53      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.35/0.53  thf('24', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (~ (v1_relat_1 @ X0)
% 0.35/0.53          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A))
% 0.35/0.53          | ((k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A))
% 0.35/0.53              = (k2_wellord1 @ X0 @ sk_A)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['22', '23'])).
% 0.35/0.53  thf('25', plain,
% 0.35/0.53      (![X15 : $i, X16 : $i]:
% 0.35/0.53         (~ (v1_relat_1 @ X15) | (v1_relat_1 @ (k2_wellord1 @ X15 @ X16)))),
% 0.35/0.53      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.35/0.53  thf('26', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (((k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A))
% 0.35/0.53            = (k2_wellord1 @ X0 @ sk_A))
% 0.35/0.53          | ~ (v1_relat_1 @ X0))),
% 0.35/0.53      inference('clc', [status(thm)], ['24', '25'])).
% 0.35/0.53  thf('27', plain,
% 0.35/0.53      (![X17 : $i, X18 : $i]:
% 0.35/0.53         (((k2_wellord1 @ X18 @ X17)
% 0.35/0.53            = (k7_relat_1 @ (k8_relat_1 @ X17 @ X18) @ X17))
% 0.35/0.53          | ~ (v1_relat_1 @ X18))),
% 0.35/0.53      inference('cnf', [status(esa)], [t17_wellord1])).
% 0.35/0.53  thf('28', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)
% 0.35/0.53            = (k7_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B))
% 0.35/0.53          | ~ (v1_relat_1 @ X0)
% 0.35/0.53          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A)))),
% 0.35/0.53      inference('sup+', [status(thm)], ['26', '27'])).
% 0.35/0.53  thf('29', plain,
% 0.35/0.53      (![X15 : $i, X16 : $i]:
% 0.35/0.53         (~ (v1_relat_1 @ X15) | (v1_relat_1 @ (k2_wellord1 @ X15 @ X16)))),
% 0.35/0.53      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.35/0.53  thf('30', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (~ (v1_relat_1 @ X0)
% 0.35/0.53          | ((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)
% 0.35/0.53              = (k7_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)))),
% 0.35/0.53      inference('clc', [status(thm)], ['28', '29'])).
% 0.35/0.53  thf('31', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_B) @ sk_A)
% 0.35/0.53            = (k7_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B))
% 0.35/0.53          | ~ (v1_relat_1 @ X0)
% 0.35/0.53          | ~ (v1_relat_1 @ X0))),
% 0.35/0.53      inference('sup+', [status(thm)], ['13', '30'])).
% 0.35/0.53  thf('32', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (~ (v1_relat_1 @ X0)
% 0.35/0.53          | ((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_B) @ sk_A)
% 0.35/0.53              = (k7_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)))),
% 0.35/0.53      inference('simplify', [status(thm)], ['31'])).
% 0.35/0.53  thf('33', plain,
% 0.35/0.53      (((k2_wellord1 @ (k2_wellord1 @ sk_C @ sk_B) @ sk_A)
% 0.35/0.53         != (k2_wellord1 @ sk_C @ sk_A))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('34', plain,
% 0.35/0.53      ((((k7_relat_1 @ (k2_wellord1 @ sk_C @ sk_A) @ sk_B)
% 0.35/0.53          != (k2_wellord1 @ sk_C @ sk_A))
% 0.35/0.53        | ~ (v1_relat_1 @ sk_C))),
% 0.35/0.53      inference('sup-', [status(thm)], ['32', '33'])).
% 0.35/0.53  thf('35', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('36', plain,
% 0.35/0.53      (((k7_relat_1 @ (k2_wellord1 @ sk_C @ sk_A) @ sk_B)
% 0.35/0.53         != (k2_wellord1 @ sk_C @ sk_A))),
% 0.35/0.53      inference('demod', [status(thm)], ['34', '35'])).
% 0.35/0.53  thf('37', plain,
% 0.35/0.53      ((((k2_wellord1 @ sk_C @ sk_A) != (k2_wellord1 @ sk_C @ sk_A))
% 0.35/0.53        | ~ (v1_relat_1 @ sk_C))),
% 0.35/0.53      inference('sup-', [status(thm)], ['12', '36'])).
% 0.35/0.53  thf('38', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('39', plain,
% 0.35/0.53      (((k2_wellord1 @ sk_C @ sk_A) != (k2_wellord1 @ sk_C @ sk_A))),
% 0.35/0.53      inference('demod', [status(thm)], ['37', '38'])).
% 0.35/0.53  thf('40', plain, ($false), inference('simplify', [status(thm)], ['39'])).
% 0.35/0.53  
% 0.35/0.53  % SZS output end Refutation
% 0.35/0.53  
% 0.35/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

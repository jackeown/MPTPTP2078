%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HPp04YWWnK

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:33 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   61 (  66 expanded)
%              Number of leaves         :   27 (  31 expanded)
%              Depth                    :   11
%              Number of atoms          :  449 ( 495 expanded)
%              Number of equality atoms :   41 (  46 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t89_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ) )).

thf('0',plain,(
    ! [X48: $i,X49: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X48 @ X49 ) ) @ ( k1_relat_1 @ X48 ) )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t89_relat_1])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('1',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X50 ) @ X51 )
      | ( ( k7_relat_1 @ X50 @ X51 )
        = X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
        = ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( v1_relat_1 @ X43 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X43 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['2','3'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('5',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X45 @ X46 ) @ X47 )
        = ( k7_relat_1 @ X45 @ ( k3_xboole_0 @ X46 @ X47 ) ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X1 @ X0 )
        = ( k7_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = ( k7_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ X1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t192_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( k7_relat_1 @ B @ A )
          = ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t192_relat_1])).

thf('8',plain,(
    ( k7_relat_1 @ sk_B @ sk_A )
 != ( k7_relat_1 @ sk_B @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('9',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k3_enumset1 @ X17 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_enumset1 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k1_enumset1 @ X12 @ X12 @ X13 )
      = ( k2_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('11',plain,(
    ! [X11: $i] :
      ( ( k2_tarski @ X11 @ X11 )
      = ( k1_tarski @ X11 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t48_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k3_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_xboole_0 @ ( k2_tarski @ X6 @ X7 ) @ ( k1_enumset1 @ X8 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t48_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X1 @ X0 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('16',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k2_enumset1 @ X14 @ X14 @ X15 @ X16 )
      = ( k1_enumset1 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t123_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ D @ B @ C @ A ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X1 @ X2 @ X0 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t123_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X11: $i] :
      ( ( k2_tarski @ X11 @ X11 )
      = ( k1_tarski @ X11 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('20',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_tarski @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k1_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','18','19','20'])).

thf('22',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k1_enumset1 @ X12 @ X12 @ X13 )
      = ( k2_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ( k7_relat_1 @ sk_B @ sk_A )
 != ( k7_relat_1 @ sk_B @ ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['8','27'])).

thf('29',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
     != ( k7_relat_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['7','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ( k7_relat_1 @ sk_B @ sk_A )
 != ( k7_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    $false ),
    inference(simplify,[status(thm)],['31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HPp04YWWnK
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:28:18 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.54/0.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.54/0.73  % Solved by: fo/fo7.sh
% 0.54/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.73  % done 405 iterations in 0.281s
% 0.54/0.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.54/0.73  % SZS output start Refutation
% 0.54/0.73  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.54/0.73  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.54/0.73  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.54/0.73  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.54/0.73  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.54/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.73  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.54/0.73  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.54/0.73  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.54/0.73  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.54/0.73  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.54/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.73  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.54/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.73  thf(t89_relat_1, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( v1_relat_1 @ B ) =>
% 0.54/0.73       ( r1_tarski @
% 0.54/0.73         ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ))).
% 0.54/0.73  thf('0', plain,
% 0.54/0.73      (![X48 : $i, X49 : $i]:
% 0.54/0.73         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X48 @ X49)) @ 
% 0.54/0.73           (k1_relat_1 @ X48))
% 0.54/0.73          | ~ (v1_relat_1 @ X48))),
% 0.54/0.73      inference('cnf', [status(esa)], [t89_relat_1])).
% 0.54/0.73  thf(t97_relat_1, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( v1_relat_1 @ B ) =>
% 0.54/0.73       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.54/0.73         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.54/0.73  thf('1', plain,
% 0.54/0.73      (![X50 : $i, X51 : $i]:
% 0.54/0.73         (~ (r1_tarski @ (k1_relat_1 @ X50) @ X51)
% 0.54/0.73          | ((k7_relat_1 @ X50 @ X51) = (X50))
% 0.54/0.73          | ~ (v1_relat_1 @ X50))),
% 0.54/0.73      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.54/0.73  thf('2', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         (~ (v1_relat_1 @ X0)
% 0.54/0.73          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.54/0.73          | ((k7_relat_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.54/0.73              = (k7_relat_1 @ X0 @ X1)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['0', '1'])).
% 0.54/0.73  thf(dt_k7_relat_1, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.54/0.73  thf('3', plain,
% 0.54/0.73      (![X43 : $i, X44 : $i]:
% 0.54/0.73         (~ (v1_relat_1 @ X43) | (v1_relat_1 @ (k7_relat_1 @ X43 @ X44)))),
% 0.54/0.73      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.54/0.73  thf('4', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         (((k7_relat_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.54/0.73            = (k7_relat_1 @ X0 @ X1))
% 0.54/0.73          | ~ (v1_relat_1 @ X0))),
% 0.54/0.73      inference('clc', [status(thm)], ['2', '3'])).
% 0.54/0.73  thf(t100_relat_1, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i]:
% 0.54/0.73     ( ( v1_relat_1 @ C ) =>
% 0.54/0.73       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.54/0.73         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.54/0.73  thf('5', plain,
% 0.54/0.73      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.54/0.73         (((k7_relat_1 @ (k7_relat_1 @ X45 @ X46) @ X47)
% 0.54/0.73            = (k7_relat_1 @ X45 @ (k3_xboole_0 @ X46 @ X47)))
% 0.54/0.73          | ~ (v1_relat_1 @ X45))),
% 0.54/0.73      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.54/0.73  thf('6', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         (((k7_relat_1 @ X1 @ X0)
% 0.54/0.73            = (k7_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ (k1_relat_1 @ X1))))
% 0.54/0.73          | ~ (v1_relat_1 @ X1)
% 0.54/0.73          | ~ (v1_relat_1 @ X1))),
% 0.54/0.73      inference('sup+', [status(thm)], ['4', '5'])).
% 0.54/0.73  thf('7', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         (~ (v1_relat_1 @ X1)
% 0.54/0.73          | ((k7_relat_1 @ X1 @ X0)
% 0.54/0.73              = (k7_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ (k1_relat_1 @ X1)))))),
% 0.54/0.73      inference('simplify', [status(thm)], ['6'])).
% 0.54/0.73  thf(t192_relat_1, conjecture,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( v1_relat_1 @ B ) =>
% 0.54/0.73       ( ( k7_relat_1 @ B @ A ) =
% 0.54/0.73         ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 0.54/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.73    (~( ![A:$i,B:$i]:
% 0.54/0.73        ( ( v1_relat_1 @ B ) =>
% 0.54/0.73          ( ( k7_relat_1 @ B @ A ) =
% 0.54/0.73            ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )),
% 0.54/0.73    inference('cnf.neg', [status(esa)], [t192_relat_1])).
% 0.54/0.73  thf('8', plain,
% 0.54/0.73      (((k7_relat_1 @ sk_B @ sk_A)
% 0.54/0.73         != (k7_relat_1 @ sk_B @ (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf(t72_enumset1, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.73     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.54/0.73  thf('9', plain,
% 0.54/0.73      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.54/0.73         ((k3_enumset1 @ X17 @ X17 @ X18 @ X19 @ X20)
% 0.54/0.73           = (k2_enumset1 @ X17 @ X18 @ X19 @ X20))),
% 0.54/0.73      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.54/0.73  thf(t70_enumset1, axiom,
% 0.54/0.73    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.54/0.73  thf('10', plain,
% 0.54/0.73      (![X12 : $i, X13 : $i]:
% 0.54/0.73         ((k1_enumset1 @ X12 @ X12 @ X13) = (k2_tarski @ X12 @ X13))),
% 0.54/0.73      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.54/0.73  thf(t69_enumset1, axiom,
% 0.54/0.73    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.54/0.73  thf('11', plain,
% 0.54/0.73      (![X11 : $i]: ((k2_tarski @ X11 @ X11) = (k1_tarski @ X11))),
% 0.54/0.73      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.54/0.73  thf('12', plain,
% 0.54/0.73      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.54/0.73      inference('sup+', [status(thm)], ['10', '11'])).
% 0.54/0.73  thf(t48_enumset1, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.54/0.73     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.54/0.73       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ))).
% 0.54/0.73  thf('13', plain,
% 0.54/0.73      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.54/0.73         ((k3_enumset1 @ X6 @ X7 @ X8 @ X9 @ X10)
% 0.54/0.73           = (k2_xboole_0 @ (k2_tarski @ X6 @ X7) @ 
% 0.54/0.73              (k1_enumset1 @ X8 @ X9 @ X10)))),
% 0.54/0.73      inference('cnf', [status(esa)], [t48_enumset1])).
% 0.54/0.73  thf('14', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.73         ((k3_enumset1 @ X2 @ X1 @ X0 @ X0 @ X0)
% 0.54/0.73           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)))),
% 0.54/0.73      inference('sup+', [status(thm)], ['12', '13'])).
% 0.54/0.73  thf('15', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         ((k2_enumset1 @ X1 @ X0 @ X0 @ X0)
% 0.54/0.73           = (k2_xboole_0 @ (k2_tarski @ X1 @ X1) @ (k1_tarski @ X0)))),
% 0.54/0.73      inference('sup+', [status(thm)], ['9', '14'])).
% 0.54/0.73  thf(t71_enumset1, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i]:
% 0.54/0.73     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.54/0.73  thf('16', plain,
% 0.54/0.73      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.54/0.73         ((k2_enumset1 @ X14 @ X14 @ X15 @ X16)
% 0.54/0.73           = (k1_enumset1 @ X14 @ X15 @ X16))),
% 0.54/0.73      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.54/0.73  thf(t123_enumset1, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.73     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ D @ B @ C @ A ) ))).
% 0.54/0.73  thf('17', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.54/0.73         ((k2_enumset1 @ X3 @ X1 @ X2 @ X0) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.54/0.73      inference('cnf', [status(esa)], [t123_enumset1])).
% 0.54/0.73  thf('18', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.73         ((k2_enumset1 @ X0 @ X2 @ X1 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.54/0.73      inference('sup+', [status(thm)], ['16', '17'])).
% 0.54/0.73  thf('19', plain,
% 0.54/0.73      (![X11 : $i]: ((k2_tarski @ X11 @ X11) = (k1_tarski @ X11))),
% 0.54/0.73      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.54/0.73  thf(t41_enumset1, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( k2_tarski @ A @ B ) =
% 0.54/0.73       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.54/0.73  thf('20', plain,
% 0.54/0.73      (![X4 : $i, X5 : $i]:
% 0.54/0.73         ((k2_tarski @ X4 @ X5)
% 0.54/0.73           = (k2_xboole_0 @ (k1_tarski @ X4) @ (k1_tarski @ X5)))),
% 0.54/0.73      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.54/0.73  thf('21', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         ((k1_enumset1 @ X0 @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 0.54/0.73      inference('demod', [status(thm)], ['15', '18', '19', '20'])).
% 0.54/0.73  thf('22', plain,
% 0.54/0.73      (![X12 : $i, X13 : $i]:
% 0.54/0.73         ((k1_enumset1 @ X12 @ X12 @ X13) = (k2_tarski @ X12 @ X13))),
% 0.54/0.73      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.54/0.73  thf(t12_setfam_1, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.54/0.73  thf('23', plain,
% 0.54/0.73      (![X41 : $i, X42 : $i]:
% 0.54/0.73         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 0.54/0.73      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.54/0.73  thf('24', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         ((k1_setfam_1 @ (k1_enumset1 @ X1 @ X1 @ X0))
% 0.54/0.73           = (k3_xboole_0 @ X1 @ X0))),
% 0.54/0.73      inference('sup+', [status(thm)], ['22', '23'])).
% 0.54/0.73  thf('25', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.54/0.73      inference('sup+', [status(thm)], ['21', '24'])).
% 0.54/0.73  thf('26', plain,
% 0.54/0.73      (![X41 : $i, X42 : $i]:
% 0.54/0.73         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 0.54/0.73      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.54/0.73  thf('27', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.54/0.73      inference('sup+', [status(thm)], ['25', '26'])).
% 0.54/0.73  thf('28', plain,
% 0.54/0.73      (((k7_relat_1 @ sk_B @ sk_A)
% 0.54/0.73         != (k7_relat_1 @ sk_B @ (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.54/0.73      inference('demod', [status(thm)], ['8', '27'])).
% 0.54/0.73  thf('29', plain,
% 0.54/0.73      ((((k7_relat_1 @ sk_B @ sk_A) != (k7_relat_1 @ sk_B @ sk_A))
% 0.54/0.73        | ~ (v1_relat_1 @ sk_B))),
% 0.54/0.73      inference('sup-', [status(thm)], ['7', '28'])).
% 0.54/0.73  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('31', plain,
% 0.54/0.73      (((k7_relat_1 @ sk_B @ sk_A) != (k7_relat_1 @ sk_B @ sk_A))),
% 0.54/0.73      inference('demod', [status(thm)], ['29', '30'])).
% 0.54/0.73  thf('32', plain, ($false), inference('simplify', [status(thm)], ['31'])).
% 0.54/0.73  
% 0.54/0.73  % SZS output end Refutation
% 0.54/0.73  
% 0.54/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

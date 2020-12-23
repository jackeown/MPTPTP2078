%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GoCyt8Jxwc

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:45 EST 2020

% Result     : Theorem 0.57s
% Output     : Refutation 0.57s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 179 expanded)
%              Number of leaves         :   26 (  65 expanded)
%              Depth                    :   12
%              Number of atoms          :  458 (1273 expanded)
%              Number of equality atoms :   62 ( 179 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X21: $i] :
      ( ( k2_tarski @ X21 @ X21 )
      = ( k1_tarski @ X21 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k1_enumset1 @ X22 @ X22 @ X23 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k2_enumset1 @ X12 @ X13 @ X14 @ X15 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X12 @ X13 @ X14 ) @ ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('4',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k2_enumset1 @ X24 @ X24 @ X25 @ X26 )
      = ( k1_enumset1 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('5',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k1_enumset1 @ X22 @ X22 @ X23 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','7'])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('9',plain,(
    ! [X33: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X33 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf(t10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) )
         != ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) )).

thf('10',plain,(
    ! [X31: $i,X32: $i] :
      ( ( X31 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( k2_xboole_0 @ X31 @ X32 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X31 ) @ ( k1_setfam_1 @ X32 ) ) )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t10_setfam_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X1 ) @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ ( k1_tarski @ X1 ) ) @ X0 ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X33: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X33 ) )
      = X33 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t12_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
        = ( k3_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_setfam_1])).

thf('15',plain,(
    ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
     != ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t16_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        & ( A = B ) ) )).

thf('18',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X29 ) @ ( k1_tarski @ X30 ) )
      | ( X29 != X30 ) ) ),
    inference(cnf,[status(esa)],[t16_zfmisc_1])).

thf('19',plain,(
    ! [X30: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X30 ) @ ( k1_tarski @ X30 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ~ ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('22',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) )
      = ( k4_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('26',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('30',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['25','30'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('32',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_xboole_0 @ X9 @ X11 )
      | ( ( k4_xboole_0 @ X9 @ X11 )
       != X9 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['33'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('35',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['20','36'])).

thf('38',plain,(
    ! [X30: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X30 ) @ ( k1_tarski @ X30 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('39',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['20','36'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['39','40','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GoCyt8Jxwc
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:38:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.57/0.76  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.57/0.76  % Solved by: fo/fo7.sh
% 0.57/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.57/0.76  % done 580 iterations in 0.291s
% 0.57/0.76  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.57/0.76  % SZS output start Refutation
% 0.57/0.76  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.57/0.76  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.57/0.76  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.57/0.76  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.57/0.76  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.57/0.76  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.57/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.57/0.76  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.57/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.57/0.76  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.57/0.76  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.57/0.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.57/0.76  thf(t69_enumset1, axiom,
% 0.57/0.76    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.57/0.76  thf('0', plain, (![X21 : $i]: ((k2_tarski @ X21 @ X21) = (k1_tarski @ X21))),
% 0.57/0.76      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.57/0.76  thf(t70_enumset1, axiom,
% 0.57/0.76    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.57/0.76  thf('1', plain,
% 0.57/0.76      (![X22 : $i, X23 : $i]:
% 0.57/0.76         ((k1_enumset1 @ X22 @ X22 @ X23) = (k2_tarski @ X22 @ X23))),
% 0.57/0.76      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.57/0.76  thf(t46_enumset1, axiom,
% 0.57/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.57/0.76     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.57/0.76       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.57/0.76  thf('2', plain,
% 0.57/0.76      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.57/0.76         ((k2_enumset1 @ X12 @ X13 @ X14 @ X15)
% 0.57/0.76           = (k2_xboole_0 @ (k1_enumset1 @ X12 @ X13 @ X14) @ (k1_tarski @ X15)))),
% 0.57/0.76      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.57/0.76  thf('3', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.76         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.57/0.76           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.57/0.76      inference('sup+', [status(thm)], ['1', '2'])).
% 0.57/0.76  thf(t71_enumset1, axiom,
% 0.57/0.76    (![A:$i,B:$i,C:$i]:
% 0.57/0.76     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.57/0.76  thf('4', plain,
% 0.57/0.76      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.57/0.76         ((k2_enumset1 @ X24 @ X24 @ X25 @ X26)
% 0.57/0.76           = (k1_enumset1 @ X24 @ X25 @ X26))),
% 0.57/0.76      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.57/0.76  thf('5', plain,
% 0.57/0.76      (![X22 : $i, X23 : $i]:
% 0.57/0.76         ((k1_enumset1 @ X22 @ X22 @ X23) = (k2_tarski @ X22 @ X23))),
% 0.57/0.76      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.57/0.76  thf('6', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i]:
% 0.57/0.76         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.57/0.76      inference('sup+', [status(thm)], ['4', '5'])).
% 0.57/0.76  thf('7', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i]:
% 0.57/0.76         ((k2_xboole_0 @ (k2_tarski @ X1 @ X1) @ (k1_tarski @ X0))
% 0.57/0.76           = (k2_tarski @ X1 @ X0))),
% 0.57/0.76      inference('sup+', [status(thm)], ['3', '6'])).
% 0.57/0.76  thf('8', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i]:
% 0.57/0.76         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.57/0.76           = (k2_tarski @ X0 @ X1))),
% 0.57/0.76      inference('sup+', [status(thm)], ['0', '7'])).
% 0.57/0.76  thf(t11_setfam_1, axiom,
% 0.57/0.76    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.57/0.76  thf('9', plain, (![X33 : $i]: ((k1_setfam_1 @ (k1_tarski @ X33)) = (X33))),
% 0.57/0.76      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.57/0.76  thf(t10_setfam_1, axiom,
% 0.57/0.76    (![A:$i,B:$i]:
% 0.57/0.76     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.57/0.76          ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) ) !=
% 0.57/0.76            ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) ))).
% 0.57/0.76  thf('10', plain,
% 0.57/0.76      (![X31 : $i, X32 : $i]:
% 0.57/0.76         (((X31) = (k1_xboole_0))
% 0.57/0.76          | ((k1_setfam_1 @ (k2_xboole_0 @ X31 @ X32))
% 0.57/0.76              = (k3_xboole_0 @ (k1_setfam_1 @ X31) @ (k1_setfam_1 @ X32)))
% 0.57/0.76          | ((X32) = (k1_xboole_0)))),
% 0.57/0.76      inference('cnf', [status(esa)], [t10_setfam_1])).
% 0.57/0.76  thf('11', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i]:
% 0.57/0.76         (((k1_setfam_1 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.57/0.76            = (k3_xboole_0 @ (k1_setfam_1 @ X1) @ X0))
% 0.57/0.76          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.57/0.76          | ((X1) = (k1_xboole_0)))),
% 0.57/0.76      inference('sup+', [status(thm)], ['9', '10'])).
% 0.57/0.76  thf('12', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i]:
% 0.57/0.76         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.57/0.76            = (k3_xboole_0 @ (k1_setfam_1 @ (k1_tarski @ X1)) @ X0))
% 0.57/0.76          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.57/0.76          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.57/0.76      inference('sup+', [status(thm)], ['8', '11'])).
% 0.57/0.76  thf('13', plain, (![X33 : $i]: ((k1_setfam_1 @ (k1_tarski @ X33)) = (X33))),
% 0.57/0.76      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.57/0.76  thf('14', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i]:
% 0.57/0.76         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))
% 0.57/0.76          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.57/0.76          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.57/0.76      inference('demod', [status(thm)], ['12', '13'])).
% 0.57/0.76  thf(t12_setfam_1, conjecture,
% 0.57/0.76    (![A:$i,B:$i]:
% 0.57/0.76     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.57/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.57/0.76    (~( ![A:$i,B:$i]:
% 0.57/0.76        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ) )),
% 0.57/0.76    inference('cnf.neg', [status(esa)], [t12_setfam_1])).
% 0.57/0.76  thf('15', plain,
% 0.57/0.76      (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.57/0.76         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.57/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.76  thf('16', plain,
% 0.57/0.76      ((((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))
% 0.57/0.76        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.57/0.76        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.57/0.76      inference('sup-', [status(thm)], ['14', '15'])).
% 0.57/0.76  thf('17', plain,
% 0.57/0.76      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.57/0.76        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.57/0.76      inference('simplify', [status(thm)], ['16'])).
% 0.57/0.76  thf(t16_zfmisc_1, axiom,
% 0.57/0.76    (![A:$i,B:$i]:
% 0.57/0.76     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) & 
% 0.57/0.76          ( ( A ) = ( B ) ) ) ))).
% 0.57/0.76  thf('18', plain,
% 0.57/0.76      (![X29 : $i, X30 : $i]:
% 0.57/0.76         (~ (r1_xboole_0 @ (k1_tarski @ X29) @ (k1_tarski @ X30))
% 0.57/0.76          | ((X29) != (X30)))),
% 0.57/0.76      inference('cnf', [status(esa)], [t16_zfmisc_1])).
% 0.57/0.76  thf('19', plain,
% 0.57/0.76      (![X30 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X30) @ (k1_tarski @ X30))),
% 0.57/0.76      inference('simplify', [status(thm)], ['18'])).
% 0.57/0.76  thf('20', plain,
% 0.57/0.76      ((~ (r1_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0)
% 0.57/0.76        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.57/0.76      inference('sup-', [status(thm)], ['17', '19'])).
% 0.57/0.76  thf(commutativity_k3_xboole_0, axiom,
% 0.57/0.76    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.57/0.76  thf('21', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.57/0.76      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.57/0.76  thf(t2_boole, axiom,
% 0.57/0.76    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.57/0.76  thf('22', plain,
% 0.57/0.76      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.57/0.76      inference('cnf', [status(esa)], [t2_boole])).
% 0.57/0.76  thf('23', plain,
% 0.57/0.76      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.57/0.76      inference('sup+', [status(thm)], ['21', '22'])).
% 0.57/0.76  thf(t47_xboole_1, axiom,
% 0.57/0.76    (![A:$i,B:$i]:
% 0.57/0.76     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.57/0.76  thf('24', plain,
% 0.57/0.76      (![X5 : $i, X6 : $i]:
% 0.57/0.76         ((k4_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6))
% 0.57/0.76           = (k4_xboole_0 @ X5 @ X6))),
% 0.57/0.76      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.57/0.76  thf('25', plain,
% 0.57/0.76      (![X0 : $i]:
% 0.57/0.76         ((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.57/0.76           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.57/0.76      inference('sup+', [status(thm)], ['23', '24'])).
% 0.57/0.76  thf(t48_xboole_1, axiom,
% 0.57/0.76    (![A:$i,B:$i]:
% 0.57/0.76     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.57/0.76  thf('26', plain,
% 0.57/0.76      (![X7 : $i, X8 : $i]:
% 0.57/0.76         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.57/0.76           = (k3_xboole_0 @ X7 @ X8))),
% 0.57/0.76      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.57/0.76  thf('27', plain,
% 0.57/0.76      (![X0 : $i]:
% 0.57/0.76         ((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.57/0.76           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.57/0.76      inference('sup+', [status(thm)], ['23', '24'])).
% 0.57/0.76  thf('28', plain,
% 0.57/0.76      (![X0 : $i]:
% 0.57/0.76         ((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.57/0.76           = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.57/0.76      inference('sup+', [status(thm)], ['26', '27'])).
% 0.57/0.76  thf('29', plain,
% 0.57/0.76      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.57/0.76      inference('sup+', [status(thm)], ['21', '22'])).
% 0.57/0.76  thf('30', plain,
% 0.57/0.76      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.57/0.76      inference('demod', [status(thm)], ['28', '29'])).
% 0.57/0.76  thf('31', plain,
% 0.57/0.76      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.57/0.76      inference('demod', [status(thm)], ['25', '30'])).
% 0.57/0.76  thf(t83_xboole_1, axiom,
% 0.57/0.76    (![A:$i,B:$i]:
% 0.57/0.76     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.57/0.76  thf('32', plain,
% 0.57/0.76      (![X9 : $i, X11 : $i]:
% 0.57/0.76         ((r1_xboole_0 @ X9 @ X11) | ((k4_xboole_0 @ X9 @ X11) != (X9)))),
% 0.57/0.76      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.57/0.76  thf('33', plain,
% 0.57/0.76      (![X0 : $i]:
% 0.57/0.76         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.57/0.76      inference('sup-', [status(thm)], ['31', '32'])).
% 0.57/0.76  thf('34', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.57/0.76      inference('simplify', [status(thm)], ['33'])).
% 0.57/0.76  thf(symmetry_r1_xboole_0, axiom,
% 0.57/0.76    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.57/0.76  thf('35', plain,
% 0.57/0.76      (![X2 : $i, X3 : $i]:
% 0.57/0.76         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.57/0.76      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.57/0.76  thf('36', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.57/0.76      inference('sup-', [status(thm)], ['34', '35'])).
% 0.57/0.76  thf('37', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.57/0.76      inference('demod', [status(thm)], ['20', '36'])).
% 0.57/0.76  thf('38', plain,
% 0.57/0.76      (![X30 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X30) @ (k1_tarski @ X30))),
% 0.57/0.76      inference('simplify', [status(thm)], ['18'])).
% 0.57/0.76  thf('39', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0)),
% 0.57/0.76      inference('sup-', [status(thm)], ['37', '38'])).
% 0.57/0.76  thf('40', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.57/0.76      inference('demod', [status(thm)], ['20', '36'])).
% 0.57/0.76  thf('41', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.57/0.76      inference('simplify', [status(thm)], ['33'])).
% 0.57/0.76  thf('42', plain, ($false),
% 0.57/0.76      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.57/0.76  
% 0.57/0.76  % SZS output end Refutation
% 0.57/0.76  
% 0.60/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

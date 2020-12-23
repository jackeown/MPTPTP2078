%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Lxr5wpDCSp

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:50 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   60 (  77 expanded)
%              Number of leaves         :   23 (  33 expanded)
%              Depth                    :   12
%              Number of atoms          :  433 ( 560 expanded)
%              Number of equality atoms :   55 (  71 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t12_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
        = ( k3_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_setfam_1])).

thf('0',plain,(
    ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_enumset1 @ X15 @ X15 @ X16 )
      = ( k2_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k2_enumset1 @ X17 @ X17 @ X18 @ X19 )
      = ( k1_enumset1 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t50_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k3_enumset1 @ X3 @ X4 @ X5 @ X6 @ X7 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X4 @ X5 @ X6 ) @ ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_enumset1 @ X15 @ X15 @ X16 )
      = ( k2_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('6',plain,(
    ! [X14: $i] :
      ( ( k2_tarski @ X14 @ X14 )
      = ( k1_tarski @ X14 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('7',plain,(
    ! [X32: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X32 ) )
      = X32 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_enumset1 @ X0 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf(t10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) )
         != ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) )).

thf('10',plain,(
    ! [X30: $i,X31: $i] :
      ( ( X30 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( k2_xboole_0 @ X30 @ X31 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X30 ) @ ( k1_setfam_1 @ X31 ) ) )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t10_setfam_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_xboole_0 @ ( k1_enumset1 @ X0 @ X0 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ ( k1_setfam_1 @ X1 ) ) )
      | ( X1 = k1_xboole_0 )
      | ( ( k1_enumset1 @ X0 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_enumset1 @ X15 @ X15 @ X16 )
      = ( k2_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('13',plain,(
    ! [X14: $i] :
      ( ( k2_tarski @ X14 @ X14 )
      = ( k1_tarski @ X14 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X14: $i] :
      ( ( k2_tarski @ X14 @ X14 )
      = ( k1_tarski @ X14 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t19_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k1_tarski @ A ) ) )).

thf('16',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X28 ) @ ( k2_tarski @ X28 @ X29 ) )
      = ( k1_tarski @ X28 ) ) ),
    inference(cnf,[status(esa)],[t19_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('18',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t16_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        & ( A = B ) ) )).

thf('20',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X26 ) @ ( k1_tarski @ X27 ) )
      | ( X26 != X27 ) ) ),
    inference(cnf,[status(esa)],[t16_zfmisc_1])).

thf('21',plain,(
    ! [X27: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X27 ) @ ( k1_tarski @ X27 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_xboole_0 @ ( k1_enumset1 @ X0 @ X0 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ ( k1_setfam_1 @ X1 ) ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['11','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['4','24'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('26',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k3_enumset1 @ X20 @ X20 @ X21 @ X22 @ X23 )
      = ( k2_enumset1 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('27',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k2_enumset1 @ X17 @ X17 @ X18 @ X19 )
      = ( k1_enumset1 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X32: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X32 ) )
      = X32 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['25','28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['19','21'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','32'])).

thf('34',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','33'])).

thf('35',plain,(
    $false ),
    inference(simplify,[status(thm)],['34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Lxr5wpDCSp
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:45:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.36/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.52  % Solved by: fo/fo7.sh
% 0.36/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.52  % done 162 iterations in 0.075s
% 0.36/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.52  % SZS output start Refutation
% 0.36/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.52  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.36/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.36/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.52  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.36/0.52  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.36/0.52  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.36/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.52  thf(t12_setfam_1, conjecture,
% 0.36/0.52    (![A:$i,B:$i]:
% 0.36/0.52     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.36/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.52    (~( ![A:$i,B:$i]:
% 0.36/0.52        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ) )),
% 0.36/0.52    inference('cnf.neg', [status(esa)], [t12_setfam_1])).
% 0.36/0.52  thf('0', plain,
% 0.36/0.52      (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.36/0.52         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf(t70_enumset1, axiom,
% 0.36/0.52    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.36/0.52  thf('1', plain,
% 0.36/0.52      (![X15 : $i, X16 : $i]:
% 0.36/0.52         ((k1_enumset1 @ X15 @ X15 @ X16) = (k2_tarski @ X15 @ X16))),
% 0.36/0.52      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.36/0.52  thf(t71_enumset1, axiom,
% 0.36/0.52    (![A:$i,B:$i,C:$i]:
% 0.36/0.52     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.36/0.52  thf('2', plain,
% 0.36/0.52      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.36/0.52         ((k2_enumset1 @ X17 @ X17 @ X18 @ X19)
% 0.36/0.52           = (k1_enumset1 @ X17 @ X18 @ X19))),
% 0.36/0.52      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.36/0.52  thf(t50_enumset1, axiom,
% 0.36/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.36/0.52     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.36/0.52       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ))).
% 0.36/0.52  thf('3', plain,
% 0.36/0.52      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.36/0.52         ((k3_enumset1 @ X3 @ X4 @ X5 @ X6 @ X7)
% 0.36/0.52           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X4 @ X5 @ X6) @ 
% 0.36/0.52              (k1_tarski @ X7)))),
% 0.36/0.52      inference('cnf', [status(esa)], [t50_enumset1])).
% 0.36/0.52  thf('4', plain,
% 0.36/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.52         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3)
% 0.36/0.52           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 0.36/0.52      inference('sup+', [status(thm)], ['2', '3'])).
% 0.36/0.52  thf('5', plain,
% 0.36/0.52      (![X15 : $i, X16 : $i]:
% 0.36/0.52         ((k1_enumset1 @ X15 @ X15 @ X16) = (k2_tarski @ X15 @ X16))),
% 0.36/0.52      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.36/0.52  thf(t69_enumset1, axiom,
% 0.36/0.52    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.36/0.52  thf('6', plain, (![X14 : $i]: ((k2_tarski @ X14 @ X14) = (k1_tarski @ X14))),
% 0.36/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.52  thf(t11_setfam_1, axiom,
% 0.36/0.52    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.36/0.52  thf('7', plain, (![X32 : $i]: ((k1_setfam_1 @ (k1_tarski @ X32)) = (X32))),
% 0.36/0.52      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.36/0.52  thf('8', plain, (![X0 : $i]: ((k1_setfam_1 @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.36/0.52      inference('sup+', [status(thm)], ['6', '7'])).
% 0.36/0.52  thf('9', plain,
% 0.36/0.52      (![X0 : $i]: ((k1_setfam_1 @ (k1_enumset1 @ X0 @ X0 @ X0)) = (X0))),
% 0.36/0.52      inference('sup+', [status(thm)], ['5', '8'])).
% 0.36/0.52  thf(t10_setfam_1, axiom,
% 0.36/0.52    (![A:$i,B:$i]:
% 0.36/0.52     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.36/0.52          ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) ) !=
% 0.36/0.52            ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) ))).
% 0.36/0.52  thf('10', plain,
% 0.36/0.52      (![X30 : $i, X31 : $i]:
% 0.36/0.52         (((X30) = (k1_xboole_0))
% 0.36/0.52          | ((k1_setfam_1 @ (k2_xboole_0 @ X30 @ X31))
% 0.36/0.52              = (k3_xboole_0 @ (k1_setfam_1 @ X30) @ (k1_setfam_1 @ X31)))
% 0.36/0.52          | ((X31) = (k1_xboole_0)))),
% 0.36/0.52      inference('cnf', [status(esa)], [t10_setfam_1])).
% 0.36/0.52  thf('11', plain,
% 0.36/0.52      (![X0 : $i, X1 : $i]:
% 0.36/0.52         (((k1_setfam_1 @ (k2_xboole_0 @ (k1_enumset1 @ X0 @ X0 @ X0) @ X1))
% 0.36/0.52            = (k3_xboole_0 @ X0 @ (k1_setfam_1 @ X1)))
% 0.36/0.52          | ((X1) = (k1_xboole_0))
% 0.36/0.52          | ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_xboole_0)))),
% 0.36/0.52      inference('sup+', [status(thm)], ['9', '10'])).
% 0.36/0.52  thf('12', plain,
% 0.36/0.52      (![X15 : $i, X16 : $i]:
% 0.36/0.52         ((k1_enumset1 @ X15 @ X15 @ X16) = (k2_tarski @ X15 @ X16))),
% 0.36/0.52      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.36/0.52  thf('13', plain,
% 0.36/0.52      (![X14 : $i]: ((k2_tarski @ X14 @ X14) = (k1_tarski @ X14))),
% 0.36/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.52  thf('14', plain,
% 0.36/0.52      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.36/0.52      inference('sup+', [status(thm)], ['12', '13'])).
% 0.36/0.52  thf('15', plain,
% 0.36/0.52      (![X14 : $i]: ((k2_tarski @ X14 @ X14) = (k1_tarski @ X14))),
% 0.36/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.52  thf(t19_zfmisc_1, axiom,
% 0.36/0.52    (![A:$i,B:$i]:
% 0.36/0.52     ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.36/0.52       ( k1_tarski @ A ) ))).
% 0.36/0.52  thf('16', plain,
% 0.36/0.52      (![X28 : $i, X29 : $i]:
% 0.36/0.52         ((k3_xboole_0 @ (k1_tarski @ X28) @ (k2_tarski @ X28 @ X29))
% 0.36/0.52           = (k1_tarski @ X28))),
% 0.36/0.52      inference('cnf', [status(esa)], [t19_zfmisc_1])).
% 0.36/0.52  thf('17', plain,
% 0.36/0.52      (![X0 : $i]:
% 0.36/0.52         ((k3_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.36/0.52           = (k1_tarski @ X0))),
% 0.36/0.52      inference('sup+', [status(thm)], ['15', '16'])).
% 0.36/0.52  thf(d7_xboole_0, axiom,
% 0.36/0.52    (![A:$i,B:$i]:
% 0.36/0.52     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.36/0.52       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.36/0.52  thf('18', plain,
% 0.36/0.52      (![X0 : $i, X2 : $i]:
% 0.36/0.52         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.36/0.52      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.36/0.52  thf('19', plain,
% 0.36/0.52      (![X0 : $i]:
% 0.36/0.52         (((k1_tarski @ X0) != (k1_xboole_0))
% 0.36/0.52          | (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 0.36/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.36/0.52  thf(t16_zfmisc_1, axiom,
% 0.36/0.52    (![A:$i,B:$i]:
% 0.36/0.52     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) & 
% 0.36/0.52          ( ( A ) = ( B ) ) ) ))).
% 0.36/0.52  thf('20', plain,
% 0.36/0.52      (![X26 : $i, X27 : $i]:
% 0.36/0.52         (~ (r1_xboole_0 @ (k1_tarski @ X26) @ (k1_tarski @ X27))
% 0.36/0.52          | ((X26) != (X27)))),
% 0.36/0.52      inference('cnf', [status(esa)], [t16_zfmisc_1])).
% 0.36/0.52  thf('21', plain,
% 0.36/0.52      (![X27 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X27) @ (k1_tarski @ X27))),
% 0.36/0.52      inference('simplify', [status(thm)], ['20'])).
% 0.36/0.52  thf('22', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.36/0.52      inference('clc', [status(thm)], ['19', '21'])).
% 0.36/0.52  thf('23', plain,
% 0.36/0.52      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) != (k1_xboole_0))),
% 0.36/0.52      inference('sup-', [status(thm)], ['14', '22'])).
% 0.36/0.52  thf('24', plain,
% 0.36/0.52      (![X0 : $i, X1 : $i]:
% 0.36/0.52         (((k1_setfam_1 @ (k2_xboole_0 @ (k1_enumset1 @ X0 @ X0 @ X0) @ X1))
% 0.36/0.52            = (k3_xboole_0 @ X0 @ (k1_setfam_1 @ X1)))
% 0.36/0.52          | ((X1) = (k1_xboole_0)))),
% 0.36/0.52      inference('simplify_reflect-', [status(thm)], ['11', '23'])).
% 0.36/0.52  thf('25', plain,
% 0.36/0.52      (![X0 : $i, X1 : $i]:
% 0.36/0.52         (((k1_setfam_1 @ (k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0))
% 0.36/0.52            = (k3_xboole_0 @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0))))
% 0.36/0.52          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.36/0.52      inference('sup+', [status(thm)], ['4', '24'])).
% 0.36/0.52  thf(t72_enumset1, axiom,
% 0.36/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.52     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.36/0.52  thf('26', plain,
% 0.36/0.52      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.36/0.52         ((k3_enumset1 @ X20 @ X20 @ X21 @ X22 @ X23)
% 0.36/0.52           = (k2_enumset1 @ X20 @ X21 @ X22 @ X23))),
% 0.36/0.52      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.36/0.52  thf('27', plain,
% 0.36/0.52      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.36/0.52         ((k2_enumset1 @ X17 @ X17 @ X18 @ X19)
% 0.36/0.52           = (k1_enumset1 @ X17 @ X18 @ X19))),
% 0.36/0.52      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.36/0.52  thf('28', plain,
% 0.36/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.52         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.36/0.52      inference('sup+', [status(thm)], ['26', '27'])).
% 0.36/0.52  thf('29', plain, (![X32 : $i]: ((k1_setfam_1 @ (k1_tarski @ X32)) = (X32))),
% 0.36/0.52      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.36/0.52  thf('30', plain,
% 0.36/0.52      (![X0 : $i, X1 : $i]:
% 0.36/0.52         (((k1_setfam_1 @ (k1_enumset1 @ X1 @ X1 @ X0))
% 0.36/0.52            = (k3_xboole_0 @ X1 @ X0))
% 0.36/0.52          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.36/0.52      inference('demod', [status(thm)], ['25', '28', '29'])).
% 0.36/0.52  thf('31', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.36/0.52      inference('clc', [status(thm)], ['19', '21'])).
% 0.36/0.52  thf('32', plain,
% 0.36/0.52      (![X0 : $i, X1 : $i]:
% 0.36/0.52         ((k1_setfam_1 @ (k1_enumset1 @ X1 @ X1 @ X0))
% 0.36/0.52           = (k3_xboole_0 @ X1 @ X0))),
% 0.36/0.52      inference('simplify_reflect-', [status(thm)], ['30', '31'])).
% 0.36/0.52  thf('33', plain,
% 0.36/0.52      (![X0 : $i, X1 : $i]:
% 0.36/0.52         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))),
% 0.36/0.52      inference('sup+', [status(thm)], ['1', '32'])).
% 0.36/0.52  thf('34', plain,
% 0.36/0.52      (((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.36/0.52      inference('demod', [status(thm)], ['0', '33'])).
% 0.36/0.52  thf('35', plain, ($false), inference('simplify', [status(thm)], ['34'])).
% 0.36/0.52  
% 0.36/0.52  % SZS output end Refutation
% 0.36/0.52  
% 0.36/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

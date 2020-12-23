%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YviN4hBAGG

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:34 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :   63 (  68 expanded)
%              Number of leaves         :   27 (  31 expanded)
%              Depth                    :   11
%              Number of atoms          :  472 ( 520 expanded)
%              Number of equality atoms :   43 (  48 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t89_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ) )).

thf('0',plain,(
    ! [X49: $i,X50: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X49 @ X50 ) ) @ ( k1_relat_1 @ X49 ) )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t89_relat_1])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('1',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X51 ) @ X52 )
      | ( ( k7_relat_1 @ X51 @ X52 )
        = X51 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
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
    ! [X44: $i,X45: $i] :
      ( ~ ( v1_relat_1 @ X44 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X44 @ X45 ) ) ) ),
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
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X46 @ X47 ) @ X48 )
        = ( k7_relat_1 @ X46 @ ( k3_xboole_0 @ X47 @ X48 ) ) )
      | ~ ( v1_relat_1 @ X46 ) ) ),
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

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_enumset1 @ X13 @ X13 @ X14 )
      = ( k2_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('10',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t48_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k3_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 )
      = ( k2_xboole_0 @ ( k2_tarski @ X7 @ X8 ) @ ( k1_enumset1 @ X9 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t48_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X1 @ X0 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t43_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ) )).

thf('14',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X4 @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X5 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X1 @ X0 @ X0 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('16',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k2_enumset1 @ X15 @ X15 @ X16 @ X17 )
      = ( k1_enumset1 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('17',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_enumset1 @ X13 @ X13 @ X14 )
      = ( k2_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t125_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ D @ C @ B @ A ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t125_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X1 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('21',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k3_enumset1 @ X18 @ X18 @ X19 @ X20 @ X21 )
      = ( k2_enumset1 @ X18 @ X19 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X1 @ X1 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','22'])).

thf('24',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_enumset1 @ X13 @ X13 @ X14 )
      = ( k2_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('25',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X42 @ X43 ) )
      = ( k3_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X42 @ X43 ) )
      = ( k3_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ( k7_relat_1 @ sk_B @ sk_A )
 != ( k7_relat_1 @ sk_B @ ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['8','29'])).

thf('31',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
     != ( k7_relat_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['7','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ( k7_relat_1 @ sk_B @ sk_A )
 != ( k7_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    $false ),
    inference(simplify,[status(thm)],['33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YviN4hBAGG
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:42:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.51/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.51/0.71  % Solved by: fo/fo7.sh
% 0.51/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.71  % done 437 iterations in 0.260s
% 0.51/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.51/0.71  % SZS output start Refutation
% 0.51/0.71  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.51/0.71  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.51/0.71  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.51/0.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.51/0.71  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.51/0.71  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.51/0.71  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.51/0.71  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.51/0.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.51/0.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.51/0.71  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.51/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.51/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.51/0.71  thf(t89_relat_1, axiom,
% 0.51/0.71    (![A:$i,B:$i]:
% 0.51/0.71     ( ( v1_relat_1 @ B ) =>
% 0.51/0.71       ( r1_tarski @
% 0.51/0.71         ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ))).
% 0.51/0.71  thf('0', plain,
% 0.51/0.71      (![X49 : $i, X50 : $i]:
% 0.51/0.71         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X49 @ X50)) @ 
% 0.51/0.71           (k1_relat_1 @ X49))
% 0.51/0.71          | ~ (v1_relat_1 @ X49))),
% 0.51/0.71      inference('cnf', [status(esa)], [t89_relat_1])).
% 0.51/0.71  thf(t97_relat_1, axiom,
% 0.51/0.71    (![A:$i,B:$i]:
% 0.51/0.71     ( ( v1_relat_1 @ B ) =>
% 0.51/0.71       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.51/0.71         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.51/0.71  thf('1', plain,
% 0.51/0.71      (![X51 : $i, X52 : $i]:
% 0.51/0.71         (~ (r1_tarski @ (k1_relat_1 @ X51) @ X52)
% 0.51/0.71          | ((k7_relat_1 @ X51 @ X52) = (X51))
% 0.51/0.71          | ~ (v1_relat_1 @ X51))),
% 0.51/0.71      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.51/0.71  thf('2', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]:
% 0.51/0.71         (~ (v1_relat_1 @ X0)
% 0.51/0.71          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.51/0.71          | ((k7_relat_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.51/0.71              = (k7_relat_1 @ X0 @ X1)))),
% 0.51/0.71      inference('sup-', [status(thm)], ['0', '1'])).
% 0.51/0.71  thf(dt_k7_relat_1, axiom,
% 0.51/0.71    (![A:$i,B:$i]:
% 0.51/0.71     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.51/0.71  thf('3', plain,
% 0.51/0.71      (![X44 : $i, X45 : $i]:
% 0.51/0.71         (~ (v1_relat_1 @ X44) | (v1_relat_1 @ (k7_relat_1 @ X44 @ X45)))),
% 0.51/0.71      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.51/0.71  thf('4', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]:
% 0.51/0.71         (((k7_relat_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.51/0.71            = (k7_relat_1 @ X0 @ X1))
% 0.51/0.71          | ~ (v1_relat_1 @ X0))),
% 0.51/0.71      inference('clc', [status(thm)], ['2', '3'])).
% 0.51/0.71  thf(t100_relat_1, axiom,
% 0.51/0.71    (![A:$i,B:$i,C:$i]:
% 0.51/0.71     ( ( v1_relat_1 @ C ) =>
% 0.51/0.71       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.51/0.71         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.51/0.71  thf('5', plain,
% 0.51/0.71      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.51/0.71         (((k7_relat_1 @ (k7_relat_1 @ X46 @ X47) @ X48)
% 0.51/0.71            = (k7_relat_1 @ X46 @ (k3_xboole_0 @ X47 @ X48)))
% 0.51/0.71          | ~ (v1_relat_1 @ X46))),
% 0.51/0.71      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.51/0.71  thf('6', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]:
% 0.51/0.71         (((k7_relat_1 @ X1 @ X0)
% 0.51/0.71            = (k7_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ (k1_relat_1 @ X1))))
% 0.51/0.71          | ~ (v1_relat_1 @ X1)
% 0.51/0.71          | ~ (v1_relat_1 @ X1))),
% 0.51/0.71      inference('sup+', [status(thm)], ['4', '5'])).
% 0.51/0.71  thf('7', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]:
% 0.51/0.71         (~ (v1_relat_1 @ X1)
% 0.51/0.71          | ((k7_relat_1 @ X1 @ X0)
% 0.51/0.71              = (k7_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ (k1_relat_1 @ X1)))))),
% 0.51/0.71      inference('simplify', [status(thm)], ['6'])).
% 0.51/0.71  thf(t192_relat_1, conjecture,
% 0.51/0.71    (![A:$i,B:$i]:
% 0.51/0.71     ( ( v1_relat_1 @ B ) =>
% 0.51/0.71       ( ( k7_relat_1 @ B @ A ) =
% 0.51/0.71         ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 0.51/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.71    (~( ![A:$i,B:$i]:
% 0.51/0.71        ( ( v1_relat_1 @ B ) =>
% 0.51/0.71          ( ( k7_relat_1 @ B @ A ) =
% 0.51/0.71            ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )),
% 0.51/0.71    inference('cnf.neg', [status(esa)], [t192_relat_1])).
% 0.51/0.71  thf('8', plain,
% 0.51/0.71      (((k7_relat_1 @ sk_B @ sk_A)
% 0.51/0.71         != (k7_relat_1 @ sk_B @ (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.71  thf(t70_enumset1, axiom,
% 0.51/0.71    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.51/0.71  thf('9', plain,
% 0.51/0.71      (![X13 : $i, X14 : $i]:
% 0.51/0.71         ((k1_enumset1 @ X13 @ X13 @ X14) = (k2_tarski @ X13 @ X14))),
% 0.51/0.71      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.51/0.71  thf(t69_enumset1, axiom,
% 0.51/0.71    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.51/0.71  thf('10', plain,
% 0.51/0.71      (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.51/0.71      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.51/0.71  thf('11', plain,
% 0.51/0.71      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.51/0.71      inference('sup+', [status(thm)], ['9', '10'])).
% 0.51/0.71  thf(t48_enumset1, axiom,
% 0.51/0.71    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.51/0.71     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.51/0.71       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ))).
% 0.51/0.71  thf('12', plain,
% 0.51/0.71      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.51/0.71         ((k3_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11)
% 0.51/0.71           = (k2_xboole_0 @ (k2_tarski @ X7 @ X8) @ 
% 0.51/0.71              (k1_enumset1 @ X9 @ X10 @ X11)))),
% 0.51/0.71      inference('cnf', [status(esa)], [t48_enumset1])).
% 0.51/0.71  thf('13', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.71         ((k3_enumset1 @ X2 @ X1 @ X0 @ X0 @ X0)
% 0.51/0.71           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)))),
% 0.51/0.71      inference('sup+', [status(thm)], ['11', '12'])).
% 0.51/0.71  thf(t43_enumset1, axiom,
% 0.51/0.71    (![A:$i,B:$i,C:$i]:
% 0.51/0.71     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.51/0.71       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ))).
% 0.51/0.71  thf('14', plain,
% 0.51/0.71      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.51/0.71         ((k1_enumset1 @ X4 @ X5 @ X6)
% 0.51/0.71           = (k2_xboole_0 @ (k2_tarski @ X4 @ X5) @ (k1_tarski @ X6)))),
% 0.51/0.71      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.51/0.71  thf('15', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.71         ((k3_enumset1 @ X2 @ X1 @ X0 @ X0 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.51/0.71      inference('demod', [status(thm)], ['13', '14'])).
% 0.51/0.71  thf(t71_enumset1, axiom,
% 0.51/0.71    (![A:$i,B:$i,C:$i]:
% 0.51/0.71     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.51/0.71  thf('16', plain,
% 0.51/0.71      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.51/0.71         ((k2_enumset1 @ X15 @ X15 @ X16 @ X17)
% 0.51/0.71           = (k1_enumset1 @ X15 @ X16 @ X17))),
% 0.51/0.71      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.51/0.71  thf('17', plain,
% 0.51/0.71      (![X13 : $i, X14 : $i]:
% 0.51/0.71         ((k1_enumset1 @ X13 @ X13 @ X14) = (k2_tarski @ X13 @ X14))),
% 0.51/0.71      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.51/0.71  thf('18', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]:
% 0.51/0.71         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.51/0.71      inference('sup+', [status(thm)], ['16', '17'])).
% 0.51/0.71  thf(t125_enumset1, axiom,
% 0.51/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.51/0.71     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ D @ C @ B @ A ) ))).
% 0.51/0.71  thf('19', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.51/0.71         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.51/0.71      inference('cnf', [status(esa)], [t125_enumset1])).
% 0.51/0.71  thf('20', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]:
% 0.51/0.71         ((k2_enumset1 @ X0 @ X1 @ X1 @ X1) = (k2_tarski @ X1 @ X0))),
% 0.51/0.71      inference('sup+', [status(thm)], ['18', '19'])).
% 0.51/0.71  thf(t72_enumset1, axiom,
% 0.51/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.51/0.71     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.51/0.71  thf('21', plain,
% 0.51/0.71      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.51/0.71         ((k3_enumset1 @ X18 @ X18 @ X19 @ X20 @ X21)
% 0.51/0.71           = (k2_enumset1 @ X18 @ X19 @ X20 @ X21))),
% 0.51/0.71      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.51/0.71  thf('22', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]:
% 0.51/0.71         ((k3_enumset1 @ X0 @ X0 @ X1 @ X1 @ X1) = (k2_tarski @ X1 @ X0))),
% 0.51/0.71      inference('sup+', [status(thm)], ['20', '21'])).
% 0.51/0.71  thf('23', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]:
% 0.51/0.71         ((k1_enumset1 @ X1 @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.51/0.71      inference('sup+', [status(thm)], ['15', '22'])).
% 0.51/0.71  thf('24', plain,
% 0.51/0.71      (![X13 : $i, X14 : $i]:
% 0.51/0.71         ((k1_enumset1 @ X13 @ X13 @ X14) = (k2_tarski @ X13 @ X14))),
% 0.51/0.71      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.51/0.71  thf(t12_setfam_1, axiom,
% 0.51/0.71    (![A:$i,B:$i]:
% 0.51/0.71     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.51/0.71  thf('25', plain,
% 0.51/0.71      (![X42 : $i, X43 : $i]:
% 0.51/0.71         ((k1_setfam_1 @ (k2_tarski @ X42 @ X43)) = (k3_xboole_0 @ X42 @ X43))),
% 0.51/0.71      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.51/0.71  thf('26', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]:
% 0.51/0.71         ((k1_setfam_1 @ (k1_enumset1 @ X1 @ X1 @ X0))
% 0.51/0.71           = (k3_xboole_0 @ X1 @ X0))),
% 0.51/0.71      inference('sup+', [status(thm)], ['24', '25'])).
% 0.51/0.71  thf('27', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]:
% 0.51/0.71         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.51/0.71      inference('sup+', [status(thm)], ['23', '26'])).
% 0.51/0.71  thf('28', plain,
% 0.51/0.71      (![X42 : $i, X43 : $i]:
% 0.51/0.71         ((k1_setfam_1 @ (k2_tarski @ X42 @ X43)) = (k3_xboole_0 @ X42 @ X43))),
% 0.51/0.71      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.51/0.71  thf('29', plain,
% 0.51/0.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.51/0.71      inference('sup+', [status(thm)], ['27', '28'])).
% 0.51/0.71  thf('30', plain,
% 0.51/0.71      (((k7_relat_1 @ sk_B @ sk_A)
% 0.51/0.71         != (k7_relat_1 @ sk_B @ (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.51/0.71      inference('demod', [status(thm)], ['8', '29'])).
% 0.51/0.71  thf('31', plain,
% 0.51/0.71      ((((k7_relat_1 @ sk_B @ sk_A) != (k7_relat_1 @ sk_B @ sk_A))
% 0.51/0.71        | ~ (v1_relat_1 @ sk_B))),
% 0.51/0.71      inference('sup-', [status(thm)], ['7', '30'])).
% 0.51/0.71  thf('32', plain, ((v1_relat_1 @ sk_B)),
% 0.51/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.71  thf('33', plain,
% 0.51/0.71      (((k7_relat_1 @ sk_B @ sk_A) != (k7_relat_1 @ sk_B @ sk_A))),
% 0.51/0.71      inference('demod', [status(thm)], ['31', '32'])).
% 0.51/0.71  thf('34', plain, ($false), inference('simplify', [status(thm)], ['33'])).
% 0.51/0.71  
% 0.51/0.71  % SZS output end Refutation
% 0.51/0.71  
% 0.51/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

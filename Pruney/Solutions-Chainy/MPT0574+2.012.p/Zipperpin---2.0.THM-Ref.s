%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ENKI6LELuN

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:18 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   65 (  85 expanded)
%              Number of leaves         :   26 (  36 expanded)
%              Depth                    :   14
%              Number of atoms          :  387 ( 559 expanded)
%              Number of equality atoms :   32 (  48 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('0',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X18: $i,X20: $i] :
      ( ( r1_xboole_0 @ X18 @ X20 )
      | ( ( k4_xboole_0 @ X18 @ X20 )
       != X18 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
       != ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ~ ( r1_xboole_0 @ X2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t178_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t178_relat_1])).

thf('9',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('10',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X14 @ X15 )
      | ( r1_xboole_0 @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r1_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k4_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('15',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A )
      | ( ( k4_xboole_0 @ X0 @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','16'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('19',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('20',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_tarski @ X22 @ X21 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X28 @ X29 ) )
      = ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X28 @ X29 ) )
      = ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('26',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('29',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['19','24','27','28'])).

thf(t175_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('30',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k10_relat_1 @ X30 @ ( k2_xboole_0 @ X31 @ X32 ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ X30 @ X31 ) @ ( k10_relat_1 @ X30 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t175_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('31',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ X1 ) @ ( k10_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ sk_A ) @ ( k10_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,(
    ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['35','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ENKI6LELuN
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:15:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.39/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.59  % Solved by: fo/fo7.sh
% 0.39/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.59  % done 343 iterations in 0.131s
% 0.39/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.59  % SZS output start Refutation
% 0.39/0.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.39/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.59  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.39/0.59  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.39/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.39/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.39/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.59  thf(t36_xboole_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.39/0.59  thf('0', plain,
% 0.39/0.59      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 0.39/0.59      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.39/0.59  thf(idempotence_k2_xboole_0, axiom,
% 0.39/0.59    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.39/0.59  thf('1', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.39/0.59      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.39/0.59  thf(t41_xboole_1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.39/0.59       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.39/0.59  thf('2', plain,
% 0.39/0.59      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.39/0.59         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 0.39/0.59           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 0.39/0.59      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.39/0.59  thf('3', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.39/0.59           = (k4_xboole_0 @ X1 @ X0))),
% 0.39/0.59      inference('sup+', [status(thm)], ['1', '2'])).
% 0.39/0.59  thf(t83_xboole_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.39/0.59  thf('4', plain,
% 0.39/0.59      (![X18 : $i, X20 : $i]:
% 0.39/0.59         ((r1_xboole_0 @ X18 @ X20) | ((k4_xboole_0 @ X18 @ X20) != (X18)))),
% 0.39/0.59      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.39/0.59  thf('5', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (((k4_xboole_0 @ X1 @ X0) != (k4_xboole_0 @ X1 @ X0))
% 0.39/0.59          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['3', '4'])).
% 0.39/0.59  thf('6', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.39/0.59      inference('simplify', [status(thm)], ['5'])).
% 0.39/0.59  thf(symmetry_r1_xboole_0, axiom,
% 0.39/0.59    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.39/0.59  thf('7', plain,
% 0.39/0.59      (![X1 : $i, X2 : $i]:
% 0.39/0.59         ((r1_xboole_0 @ X1 @ X2) | ~ (r1_xboole_0 @ X2 @ X1))),
% 0.39/0.59      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.39/0.59  thf('8', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.59  thf(t178_relat_1, conjecture,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( v1_relat_1 @ C ) =>
% 0.39/0.59       ( ( r1_tarski @ A @ B ) =>
% 0.39/0.59         ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.39/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.59    (~( ![A:$i,B:$i,C:$i]:
% 0.39/0.59        ( ( v1_relat_1 @ C ) =>
% 0.39/0.59          ( ( r1_tarski @ A @ B ) =>
% 0.39/0.59            ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )),
% 0.39/0.59    inference('cnf.neg', [status(esa)], [t178_relat_1])).
% 0.39/0.59  thf('9', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(t63_xboole_1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.39/0.59       ( r1_xboole_0 @ A @ C ) ))).
% 0.39/0.59  thf('10', plain,
% 0.39/0.59      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.39/0.59         (~ (r1_tarski @ X13 @ X14)
% 0.39/0.59          | ~ (r1_xboole_0 @ X14 @ X15)
% 0.39/0.59          | (r1_xboole_0 @ X13 @ X15))),
% 0.39/0.59      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.39/0.59  thf('11', plain,
% 0.39/0.59      (![X0 : $i]: ((r1_xboole_0 @ sk_A @ X0) | ~ (r1_xboole_0 @ sk_B @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['9', '10'])).
% 0.39/0.59  thf('12', plain,
% 0.39/0.59      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B))),
% 0.39/0.59      inference('sup-', [status(thm)], ['8', '11'])).
% 0.39/0.59  thf('13', plain,
% 0.39/0.59      (![X18 : $i, X19 : $i]:
% 0.39/0.59         (((k4_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_xboole_0 @ X18 @ X19))),
% 0.39/0.59      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.39/0.59  thf('14', plain,
% 0.39/0.59      (![X0 : $i]: ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B)) = (sk_A))),
% 0.39/0.59      inference('sup-', [status(thm)], ['12', '13'])).
% 0.39/0.59  thf(t38_xboole_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.39/0.59       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.39/0.59  thf('15', plain,
% 0.39/0.59      (![X6 : $i, X7 : $i]:
% 0.39/0.59         (((X6) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ (k4_xboole_0 @ X7 @ X6)))),
% 0.39/0.59      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.39/0.59  thf('16', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (r1_tarski @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A)
% 0.39/0.59          | ((k4_xboole_0 @ X0 @ sk_B) = (k1_xboole_0)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['14', '15'])).
% 0.39/0.59  thf('17', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['0', '16'])).
% 0.39/0.59  thf(t39_xboole_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.39/0.59  thf('18', plain,
% 0.39/0.59      (![X8 : $i, X9 : $i]:
% 0.39/0.59         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 0.39/0.59           = (k2_xboole_0 @ X8 @ X9))),
% 0.39/0.59      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.39/0.59  thf('19', plain,
% 0.39/0.59      (((k2_xboole_0 @ sk_B @ k1_xboole_0) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.39/0.59      inference('sup+', [status(thm)], ['17', '18'])).
% 0.39/0.59  thf(commutativity_k2_tarski, axiom,
% 0.39/0.59    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.39/0.59  thf('20', plain,
% 0.39/0.59      (![X21 : $i, X22 : $i]:
% 0.39/0.59         ((k2_tarski @ X22 @ X21) = (k2_tarski @ X21 @ X22))),
% 0.39/0.59      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.39/0.59  thf(l51_zfmisc_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.39/0.59  thf('21', plain,
% 0.39/0.59      (![X28 : $i, X29 : $i]:
% 0.39/0.59         ((k3_tarski @ (k2_tarski @ X28 @ X29)) = (k2_xboole_0 @ X28 @ X29))),
% 0.39/0.59      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.39/0.59  thf('22', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.59      inference('sup+', [status(thm)], ['20', '21'])).
% 0.39/0.59  thf('23', plain,
% 0.39/0.59      (![X28 : $i, X29 : $i]:
% 0.39/0.59         ((k3_tarski @ (k2_tarski @ X28 @ X29)) = (k2_xboole_0 @ X28 @ X29))),
% 0.39/0.59      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.39/0.59  thf('24', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.59      inference('sup+', [status(thm)], ['22', '23'])).
% 0.39/0.59  thf('25', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.59      inference('sup+', [status(thm)], ['22', '23'])).
% 0.39/0.59  thf(t1_boole, axiom,
% 0.39/0.59    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.39/0.59  thf('26', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.39/0.59      inference('cnf', [status(esa)], [t1_boole])).
% 0.39/0.59  thf('27', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.39/0.59      inference('sup+', [status(thm)], ['25', '26'])).
% 0.39/0.59  thf('28', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.59      inference('sup+', [status(thm)], ['22', '23'])).
% 0.39/0.59  thf('29', plain, (((sk_B) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.39/0.59      inference('demod', [status(thm)], ['19', '24', '27', '28'])).
% 0.39/0.59  thf(t175_relat_1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( v1_relat_1 @ C ) =>
% 0.39/0.59       ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.39/0.59         ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.39/0.59  thf('30', plain,
% 0.39/0.59      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.39/0.59         (((k10_relat_1 @ X30 @ (k2_xboole_0 @ X31 @ X32))
% 0.39/0.59            = (k2_xboole_0 @ (k10_relat_1 @ X30 @ X31) @ 
% 0.39/0.59               (k10_relat_1 @ X30 @ X32)))
% 0.39/0.59          | ~ (v1_relat_1 @ X30))),
% 0.39/0.59      inference('cnf', [status(esa)], [t175_relat_1])).
% 0.39/0.59  thf(t7_xboole_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.39/0.59  thf('31', plain,
% 0.39/0.59      (![X16 : $i, X17 : $i]: (r1_tarski @ X16 @ (k2_xboole_0 @ X16 @ X17))),
% 0.39/0.59      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.39/0.59  thf('32', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.59         ((r1_tarski @ (k10_relat_1 @ X2 @ X1) @ 
% 0.39/0.59           (k10_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.39/0.59          | ~ (v1_relat_1 @ X2))),
% 0.39/0.59      inference('sup+', [status(thm)], ['30', '31'])).
% 0.39/0.59  thf('33', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((r1_tarski @ (k10_relat_1 @ X0 @ sk_A) @ (k10_relat_1 @ X0 @ sk_B))
% 0.39/0.59          | ~ (v1_relat_1 @ X0))),
% 0.39/0.59      inference('sup+', [status(thm)], ['29', '32'])).
% 0.39/0.59  thf('34', plain,
% 0.39/0.59      (~ (r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ (k10_relat_1 @ sk_C @ sk_B))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('35', plain, (~ (v1_relat_1 @ sk_C)),
% 0.39/0.59      inference('sup-', [status(thm)], ['33', '34'])).
% 0.39/0.59  thf('36', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('37', plain, ($false), inference('demod', [status(thm)], ['35', '36'])).
% 0.39/0.59  
% 0.39/0.59  % SZS output end Refutation
% 0.39/0.59  
% 0.39/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

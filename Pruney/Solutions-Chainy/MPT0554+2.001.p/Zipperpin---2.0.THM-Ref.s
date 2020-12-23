%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dHFrCp0zQi

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:29 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   57 (  74 expanded)
%              Number of leaves         :   20 (  30 expanded)
%              Depth                    :   13
%              Number of atoms          :  355 ( 503 expanded)
%              Number of equality atoms :   17 (  28 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t156_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t156_relat_1])).

thf('3',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 )
      | ~ ( r1_tarski @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ sk_A ) @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ sk_A ) @ ( k2_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_B ),
    inference('sup+',[status(thm)],['2','11'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('13',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_tarski @ X16 @ X15 )
      = ( k2_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X17 @ X18 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X17 @ X18 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['12','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['18','23'])).

thf(t153_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k9_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('25',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k9_relat_1 @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) )
        = ( k2_xboole_0 @ ( k9_relat_1 @ X19 @ X20 ) @ ( k9_relat_1 @ X19 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t153_relat_1])).

thf('26',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('27',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ X2 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ sk_A ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['1','30'])).

thf('32',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['33','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dHFrCp0zQi
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:17:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.67  % Solved by: fo/fo7.sh
% 0.46/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.67  % done 404 iterations in 0.220s
% 0.46/0.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.67  % SZS output start Refutation
% 0.46/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.67  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.67  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.46/0.67  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.67  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.67  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.67  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.46/0.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.67  thf(d10_xboole_0, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.67  thf('0', plain,
% 0.46/0.67      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.46/0.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.67  thf('1', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.46/0.67      inference('simplify', [status(thm)], ['0'])).
% 0.46/0.67  thf(idempotence_k2_xboole_0, axiom,
% 0.46/0.67    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.46/0.67  thf('2', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.46/0.67      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.46/0.67  thf(t156_relat_1, conjecture,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( v1_relat_1 @ C ) =>
% 0.46/0.67       ( ( r1_tarski @ A @ B ) =>
% 0.46/0.67         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.46/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.67    (~( ![A:$i,B:$i,C:$i]:
% 0.46/0.67        ( ( v1_relat_1 @ C ) =>
% 0.46/0.67          ( ( r1_tarski @ A @ B ) =>
% 0.46/0.67            ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )),
% 0.46/0.67    inference('cnf.neg', [status(esa)], [t156_relat_1])).
% 0.46/0.67  thf('3', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('4', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.46/0.67      inference('simplify', [status(thm)], ['0'])).
% 0.46/0.67  thf(t43_xboole_1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.46/0.67       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.46/0.67  thf('5', plain,
% 0.46/0.67      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.46/0.67         ((r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X9)
% 0.46/0.67          | ~ (r1_tarski @ X7 @ (k2_xboole_0 @ X8 @ X9)))),
% 0.46/0.67      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.46/0.67  thf('6', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)),
% 0.46/0.67      inference('sup-', [status(thm)], ['4', '5'])).
% 0.46/0.67  thf(t1_xboole_1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.46/0.67       ( r1_tarski @ A @ C ) ))).
% 0.46/0.67  thf('7', plain,
% 0.46/0.67      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.46/0.67         (~ (r1_tarski @ X4 @ X5)
% 0.46/0.67          | ~ (r1_tarski @ X5 @ X6)
% 0.46/0.67          | (r1_tarski @ X4 @ X6))),
% 0.46/0.67      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.46/0.67  thf('8', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.67         ((r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X2)
% 0.46/0.67          | ~ (r1_tarski @ X0 @ X2))),
% 0.46/0.67      inference('sup-', [status(thm)], ['6', '7'])).
% 0.46/0.67  thf('9', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ sk_A) @ X0) @ sk_B)),
% 0.46/0.67      inference('sup-', [status(thm)], ['3', '8'])).
% 0.46/0.67  thf(t44_xboole_1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 0.46/0.67       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.46/0.67  thf('10', plain,
% 0.46/0.67      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.67         ((r1_tarski @ X10 @ (k2_xboole_0 @ X11 @ X12))
% 0.46/0.67          | ~ (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X12))),
% 0.46/0.67      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.46/0.67  thf('11', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (r1_tarski @ (k2_xboole_0 @ X0 @ sk_A) @ (k2_xboole_0 @ X0 @ sk_B))),
% 0.46/0.67      inference('sup-', [status(thm)], ['9', '10'])).
% 0.46/0.67  thf('12', plain, ((r1_tarski @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_B)),
% 0.46/0.67      inference('sup+', [status(thm)], ['2', '11'])).
% 0.46/0.67  thf(commutativity_k2_tarski, axiom,
% 0.46/0.67    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.46/0.67  thf('13', plain,
% 0.46/0.67      (![X15 : $i, X16 : $i]:
% 0.46/0.67         ((k2_tarski @ X16 @ X15) = (k2_tarski @ X15 @ X16))),
% 0.46/0.67      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.46/0.67  thf(l51_zfmisc_1, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.46/0.67  thf('14', plain,
% 0.46/0.67      (![X17 : $i, X18 : $i]:
% 0.46/0.67         ((k3_tarski @ (k2_tarski @ X17 @ X18)) = (k2_xboole_0 @ X17 @ X18))),
% 0.46/0.67      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.46/0.67  thf('15', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.67      inference('sup+', [status(thm)], ['13', '14'])).
% 0.46/0.67  thf('16', plain,
% 0.46/0.67      (![X17 : $i, X18 : $i]:
% 0.46/0.67         ((k3_tarski @ (k2_tarski @ X17 @ X18)) = (k2_xboole_0 @ X17 @ X18))),
% 0.46/0.67      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.46/0.67  thf('17', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.67      inference('sup+', [status(thm)], ['15', '16'])).
% 0.46/0.67  thf('18', plain, ((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_B)),
% 0.46/0.67      inference('demod', [status(thm)], ['12', '17'])).
% 0.46/0.67  thf('19', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.67      inference('sup+', [status(thm)], ['15', '16'])).
% 0.46/0.67  thf(t7_xboole_1, axiom,
% 0.46/0.67    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.46/0.67  thf('20', plain,
% 0.46/0.67      (![X13 : $i, X14 : $i]: (r1_tarski @ X13 @ (k2_xboole_0 @ X13 @ X14))),
% 0.46/0.67      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.46/0.67  thf('21', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.46/0.67      inference('sup+', [status(thm)], ['19', '20'])).
% 0.46/0.67  thf('22', plain,
% 0.46/0.67      (![X1 : $i, X3 : $i]:
% 0.46/0.67         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.46/0.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.67  thf('23', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 0.46/0.67          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['21', '22'])).
% 0.46/0.67  thf('24', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.46/0.67      inference('sup-', [status(thm)], ['18', '23'])).
% 0.46/0.67  thf(t153_relat_1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( v1_relat_1 @ C ) =>
% 0.46/0.67       ( ( k9_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.46/0.67         ( k2_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.46/0.67  thf('25', plain,
% 0.46/0.67      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.67         (((k9_relat_1 @ X19 @ (k2_xboole_0 @ X20 @ X21))
% 0.46/0.67            = (k2_xboole_0 @ (k9_relat_1 @ X19 @ X20) @ 
% 0.46/0.67               (k9_relat_1 @ X19 @ X21)))
% 0.46/0.67          | ~ (v1_relat_1 @ X19))),
% 0.46/0.67      inference('cnf', [status(esa)], [t153_relat_1])).
% 0.46/0.67  thf('26', plain,
% 0.46/0.67      (![X13 : $i, X14 : $i]: (r1_tarski @ X13 @ (k2_xboole_0 @ X13 @ X14))),
% 0.46/0.67      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.46/0.67  thf('27', plain,
% 0.46/0.67      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.46/0.67         (~ (r1_tarski @ X4 @ X5)
% 0.46/0.67          | ~ (r1_tarski @ X5 @ X6)
% 0.46/0.67          | (r1_tarski @ X4 @ X6))),
% 0.46/0.67      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.46/0.67  thf('28', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.67         ((r1_tarski @ X1 @ X2) | ~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 0.46/0.67      inference('sup-', [status(thm)], ['26', '27'])).
% 0.46/0.67  thf('29', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.67         (~ (r1_tarski @ (k9_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3)
% 0.46/0.67          | ~ (v1_relat_1 @ X2)
% 0.46/0.67          | (r1_tarski @ (k9_relat_1 @ X2 @ X1) @ X3))),
% 0.46/0.67      inference('sup-', [status(thm)], ['25', '28'])).
% 0.46/0.67  thf('30', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         (~ (r1_tarski @ (k9_relat_1 @ X1 @ sk_B) @ X0)
% 0.46/0.67          | (r1_tarski @ (k9_relat_1 @ X1 @ sk_A) @ X0)
% 0.46/0.67          | ~ (v1_relat_1 @ X1))),
% 0.46/0.67      inference('sup-', [status(thm)], ['24', '29'])).
% 0.46/0.67  thf('31', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (v1_relat_1 @ X0)
% 0.46/0.67          | (r1_tarski @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['1', '30'])).
% 0.46/0.67  thf('32', plain,
% 0.46/0.67      (~ (r1_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('33', plain, (~ (v1_relat_1 @ sk_C)),
% 0.46/0.67      inference('sup-', [status(thm)], ['31', '32'])).
% 0.46/0.67  thf('34', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('35', plain, ($false), inference('demod', [status(thm)], ['33', '34'])).
% 0.46/0.67  
% 0.46/0.67  % SZS output end Refutation
% 0.46/0.67  
% 0.46/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

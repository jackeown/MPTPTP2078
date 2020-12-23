%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VDgFwHQaA6

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:13 EST 2020

% Result     : Theorem 0.83s
% Output     : Refutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :   61 (  80 expanded)
%              Number of leaves         :   22 (  35 expanded)
%              Depth                    :   12
%              Number of atoms          :  393 ( 562 expanded)
%              Number of equality atoms :   37 (  56 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t216_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t216_relat_1])).

thf('0',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('2',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','1'])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('4',plain,
    ( ( k6_subset_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['2','3'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ X3 @ ( k4_xboole_0 @ X4 @ X3 ) )
      = ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('6',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ X3 @ ( k6_subset_1 @ X4 @ X3 ) )
      = ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('10',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('13',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k6_subset_1 @ ( k6_subset_1 @ X6 @ X7 ) @ X8 )
      = ( k6_subset_1 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('14',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('15',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('16',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_xboole_0 @ ( k6_subset_1 @ X9 @ X10 ) @ X10 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k6_subset_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k6_subset_1 @ X0 @ ( k2_xboole_0 @ sk_B @ k1_xboole_0 ) ) @ sk_A ) ),
    inference('sup+',[status(thm)],['8','17'])).

thf('19',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k6_subset_1 @ ( k6_subset_1 @ X6 @ X7 ) @ X8 )
      = ( k6_subset_1 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('20',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('21',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('22',plain,(
    ! [X5: $i] :
      ( ( k6_subset_1 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k6_subset_1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k6_subset_1 @ X0 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['18','23'])).

thf(t212_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('25',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k1_relat_1 @ ( k6_subset_1 @ X15 @ ( k7_relat_1 @ X15 @ X16 ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ X15 ) @ X16 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t212_relat_1])).

thf(t95_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('26',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X17 ) @ X18 )
      | ( ( k7_relat_1 @ X17 @ X18 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k6_subset_1 @ ( k1_relat_1 @ X1 ) @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_subset_1 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( ( k7_relat_1 @ ( k6_subset_1 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_subset_1 @ X0 @ ( k7_relat_1 @ X0 @ sk_B ) ) @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k6_subset_1 @ X0 @ ( k7_relat_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf(fc2_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_xboole_0 @ A @ B ) ) ) )).

thf('29',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( v1_relat_1 @ ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_relat_1])).

thf('30',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('31',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( v1_relat_1 @ ( k6_subset_1 @ X13 @ X14 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ ( k6_subset_1 @ X0 @ ( k7_relat_1 @ X0 @ sk_B ) ) @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['28','31'])).

thf('33',plain,(
    ( k7_relat_1 @ ( k6_subset_1 @ sk_C @ ( k7_relat_1 @ sk_C @ sk_B ) ) @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    $false ),
    inference(simplify,[status(thm)],['36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VDgFwHQaA6
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:17:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.83/1.00  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.83/1.00  % Solved by: fo/fo7.sh
% 0.83/1.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.83/1.00  % done 961 iterations in 0.552s
% 0.83/1.00  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.83/1.00  % SZS output start Refutation
% 0.83/1.00  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.83/1.00  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.83/1.00  thf(sk_C_type, type, sk_C: $i).
% 0.83/1.00  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.83/1.00  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.83/1.00  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.83/1.00  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.83/1.00  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.83/1.00  thf(sk_A_type, type, sk_A: $i).
% 0.83/1.00  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.83/1.00  thf(sk_B_type, type, sk_B: $i).
% 0.83/1.00  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.83/1.00  thf(t216_relat_1, conjecture,
% 0.83/1.00    (![A:$i,B:$i,C:$i]:
% 0.83/1.00     ( ( v1_relat_1 @ C ) =>
% 0.83/1.00       ( ( r1_tarski @ A @ B ) =>
% 0.83/1.00         ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A ) =
% 0.83/1.00           ( k1_xboole_0 ) ) ) ))).
% 0.83/1.00  thf(zf_stmt_0, negated_conjecture,
% 0.83/1.00    (~( ![A:$i,B:$i,C:$i]:
% 0.83/1.00        ( ( v1_relat_1 @ C ) =>
% 0.83/1.00          ( ( r1_tarski @ A @ B ) =>
% 0.83/1.00            ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A ) =
% 0.83/1.00              ( k1_xboole_0 ) ) ) ) )),
% 0.83/1.00    inference('cnf.neg', [status(esa)], [t216_relat_1])).
% 0.83/1.00  thf('0', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.83/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.00  thf(l32_xboole_1, axiom,
% 0.83/1.00    (![A:$i,B:$i]:
% 0.83/1.00     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.83/1.00  thf('1', plain,
% 0.83/1.00      (![X0 : $i, X2 : $i]:
% 0.83/1.00         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.83/1.00      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.83/1.00  thf('2', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.83/1.00      inference('sup-', [status(thm)], ['0', '1'])).
% 0.83/1.00  thf(redefinition_k6_subset_1, axiom,
% 0.83/1.00    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.83/1.00  thf('3', plain,
% 0.83/1.00      (![X11 : $i, X12 : $i]:
% 0.83/1.00         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.83/1.00      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.83/1.00  thf('4', plain, (((k6_subset_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.83/1.00      inference('demod', [status(thm)], ['2', '3'])).
% 0.83/1.00  thf(t39_xboole_1, axiom,
% 0.83/1.00    (![A:$i,B:$i]:
% 0.83/1.00     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.83/1.00  thf('5', plain,
% 0.83/1.00      (![X3 : $i, X4 : $i]:
% 0.83/1.00         ((k2_xboole_0 @ X3 @ (k4_xboole_0 @ X4 @ X3))
% 0.83/1.00           = (k2_xboole_0 @ X3 @ X4))),
% 0.83/1.00      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.83/1.00  thf('6', plain,
% 0.83/1.00      (![X11 : $i, X12 : $i]:
% 0.83/1.00         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.83/1.00      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.83/1.00  thf('7', plain,
% 0.83/1.00      (![X3 : $i, X4 : $i]:
% 0.83/1.00         ((k2_xboole_0 @ X3 @ (k6_subset_1 @ X4 @ X3))
% 0.83/1.00           = (k2_xboole_0 @ X3 @ X4))),
% 0.83/1.00      inference('demod', [status(thm)], ['5', '6'])).
% 0.83/1.00  thf('8', plain,
% 0.83/1.00      (((k2_xboole_0 @ sk_B @ k1_xboole_0) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.83/1.00      inference('sup+', [status(thm)], ['4', '7'])).
% 0.83/1.00  thf(t41_xboole_1, axiom,
% 0.83/1.00    (![A:$i,B:$i,C:$i]:
% 0.83/1.00     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.83/1.00       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.83/1.00  thf('9', plain,
% 0.83/1.00      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.83/1.00         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 0.83/1.00           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 0.83/1.00      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.83/1.00  thf('10', plain,
% 0.83/1.00      (![X11 : $i, X12 : $i]:
% 0.83/1.00         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.83/1.00      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.83/1.00  thf('11', plain,
% 0.83/1.00      (![X11 : $i, X12 : $i]:
% 0.83/1.00         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.83/1.00      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.83/1.00  thf('12', plain,
% 0.83/1.00      (![X11 : $i, X12 : $i]:
% 0.83/1.00         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.83/1.00      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.83/1.00  thf('13', plain,
% 0.83/1.00      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.83/1.00         ((k6_subset_1 @ (k6_subset_1 @ X6 @ X7) @ X8)
% 0.83/1.00           = (k6_subset_1 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 0.83/1.00      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.83/1.00  thf(t79_xboole_1, axiom,
% 0.83/1.00    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.83/1.00  thf('14', plain,
% 0.83/1.00      (![X9 : $i, X10 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X10)),
% 0.83/1.00      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.83/1.00  thf('15', plain,
% 0.83/1.00      (![X11 : $i, X12 : $i]:
% 0.83/1.00         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.83/1.00      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.83/1.00  thf('16', plain,
% 0.83/1.00      (![X9 : $i, X10 : $i]: (r1_xboole_0 @ (k6_subset_1 @ X9 @ X10) @ X10)),
% 0.83/1.00      inference('demod', [status(thm)], ['14', '15'])).
% 0.83/1.00  thf('17', plain,
% 0.83/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.00         (r1_xboole_0 @ (k6_subset_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X0)),
% 0.83/1.00      inference('sup+', [status(thm)], ['13', '16'])).
% 0.83/1.00  thf('18', plain,
% 0.83/1.00      (![X0 : $i]:
% 0.83/1.00         (r1_xboole_0 @ 
% 0.83/1.00          (k6_subset_1 @ X0 @ (k2_xboole_0 @ sk_B @ k1_xboole_0)) @ sk_A)),
% 0.83/1.00      inference('sup+', [status(thm)], ['8', '17'])).
% 0.83/1.00  thf('19', plain,
% 0.83/1.00      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.83/1.00         ((k6_subset_1 @ (k6_subset_1 @ X6 @ X7) @ X8)
% 0.83/1.00           = (k6_subset_1 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 0.83/1.00      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.83/1.00  thf(t3_boole, axiom,
% 0.83/1.00    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.83/1.00  thf('20', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.83/1.00      inference('cnf', [status(esa)], [t3_boole])).
% 0.83/1.00  thf('21', plain,
% 0.83/1.00      (![X11 : $i, X12 : $i]:
% 0.83/1.00         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.83/1.00      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.83/1.00  thf('22', plain, (![X5 : $i]: ((k6_subset_1 @ X5 @ k1_xboole_0) = (X5))),
% 0.83/1.00      inference('demod', [status(thm)], ['20', '21'])).
% 0.83/1.00  thf('23', plain,
% 0.83/1.00      (![X0 : $i, X1 : $i]:
% 0.83/1.00         ((k6_subset_1 @ X1 @ (k2_xboole_0 @ X0 @ k1_xboole_0))
% 0.83/1.00           = (k6_subset_1 @ X1 @ X0))),
% 0.83/1.00      inference('sup+', [status(thm)], ['19', '22'])).
% 0.83/1.00  thf('24', plain,
% 0.83/1.00      (![X0 : $i]: (r1_xboole_0 @ (k6_subset_1 @ X0 @ sk_B) @ sk_A)),
% 0.83/1.00      inference('demod', [status(thm)], ['18', '23'])).
% 0.83/1.00  thf(t212_relat_1, axiom,
% 0.83/1.00    (![A:$i,B:$i]:
% 0.83/1.00     ( ( v1_relat_1 @ B ) =>
% 0.83/1.00       ( ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.83/1.00         ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.83/1.00  thf('25', plain,
% 0.83/1.00      (![X15 : $i, X16 : $i]:
% 0.83/1.00         (((k1_relat_1 @ (k6_subset_1 @ X15 @ (k7_relat_1 @ X15 @ X16)))
% 0.83/1.00            = (k6_subset_1 @ (k1_relat_1 @ X15) @ X16))
% 0.83/1.00          | ~ (v1_relat_1 @ X15))),
% 0.83/1.00      inference('cnf', [status(esa)], [t212_relat_1])).
% 0.83/1.00  thf(t95_relat_1, axiom,
% 0.83/1.00    (![A:$i,B:$i]:
% 0.83/1.00     ( ( v1_relat_1 @ B ) =>
% 0.83/1.00       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.83/1.00         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.83/1.00  thf('26', plain,
% 0.83/1.00      (![X17 : $i, X18 : $i]:
% 0.83/1.00         (~ (r1_xboole_0 @ (k1_relat_1 @ X17) @ X18)
% 0.83/1.00          | ((k7_relat_1 @ X17 @ X18) = (k1_xboole_0))
% 0.83/1.00          | ~ (v1_relat_1 @ X17))),
% 0.83/1.00      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.83/1.00  thf('27', plain,
% 0.83/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.00         (~ (r1_xboole_0 @ (k6_subset_1 @ (k1_relat_1 @ X1) @ X0) @ X2)
% 0.83/1.00          | ~ (v1_relat_1 @ X1)
% 0.83/1.00          | ~ (v1_relat_1 @ (k6_subset_1 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 0.83/1.00          | ((k7_relat_1 @ (k6_subset_1 @ X1 @ (k7_relat_1 @ X1 @ X0)) @ X2)
% 0.83/1.00              = (k1_xboole_0)))),
% 0.83/1.00      inference('sup-', [status(thm)], ['25', '26'])).
% 0.83/1.00  thf('28', plain,
% 0.83/1.00      (![X0 : $i]:
% 0.83/1.00         (((k7_relat_1 @ (k6_subset_1 @ X0 @ (k7_relat_1 @ X0 @ sk_B)) @ sk_A)
% 0.83/1.00            = (k1_xboole_0))
% 0.83/1.00          | ~ (v1_relat_1 @ (k6_subset_1 @ X0 @ (k7_relat_1 @ X0 @ sk_B)))
% 0.83/1.00          | ~ (v1_relat_1 @ X0))),
% 0.83/1.00      inference('sup-', [status(thm)], ['24', '27'])).
% 0.83/1.00  thf(fc2_relat_1, axiom,
% 0.83/1.00    (![A:$i,B:$i]:
% 0.83/1.00     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_xboole_0 @ A @ B ) ) ))).
% 0.83/1.00  thf('29', plain,
% 0.83/1.00      (![X13 : $i, X14 : $i]:
% 0.83/1.00         (~ (v1_relat_1 @ X13) | (v1_relat_1 @ (k4_xboole_0 @ X13 @ X14)))),
% 0.83/1.00      inference('cnf', [status(esa)], [fc2_relat_1])).
% 0.83/1.00  thf('30', plain,
% 0.83/1.00      (![X11 : $i, X12 : $i]:
% 0.83/1.00         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.83/1.00      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.83/1.00  thf('31', plain,
% 0.83/1.00      (![X13 : $i, X14 : $i]:
% 0.83/1.00         (~ (v1_relat_1 @ X13) | (v1_relat_1 @ (k6_subset_1 @ X13 @ X14)))),
% 0.83/1.00      inference('demod', [status(thm)], ['29', '30'])).
% 0.83/1.00  thf('32', plain,
% 0.83/1.00      (![X0 : $i]:
% 0.83/1.00         (~ (v1_relat_1 @ X0)
% 0.83/1.00          | ((k7_relat_1 @ (k6_subset_1 @ X0 @ (k7_relat_1 @ X0 @ sk_B)) @ sk_A)
% 0.83/1.00              = (k1_xboole_0)))),
% 0.83/1.00      inference('clc', [status(thm)], ['28', '31'])).
% 0.83/1.00  thf('33', plain,
% 0.83/1.00      (((k7_relat_1 @ (k6_subset_1 @ sk_C @ (k7_relat_1 @ sk_C @ sk_B)) @ sk_A)
% 0.83/1.00         != (k1_xboole_0))),
% 0.83/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.00  thf('34', plain,
% 0.83/1.00      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_C))),
% 0.83/1.00      inference('sup-', [status(thm)], ['32', '33'])).
% 0.83/1.00  thf('35', plain, ((v1_relat_1 @ sk_C)),
% 0.83/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.00  thf('36', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.83/1.00      inference('demod', [status(thm)], ['34', '35'])).
% 0.83/1.00  thf('37', plain, ($false), inference('simplify', [status(thm)], ['36'])).
% 0.83/1.00  
% 0.83/1.00  % SZS output end Refutation
% 0.83/1.00  
% 0.83/1.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Tx2i73gMj4

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:27 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   50 (  86 expanded)
%              Number of leaves         :   16 (  32 expanded)
%              Depth                    :   14
%              Number of atoms          :  454 ( 853 expanded)
%              Number of equality atoms :   17 (  39 expanded)
%              Maximal formula depth    :   14 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) @ X9 )
        = ( k7_relat_1 @ X7 @ ( k3_xboole_0 @ X8 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) )
        = ( k9_relat_1 @ X12 @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
        = ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
        = ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) )
        = ( k9_relat_1 @ X12 @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) )
        = ( k9_relat_1 @ X12 @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X10 @ X11 ) @ ( k2_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k9_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['12','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k9_relat_1 @ X2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf(t154_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t154_relat_1])).

thf('26',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B ) @ ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B ) @ ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    $false ),
    inference(demod,[status(thm)],['30','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Tx2i73gMj4
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:34:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.59/0.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.77  % Solved by: fo/fo7.sh
% 0.59/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.77  % done 167 iterations in 0.285s
% 0.59/0.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.77  % SZS output start Refutation
% 0.59/0.77  thf(sk_C_type, type, sk_C: $i).
% 0.59/0.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.77  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.77  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.59/0.77  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.59/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.77  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.59/0.77  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.59/0.77  thf(t100_relat_1, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( ( v1_relat_1 @ C ) =>
% 0.59/0.77       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.59/0.77         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.59/0.77  thf('0', plain,
% 0.59/0.77      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.59/0.77         (((k7_relat_1 @ (k7_relat_1 @ X7 @ X8) @ X9)
% 0.59/0.77            = (k7_relat_1 @ X7 @ (k3_xboole_0 @ X8 @ X9)))
% 0.59/0.77          | ~ (v1_relat_1 @ X7))),
% 0.59/0.77      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.59/0.77  thf(t148_relat_1, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( v1_relat_1 @ B ) =>
% 0.59/0.77       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.59/0.77  thf('1', plain,
% 0.59/0.77      (![X12 : $i, X13 : $i]:
% 0.59/0.77         (((k2_relat_1 @ (k7_relat_1 @ X12 @ X13)) = (k9_relat_1 @ X12 @ X13))
% 0.59/0.77          | ~ (v1_relat_1 @ X12))),
% 0.59/0.77      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.59/0.77  thf('2', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (((k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 0.59/0.77            = (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.59/0.77          | ~ (v1_relat_1 @ X2)
% 0.59/0.77          | ~ (v1_relat_1 @ X2))),
% 0.59/0.77      inference('sup+', [status(thm)], ['0', '1'])).
% 0.59/0.77  thf('3', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (~ (v1_relat_1 @ X2)
% 0.59/0.77          | ((k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 0.59/0.77              = (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.59/0.77      inference('simplify', [status(thm)], ['2'])).
% 0.59/0.77  thf('4', plain,
% 0.59/0.77      (![X12 : $i, X13 : $i]:
% 0.59/0.77         (((k2_relat_1 @ (k7_relat_1 @ X12 @ X13)) = (k9_relat_1 @ X12 @ X13))
% 0.59/0.77          | ~ (v1_relat_1 @ X12))),
% 0.59/0.77      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.59/0.77  thf('5', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (((k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.59/0.77            = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 0.59/0.77          | ~ (v1_relat_1 @ X2)
% 0.59/0.77          | ~ (v1_relat_1 @ (k7_relat_1 @ X2 @ X1)))),
% 0.59/0.77      inference('sup+', [status(thm)], ['3', '4'])).
% 0.59/0.77  thf(dt_k7_relat_1, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.59/0.77  thf('6', plain,
% 0.59/0.77      (![X5 : $i, X6 : $i]:
% 0.59/0.77         (~ (v1_relat_1 @ X5) | (v1_relat_1 @ (k7_relat_1 @ X5 @ X6)))),
% 0.59/0.77      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.59/0.77  thf('7', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (~ (v1_relat_1 @ X2)
% 0.59/0.77          | ((k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.59/0.77              = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)))),
% 0.59/0.77      inference('clc', [status(thm)], ['5', '6'])).
% 0.59/0.77  thf(commutativity_k3_xboole_0, axiom,
% 0.59/0.77    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.59/0.77  thf('8', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.77      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.59/0.77  thf('9', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (~ (v1_relat_1 @ X2)
% 0.59/0.77          | ((k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.59/0.77              = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)))),
% 0.59/0.77      inference('clc', [status(thm)], ['5', '6'])).
% 0.59/0.77  thf('10', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (((k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.59/0.77            = (k9_relat_1 @ (k7_relat_1 @ X2 @ X0) @ X1))
% 0.59/0.77          | ~ (v1_relat_1 @ X2))),
% 0.59/0.77      inference('sup+', [status(thm)], ['8', '9'])).
% 0.59/0.77  thf('11', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (((k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)
% 0.59/0.77            = (k9_relat_1 @ (k7_relat_1 @ X2 @ X0) @ X1))
% 0.59/0.77          | ~ (v1_relat_1 @ X2)
% 0.59/0.77          | ~ (v1_relat_1 @ X2))),
% 0.59/0.77      inference('sup+', [status(thm)], ['7', '10'])).
% 0.59/0.77  thf('12', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (~ (v1_relat_1 @ X2)
% 0.59/0.77          | ((k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)
% 0.59/0.77              = (k9_relat_1 @ (k7_relat_1 @ X2 @ X0) @ X1)))),
% 0.59/0.77      inference('simplify', [status(thm)], ['11'])).
% 0.59/0.77  thf('13', plain,
% 0.59/0.77      (![X12 : $i, X13 : $i]:
% 0.59/0.77         (((k2_relat_1 @ (k7_relat_1 @ X12 @ X13)) = (k9_relat_1 @ X12 @ X13))
% 0.59/0.77          | ~ (v1_relat_1 @ X12))),
% 0.59/0.77      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.59/0.77  thf(t144_relat_1, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( v1_relat_1 @ B ) =>
% 0.59/0.77       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.59/0.77  thf('14', plain,
% 0.59/0.77      (![X10 : $i, X11 : $i]:
% 0.59/0.77         ((r1_tarski @ (k9_relat_1 @ X10 @ X11) @ (k2_relat_1 @ X10))
% 0.59/0.77          | ~ (v1_relat_1 @ X10))),
% 0.59/0.77      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.59/0.77  thf('15', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         ((r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 0.59/0.77           (k9_relat_1 @ X1 @ X0))
% 0.59/0.77          | ~ (v1_relat_1 @ X1)
% 0.59/0.77          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.59/0.77      inference('sup+', [status(thm)], ['13', '14'])).
% 0.59/0.77  thf('16', plain,
% 0.59/0.77      (![X5 : $i, X6 : $i]:
% 0.59/0.77         (~ (v1_relat_1 @ X5) | (v1_relat_1 @ (k7_relat_1 @ X5 @ X6)))),
% 0.59/0.77      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.59/0.77  thf('17', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (~ (v1_relat_1 @ X1)
% 0.59/0.77          | (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 0.59/0.77             (k9_relat_1 @ X1 @ X0)))),
% 0.59/0.77      inference('clc', [status(thm)], ['15', '16'])).
% 0.59/0.77  thf('18', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         ((r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0) @ 
% 0.59/0.77           (k9_relat_1 @ X2 @ X0))
% 0.59/0.77          | ~ (v1_relat_1 @ X2)
% 0.59/0.77          | ~ (v1_relat_1 @ X2))),
% 0.59/0.77      inference('sup+', [status(thm)], ['12', '17'])).
% 0.59/0.77  thf('19', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (~ (v1_relat_1 @ X2)
% 0.59/0.77          | (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0) @ 
% 0.59/0.77             (k9_relat_1 @ X2 @ X0)))),
% 0.59/0.77      inference('simplify', [status(thm)], ['18'])).
% 0.59/0.77  thf('20', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (~ (v1_relat_1 @ X1)
% 0.59/0.77          | (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 0.59/0.77             (k9_relat_1 @ X1 @ X0)))),
% 0.59/0.77      inference('clc', [status(thm)], ['15', '16'])).
% 0.59/0.77  thf(t19_xboole_1, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.59/0.77       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.59/0.77  thf('21', plain,
% 0.59/0.77      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.59/0.77         (~ (r1_tarski @ X2 @ X3)
% 0.59/0.77          | ~ (r1_tarski @ X2 @ X4)
% 0.59/0.77          | (r1_tarski @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.59/0.77      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.59/0.77  thf('22', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.77         (~ (v1_relat_1 @ X1)
% 0.59/0.77          | (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 0.59/0.77             (k3_xboole_0 @ (k9_relat_1 @ X1 @ X0) @ X3))
% 0.59/0.77          | ~ (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ X3))),
% 0.59/0.77      inference('sup-', [status(thm)], ['20', '21'])).
% 0.59/0.77  thf('23', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (~ (v1_relat_1 @ X1)
% 0.59/0.77          | (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0) @ 
% 0.59/0.77             (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ (k9_relat_1 @ X1 @ X0)))
% 0.59/0.77          | ~ (v1_relat_1 @ X1))),
% 0.59/0.77      inference('sup-', [status(thm)], ['19', '22'])).
% 0.59/0.77  thf('24', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         ((r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0) @ 
% 0.59/0.77           (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ (k9_relat_1 @ X1 @ X0)))
% 0.59/0.77          | ~ (v1_relat_1 @ X1))),
% 0.59/0.77      inference('simplify', [status(thm)], ['23'])).
% 0.59/0.77  thf('25', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (~ (v1_relat_1 @ X2)
% 0.59/0.77          | ((k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.59/0.77              = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)))),
% 0.59/0.77      inference('clc', [status(thm)], ['5', '6'])).
% 0.59/0.77  thf(t154_relat_1, conjecture,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( ( v1_relat_1 @ C ) =>
% 0.59/0.77       ( r1_tarski @
% 0.59/0.77         ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.59/0.77         ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.59/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.77    (~( ![A:$i,B:$i,C:$i]:
% 0.59/0.77        ( ( v1_relat_1 @ C ) =>
% 0.59/0.77          ( r1_tarski @
% 0.59/0.77            ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.59/0.77            ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )),
% 0.59/0.77    inference('cnf.neg', [status(esa)], [t154_relat_1])).
% 0.59/0.77  thf('26', plain,
% 0.59/0.77      (~ (r1_tarski @ (k9_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 0.59/0.77          (k3_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ 
% 0.59/0.77           (k9_relat_1 @ sk_C @ sk_B)))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('27', plain,
% 0.59/0.77      ((~ (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B) @ 
% 0.59/0.77           (k3_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ 
% 0.59/0.77            (k9_relat_1 @ sk_C @ sk_B)))
% 0.59/0.77        | ~ (v1_relat_1 @ sk_C))),
% 0.59/0.77      inference('sup-', [status(thm)], ['25', '26'])).
% 0.59/0.77  thf('28', plain, ((v1_relat_1 @ sk_C)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('29', plain,
% 0.59/0.77      (~ (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B) @ 
% 0.59/0.77          (k3_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ 
% 0.59/0.77           (k9_relat_1 @ sk_C @ sk_B)))),
% 0.59/0.77      inference('demod', [status(thm)], ['27', '28'])).
% 0.59/0.77  thf('30', plain, (~ (v1_relat_1 @ sk_C)),
% 0.59/0.77      inference('sup-', [status(thm)], ['24', '29'])).
% 0.59/0.77  thf('31', plain, ((v1_relat_1 @ sk_C)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('32', plain, ($false), inference('demod', [status(thm)], ['30', '31'])).
% 0.59/0.77  
% 0.59/0.77  % SZS output end Refutation
% 0.59/0.77  
% 0.59/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

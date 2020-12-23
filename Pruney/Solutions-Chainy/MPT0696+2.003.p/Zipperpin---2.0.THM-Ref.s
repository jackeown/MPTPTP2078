%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.isGYErrUDZ

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:37 EST 2020

% Result     : Theorem 2.54s
% Output     : Refutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   52 (  70 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :   12
%              Number of atoms          :  425 ( 584 expanded)
%              Number of equality atoms :   22 (  38 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('0',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('7',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X22 @ X21 ) @ X23 )
        = ( k3_xboole_0 @ X21 @ ( k10_relat_1 @ X22 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('8',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X22 @ X21 ) @ X23 )
        = ( k3_xboole_0 @ X21 @ ( k10_relat_1 @ X22 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) )
        = ( k9_relat_1 @ X17 @ X18 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t168_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k10_relat_1 @ B @ A )
        = ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ) )).

thf('10',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k10_relat_1 @ X19 @ X20 )
        = ( k10_relat_1 @ X19 @ ( k3_xboole_0 @ ( k2_relat_1 @ X19 ) @ X20 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) @ X2 ) ) ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k3_xboole_0 @ X1 @ ( k10_relat_1 @ X2 @ ( k3_xboole_0 @ ( k9_relat_1 @ X2 @ X1 ) @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k3_xboole_0 @ X1 @ ( k10_relat_1 @ X2 @ ( k3_xboole_0 @ ( k9_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X3 @ ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ X3 @ ( k10_relat_1 @ X2 @ ( k3_xboole_0 @ ( k9_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X3 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ X3 @ ( k10_relat_1 @ X1 @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X3 @ ( k10_relat_1 @ X1 @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X3 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ X1 @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) ) @ ( k10_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','22'])).

thf(t151_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) @ ( k10_relat_1 @ C @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( r1_tarski @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) @ ( k10_relat_1 @ C @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t151_funct_1])).

thf('24',plain,(
    ~ ( r1_tarski @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C @ sk_B ) ) @ ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('26',plain,(
    ~ ( r1_tarski @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C @ sk_B ) ) @ ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_B @ ( k9_relat_1 @ sk_C @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['27','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.isGYErrUDZ
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:11:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.54/2.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.54/2.72  % Solved by: fo/fo7.sh
% 2.54/2.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.54/2.72  % done 1734 iterations in 2.268s
% 2.54/2.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.54/2.72  % SZS output start Refutation
% 2.54/2.72  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.54/2.72  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 2.54/2.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.54/2.72  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 2.54/2.72  thf(sk_C_type, type, sk_C: $i).
% 2.54/2.72  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.54/2.72  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 2.54/2.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.54/2.72  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.54/2.72  thf(sk_A_type, type, sk_A: $i).
% 2.54/2.72  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 2.54/2.72  thf(sk_B_type, type, sk_B: $i).
% 2.54/2.72  thf(commutativity_k2_tarski, axiom,
% 2.54/2.72    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 2.54/2.72  thf('0', plain,
% 2.54/2.72      (![X6 : $i, X7 : $i]: ((k2_tarski @ X7 @ X6) = (k2_tarski @ X6 @ X7))),
% 2.54/2.72      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 2.54/2.72  thf(t12_setfam_1, axiom,
% 2.54/2.72    (![A:$i,B:$i]:
% 2.54/2.72     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.54/2.72  thf('1', plain,
% 2.54/2.72      (![X13 : $i, X14 : $i]:
% 2.54/2.72         ((k1_setfam_1 @ (k2_tarski @ X13 @ X14)) = (k3_xboole_0 @ X13 @ X14))),
% 2.54/2.72      inference('cnf', [status(esa)], [t12_setfam_1])).
% 2.54/2.72  thf('2', plain,
% 2.54/2.72      (![X0 : $i, X1 : $i]:
% 2.54/2.72         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 2.54/2.72      inference('sup+', [status(thm)], ['0', '1'])).
% 2.54/2.72  thf('3', plain,
% 2.54/2.72      (![X13 : $i, X14 : $i]:
% 2.54/2.72         ((k1_setfam_1 @ (k2_tarski @ X13 @ X14)) = (k3_xboole_0 @ X13 @ X14))),
% 2.54/2.72      inference('cnf', [status(esa)], [t12_setfam_1])).
% 2.54/2.72  thf('4', plain,
% 2.54/2.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.54/2.72      inference('sup+', [status(thm)], ['2', '3'])).
% 2.54/2.72  thf(d10_xboole_0, axiom,
% 2.54/2.72    (![A:$i,B:$i]:
% 2.54/2.72     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.54/2.72  thf('5', plain,
% 2.54/2.72      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 2.54/2.72      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.54/2.72  thf('6', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.54/2.72      inference('simplify', [status(thm)], ['5'])).
% 2.54/2.72  thf(t139_funct_1, axiom,
% 2.54/2.72    (![A:$i,B:$i,C:$i]:
% 2.54/2.72     ( ( v1_relat_1 @ C ) =>
% 2.54/2.72       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 2.54/2.72         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 2.54/2.72  thf('7', plain,
% 2.54/2.72      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.54/2.72         (((k10_relat_1 @ (k7_relat_1 @ X22 @ X21) @ X23)
% 2.54/2.72            = (k3_xboole_0 @ X21 @ (k10_relat_1 @ X22 @ X23)))
% 2.54/2.72          | ~ (v1_relat_1 @ X22))),
% 2.54/2.72      inference('cnf', [status(esa)], [t139_funct_1])).
% 2.54/2.72  thf('8', plain,
% 2.54/2.72      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.54/2.72         (((k10_relat_1 @ (k7_relat_1 @ X22 @ X21) @ X23)
% 2.54/2.72            = (k3_xboole_0 @ X21 @ (k10_relat_1 @ X22 @ X23)))
% 2.54/2.72          | ~ (v1_relat_1 @ X22))),
% 2.54/2.72      inference('cnf', [status(esa)], [t139_funct_1])).
% 2.54/2.72  thf(t148_relat_1, axiom,
% 2.54/2.72    (![A:$i,B:$i]:
% 2.54/2.72     ( ( v1_relat_1 @ B ) =>
% 2.54/2.72       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 2.54/2.72  thf('9', plain,
% 2.54/2.72      (![X17 : $i, X18 : $i]:
% 2.54/2.72         (((k2_relat_1 @ (k7_relat_1 @ X17 @ X18)) = (k9_relat_1 @ X17 @ X18))
% 2.54/2.72          | ~ (v1_relat_1 @ X17))),
% 2.54/2.72      inference('cnf', [status(esa)], [t148_relat_1])).
% 2.54/2.72  thf(t168_relat_1, axiom,
% 2.54/2.72    (![A:$i,B:$i]:
% 2.54/2.72     ( ( v1_relat_1 @ B ) =>
% 2.54/2.72       ( ( k10_relat_1 @ B @ A ) =
% 2.54/2.72         ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ))).
% 2.54/2.72  thf('10', plain,
% 2.54/2.72      (![X19 : $i, X20 : $i]:
% 2.54/2.72         (((k10_relat_1 @ X19 @ X20)
% 2.54/2.72            = (k10_relat_1 @ X19 @ (k3_xboole_0 @ (k2_relat_1 @ X19) @ X20)))
% 2.54/2.72          | ~ (v1_relat_1 @ X19))),
% 2.54/2.72      inference('cnf', [status(esa)], [t168_relat_1])).
% 2.54/2.72  thf('11', plain,
% 2.54/2.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.54/2.72         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 2.54/2.72            = (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 2.54/2.72               (k3_xboole_0 @ (k9_relat_1 @ X1 @ X0) @ X2)))
% 2.54/2.72          | ~ (v1_relat_1 @ X1)
% 2.54/2.72          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 2.54/2.72      inference('sup+', [status(thm)], ['9', '10'])).
% 2.54/2.72  thf(dt_k7_relat_1, axiom,
% 2.54/2.72    (![A:$i,B:$i]:
% 2.54/2.72     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 2.54/2.72  thf('12', plain,
% 2.54/2.72      (![X15 : $i, X16 : $i]:
% 2.54/2.72         (~ (v1_relat_1 @ X15) | (v1_relat_1 @ (k7_relat_1 @ X15 @ X16)))),
% 2.54/2.72      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 2.54/2.72  thf('13', plain,
% 2.54/2.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.54/2.72         (~ (v1_relat_1 @ X1)
% 2.54/2.72          | ((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 2.54/2.72              = (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 2.54/2.72                 (k3_xboole_0 @ (k9_relat_1 @ X1 @ X0) @ X2))))),
% 2.54/2.72      inference('clc', [status(thm)], ['11', '12'])).
% 2.54/2.72  thf('14', plain,
% 2.54/2.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.54/2.72         (((k10_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)
% 2.54/2.72            = (k3_xboole_0 @ X1 @ 
% 2.54/2.72               (k10_relat_1 @ X2 @ (k3_xboole_0 @ (k9_relat_1 @ X2 @ X1) @ X0))))
% 2.54/2.72          | ~ (v1_relat_1 @ X2)
% 2.54/2.72          | ~ (v1_relat_1 @ X2))),
% 2.54/2.72      inference('sup+', [status(thm)], ['8', '13'])).
% 2.54/2.72  thf('15', plain,
% 2.54/2.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.54/2.72         (~ (v1_relat_1 @ X2)
% 2.54/2.72          | ((k10_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)
% 2.54/2.72              = (k3_xboole_0 @ X1 @ 
% 2.54/2.72                 (k10_relat_1 @ X2 @ 
% 2.54/2.72                  (k3_xboole_0 @ (k9_relat_1 @ X2 @ X1) @ X0)))))),
% 2.54/2.72      inference('simplify', [status(thm)], ['14'])).
% 2.54/2.72  thf('16', plain,
% 2.54/2.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.54/2.72      inference('sup+', [status(thm)], ['2', '3'])).
% 2.54/2.72  thf(t18_xboole_1, axiom,
% 2.54/2.72    (![A:$i,B:$i,C:$i]:
% 2.54/2.72     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 2.54/2.72  thf('17', plain,
% 2.54/2.72      (![X3 : $i, X4 : $i, X5 : $i]:
% 2.54/2.72         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ X3 @ (k3_xboole_0 @ X4 @ X5)))),
% 2.54/2.72      inference('cnf', [status(esa)], [t18_xboole_1])).
% 2.54/2.72  thf('18', plain,
% 2.54/2.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.54/2.72         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X0))),
% 2.54/2.72      inference('sup-', [status(thm)], ['16', '17'])).
% 2.54/2.72  thf('19', plain,
% 2.54/2.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.54/2.72         (~ (r1_tarski @ X3 @ (k10_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 2.54/2.72          | ~ (v1_relat_1 @ X2)
% 2.54/2.72          | (r1_tarski @ X3 @ 
% 2.54/2.72             (k10_relat_1 @ X2 @ (k3_xboole_0 @ (k9_relat_1 @ X2 @ X1) @ X0))))),
% 2.54/2.72      inference('sup-', [status(thm)], ['15', '18'])).
% 2.54/2.72  thf('20', plain,
% 2.54/2.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.54/2.72         (~ (r1_tarski @ X3 @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)))
% 2.54/2.72          | ~ (v1_relat_1 @ X1)
% 2.54/2.72          | (r1_tarski @ X3 @ 
% 2.54/2.72             (k10_relat_1 @ X1 @ (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ X0)))
% 2.54/2.72          | ~ (v1_relat_1 @ X1))),
% 2.54/2.72      inference('sup-', [status(thm)], ['7', '19'])).
% 2.54/2.72  thf('21', plain,
% 2.54/2.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.54/2.72         ((r1_tarski @ X3 @ 
% 2.54/2.72           (k10_relat_1 @ X1 @ (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ X0)))
% 2.54/2.72          | ~ (v1_relat_1 @ X1)
% 2.54/2.72          | ~ (r1_tarski @ X3 @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))))),
% 2.54/2.72      inference('simplify', [status(thm)], ['20'])).
% 2.54/2.72  thf('22', plain,
% 2.54/2.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.54/2.72         (~ (v1_relat_1 @ X1)
% 2.54/2.72          | (r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 2.54/2.72             (k10_relat_1 @ X1 @ (k3_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ X0))))),
% 2.54/2.72      inference('sup-', [status(thm)], ['6', '21'])).
% 2.54/2.72  thf('23', plain,
% 2.54/2.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.54/2.72         ((r1_tarski @ (k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ X2)) @ 
% 2.54/2.72           (k10_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ (k9_relat_1 @ X1 @ X0))))
% 2.54/2.72          | ~ (v1_relat_1 @ X1))),
% 2.54/2.72      inference('sup+', [status(thm)], ['4', '22'])).
% 2.54/2.72  thf(t151_funct_1, conjecture,
% 2.54/2.72    (![A:$i,B:$i,C:$i]:
% 2.54/2.72     ( ( v1_relat_1 @ C ) =>
% 2.54/2.72       ( r1_tarski @
% 2.54/2.72         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) @ 
% 2.54/2.72         ( k10_relat_1 @ C @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ) ))).
% 2.54/2.72  thf(zf_stmt_0, negated_conjecture,
% 2.54/2.72    (~( ![A:$i,B:$i,C:$i]:
% 2.54/2.72        ( ( v1_relat_1 @ C ) =>
% 2.54/2.72          ( r1_tarski @
% 2.54/2.72            ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) @ 
% 2.54/2.72            ( k10_relat_1 @ C @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ) ) )),
% 2.54/2.72    inference('cnf.neg', [status(esa)], [t151_funct_1])).
% 2.54/2.72  thf('24', plain,
% 2.54/2.72      (~ (r1_tarski @ (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_C @ sk_B)) @ 
% 2.54/2.72          (k10_relat_1 @ sk_C @ 
% 2.54/2.72           (k3_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ sk_B)))),
% 2.54/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.72  thf('25', plain,
% 2.54/2.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.54/2.72      inference('sup+', [status(thm)], ['2', '3'])).
% 2.54/2.72  thf('26', plain,
% 2.54/2.72      (~ (r1_tarski @ (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_C @ sk_B)) @ 
% 2.54/2.72          (k10_relat_1 @ sk_C @ 
% 2.54/2.72           (k3_xboole_0 @ sk_B @ (k9_relat_1 @ sk_C @ sk_A))))),
% 2.54/2.72      inference('demod', [status(thm)], ['24', '25'])).
% 2.54/2.72  thf('27', plain, (~ (v1_relat_1 @ sk_C)),
% 2.54/2.72      inference('sup-', [status(thm)], ['23', '26'])).
% 2.54/2.72  thf('28', plain, ((v1_relat_1 @ sk_C)),
% 2.54/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.72  thf('29', plain, ($false), inference('demod', [status(thm)], ['27', '28'])).
% 2.54/2.72  
% 2.54/2.72  % SZS output end Refutation
% 2.54/2.72  
% 2.54/2.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

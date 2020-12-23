%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9AsQx3dtVS

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:30 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :   46 (  53 expanded)
%              Number of leaves         :   17 (  22 expanded)
%              Depth                    :   12
%              Number of atoms          :  281 ( 350 expanded)
%              Number of equality atoms :   12 (  14 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
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

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      | ~ ( r1_tarski @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ sk_A ) @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_tarski @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ sk_A ) @ ( k2_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_B ),
    inference('sup+',[status(thm)],['0','10'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('13',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['13','18'])).

thf(t153_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k9_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('20',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k9_relat_1 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) )
        = ( k2_xboole_0 @ ( k9_relat_1 @ X17 @ X18 ) @ ( k9_relat_1 @ X17 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t153_relat_1])).

thf('21',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ X1 ) @ ( k9_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['25','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9AsQx3dtVS
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:34:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.58/0.79  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.58/0.79  % Solved by: fo/fo7.sh
% 0.58/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.79  % done 819 iterations in 0.359s
% 0.58/0.79  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.58/0.79  % SZS output start Refutation
% 0.58/0.79  thf(sk_C_type, type, sk_C: $i).
% 0.58/0.79  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.58/0.79  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.58/0.79  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.79  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.58/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.79  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.79  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.58/0.79  thf(idempotence_k2_xboole_0, axiom,
% 0.58/0.79    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.58/0.79  thf('0', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 0.58/0.79      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.58/0.79  thf(t156_relat_1, conjecture,
% 0.58/0.79    (![A:$i,B:$i,C:$i]:
% 0.58/0.79     ( ( v1_relat_1 @ C ) =>
% 0.58/0.79       ( ( r1_tarski @ A @ B ) =>
% 0.58/0.79         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.58/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.79    (~( ![A:$i,B:$i,C:$i]:
% 0.58/0.79        ( ( v1_relat_1 @ C ) =>
% 0.58/0.79          ( ( r1_tarski @ A @ B ) =>
% 0.58/0.79            ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )),
% 0.58/0.79    inference('cnf.neg', [status(esa)], [t156_relat_1])).
% 0.58/0.79  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf(d10_xboole_0, axiom,
% 0.58/0.79    (![A:$i,B:$i]:
% 0.58/0.79     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.58/0.79  thf('2', plain,
% 0.58/0.79      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 0.58/0.79      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.58/0.79  thf('3', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.58/0.79      inference('simplify', [status(thm)], ['2'])).
% 0.58/0.79  thf(t43_xboole_1, axiom,
% 0.58/0.79    (![A:$i,B:$i,C:$i]:
% 0.58/0.79     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.58/0.79       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.58/0.79  thf('4', plain,
% 0.58/0.79      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.58/0.79         ((r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.58/0.79          | ~ (r1_tarski @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.58/0.79      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.58/0.79  thf('5', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]:
% 0.58/0.79         (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)),
% 0.58/0.79      inference('sup-', [status(thm)], ['3', '4'])).
% 0.58/0.79  thf(t1_xboole_1, axiom,
% 0.58/0.79    (![A:$i,B:$i,C:$i]:
% 0.58/0.79     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.58/0.79       ( r1_tarski @ A @ C ) ))).
% 0.58/0.79  thf('6', plain,
% 0.58/0.79      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.58/0.79         (~ (r1_tarski @ X6 @ X7)
% 0.58/0.79          | ~ (r1_tarski @ X7 @ X8)
% 0.58/0.79          | (r1_tarski @ X6 @ X8))),
% 0.58/0.79      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.58/0.79  thf('7', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.79         ((r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X2)
% 0.58/0.79          | ~ (r1_tarski @ X0 @ X2))),
% 0.58/0.79      inference('sup-', [status(thm)], ['5', '6'])).
% 0.58/0.79  thf('8', plain,
% 0.58/0.79      (![X0 : $i]:
% 0.58/0.79         (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ sk_A) @ X0) @ sk_B)),
% 0.58/0.79      inference('sup-', [status(thm)], ['1', '7'])).
% 0.58/0.79  thf(t44_xboole_1, axiom,
% 0.58/0.79    (![A:$i,B:$i,C:$i]:
% 0.58/0.79     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 0.58/0.79       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.58/0.79  thf('9', plain,
% 0.58/0.79      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.58/0.79         ((r1_tarski @ X12 @ (k2_xboole_0 @ X13 @ X14))
% 0.58/0.79          | ~ (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X14))),
% 0.58/0.79      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.58/0.79  thf('10', plain,
% 0.58/0.79      (![X0 : $i]:
% 0.58/0.79         (r1_tarski @ (k2_xboole_0 @ X0 @ sk_A) @ (k2_xboole_0 @ X0 @ sk_B))),
% 0.58/0.79      inference('sup-', [status(thm)], ['8', '9'])).
% 0.58/0.79  thf('11', plain, ((r1_tarski @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_B)),
% 0.58/0.79      inference('sup+', [status(thm)], ['0', '10'])).
% 0.58/0.79  thf(commutativity_k2_xboole_0, axiom,
% 0.58/0.79    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.58/0.79  thf('12', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.58/0.79      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.58/0.79  thf('13', plain, ((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_B)),
% 0.58/0.79      inference('demod', [status(thm)], ['11', '12'])).
% 0.58/0.79  thf('14', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.58/0.79      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.58/0.79  thf(t7_xboole_1, axiom,
% 0.58/0.79    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.58/0.79  thf('15', plain,
% 0.58/0.79      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 0.58/0.79      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.58/0.79  thf('16', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.58/0.79      inference('sup+', [status(thm)], ['14', '15'])).
% 0.58/0.79  thf('17', plain,
% 0.58/0.79      (![X3 : $i, X5 : $i]:
% 0.58/0.79         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 0.58/0.79      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.58/0.79  thf('18', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]:
% 0.58/0.79         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 0.58/0.79          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['16', '17'])).
% 0.58/0.79  thf('19', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.58/0.79      inference('sup-', [status(thm)], ['13', '18'])).
% 0.58/0.79  thf(t153_relat_1, axiom,
% 0.58/0.79    (![A:$i,B:$i,C:$i]:
% 0.58/0.79     ( ( v1_relat_1 @ C ) =>
% 0.58/0.79       ( ( k9_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.58/0.79         ( k2_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.58/0.79  thf('20', plain,
% 0.58/0.79      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.58/0.79         (((k9_relat_1 @ X17 @ (k2_xboole_0 @ X18 @ X19))
% 0.58/0.79            = (k2_xboole_0 @ (k9_relat_1 @ X17 @ X18) @ 
% 0.58/0.79               (k9_relat_1 @ X17 @ X19)))
% 0.58/0.79          | ~ (v1_relat_1 @ X17))),
% 0.58/0.79      inference('cnf', [status(esa)], [t153_relat_1])).
% 0.58/0.79  thf('21', plain,
% 0.58/0.79      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 0.58/0.79      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.58/0.79  thf('22', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.79         ((r1_tarski @ (k9_relat_1 @ X2 @ X1) @ 
% 0.58/0.79           (k9_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.58/0.79          | ~ (v1_relat_1 @ X2))),
% 0.58/0.79      inference('sup+', [status(thm)], ['20', '21'])).
% 0.58/0.79  thf('23', plain,
% 0.58/0.79      (![X0 : $i]:
% 0.58/0.79         ((r1_tarski @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B))
% 0.58/0.79          | ~ (v1_relat_1 @ X0))),
% 0.58/0.79      inference('sup+', [status(thm)], ['19', '22'])).
% 0.58/0.79  thf('24', plain,
% 0.58/0.79      (~ (r1_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('25', plain, (~ (v1_relat_1 @ sk_C)),
% 0.58/0.79      inference('sup-', [status(thm)], ['23', '24'])).
% 0.58/0.79  thf('26', plain, ((v1_relat_1 @ sk_C)),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('27', plain, ($false), inference('demod', [status(thm)], ['25', '26'])).
% 0.58/0.79  
% 0.58/0.79  % SZS output end Refutation
% 0.58/0.79  
% 0.58/0.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

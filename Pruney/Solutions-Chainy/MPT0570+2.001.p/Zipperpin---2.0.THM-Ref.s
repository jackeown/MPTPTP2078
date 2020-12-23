%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6S3vghsJR3

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:07 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   65 (  78 expanded)
%              Number of leaves         :   27 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :  346 ( 502 expanded)
%              Number of equality atoms :   30 (  46 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('0',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_xboole_0 @ X13 )
      | ~ ( v1_xboole_0 @ X14 )
      | ( X13 = X14 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf(t174_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( A != k1_xboole_0 )
          & ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
          & ( ( k10_relat_1 @ B @ A )
            = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ~ ( ( A != k1_xboole_0 )
            & ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
            & ( ( k10_relat_1 @ B @ A )
              = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t174_relat_1])).

thf('1',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( sk_A != X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('3',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( sk_A != X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['4'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('6',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('7',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('9',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X11 @ X12 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('14',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('15',plain,
    ( sk_A
    = ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('16',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('17',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('18',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k1_setfam_1 @ ( k2_tarski @ X3 @ X6 ) ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( r1_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,
    ( ( k10_relat_1 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t173_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k10_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('21',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k10_relat_1 @ X19 @ X20 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ X19 ) @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t173_relat_1])).

thf('22',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ),
    inference(simplify,[status(thm)],['24'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('26',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_tarski @ X16 @ X15 )
      = ( k2_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('27',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('28',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('29',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ ( k1_setfam_1 @ ( k2_tarski @ X3 @ X4 ) ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k1_setfam_1 @ ( k2_tarski @ X3 @ X6 ) ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r1_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['25','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','33'])).

thf('35',plain,(
    v1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['6','34'])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['5','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6S3vghsJR3
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:28:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.40/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.62  % Solved by: fo/fo7.sh
% 0.40/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.62  % done 304 iterations in 0.152s
% 0.40/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.62  % SZS output start Refutation
% 0.40/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.40/0.62  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.40/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.40/0.62  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.40/0.62  thf(sk_B_type, type, sk_B: $i > $i).
% 0.40/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.40/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.62  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.40/0.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.40/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.40/0.62  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.40/0.62  thf(t8_boole, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.40/0.62  thf('0', plain,
% 0.40/0.62      (![X13 : $i, X14 : $i]:
% 0.40/0.62         (~ (v1_xboole_0 @ X13) | ~ (v1_xboole_0 @ X14) | ((X13) = (X14)))),
% 0.40/0.62      inference('cnf', [status(esa)], [t8_boole])).
% 0.40/0.62  thf(t174_relat_1, conjecture,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( v1_relat_1 @ B ) =>
% 0.40/0.62       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.40/0.62            ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) & 
% 0.40/0.62            ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.40/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.62    (~( ![A:$i,B:$i]:
% 0.40/0.62        ( ( v1_relat_1 @ B ) =>
% 0.40/0.62          ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.40/0.62               ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) & 
% 0.40/0.62               ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.40/0.62    inference('cnf.neg', [status(esa)], [t174_relat_1])).
% 0.40/0.62  thf('1', plain, (((sk_A) != (k1_xboole_0))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('2', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (((sk_A) != (X0))
% 0.40/0.62          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.40/0.62          | ~ (v1_xboole_0 @ X0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['0', '1'])).
% 0.40/0.62  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.40/0.62  thf('3', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.40/0.62  thf('4', plain, (![X0 : $i]: (((sk_A) != (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.40/0.62      inference('demod', [status(thm)], ['2', '3'])).
% 0.40/0.62  thf('5', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.40/0.62      inference('simplify', [status(thm)], ['4'])).
% 0.40/0.62  thf(d1_xboole_0, axiom,
% 0.40/0.62    (![A:$i]:
% 0.40/0.62     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.40/0.62  thf('6', plain,
% 0.40/0.62      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.40/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.40/0.62  thf('7', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_B_1))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf(l32_xboole_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.40/0.62  thf('8', plain,
% 0.40/0.62      (![X7 : $i, X9 : $i]:
% 0.40/0.62         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.40/0.62      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.40/0.62  thf('9', plain,
% 0.40/0.62      (((k4_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B_1)) = (k1_xboole_0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['7', '8'])).
% 0.40/0.62  thf(t48_xboole_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.40/0.62  thf('10', plain,
% 0.40/0.62      (![X11 : $i, X12 : $i]:
% 0.40/0.62         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.40/0.62           = (k3_xboole_0 @ X11 @ X12))),
% 0.40/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.40/0.62  thf(t12_setfam_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.40/0.62  thf('11', plain,
% 0.40/0.62      (![X17 : $i, X18 : $i]:
% 0.40/0.62         ((k1_setfam_1 @ (k2_tarski @ X17 @ X18)) = (k3_xboole_0 @ X17 @ X18))),
% 0.40/0.62      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.40/0.62  thf('12', plain,
% 0.40/0.62      (![X11 : $i, X12 : $i]:
% 0.40/0.62         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.40/0.62           = (k1_setfam_1 @ (k2_tarski @ X11 @ X12)))),
% 0.40/0.62      inference('demod', [status(thm)], ['10', '11'])).
% 0.40/0.62  thf('13', plain,
% 0.40/0.62      (((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 0.40/0.62         = (k1_setfam_1 @ (k2_tarski @ sk_A @ (k2_relat_1 @ sk_B_1))))),
% 0.40/0.62      inference('sup+', [status(thm)], ['9', '12'])).
% 0.40/0.62  thf(t3_boole, axiom,
% 0.40/0.62    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.40/0.62  thf('14', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.40/0.62      inference('cnf', [status(esa)], [t3_boole])).
% 0.40/0.62  thf('15', plain,
% 0.40/0.62      (((sk_A) = (k1_setfam_1 @ (k2_tarski @ sk_A @ (k2_relat_1 @ sk_B_1))))),
% 0.40/0.62      inference('demod', [status(thm)], ['13', '14'])).
% 0.40/0.62  thf(t4_xboole_0, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.40/0.62            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.40/0.62       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.40/0.62            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.40/0.62  thf('16', plain,
% 0.40/0.62      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.40/0.62         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.40/0.62          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.40/0.62      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.40/0.62  thf('17', plain,
% 0.40/0.62      (![X17 : $i, X18 : $i]:
% 0.40/0.62         ((k1_setfam_1 @ (k2_tarski @ X17 @ X18)) = (k3_xboole_0 @ X17 @ X18))),
% 0.40/0.62      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.40/0.62  thf('18', plain,
% 0.40/0.62      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.40/0.62         (~ (r2_hidden @ X5 @ (k1_setfam_1 @ (k2_tarski @ X3 @ X6)))
% 0.40/0.62          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.40/0.62      inference('demod', [status(thm)], ['16', '17'])).
% 0.40/0.62  thf('19', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (~ (r2_hidden @ X0 @ sk_A)
% 0.40/0.62          | ~ (r1_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B_1)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['15', '18'])).
% 0.40/0.62  thf('20', plain, (((k10_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf(t173_relat_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( v1_relat_1 @ B ) =>
% 0.40/0.62       ( ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.40/0.62         ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.40/0.62  thf('21', plain,
% 0.40/0.62      (![X19 : $i, X20 : $i]:
% 0.40/0.62         (((k10_relat_1 @ X19 @ X20) != (k1_xboole_0))
% 0.40/0.62          | (r1_xboole_0 @ (k2_relat_1 @ X19) @ X20)
% 0.40/0.62          | ~ (v1_relat_1 @ X19))),
% 0.40/0.62      inference('cnf', [status(esa)], [t173_relat_1])).
% 0.40/0.62  thf('22', plain,
% 0.40/0.62      ((((k1_xboole_0) != (k1_xboole_0))
% 0.40/0.62        | ~ (v1_relat_1 @ sk_B_1)
% 0.40/0.62        | (r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A))),
% 0.40/0.62      inference('sup-', [status(thm)], ['20', '21'])).
% 0.40/0.62  thf('23', plain, ((v1_relat_1 @ sk_B_1)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('24', plain,
% 0.40/0.62      ((((k1_xboole_0) != (k1_xboole_0))
% 0.40/0.62        | (r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A))),
% 0.40/0.62      inference('demod', [status(thm)], ['22', '23'])).
% 0.40/0.62  thf('25', plain, ((r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A)),
% 0.40/0.62      inference('simplify', [status(thm)], ['24'])).
% 0.40/0.62  thf(commutativity_k2_tarski, axiom,
% 0.40/0.62    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.40/0.62  thf('26', plain,
% 0.40/0.62      (![X15 : $i, X16 : $i]:
% 0.40/0.62         ((k2_tarski @ X16 @ X15) = (k2_tarski @ X15 @ X16))),
% 0.40/0.62      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.40/0.62  thf('27', plain,
% 0.40/0.62      (![X3 : $i, X4 : $i]:
% 0.40/0.62         ((r1_xboole_0 @ X3 @ X4)
% 0.40/0.62          | (r2_hidden @ (sk_C @ X4 @ X3) @ (k3_xboole_0 @ X3 @ X4)))),
% 0.40/0.62      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.40/0.62  thf('28', plain,
% 0.40/0.62      (![X17 : $i, X18 : $i]:
% 0.40/0.62         ((k1_setfam_1 @ (k2_tarski @ X17 @ X18)) = (k3_xboole_0 @ X17 @ X18))),
% 0.40/0.62      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.40/0.62  thf('29', plain,
% 0.40/0.62      (![X3 : $i, X4 : $i]:
% 0.40/0.62         ((r1_xboole_0 @ X3 @ X4)
% 0.40/0.62          | (r2_hidden @ (sk_C @ X4 @ X3) @ 
% 0.40/0.62             (k1_setfam_1 @ (k2_tarski @ X3 @ X4))))),
% 0.40/0.62      inference('demod', [status(thm)], ['27', '28'])).
% 0.40/0.62  thf('30', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         ((r2_hidden @ (sk_C @ X1 @ X0) @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 0.40/0.62          | (r1_xboole_0 @ X0 @ X1))),
% 0.40/0.62      inference('sup+', [status(thm)], ['26', '29'])).
% 0.40/0.62  thf('31', plain,
% 0.40/0.62      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.40/0.62         (~ (r2_hidden @ X5 @ (k1_setfam_1 @ (k2_tarski @ X3 @ X6)))
% 0.40/0.62          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.40/0.62      inference('demod', [status(thm)], ['16', '17'])).
% 0.40/0.62  thf('32', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['30', '31'])).
% 0.40/0.62  thf('33', plain, ((r1_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B_1))),
% 0.40/0.62      inference('sup-', [status(thm)], ['25', '32'])).
% 0.40/0.62  thf('34', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_A)),
% 0.40/0.62      inference('demod', [status(thm)], ['19', '33'])).
% 0.40/0.62  thf('35', plain, ((v1_xboole_0 @ sk_A)),
% 0.40/0.62      inference('sup-', [status(thm)], ['6', '34'])).
% 0.40/0.62  thf('36', plain, ($false), inference('demod', [status(thm)], ['5', '35'])).
% 0.40/0.62  
% 0.40/0.62  % SZS output end Refutation
% 0.40/0.62  
% 0.47/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

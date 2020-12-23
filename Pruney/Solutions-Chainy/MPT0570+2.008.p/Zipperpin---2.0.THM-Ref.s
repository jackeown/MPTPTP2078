%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XPljfO25HA

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:08 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   51 (  57 expanded)
%              Number of leaves         :   23 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :  250 ( 334 expanded)
%              Number of equality atoms :   25 (  37 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('0',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_xboole_0 @ X15 )
      | ~ ( v1_xboole_0 @ X16 )
      | ( X15 = X16 ) ) ),
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
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
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
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('11',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('13',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('15',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,
    ( ( k10_relat_1 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t173_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k10_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('19',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k10_relat_1 @ X19 @ X20 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ X19 ) @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t173_relat_1])).

thf('20',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','23'])).

thf('25',plain,(
    v1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['6','24'])).

thf('26',plain,(
    $false ),
    inference(demod,[status(thm)],['5','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XPljfO25HA
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:11:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.19/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.54  % Solved by: fo/fo7.sh
% 0.19/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.54  % done 191 iterations in 0.089s
% 0.19/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.54  % SZS output start Refutation
% 0.19/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.54  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.19/0.54  thf(t8_boole, axiom,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.19/0.54  thf('0', plain,
% 0.19/0.54      (![X15 : $i, X16 : $i]:
% 0.19/0.54         (~ (v1_xboole_0 @ X15) | ~ (v1_xboole_0 @ X16) | ((X15) = (X16)))),
% 0.19/0.54      inference('cnf', [status(esa)], [t8_boole])).
% 0.19/0.54  thf(t174_relat_1, conjecture,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( v1_relat_1 @ B ) =>
% 0.19/0.54       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.19/0.54            ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) & 
% 0.19/0.54            ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.19/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.54    (~( ![A:$i,B:$i]:
% 0.19/0.54        ( ( v1_relat_1 @ B ) =>
% 0.19/0.54          ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.19/0.54               ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) & 
% 0.19/0.54               ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.19/0.54    inference('cnf.neg', [status(esa)], [t174_relat_1])).
% 0.19/0.54  thf('1', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('2', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         (((sk_A) != (X0))
% 0.19/0.54          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.19/0.54          | ~ (v1_xboole_0 @ X0))),
% 0.19/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.54  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.19/0.54  thf('3', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.54  thf('4', plain, (![X0 : $i]: (((sk_A) != (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.19/0.54      inference('demod', [status(thm)], ['2', '3'])).
% 0.19/0.54  thf('5', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.19/0.54      inference('simplify', [status(thm)], ['4'])).
% 0.19/0.54  thf(d1_xboole_0, axiom,
% 0.19/0.54    (![A:$i]:
% 0.19/0.54     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.19/0.54  thf('6', plain,
% 0.19/0.54      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.19/0.54      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.19/0.54  thf('7', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_B_1))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf(l32_xboole_1, axiom,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.54  thf('8', plain,
% 0.19/0.54      (![X9 : $i, X11 : $i]:
% 0.19/0.54         (((k4_xboole_0 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 0.19/0.54      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.19/0.54  thf('9', plain,
% 0.19/0.54      (((k4_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B_1)) = (k1_xboole_0))),
% 0.19/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.54  thf(t48_xboole_1, axiom,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.19/0.54  thf('10', plain,
% 0.19/0.54      (![X13 : $i, X14 : $i]:
% 0.19/0.54         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.19/0.54           = (k3_xboole_0 @ X13 @ X14))),
% 0.19/0.54      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.19/0.54  thf('11', plain,
% 0.19/0.54      (((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 0.19/0.54         = (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B_1)))),
% 0.19/0.54      inference('sup+', [status(thm)], ['9', '10'])).
% 0.19/0.54  thf(t3_boole, axiom,
% 0.19/0.54    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.19/0.54  thf('12', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.19/0.54      inference('cnf', [status(esa)], [t3_boole])).
% 0.19/0.54  thf('13', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B_1)))),
% 0.19/0.54      inference('demod', [status(thm)], ['11', '12'])).
% 0.19/0.54  thf(commutativity_k3_xboole_0, axiom,
% 0.19/0.54    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.19/0.54  thf('14', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.54  thf(t4_xboole_0, axiom,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.54            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.54       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.19/0.54            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.19/0.54  thf('15', plain,
% 0.19/0.54      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.19/0.54         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.19/0.54          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.19/0.54      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.19/0.54  thf('16', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.54         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.19/0.54          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.19/0.54      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.54  thf('17', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         (~ (r2_hidden @ X0 @ sk_A)
% 0.19/0.54          | ~ (r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A))),
% 0.19/0.54      inference('sup-', [status(thm)], ['13', '16'])).
% 0.19/0.54  thf('18', plain, (((k10_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf(t173_relat_1, axiom,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( v1_relat_1 @ B ) =>
% 0.19/0.54       ( ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.19/0.54         ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.19/0.54  thf('19', plain,
% 0.19/0.54      (![X19 : $i, X20 : $i]:
% 0.19/0.54         (((k10_relat_1 @ X19 @ X20) != (k1_xboole_0))
% 0.19/0.54          | (r1_xboole_0 @ (k2_relat_1 @ X19) @ X20)
% 0.19/0.54          | ~ (v1_relat_1 @ X19))),
% 0.19/0.54      inference('cnf', [status(esa)], [t173_relat_1])).
% 0.19/0.54  thf('20', plain,
% 0.19/0.54      ((((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.54        | ~ (v1_relat_1 @ sk_B_1)
% 0.19/0.54        | (r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A))),
% 0.19/0.54      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.54  thf('21', plain, ((v1_relat_1 @ sk_B_1)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('22', plain,
% 0.19/0.54      ((((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.54        | (r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A))),
% 0.19/0.54      inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.54  thf('23', plain, ((r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A)),
% 0.19/0.54      inference('simplify', [status(thm)], ['22'])).
% 0.19/0.54  thf('24', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_A)),
% 0.19/0.54      inference('demod', [status(thm)], ['17', '23'])).
% 0.19/0.54  thf('25', plain, ((v1_xboole_0 @ sk_A)),
% 0.19/0.54      inference('sup-', [status(thm)], ['6', '24'])).
% 0.19/0.54  thf('26', plain, ($false), inference('demod', [status(thm)], ['5', '25'])).
% 0.19/0.54  
% 0.19/0.54  % SZS output end Refutation
% 0.19/0.54  
% 0.19/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

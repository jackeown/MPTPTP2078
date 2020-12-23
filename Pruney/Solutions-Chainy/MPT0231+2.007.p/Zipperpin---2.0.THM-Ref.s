%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eetDXbOwBP

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   51 (  73 expanded)
%              Number of leaves         :   17 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :  304 ( 504 expanded)
%              Number of equality atoms :   29 (  50 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t26_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
     => ( A = C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
       => ( A = C ) ) ),
    inference('cnf.neg',[status(esa)],[t26_zfmisc_1])).

thf('0',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X8: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X8 @ X10 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('2',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('4',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( X23 != X22 )
      | ( r2_hidden @ X23 @ X24 )
      | ( X24
       != ( k2_tarski @ X25 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('5',plain,(
    ! [X22: $i,X25: $i] :
      ( r2_hidden @ X22 @ ( k2_tarski @ X25 @ X22 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('7',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,
    ( ( r2_hidden @ sk_B @ k1_xboole_0 )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('10',plain,(
    ! [X13: $i] :
      ( r1_xboole_0 @ X13 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('11',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('14',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['15'])).

thf('17',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_C_1 ) ),
    inference(clc,[status(thm)],['9','16'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('18',plain,(
    ! [X17: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X20 @ X19 )
      | ( X20 = X17 )
      | ( X19
       != ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('19',plain,(
    ! [X17: $i,X20: $i] :
      ( ( X20 = X17 )
      | ~ ( r2_hidden @ X20 @ ( k1_tarski @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    sk_B = sk_C_1 ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_1 ) @ ( k1_tarski @ sk_C_1 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['2','20'])).

thf('22',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( X23 != X25 )
      | ( r2_hidden @ X23 @ X24 )
      | ( X24
       != ( k2_tarski @ X25 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('23',plain,(
    ! [X22: $i,X25: $i] :
      ( r2_hidden @ X25 @ ( k2_tarski @ X25 @ X22 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X1 @ ( k4_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r2_hidden @ sk_A @ k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['21','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['15'])).

thf('28',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_C_1 ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X17: $i,X20: $i] :
      ( ( X20 = X17 )
      | ~ ( r2_hidden @ X20 @ ( k1_tarski @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('30',plain,(
    sk_A = sk_C_1 ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['30','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eetDXbOwBP
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:37:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 237 iterations in 0.088s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.54  thf(t26_zfmisc_1, conjecture,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.21/0.54       ( ( A ) = ( C ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.54        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.21/0.54          ( ( A ) = ( C ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t26_zfmisc_1])).
% 0.21/0.54  thf('0', plain,
% 0.21/0.54      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C_1))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(l32_xboole_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.54  thf('1', plain,
% 0.21/0.54      (![X8 : $i, X10 : $i]:
% 0.21/0.54         (((k4_xboole_0 @ X8 @ X10) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ X10))),
% 0.21/0.54      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C_1))
% 0.21/0.54         = (k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C_1))
% 0.21/0.54         = (k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.54  thf(d2_tarski, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.21/0.54       ( ![D:$i]:
% 0.21/0.54         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.21/0.54  thf('4', plain,
% 0.21/0.54      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.54         (((X23) != (X22))
% 0.21/0.54          | (r2_hidden @ X23 @ X24)
% 0.21/0.54          | ((X24) != (k2_tarski @ X25 @ X22)))),
% 0.21/0.54      inference('cnf', [status(esa)], [d2_tarski])).
% 0.21/0.54  thf('5', plain,
% 0.21/0.54      (![X22 : $i, X25 : $i]: (r2_hidden @ X22 @ (k2_tarski @ X25 @ X22))),
% 0.21/0.54      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.54  thf(d5_xboole_0, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.21/0.54       ( ![D:$i]:
% 0.21/0.54         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.54           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.21/0.54  thf('6', plain,
% 0.21/0.54      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X2 @ X3)
% 0.21/0.54          | (r2_hidden @ X2 @ X4)
% 0.21/0.54          | (r2_hidden @ X2 @ X5)
% 0.21/0.54          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.21/0.54      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.54  thf('7', plain,
% 0.21/0.54      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.54         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 0.21/0.54          | (r2_hidden @ X2 @ X4)
% 0.21/0.54          | ~ (r2_hidden @ X2 @ X3))),
% 0.21/0.54      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.54  thf('8', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         ((r2_hidden @ X0 @ X2)
% 0.21/0.54          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['5', '7'])).
% 0.21/0.54  thf('9', plain,
% 0.21/0.54      (((r2_hidden @ sk_B @ k1_xboole_0)
% 0.21/0.54        | (r2_hidden @ sk_B @ (k1_tarski @ sk_C_1)))),
% 0.21/0.54      inference('sup+', [status(thm)], ['3', '8'])).
% 0.21/0.54  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.21/0.54  thf('10', plain, (![X13 : $i]: (r1_xboole_0 @ X13 @ k1_xboole_0)),
% 0.21/0.54      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.54  thf(t83_xboole_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.54  thf('11', plain,
% 0.21/0.54      (![X14 : $i, X15 : $i]:
% 0.21/0.54         (((k4_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_xboole_0 @ X14 @ X15))),
% 0.21/0.54      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.54  thf('12', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.54  thf('13', plain,
% 0.21/0.54      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X6 @ X5)
% 0.21/0.54          | ~ (r2_hidden @ X6 @ X4)
% 0.21/0.54          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.21/0.54      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.54  thf('14', plain,
% 0.21/0.54      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X6 @ X4)
% 0.21/0.54          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.54  thf('15', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['12', '14'])).
% 0.21/0.54  thf('16', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.54      inference('condensation', [status(thm)], ['15'])).
% 0.21/0.54  thf('17', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_C_1))),
% 0.21/0.54      inference('clc', [status(thm)], ['9', '16'])).
% 0.21/0.54  thf(d1_tarski, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.54  thf('18', plain,
% 0.21/0.54      (![X17 : $i, X19 : $i, X20 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X20 @ X19)
% 0.21/0.54          | ((X20) = (X17))
% 0.21/0.54          | ((X19) != (k1_tarski @ X17)))),
% 0.21/0.54      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.54  thf('19', plain,
% 0.21/0.54      (![X17 : $i, X20 : $i]:
% 0.21/0.54         (((X20) = (X17)) | ~ (r2_hidden @ X20 @ (k1_tarski @ X17)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.54  thf('20', plain, (((sk_B) = (sk_C_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['17', '19'])).
% 0.21/0.54  thf('21', plain,
% 0.21/0.54      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_C_1) @ (k1_tarski @ sk_C_1))
% 0.21/0.54         = (k1_xboole_0))),
% 0.21/0.54      inference('demod', [status(thm)], ['2', '20'])).
% 0.21/0.54  thf('22', plain,
% 0.21/0.54      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.54         (((X23) != (X25))
% 0.21/0.54          | (r2_hidden @ X23 @ X24)
% 0.21/0.54          | ((X24) != (k2_tarski @ X25 @ X22)))),
% 0.21/0.54      inference('cnf', [status(esa)], [d2_tarski])).
% 0.21/0.54  thf('23', plain,
% 0.21/0.54      (![X22 : $i, X25 : $i]: (r2_hidden @ X25 @ (k2_tarski @ X25 @ X22))),
% 0.21/0.54      inference('simplify', [status(thm)], ['22'])).
% 0.21/0.54  thf('24', plain,
% 0.21/0.54      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.54         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 0.21/0.54          | (r2_hidden @ X2 @ X4)
% 0.21/0.54          | ~ (r2_hidden @ X2 @ X3))),
% 0.21/0.54      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.54  thf('25', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         ((r2_hidden @ X1 @ X2)
% 0.21/0.54          | (r2_hidden @ X1 @ (k4_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.54  thf('26', plain,
% 0.21/0.54      (((r2_hidden @ sk_A @ k1_xboole_0)
% 0.21/0.54        | (r2_hidden @ sk_A @ (k1_tarski @ sk_C_1)))),
% 0.21/0.54      inference('sup+', [status(thm)], ['21', '25'])).
% 0.21/0.54  thf('27', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.54      inference('condensation', [status(thm)], ['15'])).
% 0.21/0.54  thf('28', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_C_1))),
% 0.21/0.54      inference('clc', [status(thm)], ['26', '27'])).
% 0.21/0.54  thf('29', plain,
% 0.21/0.54      (![X17 : $i, X20 : $i]:
% 0.21/0.54         (((X20) = (X17)) | ~ (r2_hidden @ X20 @ (k1_tarski @ X17)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.54  thf('30', plain, (((sk_A) = (sk_C_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.54  thf('31', plain, (((sk_A) != (sk_C_1))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('32', plain, ($false),
% 0.21/0.54      inference('simplify_reflect-', [status(thm)], ['30', '31'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

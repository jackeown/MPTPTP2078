%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SZhopCgXXx

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:04 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   51 (  58 expanded)
%              Number of leaves         :   20 (  26 expanded)
%              Depth                    :   12
%              Number of atoms          :  229 ( 275 expanded)
%              Number of equality atoms :   22 (  25 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(t50_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t50_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ sk_C_1 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ sk_C_1 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ~ ( v1_xboole_0 @ ( k2_xboole_0 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( v1_xboole_0 @ X8 )
      | ~ ( v1_xboole_0 @ ( k2_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_xboole_0])).

thf('3',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('4',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('5',plain,(
    v1_xboole_0 @ sk_C_1 ),
    inference(demod,[status(thm)],['3','4'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('7',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['0','7'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('10',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X8: $i,X9: $i] :
      ( ( v1_xboole_0 @ X8 )
      | ~ ( v1_xboole_0 @ ( k2_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_xboole_0])).

thf('12',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('14',plain,(
    v1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('16',plain,
    ( ( k2_tarski @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['14','15'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('17',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X16 != X15 )
      | ( r2_hidden @ X16 @ X17 )
      | ( X17
       != ( k2_tarski @ X18 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('18',plain,(
    ! [X15: $i,X18: $i] :
      ( r2_hidden @ X15 @ ( k2_tarski @ X18 @ X15 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    r2_hidden @ sk_B_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['16','18'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('20',plain,(
    ! [X12: $i] :
      ( r1_xboole_0 @ X12 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('21',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('22',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X12: $i] :
      ( r1_xboole_0 @ X12 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('28',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    $false ),
    inference('sup-',[status(thm)],['19','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SZhopCgXXx
% 0.15/0.39  % Computer   : n018.cluster.edu
% 0.15/0.39  % Model      : x86_64 x86_64
% 0.15/0.39  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.39  % Memory     : 8042.1875MB
% 0.15/0.39  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.39  % CPULimit   : 60
% 0.15/0.39  % DateTime   : Tue Dec  1 20:46:27 EST 2020
% 0.15/0.39  % CPUTime    : 
% 0.15/0.39  % Running portfolio for 600 s
% 0.15/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.39  % Number of cores: 8
% 0.15/0.39  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 0.25/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.55  % Solved by: fo/fo7.sh
% 0.25/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.55  % done 69 iterations in 0.050s
% 0.25/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.55  % SZS output start Refutation
% 0.25/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.25/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.25/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.25/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.25/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.25/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.25/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.25/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.25/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.25/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.25/0.55  thf(t50_zfmisc_1, conjecture,
% 0.25/0.55    (![A:$i,B:$i,C:$i]:
% 0.25/0.55     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 0.25/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.25/0.55        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) )),
% 0.25/0.55    inference('cnf.neg', [status(esa)], [t50_zfmisc_1])).
% 0.25/0.55  thf('0', plain,
% 0.25/0.55      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ sk_C_1) = (k1_xboole_0))),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('1', plain,
% 0.25/0.55      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ sk_C_1) = (k1_xboole_0))),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf(fc5_xboole_0, axiom,
% 0.25/0.55    (![A:$i,B:$i]:
% 0.25/0.55     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.25/0.55       ( ~( v1_xboole_0 @ ( k2_xboole_0 @ B @ A ) ) ) ))).
% 0.25/0.55  thf('2', plain,
% 0.25/0.55      (![X8 : $i, X9 : $i]:
% 0.25/0.55         ((v1_xboole_0 @ X8) | ~ (v1_xboole_0 @ (k2_xboole_0 @ X9 @ X8)))),
% 0.25/0.55      inference('cnf', [status(esa)], [fc5_xboole_0])).
% 0.25/0.55  thf('3', plain, ((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_C_1))),
% 0.25/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.25/0.55  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.25/0.55  thf('4', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.25/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.25/0.55  thf('5', plain, ((v1_xboole_0 @ sk_C_1)),
% 0.25/0.55      inference('demod', [status(thm)], ['3', '4'])).
% 0.25/0.55  thf(l13_xboole_0, axiom,
% 0.25/0.55    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.25/0.55  thf('6', plain,
% 0.25/0.55      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X2))),
% 0.25/0.55      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.25/0.55  thf('7', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.25/0.55      inference('sup-', [status(thm)], ['5', '6'])).
% 0.25/0.55  thf('8', plain,
% 0.25/0.55      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ k1_xboole_0)
% 0.25/0.55         = (k1_xboole_0))),
% 0.25/0.55      inference('demod', [status(thm)], ['0', '7'])).
% 0.25/0.55  thf(commutativity_k2_xboole_0, axiom,
% 0.25/0.55    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.25/0.55  thf('9', plain,
% 0.25/0.55      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.25/0.55      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.25/0.55  thf('10', plain,
% 0.25/0.55      (((k2_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1))
% 0.25/0.55         = (k1_xboole_0))),
% 0.25/0.55      inference('demod', [status(thm)], ['8', '9'])).
% 0.25/0.55  thf('11', plain,
% 0.25/0.55      (![X8 : $i, X9 : $i]:
% 0.25/0.55         ((v1_xboole_0 @ X8) | ~ (v1_xboole_0 @ (k2_xboole_0 @ X9 @ X8)))),
% 0.25/0.55      inference('cnf', [status(esa)], [fc5_xboole_0])).
% 0.25/0.55  thf('12', plain,
% 0.25/0.55      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.25/0.55        | (v1_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1)))),
% 0.25/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.25/0.55  thf('13', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.25/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.25/0.55  thf('14', plain, ((v1_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1))),
% 0.25/0.55      inference('demod', [status(thm)], ['12', '13'])).
% 0.25/0.55  thf('15', plain,
% 0.25/0.55      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X2))),
% 0.25/0.55      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.25/0.55  thf('16', plain, (((k2_tarski @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.25/0.55      inference('sup-', [status(thm)], ['14', '15'])).
% 0.25/0.55  thf(d2_tarski, axiom,
% 0.25/0.55    (![A:$i,B:$i,C:$i]:
% 0.25/0.55     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.25/0.55       ( ![D:$i]:
% 0.25/0.55         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.25/0.55  thf('17', plain,
% 0.25/0.55      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.25/0.55         (((X16) != (X15))
% 0.25/0.55          | (r2_hidden @ X16 @ X17)
% 0.25/0.55          | ((X17) != (k2_tarski @ X18 @ X15)))),
% 0.25/0.55      inference('cnf', [status(esa)], [d2_tarski])).
% 0.25/0.55  thf('18', plain,
% 0.25/0.55      (![X15 : $i, X18 : $i]: (r2_hidden @ X15 @ (k2_tarski @ X18 @ X15))),
% 0.25/0.55      inference('simplify', [status(thm)], ['17'])).
% 0.25/0.55  thf('19', plain, ((r2_hidden @ sk_B_1 @ k1_xboole_0)),
% 0.25/0.55      inference('sup+', [status(thm)], ['16', '18'])).
% 0.25/0.55  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.25/0.55  thf('20', plain, (![X12 : $i]: (r1_xboole_0 @ X12 @ k1_xboole_0)),
% 0.25/0.55      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.25/0.55  thf(t7_xboole_0, axiom,
% 0.25/0.55    (![A:$i]:
% 0.25/0.55     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.25/0.55          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.25/0.55  thf('21', plain,
% 0.25/0.55      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 0.25/0.55      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.25/0.55  thf(t4_xboole_0, axiom,
% 0.25/0.55    (![A:$i,B:$i]:
% 0.25/0.55     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.25/0.55            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.25/0.55       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.25/0.55            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.25/0.55  thf('22', plain,
% 0.25/0.55      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.25/0.55         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.25/0.55          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.25/0.55      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.25/0.55  thf('23', plain,
% 0.25/0.55      (![X0 : $i, X1 : $i]:
% 0.25/0.55         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.25/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.25/0.55  thf('24', plain,
% 0.25/0.55      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.25/0.55      inference('sup-', [status(thm)], ['20', '23'])).
% 0.25/0.55  thf('25', plain,
% 0.25/0.55      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.25/0.55         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.25/0.55          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.25/0.55      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.25/0.55  thf('26', plain,
% 0.25/0.55      (![X0 : $i, X1 : $i]:
% 0.25/0.55         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.25/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.25/0.55  thf('27', plain, (![X12 : $i]: (r1_xboole_0 @ X12 @ k1_xboole_0)),
% 0.25/0.55      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.25/0.55  thf('28', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.25/0.55      inference('demod', [status(thm)], ['26', '27'])).
% 0.25/0.55  thf('29', plain, ($false), inference('sup-', [status(thm)], ['19', '28'])).
% 0.25/0.55  
% 0.25/0.55  % SZS output end Refutation
% 0.25/0.55  
% 0.25/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

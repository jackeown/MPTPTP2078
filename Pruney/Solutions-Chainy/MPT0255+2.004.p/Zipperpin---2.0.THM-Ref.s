%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3Rc0qoiHie

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:56 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   52 (  56 expanded)
%              Number of leaves         :   23 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :  234 ( 267 expanded)
%              Number of equality atoms :   21 (  23 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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
    ! [X9: $i,X10: $i] :
      ( ( v1_xboole_0 @ X9 )
      | ~ ( v1_xboole_0 @ ( k2_xboole_0 @ X10 @ X9 ) ) ) ),
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
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('7',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['0','7'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('10',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B_1 ) @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['8','9'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) )
    | ( k1_xboole_0
      = ( k2_tarski @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('13',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('14',plain,
    ( k1_xboole_0
    = ( k2_tarski @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('15',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( X18 != X20 )
      | ( r2_hidden @ X18 @ X19 )
      | ( X19
       != ( k2_tarski @ X20 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('16',plain,(
    ! [X17: $i,X20: $i] :
      ( r2_hidden @ X20 @ ( k2_tarski @ X20 @ X17 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['14','16'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('18',plain,(
    ! [X12: $i] :
      ( r1_xboole_0 @ X12 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('19',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('20',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X1 @ X4 ) )
      | ~ ( r1_xboole_0 @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X1 @ X4 ) )
      | ~ ( r1_xboole_0 @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X12: $i] :
      ( r1_xboole_0 @ X12 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('26',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    $false ),
    inference('sup-',[status(thm)],['17','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3Rc0qoiHie
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:00:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 169 iterations in 0.100s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.55  thf(t50_zfmisc_1, conjecture,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.55        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t50_zfmisc_1])).
% 0.20/0.55  thf('0', plain,
% 0.20/0.55      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ sk_C_1) = (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('1', plain,
% 0.20/0.55      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ sk_C_1) = (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(fc5_xboole_0, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.55       ( ~( v1_xboole_0 @ ( k2_xboole_0 @ B @ A ) ) ) ))).
% 0.20/0.55  thf('2', plain,
% 0.20/0.55      (![X9 : $i, X10 : $i]:
% 0.20/0.55         ((v1_xboole_0 @ X9) | ~ (v1_xboole_0 @ (k2_xboole_0 @ X10 @ X9)))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc5_xboole_0])).
% 0.20/0.55  thf('3', plain, ((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_C_1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.55  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.55  thf('4', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.55  thf('5', plain, ((v1_xboole_0 @ sk_C_1)),
% 0.20/0.55      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.55  thf(l13_xboole_0, axiom,
% 0.20/0.55    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.55  thf('6', plain,
% 0.20/0.55      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.55      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.55  thf('7', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.55  thf('8', plain,
% 0.20/0.55      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ k1_xboole_0)
% 0.20/0.55         = (k1_xboole_0))),
% 0.20/0.55      inference('demod', [status(thm)], ['0', '7'])).
% 0.20/0.55  thf(t7_xboole_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.55  thf('9', plain,
% 0.20/0.55      (![X13 : $i, X14 : $i]: (r1_tarski @ X13 @ (k2_xboole_0 @ X13 @ X14))),
% 0.20/0.55      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.20/0.55  thf('10', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_B_1) @ k1_xboole_0)),
% 0.20/0.55      inference('sup+', [status(thm)], ['8', '9'])).
% 0.20/0.55  thf(d10_xboole_0, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.55  thf('11', plain,
% 0.20/0.55      (![X6 : $i, X8 : $i]:
% 0.20/0.55         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 0.20/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.55  thf('12', plain,
% 0.20/0.55      ((~ (r1_tarski @ k1_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1))
% 0.20/0.55        | ((k1_xboole_0) = (k2_tarski @ sk_A @ sk_B_1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.55  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.55  thf('13', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 0.20/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.55  thf('14', plain, (((k1_xboole_0) = (k2_tarski @ sk_A @ sk_B_1))),
% 0.20/0.55      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.55  thf(d2_tarski, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.20/0.55       ( ![D:$i]:
% 0.20/0.55         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.20/0.55  thf('15', plain,
% 0.20/0.55      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.55         (((X18) != (X20))
% 0.20/0.55          | (r2_hidden @ X18 @ X19)
% 0.20/0.55          | ((X19) != (k2_tarski @ X20 @ X17)))),
% 0.20/0.55      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.55  thf('16', plain,
% 0.20/0.55      (![X17 : $i, X20 : $i]: (r2_hidden @ X20 @ (k2_tarski @ X20 @ X17))),
% 0.20/0.55      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.55  thf('17', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.20/0.55      inference('sup+', [status(thm)], ['14', '16'])).
% 0.20/0.55  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.55  thf('18', plain, (![X12 : $i]: (r1_xboole_0 @ X12 @ k1_xboole_0)),
% 0.20/0.55      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.55  thf(t7_xboole_0, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.55          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.55  thf('19', plain,
% 0.20/0.55      (![X5 : $i]: (((X5) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X5) @ X5))),
% 0.20/0.55      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.55  thf(t4_xboole_0, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.55            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.55       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.55            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.55  thf('20', plain,
% 0.20/0.55      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X1 @ X4))
% 0.20/0.55          | ~ (r1_xboole_0 @ X1 @ X4))),
% 0.20/0.55      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.55  thf('21', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.55  thf('22', plain,
% 0.20/0.55      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['18', '21'])).
% 0.20/0.55  thf('23', plain,
% 0.20/0.55      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X1 @ X4))
% 0.20/0.55          | ~ (r1_xboole_0 @ X1 @ X4))),
% 0.20/0.55      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.55  thf('24', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.55  thf('25', plain, (![X12 : $i]: (r1_xboole_0 @ X12 @ k1_xboole_0)),
% 0.20/0.55      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.55  thf('26', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.20/0.55      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.55  thf('27', plain, ($false), inference('sup-', [status(thm)], ['17', '26'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

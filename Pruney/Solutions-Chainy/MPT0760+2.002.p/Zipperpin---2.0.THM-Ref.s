%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MVDyVERchY

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:19 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   47 (  61 expanded)
%              Number of leaves         :   19 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :  281 ( 398 expanded)
%              Number of equality atoms :   15 (  22 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('0',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X8: $i] :
      ( ( X8
        = ( k1_relat_1 @ X5 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X8 @ X5 ) @ ( sk_D @ X8 @ X5 ) ) @ X5 )
      | ( r2_hidden @ ( sk_C @ X8 @ X5 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X0
        = ( k1_relat_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X0
        = ( k1_relat_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','8'])).

thf(t2_wellord1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k3_relat_1 @ B ) )
        | ( ( k1_wellord1 @ B @ A )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ B ) )
          | ( ( k1_wellord1 @ B @ A )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t2_wellord1])).

thf('10',plain,(
    ( k1_wellord1 @ sk_B_1 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_wellord1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( v1_xboole_0 @ ( k1_wellord1 @ sk_B_1 @ sk_A ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('14',plain,(
    ~ ( v1_xboole_0 @ ( k1_wellord1 @ sk_B_1 @ sk_A ) ) ),
    inference('simplify_reflect+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(d1_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k1_wellord1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ( ( D != B )
                & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) )).

thf('16',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X16
       != ( k1_wellord1 @ X15 @ X14 ) )
      | ( r2_hidden @ ( k4_tarski @ X17 @ X14 ) @ X15 )
      | ~ ( r2_hidden @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('17',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( r2_hidden @ X17 @ ( k1_wellord1 @ X15 @ X14 ) )
      | ( r2_hidden @ ( k4_tarski @ X17 @ X14 ) @ X15 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_wellord1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k1_wellord1 @ X1 @ X0 ) ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf(t30_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) )).

thf('19',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X12 )
      | ( r2_hidden @ X11 @ ( k3_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t30_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k1_wellord1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) )
      | ( v1_xboole_0 @ ( k1_wellord1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ( v1_xboole_0 @ ( k1_wellord1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_xboole_0 @ ( k1_wellord1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    $false ),
    inference(demod,[status(thm)],['14','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MVDyVERchY
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 21:03:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.37/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.62  % Solved by: fo/fo7.sh
% 0.37/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.62  % done 123 iterations in 0.137s
% 0.37/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.62  % SZS output start Refutation
% 0.37/0.62  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.37/0.62  thf(sk_B_type, type, sk_B: $i > $i).
% 0.37/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.62  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 0.37/0.62  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.37/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.62  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.37/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.62  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.37/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.62  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.37/0.62  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.62  thf(d4_relat_1, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.37/0.62       ( ![C:$i]:
% 0.37/0.62         ( ( r2_hidden @ C @ B ) <=>
% 0.37/0.62           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.37/0.62  thf('1', plain,
% 0.37/0.62      (![X5 : $i, X8 : $i]:
% 0.37/0.62         (((X8) = (k1_relat_1 @ X5))
% 0.37/0.62          | (r2_hidden @ (k4_tarski @ (sk_C @ X8 @ X5) @ (sk_D @ X8 @ X5)) @ X5)
% 0.37/0.62          | (r2_hidden @ (sk_C @ X8 @ X5) @ X8))),
% 0.37/0.62      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.37/0.62  thf(d1_xboole_0, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.37/0.62  thf('2', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.37/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.37/0.62  thf('3', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 0.37/0.62          | ((X1) = (k1_relat_1 @ X0))
% 0.37/0.62          | ~ (v1_xboole_0 @ X0))),
% 0.37/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.62  thf('4', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.37/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.37/0.62  thf('5', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         (~ (v1_xboole_0 @ X1)
% 0.37/0.62          | ((X0) = (k1_relat_1 @ X1))
% 0.37/0.62          | ~ (v1_xboole_0 @ X0))),
% 0.37/0.62      inference('sup-', [status(thm)], ['3', '4'])).
% 0.37/0.62  thf('6', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         (~ (v1_xboole_0 @ X1)
% 0.37/0.62          | ((X0) = (k1_relat_1 @ X1))
% 0.37/0.62          | ~ (v1_xboole_0 @ X0))),
% 0.37/0.62      inference('sup-', [status(thm)], ['3', '4'])).
% 0.37/0.62  thf('7', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.62         (((X1) = (X0))
% 0.37/0.62          | ~ (v1_xboole_0 @ X0)
% 0.37/0.62          | ~ (v1_xboole_0 @ X2)
% 0.37/0.62          | ~ (v1_xboole_0 @ X1)
% 0.37/0.62          | ~ (v1_xboole_0 @ X2))),
% 0.37/0.62      inference('sup+', [status(thm)], ['5', '6'])).
% 0.37/0.62  thf('8', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.62         (~ (v1_xboole_0 @ X1)
% 0.37/0.62          | ~ (v1_xboole_0 @ X2)
% 0.37/0.62          | ~ (v1_xboole_0 @ X0)
% 0.37/0.62          | ((X1) = (X0)))),
% 0.37/0.62      inference('simplify', [status(thm)], ['7'])).
% 0.37/0.62  thf('9', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         (((X0) = (X1)) | ~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.62      inference('sup-', [status(thm)], ['0', '8'])).
% 0.37/0.62  thf(t2_wellord1, conjecture,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( v1_relat_1 @ B ) =>
% 0.37/0.62       ( ( r2_hidden @ A @ ( k3_relat_1 @ B ) ) | 
% 0.37/0.62         ( ( k1_wellord1 @ B @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.37/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.62    (~( ![A:$i,B:$i]:
% 0.37/0.62        ( ( v1_relat_1 @ B ) =>
% 0.37/0.62          ( ( r2_hidden @ A @ ( k3_relat_1 @ B ) ) | 
% 0.37/0.62            ( ( k1_wellord1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) )),
% 0.37/0.62    inference('cnf.neg', [status(esa)], [t2_wellord1])).
% 0.37/0.62  thf('10', plain, (((k1_wellord1 @ sk_B_1 @ sk_A) != (k1_xboole_0))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('11', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (((X0) != (k1_xboole_0))
% 0.37/0.62          | ~ (v1_xboole_0 @ X0)
% 0.37/0.62          | ~ (v1_xboole_0 @ (k1_wellord1 @ sk_B_1 @ sk_A)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['9', '10'])).
% 0.37/0.62  thf('12', plain,
% 0.37/0.62      ((~ (v1_xboole_0 @ (k1_wellord1 @ sk_B_1 @ sk_A))
% 0.37/0.62        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.37/0.62      inference('simplify', [status(thm)], ['11'])).
% 0.37/0.62  thf('13', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.62  thf('14', plain, (~ (v1_xboole_0 @ (k1_wellord1 @ sk_B_1 @ sk_A))),
% 0.37/0.62      inference('simplify_reflect+', [status(thm)], ['12', '13'])).
% 0.37/0.62  thf('15', plain,
% 0.37/0.62      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.37/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.37/0.62  thf(d1_wellord1, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( v1_relat_1 @ A ) =>
% 0.37/0.62       ( ![B:$i,C:$i]:
% 0.37/0.62         ( ( ( C ) = ( k1_wellord1 @ A @ B ) ) <=>
% 0.37/0.62           ( ![D:$i]:
% 0.37/0.62             ( ( r2_hidden @ D @ C ) <=>
% 0.37/0.62               ( ( ( D ) != ( B ) ) & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) ) ))).
% 0.37/0.62  thf('16', plain,
% 0.37/0.62      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.37/0.62         (((X16) != (k1_wellord1 @ X15 @ X14))
% 0.37/0.62          | (r2_hidden @ (k4_tarski @ X17 @ X14) @ X15)
% 0.37/0.62          | ~ (r2_hidden @ X17 @ X16)
% 0.37/0.62          | ~ (v1_relat_1 @ X15))),
% 0.37/0.62      inference('cnf', [status(esa)], [d1_wellord1])).
% 0.37/0.62  thf('17', plain,
% 0.37/0.62      (![X14 : $i, X15 : $i, X17 : $i]:
% 0.37/0.62         (~ (v1_relat_1 @ X15)
% 0.37/0.62          | ~ (r2_hidden @ X17 @ (k1_wellord1 @ X15 @ X14))
% 0.37/0.62          | (r2_hidden @ (k4_tarski @ X17 @ X14) @ X15))),
% 0.37/0.62      inference('simplify', [status(thm)], ['16'])).
% 0.37/0.62  thf('18', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         ((v1_xboole_0 @ (k1_wellord1 @ X1 @ X0))
% 0.37/0.62          | (r2_hidden @ (k4_tarski @ (sk_B @ (k1_wellord1 @ X1 @ X0)) @ X0) @ 
% 0.37/0.62             X1)
% 0.37/0.62          | ~ (v1_relat_1 @ X1))),
% 0.37/0.62      inference('sup-', [status(thm)], ['15', '17'])).
% 0.37/0.62  thf(t30_relat_1, axiom,
% 0.37/0.62    (![A:$i,B:$i,C:$i]:
% 0.37/0.62     ( ( v1_relat_1 @ C ) =>
% 0.37/0.62       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.37/0.62         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.37/0.62           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ))).
% 0.37/0.62  thf('19', plain,
% 0.37/0.62      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.62         (~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ X12)
% 0.37/0.62          | (r2_hidden @ X11 @ (k3_relat_1 @ X12))
% 0.37/0.62          | ~ (v1_relat_1 @ X12))),
% 0.37/0.62      inference('cnf', [status(esa)], [t30_relat_1])).
% 0.37/0.62  thf('20', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         (~ (v1_relat_1 @ X0)
% 0.37/0.62          | (v1_xboole_0 @ (k1_wellord1 @ X0 @ X1))
% 0.37/0.62          | ~ (v1_relat_1 @ X0)
% 0.37/0.62          | (r2_hidden @ X1 @ (k3_relat_1 @ X0)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['18', '19'])).
% 0.37/0.62  thf('21', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         ((r2_hidden @ X1 @ (k3_relat_1 @ X0))
% 0.37/0.62          | (v1_xboole_0 @ (k1_wellord1 @ X0 @ X1))
% 0.37/0.62          | ~ (v1_relat_1 @ X0))),
% 0.37/0.62      inference('simplify', [status(thm)], ['20'])).
% 0.37/0.62  thf('22', plain, (~ (r2_hidden @ sk_A @ (k3_relat_1 @ sk_B_1))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('23', plain,
% 0.37/0.62      ((~ (v1_relat_1 @ sk_B_1) | (v1_xboole_0 @ (k1_wellord1 @ sk_B_1 @ sk_A)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['21', '22'])).
% 0.37/0.62  thf('24', plain, ((v1_relat_1 @ sk_B_1)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('25', plain, ((v1_xboole_0 @ (k1_wellord1 @ sk_B_1 @ sk_A))),
% 0.37/0.62      inference('demod', [status(thm)], ['23', '24'])).
% 0.37/0.62  thf('26', plain, ($false), inference('demod', [status(thm)], ['14', '25'])).
% 0.37/0.62  
% 0.37/0.62  % SZS output end Refutation
% 0.37/0.62  
% 0.37/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

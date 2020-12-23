%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9boMY2KjTK

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:03 EST 2020

% Result     : Theorem 11.95s
% Output     : Refutation 11.95s
% Verified   : 
% Statistics : Number of formulae       :   46 (  54 expanded)
%              Number of leaves         :   18 (  24 expanded)
%              Depth                    :   11
%              Number of atoms          :  214 ( 256 expanded)
%              Number of equality atoms :   15 (  19 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('0',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t50_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t50_zfmisc_1])).

thf('1',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ sk_C )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('3',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['1','2'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('4',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ( X7
       != ( k2_xboole_0 @ X8 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('6',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X5 @ ( k2_xboole_0 @ X8 @ X6 ) )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('12',plain,(
    v1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_xboole_0 @ X12 )
      | ~ ( v1_xboole_0 @ X13 )
      | ( X12 = X13 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('14',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ sk_C )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ sk_C ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ sk_C )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,
    ( ( k2_tarski @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','18'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ X21 @ X22 )
      | ~ ( r1_tarski @ ( k2_tarski @ X21 @ X23 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('22',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ X0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9boMY2KjTK
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:01:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 11.95/12.12  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 11.95/12.12  % Solved by: fo/fo7.sh
% 11.95/12.12  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 11.95/12.12  % done 10975 iterations in 11.673s
% 11.95/12.12  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 11.95/12.12  % SZS output start Refutation
% 11.95/12.12  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 11.95/12.12  thf(sk_B_1_type, type, sk_B_1: $i).
% 11.95/12.12  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 11.95/12.12  thf(sk_A_type, type, sk_A: $i).
% 11.95/12.12  thf(sk_C_type, type, sk_C: $i).
% 11.95/12.12  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 11.95/12.12  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 11.95/12.12  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 11.95/12.12  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 11.95/12.12  thf(sk_B_type, type, sk_B: $i > $i).
% 11.95/12.12  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 11.95/12.12  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.95/12.12      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 11.95/12.12  thf(t50_zfmisc_1, conjecture,
% 11.95/12.12    (![A:$i,B:$i,C:$i]:
% 11.95/12.12     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 11.95/12.12  thf(zf_stmt_0, negated_conjecture,
% 11.95/12.12    (~( ![A:$i,B:$i,C:$i]:
% 11.95/12.12        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) )),
% 11.95/12.12    inference('cnf.neg', [status(esa)], [t50_zfmisc_1])).
% 11.95/12.12  thf('1', plain,
% 11.95/12.12      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ sk_C) = (k1_xboole_0))),
% 11.95/12.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.95/12.12  thf(commutativity_k2_xboole_0, axiom,
% 11.95/12.12    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 11.95/12.12  thf('2', plain,
% 11.95/12.12      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 11.95/12.12      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 11.95/12.12  thf('3', plain,
% 11.95/12.12      (((k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 11.95/12.12      inference('demod', [status(thm)], ['1', '2'])).
% 11.95/12.12  thf(d1_xboole_0, axiom,
% 11.95/12.12    (![A:$i]:
% 11.95/12.12     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 11.95/12.12  thf('4', plain,
% 11.95/12.12      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 11.95/12.12      inference('cnf', [status(esa)], [d1_xboole_0])).
% 11.95/12.12  thf(d3_xboole_0, axiom,
% 11.95/12.12    (![A:$i,B:$i,C:$i]:
% 11.95/12.12     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 11.95/12.12       ( ![D:$i]:
% 11.95/12.12         ( ( r2_hidden @ D @ C ) <=>
% 11.95/12.12           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 11.95/12.12  thf('5', plain,
% 11.95/12.12      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 11.95/12.12         (~ (r2_hidden @ X5 @ X6)
% 11.95/12.12          | (r2_hidden @ X5 @ X7)
% 11.95/12.12          | ((X7) != (k2_xboole_0 @ X8 @ X6)))),
% 11.95/12.12      inference('cnf', [status(esa)], [d3_xboole_0])).
% 11.95/12.12  thf('6', plain,
% 11.95/12.12      (![X5 : $i, X6 : $i, X8 : $i]:
% 11.95/12.12         ((r2_hidden @ X5 @ (k2_xboole_0 @ X8 @ X6)) | ~ (r2_hidden @ X5 @ X6))),
% 11.95/12.12      inference('simplify', [status(thm)], ['5'])).
% 11.95/12.12  thf('7', plain,
% 11.95/12.12      (![X0 : $i, X1 : $i]:
% 11.95/12.12         ((v1_xboole_0 @ X0)
% 11.95/12.12          | (r2_hidden @ (sk_B @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 11.95/12.12      inference('sup-', [status(thm)], ['4', '6'])).
% 11.95/12.12  thf('8', plain,
% 11.95/12.12      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 11.95/12.12      inference('cnf', [status(esa)], [d1_xboole_0])).
% 11.95/12.12  thf('9', plain,
% 11.95/12.12      (![X0 : $i, X1 : $i]:
% 11.95/12.12         ((v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ (k2_xboole_0 @ X1 @ X0)))),
% 11.95/12.12      inference('sup-', [status(thm)], ['7', '8'])).
% 11.95/12.12  thf('10', plain,
% 11.95/12.12      ((~ (v1_xboole_0 @ k1_xboole_0)
% 11.95/12.12        | (v1_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1)))),
% 11.95/12.12      inference('sup-', [status(thm)], ['3', '9'])).
% 11.95/12.12  thf('11', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.95/12.12      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 11.95/12.12  thf('12', plain, ((v1_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1))),
% 11.95/12.12      inference('demod', [status(thm)], ['10', '11'])).
% 11.95/12.12  thf(t8_boole, axiom,
% 11.95/12.12    (![A:$i,B:$i]:
% 11.95/12.12     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 11.95/12.12  thf('13', plain,
% 11.95/12.12      (![X12 : $i, X13 : $i]:
% 11.95/12.12         (~ (v1_xboole_0 @ X12) | ~ (v1_xboole_0 @ X13) | ((X12) = (X13)))),
% 11.95/12.12      inference('cnf', [status(esa)], [t8_boole])).
% 11.95/12.12  thf('14', plain,
% 11.95/12.12      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ sk_C) = (k1_xboole_0))),
% 11.95/12.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.95/12.12  thf('15', plain,
% 11.95/12.12      (![X0 : $i]:
% 11.95/12.12         (((X0) = (k1_xboole_0))
% 11.95/12.12          | ~ (v1_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ sk_C))
% 11.95/12.12          | ~ (v1_xboole_0 @ X0))),
% 11.95/12.12      inference('sup+', [status(thm)], ['13', '14'])).
% 11.95/12.12  thf('16', plain,
% 11.95/12.12      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ sk_C) = (k1_xboole_0))),
% 11.95/12.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.95/12.12  thf('17', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.95/12.12      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 11.95/12.12  thf('18', plain,
% 11.95/12.12      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 11.95/12.12      inference('demod', [status(thm)], ['15', '16', '17'])).
% 11.95/12.12  thf('19', plain, (((k2_tarski @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 11.95/12.12      inference('sup-', [status(thm)], ['12', '18'])).
% 11.95/12.12  thf(t38_zfmisc_1, axiom,
% 11.95/12.12    (![A:$i,B:$i,C:$i]:
% 11.95/12.12     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 11.95/12.12       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 11.95/12.12  thf('20', plain,
% 11.95/12.12      (![X21 : $i, X22 : $i, X23 : $i]:
% 11.95/12.12         ((r2_hidden @ X21 @ X22)
% 11.95/12.12          | ~ (r1_tarski @ (k2_tarski @ X21 @ X23) @ X22))),
% 11.95/12.12      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 11.95/12.12  thf('21', plain,
% 11.95/12.12      (![X0 : $i]: (~ (r1_tarski @ k1_xboole_0 @ X0) | (r2_hidden @ sk_A @ X0))),
% 11.95/12.12      inference('sup-', [status(thm)], ['19', '20'])).
% 11.95/12.12  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 11.95/12.12  thf('22', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 11.95/12.12      inference('cnf', [status(esa)], [t2_xboole_1])).
% 11.95/12.12  thf('23', plain, (![X0 : $i]: (r2_hidden @ sk_A @ X0)),
% 11.95/12.12      inference('demod', [status(thm)], ['21', '22'])).
% 11.95/12.12  thf('24', plain,
% 11.95/12.12      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 11.95/12.12      inference('cnf', [status(esa)], [d1_xboole_0])).
% 11.95/12.12  thf('25', plain, (![X0 : $i]: ~ (v1_xboole_0 @ X0)),
% 11.95/12.12      inference('sup-', [status(thm)], ['23', '24'])).
% 11.95/12.12  thf('26', plain, ($false), inference('sup-', [status(thm)], ['0', '25'])).
% 11.95/12.12  
% 11.95/12.12  % SZS output end Refutation
% 11.95/12.12  
% 11.95/12.13  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

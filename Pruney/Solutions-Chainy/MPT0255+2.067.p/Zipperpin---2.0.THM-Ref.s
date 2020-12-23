%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PusMAFQQeJ

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:04 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   44 (  73 expanded)
%              Number of leaves         :   19 (  29 expanded)
%              Depth                    :   13
%              Number of atoms          :  198 ( 375 expanded)
%              Number of equality atoms :   26 (  46 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('2',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf(fc5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ~ ( v1_xboole_0 @ ( k2_xboole_0 @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ ( k2_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_xboole_0])).

thf('4',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('5',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('6',plain,(
    v1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_xboole_0 @ X5 )
      | ~ ( v1_xboole_0 @ X6 )
      | ( X5 = X6 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( k1_xboole_0
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ X21 @ X22 )
      | ~ ( r1_tarski @ ( k2_tarski @ X21 @ X23 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('13',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ X0 ) ),
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
    ! [X7: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X9 )
      | ( X11 = X10 )
      | ( X11 = X7 )
      | ( X9
       != ( k2_tarski @ X10 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('16',plain,(
    ! [X7: $i,X10: $i,X11: $i] :
      ( ( X11 = X7 )
      | ( X11 = X10 )
      | ~ ( r2_hidden @ X11 @ ( k2_tarski @ X10 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A = X1 )
      | ( sk_A = X0 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference(condensation,[status(thm)],['17'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('19',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X25 ) @ X26 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference(condensation,[status(thm)],['17'])).

thf('21',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] : ( X0 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    $false ),
    inference(simplify,[status(thm)],['22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PusMAFQQeJ
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:06:39 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 77 iterations in 0.048s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.50  thf(t50_zfmisc_1, conjecture,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.50        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t50_zfmisc_1])).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(commutativity_k2_xboole_0, axiom,
% 0.22/0.50    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.50      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      (((k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.22/0.50      inference('demod', [status(thm)], ['0', '1'])).
% 0.22/0.50  thf(fc5_xboole_0, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.50       ( ~( v1_xboole_0 @ ( k2_xboole_0 @ B @ A ) ) ) ))).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      (![X2 : $i, X3 : $i]:
% 0.22/0.50         ((v1_xboole_0 @ X2) | ~ (v1_xboole_0 @ (k2_xboole_0 @ X3 @ X2)))),
% 0.22/0.50      inference('cnf', [status(esa)], [fc5_xboole_0])).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.22/0.50        | (v1_xboole_0 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.50  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.22/0.50  thf('5', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.50  thf('6', plain, ((v1_xboole_0 @ (k2_tarski @ sk_A @ sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['4', '5'])).
% 0.22/0.50  thf('7', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.50  thf(t8_boole, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (![X5 : $i, X6 : $i]:
% 0.22/0.50         (~ (v1_xboole_0 @ X5) | ~ (v1_xboole_0 @ X6) | ((X5) = (X6)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t8_boole])).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.50  thf('10', plain, (((k1_xboole_0) = (k2_tarski @ sk_A @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['6', '9'])).
% 0.22/0.50  thf(t38_zfmisc_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.22/0.50       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.22/0.50         ((r2_hidden @ X21 @ X22)
% 0.22/0.50          | ~ (r1_tarski @ (k2_tarski @ X21 @ X23) @ X22))),
% 0.22/0.50      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      (![X0 : $i]: (~ (r1_tarski @ k1_xboole_0 @ X0) | (r2_hidden @ sk_A @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.50  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.50  thf('13', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.22/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.50  thf('14', plain, (![X0 : $i]: (r2_hidden @ sk_A @ X0)),
% 0.22/0.50      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.50  thf(d2_tarski, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.22/0.50       ( ![D:$i]:
% 0.22/0.50         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      (![X7 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X11 @ X9)
% 0.22/0.50          | ((X11) = (X10))
% 0.22/0.50          | ((X11) = (X7))
% 0.22/0.50          | ((X9) != (k2_tarski @ X10 @ X7)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d2_tarski])).
% 0.22/0.50  thf('16', plain,
% 0.22/0.50      (![X7 : $i, X10 : $i, X11 : $i]:
% 0.22/0.50         (((X11) = (X7))
% 0.22/0.50          | ((X11) = (X10))
% 0.22/0.50          | ~ (r2_hidden @ X11 @ (k2_tarski @ X10 @ X7)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['15'])).
% 0.22/0.50  thf('17', plain, (![X0 : $i, X1 : $i]: (((sk_A) = (X1)) | ((sk_A) = (X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['14', '16'])).
% 0.22/0.50  thf('18', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 0.22/0.50      inference('condensation', [status(thm)], ['17'])).
% 0.22/0.50  thf(t49_zfmisc_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.22/0.50  thf('19', plain,
% 0.22/0.50      (![X25 : $i, X26 : $i]:
% 0.22/0.50         ((k2_xboole_0 @ (k1_tarski @ X25) @ X26) != (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.22/0.50  thf('20', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 0.22/0.50      inference('condensation', [status(thm)], ['17'])).
% 0.22/0.50  thf('21', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.50      inference('demod', [status(thm)], ['19', '20'])).
% 0.22/0.50  thf('22', plain, (![X0 : $i]: ((X0) != (k1_xboole_0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['18', '21'])).
% 0.22/0.50  thf('23', plain, ($false), inference('simplify', [status(thm)], ['22'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

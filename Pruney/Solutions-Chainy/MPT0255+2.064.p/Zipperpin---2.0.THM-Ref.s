%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dqq2v9Ru8J

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:04 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 105 expanded)
%              Number of leaves         :   19 (  39 expanded)
%              Depth                    :   16
%              Number of atoms          :  234 ( 527 expanded)
%              Number of equality atoms :   30 (  62 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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

thf('3',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ~ ( v1_xboole_0 @ ( k2_xboole_0 @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i] :
      ( ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ ( k2_xboole_0 @ X4 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_xboole_0])).

thf('5',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('6',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('7',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_xboole_0 @ X6 )
      | ~ ( v1_xboole_0 @ X7 )
      | ( X6 = X7 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    k1_xboole_0 = sk_C ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['2','11'])).

thf('13',plain,(
    ! [X3: $i,X4: $i] :
      ( ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ ( k2_xboole_0 @ X4 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_xboole_0])).

thf('14',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('16',plain,(
    v1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('18',plain,
    ( k1_xboole_0
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ X19 @ X20 )
      | ~ ( r1_tarski @ ( k2_tarski @ X19 @ X21 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('21',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ X0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('23',plain,(
    ! [X8: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ( X12 = X11 )
      | ( X12 = X8 )
      | ( X10
       != ( k2_tarski @ X11 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('24',plain,(
    ! [X8: $i,X11: $i,X12: $i] :
      ( ( X12 = X8 )
      | ( X12 = X11 )
      | ~ ( r2_hidden @ X12 @ ( k2_tarski @ X11 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A = X1 )
      | ( sk_A = X0 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference(condensation,[status(thm)],['25'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('27',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X23 ) @ X24 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference(condensation,[status(thm)],['25'])).

thf('29',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] : ( X0 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    $false ),
    inference(simplify,[status(thm)],['30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dqq2v9Ru8J
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:51:41 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 76 iterations in 0.049s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.48  thf(t50_zfmisc_1, conjecture,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.48        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t50_zfmisc_1])).
% 0.19/0.48  thf('0', plain,
% 0.19/0.48      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(commutativity_k2_xboole_0, axiom,
% 0.19/0.48    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.19/0.48  thf('1', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.19/0.48      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.19/0.48  thf('2', plain,
% 0.19/0.48      (((k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.19/0.48      inference('demod', [status(thm)], ['0', '1'])).
% 0.19/0.48  thf('3', plain,
% 0.19/0.48      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(fc5_xboole_0, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.48       ( ~( v1_xboole_0 @ ( k2_xboole_0 @ B @ A ) ) ) ))).
% 0.19/0.48  thf('4', plain,
% 0.19/0.48      (![X3 : $i, X4 : $i]:
% 0.19/0.48         ((v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ (k2_xboole_0 @ X4 @ X3)))),
% 0.19/0.48      inference('cnf', [status(esa)], [fc5_xboole_0])).
% 0.19/0.48  thf('5', plain, ((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_C))),
% 0.19/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.48  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.19/0.48  thf('6', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.48      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.48  thf('7', plain, ((v1_xboole_0 @ sk_C)),
% 0.19/0.48      inference('demod', [status(thm)], ['5', '6'])).
% 0.19/0.48  thf('8', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.48      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.48  thf(t8_boole, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.19/0.48  thf('9', plain,
% 0.19/0.48      (![X6 : $i, X7 : $i]:
% 0.19/0.48         (~ (v1_xboole_0 @ X6) | ~ (v1_xboole_0 @ X7) | ((X6) = (X7)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t8_boole])).
% 0.19/0.48  thf('10', plain,
% 0.19/0.48      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.48  thf('11', plain, (((k1_xboole_0) = (sk_C))),
% 0.19/0.48      inference('sup-', [status(thm)], ['7', '10'])).
% 0.19/0.48  thf('12', plain,
% 0.19/0.48      (((k2_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.19/0.48      inference('demod', [status(thm)], ['2', '11'])).
% 0.19/0.48  thf('13', plain,
% 0.19/0.48      (![X3 : $i, X4 : $i]:
% 0.19/0.48         ((v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ (k2_xboole_0 @ X4 @ X3)))),
% 0.19/0.48      inference('cnf', [status(esa)], [fc5_xboole_0])).
% 0.19/0.48  thf('14', plain,
% 0.19/0.48      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.19/0.48        | (v1_xboole_0 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.48  thf('15', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.48      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.48  thf('16', plain, ((v1_xboole_0 @ (k2_tarski @ sk_A @ sk_B))),
% 0.19/0.48      inference('demod', [status(thm)], ['14', '15'])).
% 0.19/0.48  thf('17', plain,
% 0.19/0.48      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.48  thf('18', plain, (((k1_xboole_0) = (k2_tarski @ sk_A @ sk_B))),
% 0.19/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.48  thf(t38_zfmisc_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.19/0.48       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.19/0.48  thf('19', plain,
% 0.19/0.48      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.19/0.48         ((r2_hidden @ X19 @ X20)
% 0.19/0.48          | ~ (r1_tarski @ (k2_tarski @ X19 @ X21) @ X20))),
% 0.19/0.48      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.19/0.48  thf('20', plain,
% 0.19/0.48      (![X0 : $i]: (~ (r1_tarski @ k1_xboole_0 @ X0) | (r2_hidden @ sk_A @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.48  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.19/0.48  thf('21', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.19/0.48      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.48  thf('22', plain, (![X0 : $i]: (r2_hidden @ sk_A @ X0)),
% 0.19/0.48      inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.48  thf(d2_tarski, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.19/0.48       ( ![D:$i]:
% 0.19/0.48         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.19/0.48  thf('23', plain,
% 0.19/0.48      (![X8 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X12 @ X10)
% 0.19/0.48          | ((X12) = (X11))
% 0.19/0.48          | ((X12) = (X8))
% 0.19/0.48          | ((X10) != (k2_tarski @ X11 @ X8)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d2_tarski])).
% 0.19/0.48  thf('24', plain,
% 0.19/0.48      (![X8 : $i, X11 : $i, X12 : $i]:
% 0.19/0.48         (((X12) = (X8))
% 0.19/0.48          | ((X12) = (X11))
% 0.19/0.48          | ~ (r2_hidden @ X12 @ (k2_tarski @ X11 @ X8)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['23'])).
% 0.19/0.48  thf('25', plain, (![X0 : $i, X1 : $i]: (((sk_A) = (X1)) | ((sk_A) = (X0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['22', '24'])).
% 0.19/0.48  thf('26', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 0.19/0.48      inference('condensation', [status(thm)], ['25'])).
% 0.19/0.48  thf(t49_zfmisc_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.19/0.48  thf('27', plain,
% 0.19/0.48      (![X23 : $i, X24 : $i]:
% 0.19/0.48         ((k2_xboole_0 @ (k1_tarski @ X23) @ X24) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.19/0.48  thf('28', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 0.19/0.48      inference('condensation', [status(thm)], ['25'])).
% 0.19/0.48  thf('29', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.48      inference('demod', [status(thm)], ['27', '28'])).
% 0.19/0.48  thf('30', plain, (![X0 : $i]: ((X0) != (k1_xboole_0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['26', '29'])).
% 0.19/0.48  thf('31', plain, ($false), inference('simplify', [status(thm)], ['30'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

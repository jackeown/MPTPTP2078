%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6GbxVgOfwx

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   40 (  43 expanded)
%              Number of leaves         :   18 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :  194 ( 217 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t45_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
     => ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
       => ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t45_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r2_xboole_0 @ X4 @ X6 )
      | ( X4 = X6 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('3',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = sk_B )
    | ( r2_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('4',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X27: $i,X28: $i] :
      ( r1_tarski @ X27 @ ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_tarski @ X10 @ ( k2_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t60_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_tarski @ A @ B )
        & ( r2_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ X25 @ X26 )
      | ~ ( r2_xboole_0 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t60_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['3','12'])).

thf('14',plain,(
    ! [X27: $i,X28: $i] :
      ( r1_tarski @ X27 @ ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('15',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('16',plain,(
    ! [X36: $i] :
      ( ( k2_tarski @ X36 @ X36 )
      = ( k1_tarski @ X36 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X70: $i,X71: $i,X72: $i] :
      ( ( r2_hidden @ X70 @ X71 )
      | ~ ( r1_tarski @ ( k2_tarski @ X70 @ X72 ) @ X71 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    $false ),
    inference(demod,[status(thm)],['0','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6GbxVgOfwx
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:53:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 107 iterations in 0.052s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.51  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.51  thf(t45_zfmisc_1, conjecture,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.20/0.51       ( r2_hidden @ A @ B ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i]:
% 0.20/0.51        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.20/0.51          ( r2_hidden @ A @ B ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t45_zfmisc_1])).
% 0.20/0.51  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(d8_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.20/0.51       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X4 : $i, X6 : $i]:
% 0.20/0.51         ((r2_xboole_0 @ X4 @ X6) | ((X4) = (X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.20/0.51      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      ((((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (sk_B))
% 0.20/0.51        | (r2_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.51  thf(idempotence_k3_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.20/0.51  thf('4', plain, (![X7 : $i]: ((k3_xboole_0 @ X7 @ X7) = (X7))),
% 0.20/0.51      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.20/0.51  thf(t22_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X15 : $i, X16 : $i]:
% 0.20/0.51         ((k2_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16)) = (X15))),
% 0.20/0.51      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.20/0.51  thf('6', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.51      inference('sup+', [status(thm)], ['4', '5'])).
% 0.20/0.51  thf(t7_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X27 : $i, X28 : $i]: (r1_tarski @ X27 @ (k2_xboole_0 @ X27 @ X28))),
% 0.20/0.51      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.20/0.51  thf('8', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.20/0.51      inference('sup+', [status(thm)], ['6', '7'])).
% 0.20/0.51  thf(t10_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.51         (~ (r1_tarski @ X10 @ X11)
% 0.20/0.51          | (r1_tarski @ X10 @ (k2_xboole_0 @ X12 @ X11)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.51  thf(t60_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( ~( ( r1_tarski @ A @ B ) & ( r2_xboole_0 @ B @ A ) ) ))).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X25 : $i, X26 : $i]:
% 0.20/0.51         (~ (r1_tarski @ X25 @ X26) | ~ (r2_xboole_0 @ X26 @ X25))),
% 0.20/0.51      inference('cnf', [status(esa)], [t60_xboole_1])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]: ~ (r2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)),
% 0.20/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.51  thf('13', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['3', '12'])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (![X27 : $i, X28 : $i]: (r1_tarski @ X27 @ (k2_xboole_0 @ X27 @ X28))),
% 0.20/0.51      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.20/0.51  thf('15', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.20/0.51      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.51  thf(t69_enumset1, axiom,
% 0.20/0.51    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (![X36 : $i]: ((k2_tarski @ X36 @ X36) = (k1_tarski @ X36))),
% 0.20/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.51  thf(t38_zfmisc_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.20/0.51       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (![X70 : $i, X71 : $i, X72 : $i]:
% 0.20/0.51         ((r2_hidden @ X70 @ X71)
% 0.20/0.51          | ~ (r1_tarski @ (k2_tarski @ X70 @ X72) @ X71))),
% 0.20/0.51      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.51  thf('19', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.20/0.51      inference('sup-', [status(thm)], ['15', '18'])).
% 0.20/0.51  thf('20', plain, ($false), inference('demod', [status(thm)], ['0', '19'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

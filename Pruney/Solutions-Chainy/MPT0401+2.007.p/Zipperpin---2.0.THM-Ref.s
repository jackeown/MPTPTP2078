%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KXQtgEbpV1

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   42 (  48 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :    9
%              Number of atoms          :  222 ( 280 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(t24_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ B @ ( k1_tarski @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r1_tarski @ C @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_setfam_1 @ B @ ( k1_tarski @ A ) )
       => ! [C: $i] :
            ( ( r2_hidden @ C @ B )
           => ( r1_tarski @ C @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t24_setfam_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_C_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r2_hidden @ X17 @ X15 )
      | ( r2_hidden @ X17 @ X18 )
      | ( X18
       != ( k3_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('4',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X17 @ ( k3_tarski @ X16 ) )
      | ~ ( r2_hidden @ X17 @ X15 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_tarski @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ ( k3_tarski @ sk_B ) )
      | ( r1_tarski @ sk_C_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('7',plain,(
    r1_setfam_1 @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t18_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('8',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X24 ) @ ( k3_tarski @ X25 ) )
      | ~ ( r1_setfam_1 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t18_setfam_1])).

thf('9',plain,(
    r1_tarski @ ( k3_tarski @ sk_B ) @ ( k3_tarski @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('10',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X22 @ X23 ) )
      = ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('13',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( k3_tarski @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k3_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','17'])).

thf('19',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,
    ( ( r1_tarski @ sk_C_2 @ sk_A )
    | ( r1_tarski @ sk_C_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r1_tarski @ sk_C_2 @ sk_A ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    $false ),
    inference(demod,[status(thm)],['0','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KXQtgEbpV1
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 17:59:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 61 iterations in 0.027s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.51  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 0.22/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.51  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.22/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.22/0.51  thf(t24_setfam_1, conjecture,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( r1_setfam_1 @ B @ ( k1_tarski @ A ) ) =>
% 0.22/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r1_tarski @ C @ A ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.51    (~( ![A:$i,B:$i]:
% 0.22/0.51        ( ( r1_setfam_1 @ B @ ( k1_tarski @ A ) ) =>
% 0.22/0.51          ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r1_tarski @ C @ A ) ) ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t24_setfam_1])).
% 0.22/0.51  thf('0', plain, (~ (r1_tarski @ sk_C_2 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('1', plain, ((r2_hidden @ sk_C_2 @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(d3_tarski, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.51  thf('2', plain,
% 0.22/0.51      (![X1 : $i, X3 : $i]:
% 0.22/0.51         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.22/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.51  thf(d4_tarski, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 0.22/0.51       ( ![C:$i]:
% 0.22/0.51         ( ( r2_hidden @ C @ B ) <=>
% 0.22/0.51           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 0.22/0.51  thf('3', plain,
% 0.22/0.51      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X15 @ X16)
% 0.22/0.51          | ~ (r2_hidden @ X17 @ X15)
% 0.22/0.51          | (r2_hidden @ X17 @ X18)
% 0.22/0.51          | ((X18) != (k3_tarski @ X16)))),
% 0.22/0.51      inference('cnf', [status(esa)], [d4_tarski])).
% 0.22/0.51  thf('4', plain,
% 0.22/0.51      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.22/0.51         ((r2_hidden @ X17 @ (k3_tarski @ X16))
% 0.22/0.51          | ~ (r2_hidden @ X17 @ X15)
% 0.22/0.51          | ~ (r2_hidden @ X15 @ X16))),
% 0.22/0.51      inference('simplify', [status(thm)], ['3'])).
% 0.22/0.51  thf('5', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         ((r1_tarski @ X0 @ X1)
% 0.22/0.51          | ~ (r2_hidden @ X0 @ X2)
% 0.22/0.51          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_tarski @ X2)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['2', '4'])).
% 0.22/0.51  thf('6', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((r2_hidden @ (sk_C @ X0 @ sk_C_2) @ (k3_tarski @ sk_B))
% 0.22/0.51          | (r1_tarski @ sk_C_2 @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['1', '5'])).
% 0.22/0.51  thf('7', plain, ((r1_setfam_1 @ sk_B @ (k1_tarski @ sk_A))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(t18_setfam_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( r1_setfam_1 @ A @ B ) =>
% 0.22/0.51       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.22/0.51  thf('8', plain,
% 0.22/0.51      (![X24 : $i, X25 : $i]:
% 0.22/0.51         ((r1_tarski @ (k3_tarski @ X24) @ (k3_tarski @ X25))
% 0.22/0.51          | ~ (r1_setfam_1 @ X24 @ X25))),
% 0.22/0.51      inference('cnf', [status(esa)], [t18_setfam_1])).
% 0.22/0.51  thf('9', plain,
% 0.22/0.51      ((r1_tarski @ (k3_tarski @ sk_B) @ (k3_tarski @ (k1_tarski @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.51  thf(t69_enumset1, axiom,
% 0.22/0.51    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.51  thf('10', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.22/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.51  thf(l51_zfmisc_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.51  thf('11', plain,
% 0.22/0.51      (![X22 : $i, X23 : $i]:
% 0.22/0.51         ((k3_tarski @ (k2_tarski @ X22 @ X23)) = (k2_xboole_0 @ X22 @ X23))),
% 0.22/0.51      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.22/0.51  thf('12', plain,
% 0.22/0.51      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.22/0.51      inference('sup+', [status(thm)], ['10', '11'])).
% 0.22/0.51  thf(idempotence_k2_xboole_0, axiom,
% 0.22/0.51    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.22/0.51  thf('13', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ X4) = (X4))),
% 0.22/0.51      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.22/0.51  thf('14', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.22/0.51      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.51  thf('15', plain, ((r1_tarski @ (k3_tarski @ sk_B) @ sk_A)),
% 0.22/0.51      inference('demod', [status(thm)], ['9', '14'])).
% 0.22/0.51  thf('16', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X0 @ X1)
% 0.22/0.51          | (r2_hidden @ X0 @ X2)
% 0.22/0.51          | ~ (r1_tarski @ X1 @ X2))),
% 0.22/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.51  thf('17', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k3_tarski @ sk_B)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.51  thf('18', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((r1_tarski @ sk_C_2 @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_C_2) @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['6', '17'])).
% 0.22/0.51  thf('19', plain,
% 0.22/0.51      (![X1 : $i, X3 : $i]:
% 0.22/0.51         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.22/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.51  thf('20', plain,
% 0.22/0.51      (((r1_tarski @ sk_C_2 @ sk_A) | (r1_tarski @ sk_C_2 @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.51  thf('21', plain, ((r1_tarski @ sk_C_2 @ sk_A)),
% 0.22/0.51      inference('simplify', [status(thm)], ['20'])).
% 0.22/0.51  thf('22', plain, ($false), inference('demod', [status(thm)], ['0', '21'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.avEdhvJlC6

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   36 (  41 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :    9
%              Number of atoms          :  243 ( 313 expanded)
%              Number of equality atoms :   26 (  35 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t59_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          = ( k1_tarski @ A ) )
        & ( r2_hidden @ B @ C )
        & ( A != B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
            = ( k1_tarski @ A ) )
          & ( r2_hidden @ B @ C )
          & ( A != B ) ) ),
    inference('cnf.neg',[status(esa)],[t59_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('2',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ ( k4_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('6',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('8',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) )
    = ( k4_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('10',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','11'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('13',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( X18 != X17 )
      | ( r2_hidden @ X18 @ X19 )
      | ( X19
       != ( k2_tarski @ X20 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('14',plain,(
    ! [X17: $i,X20: $i] :
      ( r2_hidden @ X17 @ ( k2_tarski @ X20 @ X17 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['12','14'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('16',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X14 )
      | ( X15 = X12 )
      | ( X14
       != ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('17',plain,(
    ! [X12: $i,X15: $i] :
      ( ( X15 = X12 )
      | ~ ( r2_hidden @ X15 @ ( k1_tarski @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['18','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.avEdhvJlC6
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:50:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 183 iterations in 0.083s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.54  thf(t59_zfmisc_1, conjecture,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ~( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) & 
% 0.20/0.54          ( r2_hidden @ B @ C ) & ( ( A ) != ( B ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.54        ( ~( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) & 
% 0.20/0.54             ( r2_hidden @ B @ C ) & ( ( A ) != ( B ) ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t59_zfmisc_1])).
% 0.20/0.54  thf('0', plain, ((r2_hidden @ sk_B @ sk_C_1)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(d5_xboole_0, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.20/0.54       ( ![D:$i]:
% 0.20/0.54         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.54           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.20/0.54  thf('1', plain,
% 0.20/0.54      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X2 @ X3)
% 0.20/0.54          | (r2_hidden @ X2 @ X4)
% 0.20/0.54          | (r2_hidden @ X2 @ X5)
% 0.20/0.54          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.54  thf('2', plain,
% 0.20/0.54      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.54         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 0.20/0.54          | (r2_hidden @ X2 @ X4)
% 0.20/0.54          | ~ (r2_hidden @ X2 @ X3))),
% 0.20/0.54      inference('simplify', [status(thm)], ['1'])).
% 0.20/0.54  thf('3', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((r2_hidden @ sk_B @ X0)
% 0.20/0.54          | (r2_hidden @ sk_B @ (k4_xboole_0 @ sk_C_1 @ X0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['0', '2'])).
% 0.20/0.54  thf('4', plain,
% 0.20/0.54      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_tarski @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.54  thf('5', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.54  thf('6', plain,
% 0.20/0.54      (((k3_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B)) = (k1_tarski @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.54  thf(t47_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.20/0.54  thf('7', plain,
% 0.20/0.54      (![X8 : $i, X9 : $i]:
% 0.20/0.54         ((k4_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9))
% 0.20/0.54           = (k4_xboole_0 @ X8 @ X9))),
% 0.20/0.54      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.20/0.54  thf('8', plain,
% 0.20/0.54      (((k4_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A))
% 0.20/0.54         = (k4_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['6', '7'])).
% 0.20/0.54  thf('9', plain,
% 0.20/0.54      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X6 @ X5)
% 0.20/0.54          | ~ (r2_hidden @ X6 @ X4)
% 0.20/0.54          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.54  thf('10', plain,
% 0.20/0.54      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X6 @ X4)
% 0.20/0.54          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['9'])).
% 0.20/0.54  thf('11', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A)))
% 0.20/0.54          | ~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['8', '10'])).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      (((r2_hidden @ sk_B @ (k1_tarski @ sk_A))
% 0.20/0.54        | ~ (r2_hidden @ sk_B @ (k2_tarski @ sk_A @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['3', '11'])).
% 0.20/0.54  thf(d2_tarski, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.20/0.54       ( ![D:$i]:
% 0.20/0.54         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.20/0.54  thf('13', plain,
% 0.20/0.54      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.54         (((X18) != (X17))
% 0.20/0.54          | (r2_hidden @ X18 @ X19)
% 0.20/0.54          | ((X19) != (k2_tarski @ X20 @ X17)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.54  thf('14', plain,
% 0.20/0.54      (![X17 : $i, X20 : $i]: (r2_hidden @ X17 @ (k2_tarski @ X20 @ X17))),
% 0.20/0.54      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.54  thf('15', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['12', '14'])).
% 0.20/0.54  thf(d1_tarski, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.54  thf('16', plain,
% 0.20/0.54      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X15 @ X14)
% 0.20/0.54          | ((X15) = (X12))
% 0.20/0.54          | ((X14) != (k1_tarski @ X12)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.54  thf('17', plain,
% 0.20/0.54      (![X12 : $i, X15 : $i]:
% 0.20/0.54         (((X15) = (X12)) | ~ (r2_hidden @ X15 @ (k1_tarski @ X12)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.54  thf('18', plain, (((sk_B) = (sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['15', '17'])).
% 0.20/0.54  thf('19', plain, (((sk_A) != (sk_B))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('20', plain, ($false),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['18', '19'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

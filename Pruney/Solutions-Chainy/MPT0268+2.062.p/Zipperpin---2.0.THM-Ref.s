%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uyuPun41iN

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:00 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   41 (  73 expanded)
%              Number of leaves         :   12 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :  277 ( 574 expanded)
%              Number of equality atoms :   26 (  56 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t65_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
          = A )
      <=> ~ ( r2_hidden @ B @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t65_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('6',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( X20 != X22 )
      | ~ ( r2_hidden @ X20 @ ( k4_xboole_0 @ X21 @ ( k1_tarski @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('7',plain,(
    ! [X21: $i,X22: $i] :
      ~ ( r2_hidden @ X22 @ ( k4_xboole_0 @ X21 @ ( k1_tarski @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','9'])).

thf('11',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','10'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('13',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( X12 = X9 )
      | ( X11
       != ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('14',plain,(
    ! [X9: $i,X12: $i] :
      ( ( X12 = X9 )
      | ~ ( r2_hidden @ X12 @ ( k1_tarski @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('19',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('22',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('23',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['2','9','22'])).

thf('24',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['21','23'])).

thf('25',plain,
    ( ( sk_A != sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','24'])).

thf('26',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['11','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uyuPun41iN
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:45:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.35/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.54  % Solved by: fo/fo7.sh
% 0.35/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.54  % done 57 iterations in 0.039s
% 0.35/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.54  % SZS output start Refutation
% 0.35/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.35/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.35/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.35/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.54  thf(t65_zfmisc_1, conjecture,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.35/0.54       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.35/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.54    (~( ![A:$i,B:$i]:
% 0.35/0.54        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.35/0.54          ( ~( r2_hidden @ B @ A ) ) ) )),
% 0.35/0.54    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 0.35/0.54  thf('0', plain,
% 0.35/0.54      ((~ (r2_hidden @ sk_B @ sk_A)
% 0.35/0.54        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('1', plain,
% 0.35/0.54      ((~ (r2_hidden @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_B @ sk_A)))),
% 0.35/0.54      inference('split', [status(esa)], ['0'])).
% 0.35/0.54  thf('2', plain,
% 0.35/0.54      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 0.35/0.54       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.35/0.54      inference('split', [status(esa)], ['0'])).
% 0.35/0.54  thf('3', plain,
% 0.35/0.54      (((r2_hidden @ sk_B @ sk_A)
% 0.35/0.54        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('4', plain,
% 0.35/0.54      (((r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.35/0.54      inference('split', [status(esa)], ['3'])).
% 0.35/0.54  thf('5', plain,
% 0.35/0.54      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))
% 0.35/0.54         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.35/0.54      inference('split', [status(esa)], ['0'])).
% 0.35/0.54  thf(t64_zfmisc_1, axiom,
% 0.35/0.54    (![A:$i,B:$i,C:$i]:
% 0.35/0.54     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.35/0.54       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.35/0.54  thf('6', plain,
% 0.35/0.54      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.35/0.54         (((X20) != (X22))
% 0.35/0.54          | ~ (r2_hidden @ X20 @ (k4_xboole_0 @ X21 @ (k1_tarski @ X22))))),
% 0.35/0.54      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.35/0.54  thf('7', plain,
% 0.35/0.54      (![X21 : $i, X22 : $i]:
% 0.35/0.54         ~ (r2_hidden @ X22 @ (k4_xboole_0 @ X21 @ (k1_tarski @ X22)))),
% 0.35/0.54      inference('simplify', [status(thm)], ['6'])).
% 0.35/0.54  thf('8', plain,
% 0.35/0.54      ((~ (r2_hidden @ sk_B @ sk_A))
% 0.35/0.54         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['5', '7'])).
% 0.35/0.54  thf('9', plain,
% 0.35/0.54      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) | 
% 0.35/0.54       ~ ((r2_hidden @ sk_B @ sk_A))),
% 0.35/0.54      inference('sup-', [status(thm)], ['4', '8'])).
% 0.35/0.54  thf('10', plain, (~ ((r2_hidden @ sk_B @ sk_A))),
% 0.35/0.54      inference('sat_resolution*', [status(thm)], ['2', '9'])).
% 0.35/0.54  thf('11', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 0.35/0.54      inference('simpl_trail', [status(thm)], ['1', '10'])).
% 0.35/0.54  thf(t3_xboole_0, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.35/0.54            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.35/0.54       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.35/0.54            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.35/0.54  thf('12', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.35/0.54      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.35/0.54  thf(d1_tarski, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.35/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.35/0.54  thf('13', plain,
% 0.35/0.54      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X12 @ X11)
% 0.35/0.54          | ((X12) = (X9))
% 0.35/0.54          | ((X11) != (k1_tarski @ X9)))),
% 0.35/0.54      inference('cnf', [status(esa)], [d1_tarski])).
% 0.35/0.54  thf('14', plain,
% 0.35/0.54      (![X9 : $i, X12 : $i]:
% 0.35/0.54         (((X12) = (X9)) | ~ (r2_hidden @ X12 @ (k1_tarski @ X9)))),
% 0.35/0.54      inference('simplify', [status(thm)], ['13'])).
% 0.35/0.54  thf('15', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.35/0.54          | ((sk_C @ (k1_tarski @ X0) @ X1) = (X0)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['12', '14'])).
% 0.35/0.54  thf('16', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.35/0.54      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.35/0.54  thf('17', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         ((r2_hidden @ X0 @ X1)
% 0.35/0.54          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.35/0.54          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.35/0.54      inference('sup+', [status(thm)], ['15', '16'])).
% 0.35/0.54  thf('18', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0)) | (r2_hidden @ X0 @ X1))),
% 0.35/0.54      inference('simplify', [status(thm)], ['17'])).
% 0.35/0.54  thf(t83_xboole_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.35/0.54  thf('19', plain,
% 0.35/0.54      (![X6 : $i, X7 : $i]:
% 0.35/0.54         (((k4_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 0.35/0.54      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.35/0.54  thf('20', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         ((r2_hidden @ X0 @ X1)
% 0.35/0.54          | ((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['18', '19'])).
% 0.35/0.54  thf('21', plain,
% 0.35/0.54      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))
% 0.35/0.54         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.35/0.54      inference('split', [status(esa)], ['3'])).
% 0.35/0.54  thf('22', plain,
% 0.35/0.54      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) | 
% 0.35/0.54       ((r2_hidden @ sk_B @ sk_A))),
% 0.35/0.54      inference('split', [status(esa)], ['3'])).
% 0.35/0.54  thf('23', plain, (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.35/0.54      inference('sat_resolution*', [status(thm)], ['2', '9', '22'])).
% 0.35/0.54  thf('24', plain, (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A))),
% 0.35/0.54      inference('simpl_trail', [status(thm)], ['21', '23'])).
% 0.35/0.54  thf('25', plain, ((((sk_A) != (sk_A)) | (r2_hidden @ sk_B @ sk_A))),
% 0.35/0.54      inference('sup-', [status(thm)], ['20', '24'])).
% 0.35/0.54  thf('26', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.35/0.54      inference('simplify', [status(thm)], ['25'])).
% 0.35/0.54  thf('27', plain, ($false), inference('demod', [status(thm)], ['11', '26'])).
% 0.35/0.54  
% 0.35/0.54  % SZS output end Refutation
% 0.35/0.54  
% 0.35/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

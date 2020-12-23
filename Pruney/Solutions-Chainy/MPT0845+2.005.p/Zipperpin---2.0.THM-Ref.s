%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Z6WVYoNej7

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:35 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   50 (  56 expanded)
%              Number of leaves         :   20 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :  258 ( 320 expanded)
%              Number of equality atoms :   13 (  15 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_tarski,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ! [D: $i] :
                  ~ ( ( r2_hidden @ D @ B )
                    & ( r2_hidden @ D @ C ) ) ) ) )).

thf('1',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( r2_hidden @ X47 @ X48 )
      | ( r2_hidden @ ( sk_C_2 @ X48 ) @ X48 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t1_mcart_1,conjecture,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ( r1_xboole_0 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ! [B: $i] :
              ~ ( ( r2_hidden @ B @ A )
                & ( r1_xboole_0 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t1_mcart_1])).

thf('3',plain,(
    ! [X50: $i] :
      ( ~ ( r2_hidden @ X50 @ sk_A )
      | ~ ( r1_xboole_0 @ X50 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( r1_xboole_0 @ ( sk_C_2 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('9',plain,(
    ! [X29: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X29 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('10',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( r2_hidden @ X44 @ X45 )
      | ( ( k4_xboole_0 @ X45 @ ( k1_tarski @ X44 ) )
       != X45 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['8','12'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X14: $i,X16: $i] :
      ( ( X14 = X16 )
      | ~ ( r1_tarski @ X16 @ X14 )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','15'])).

thf('17',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( sk_A != X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ~ ( r1_xboole_0 @ ( sk_C_2 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['4','19'])).

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

thf('21',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('22',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('23',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( r2_hidden @ X47 @ X48 )
      | ~ ( r2_hidden @ X49 @ X48 )
      | ~ ( r2_hidden @ X49 @ ( sk_C_2 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( sk_C_2 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(condensation,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( sk_C_2 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X1 @ ( sk_C_2 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( sk_C_2 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ ( sk_C_2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( sk_C_2 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    $false ),
    inference(demod,[status(thm)],['20','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Z6WVYoNej7
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:45:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.35/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.54  % Solved by: fo/fo7.sh
% 0.35/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.54  % done 260 iterations in 0.101s
% 0.35/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.54  % SZS output start Refutation
% 0.35/0.54  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.35/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.35/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.35/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.35/0.54  thf(sk_C_2_type, type, sk_C_2: $i > $i).
% 0.35/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.35/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.35/0.54  thf(d1_xboole_0, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.35/0.54  thf('0', plain,
% 0.35/0.54      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.35/0.54      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.35/0.54  thf(t7_tarski, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ~( ( r2_hidden @ A @ B ) & 
% 0.35/0.54          ( ![C:$i]:
% 0.35/0.54            ( ~( ( r2_hidden @ C @ B ) & 
% 0.35/0.54                 ( ![D:$i]:
% 0.35/0.54                   ( ~( ( r2_hidden @ D @ B ) & ( r2_hidden @ D @ C ) ) ) ) ) ) ) ) ))).
% 0.35/0.54  thf('1', plain,
% 0.35/0.54      (![X47 : $i, X48 : $i]:
% 0.35/0.54         (~ (r2_hidden @ X47 @ X48) | (r2_hidden @ (sk_C_2 @ X48) @ X48))),
% 0.35/0.54      inference('cnf', [status(esa)], [t7_tarski])).
% 0.35/0.54  thf('2', plain,
% 0.35/0.54      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r2_hidden @ (sk_C_2 @ X0) @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.35/0.54  thf(t1_mcart_1, conjecture,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.35/0.54          ( ![B:$i]: ( ~( ( r2_hidden @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ) ) ))).
% 0.35/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.54    (~( ![A:$i]:
% 0.35/0.54        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.35/0.54             ( ![B:$i]:
% 0.35/0.54               ( ~( ( r2_hidden @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ) ) ) )),
% 0.35/0.54    inference('cnf.neg', [status(esa)], [t1_mcart_1])).
% 0.39/0.54  thf('3', plain,
% 0.39/0.54      (![X50 : $i]: (~ (r2_hidden @ X50 @ sk_A) | ~ (r1_xboole_0 @ X50 @ sk_A))),
% 0.39/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.54  thf('4', plain,
% 0.39/0.54      (((v1_xboole_0 @ sk_A) | ~ (r1_xboole_0 @ (sk_C_2 @ sk_A) @ sk_A))),
% 0.39/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.54  thf(d3_tarski, axiom,
% 0.39/0.54    (![A:$i,B:$i]:
% 0.39/0.54     ( ( r1_tarski @ A @ B ) <=>
% 0.39/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.39/0.54  thf('5', plain,
% 0.39/0.54      (![X4 : $i, X6 : $i]:
% 0.39/0.54         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.39/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.54  thf('6', plain,
% 0.39/0.54      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.39/0.54      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.54  thf('7', plain,
% 0.39/0.54      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.39/0.54      inference('sup-', [status(thm)], ['5', '6'])).
% 0.39/0.54  thf('8', plain,
% 0.39/0.54      (![X4 : $i, X6 : $i]:
% 0.39/0.54         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.39/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.54  thf(t4_boole, axiom,
% 0.39/0.54    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.39/0.54  thf('9', plain,
% 0.39/0.54      (![X29 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X29) = (k1_xboole_0))),
% 0.39/0.54      inference('cnf', [status(esa)], [t4_boole])).
% 0.39/0.54  thf(t65_zfmisc_1, axiom,
% 0.39/0.54    (![A:$i,B:$i]:
% 0.39/0.54     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.39/0.54       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.39/0.54  thf('10', plain,
% 0.39/0.54      (![X44 : $i, X45 : $i]:
% 0.39/0.54         (~ (r2_hidden @ X44 @ X45)
% 0.39/0.54          | ((k4_xboole_0 @ X45 @ (k1_tarski @ X44)) != (X45)))),
% 0.39/0.54      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.39/0.54  thf('11', plain,
% 0.39/0.54      (![X0 : $i]:
% 0.39/0.54         (((k1_xboole_0) != (k1_xboole_0)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.39/0.54      inference('sup-', [status(thm)], ['9', '10'])).
% 0.39/0.54  thf('12', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.39/0.54      inference('simplify', [status(thm)], ['11'])).
% 0.39/0.54  thf('13', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.39/0.54      inference('sup-', [status(thm)], ['8', '12'])).
% 0.39/0.54  thf(d10_xboole_0, axiom,
% 0.39/0.54    (![A:$i,B:$i]:
% 0.39/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.39/0.54  thf('14', plain,
% 0.39/0.54      (![X14 : $i, X16 : $i]:
% 0.39/0.54         (((X14) = (X16))
% 0.39/0.54          | ~ (r1_tarski @ X16 @ X14)
% 0.39/0.54          | ~ (r1_tarski @ X14 @ X16))),
% 0.39/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.54  thf('15', plain,
% 0.39/0.54      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.39/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.39/0.54  thf('16', plain,
% 0.39/0.54      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.39/0.54      inference('sup-', [status(thm)], ['7', '15'])).
% 0.39/0.54  thf('17', plain, (((sk_A) != (k1_xboole_0))),
% 0.39/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.54  thf('18', plain, (![X0 : $i]: (((sk_A) != (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.39/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.39/0.54  thf('19', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.39/0.54      inference('simplify', [status(thm)], ['18'])).
% 0.39/0.54  thf('20', plain, (~ (r1_xboole_0 @ (sk_C_2 @ sk_A) @ sk_A)),
% 0.39/0.54      inference('clc', [status(thm)], ['4', '19'])).
% 0.39/0.54  thf(t3_xboole_0, axiom,
% 0.39/0.54    (![A:$i,B:$i]:
% 0.39/0.54     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.39/0.54            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.39/0.54       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.39/0.54            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.39/0.54  thf('21', plain,
% 0.39/0.54      (![X10 : $i, X11 : $i]:
% 0.39/0.54         ((r1_xboole_0 @ X10 @ X11) | (r2_hidden @ (sk_C_1 @ X11 @ X10) @ X11))),
% 0.39/0.54      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.39/0.54  thf('22', plain,
% 0.39/0.54      (![X10 : $i, X11 : $i]:
% 0.39/0.54         ((r1_xboole_0 @ X10 @ X11) | (r2_hidden @ (sk_C_1 @ X11 @ X10) @ X10))),
% 0.39/0.54      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.39/0.54  thf('23', plain,
% 0.39/0.54      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.39/0.54         (~ (r2_hidden @ X47 @ X48)
% 0.39/0.54          | ~ (r2_hidden @ X49 @ X48)
% 0.39/0.54          | ~ (r2_hidden @ X49 @ (sk_C_2 @ X48)))),
% 0.39/0.54      inference('cnf', [status(esa)], [t7_tarski])).
% 0.39/0.54  thf('24', plain,
% 0.39/0.54      (![X0 : $i, X1 : $i]:
% 0.39/0.54         (~ (r2_hidden @ X1 @ (sk_C_2 @ X0)) | ~ (r2_hidden @ X1 @ X0))),
% 0.39/0.54      inference('condensation', [status(thm)], ['23'])).
% 0.39/0.55  thf('25', plain,
% 0.39/0.55      (![X0 : $i, X1 : $i]:
% 0.39/0.55         ((r1_xboole_0 @ (sk_C_2 @ X0) @ X1)
% 0.39/0.55          | ~ (r2_hidden @ (sk_C_1 @ X1 @ (sk_C_2 @ X0)) @ X0))),
% 0.39/0.55      inference('sup-', [status(thm)], ['22', '24'])).
% 0.39/0.55  thf('26', plain,
% 0.39/0.55      (![X0 : $i]:
% 0.39/0.55         ((r1_xboole_0 @ (sk_C_2 @ X0) @ X0)
% 0.39/0.55          | (r1_xboole_0 @ (sk_C_2 @ X0) @ X0))),
% 0.39/0.55      inference('sup-', [status(thm)], ['21', '25'])).
% 0.39/0.55  thf('27', plain, (![X0 : $i]: (r1_xboole_0 @ (sk_C_2 @ X0) @ X0)),
% 0.39/0.55      inference('simplify', [status(thm)], ['26'])).
% 0.39/0.55  thf('28', plain, ($false), inference('demod', [status(thm)], ['20', '27'])).
% 0.39/0.55  
% 0.39/0.55  % SZS output end Refutation
% 0.39/0.55  
% 0.39/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ef51SjhsvT

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:00 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   45 (  87 expanded)
%              Number of leaves         :    9 (  24 expanded)
%              Depth                    :   11
%              Number of atoms          :  383 ( 805 expanded)
%              Number of equality atoms :   39 (  82 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( X16 != X15 )
      | ( r2_hidden @ X16 @ X17 )
      | ( X17
       != ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('6',plain,(
    ! [X15: $i] :
      ( r2_hidden @ X15 @ ( k1_tarski @ X15 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('9',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf('12',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','12'])).

thf('14',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','13'])).

thf('15',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['15'])).

thf('17',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['15'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X17 )
      | ( X18 = X15 )
      | ( X17
       != ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('23',plain,(
    ! [X15: $i,X18: $i] :
      ( ( X18 = X15 )
      | ~ ( r2_hidden @ X18 @ ( k1_tarski @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_D @ X1 @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['15'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('29',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('30',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['2','12','29'])).

thf('31',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['28','30'])).

thf('32',plain,
    ( ( sk_A != sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf('33',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['14','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ef51SjhsvT
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:43:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.61/1.79  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.61/1.79  % Solved by: fo/fo7.sh
% 1.61/1.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.61/1.79  % done 1605 iterations in 1.327s
% 1.61/1.79  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.61/1.79  % SZS output start Refutation
% 1.61/1.79  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.61/1.79  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.61/1.79  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.61/1.79  thf(sk_B_type, type, sk_B: $i).
% 1.61/1.79  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.61/1.79  thf(sk_A_type, type, sk_A: $i).
% 1.61/1.79  thf(t65_zfmisc_1, conjecture,
% 1.61/1.79    (![A:$i,B:$i]:
% 1.61/1.79     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 1.61/1.79       ( ~( r2_hidden @ B @ A ) ) ))).
% 1.61/1.79  thf(zf_stmt_0, negated_conjecture,
% 1.61/1.79    (~( ![A:$i,B:$i]:
% 1.61/1.79        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 1.61/1.79          ( ~( r2_hidden @ B @ A ) ) ) )),
% 1.61/1.79    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 1.61/1.79  thf('0', plain,
% 1.61/1.79      ((~ (r2_hidden @ sk_B @ sk_A)
% 1.61/1.79        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 1.61/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.79  thf('1', plain,
% 1.61/1.79      ((~ (r2_hidden @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_B @ sk_A)))),
% 1.61/1.79      inference('split', [status(esa)], ['0'])).
% 1.61/1.79  thf('2', plain,
% 1.61/1.79      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 1.61/1.79       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 1.61/1.79      inference('split', [status(esa)], ['0'])).
% 1.61/1.79  thf('3', plain,
% 1.61/1.79      (((r2_hidden @ sk_B @ sk_A)
% 1.61/1.79        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))),
% 1.61/1.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.61/1.79  thf('4', plain,
% 1.61/1.79      (((r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_B @ sk_A)))),
% 1.61/1.79      inference('split', [status(esa)], ['3'])).
% 1.61/1.79  thf(d1_tarski, axiom,
% 1.61/1.79    (![A:$i,B:$i]:
% 1.61/1.79     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.61/1.79       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.61/1.79  thf('5', plain,
% 1.61/1.79      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.61/1.79         (((X16) != (X15))
% 1.61/1.79          | (r2_hidden @ X16 @ X17)
% 1.61/1.79          | ((X17) != (k1_tarski @ X15)))),
% 1.61/1.79      inference('cnf', [status(esa)], [d1_tarski])).
% 1.61/1.79  thf('6', plain, (![X15 : $i]: (r2_hidden @ X15 @ (k1_tarski @ X15))),
% 1.61/1.79      inference('simplify', [status(thm)], ['5'])).
% 1.61/1.79  thf('7', plain,
% 1.61/1.79      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))
% 1.61/1.79         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.61/1.79      inference('split', [status(esa)], ['0'])).
% 1.61/1.79  thf(d5_xboole_0, axiom,
% 1.61/1.79    (![A:$i,B:$i,C:$i]:
% 1.61/1.79     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.61/1.79       ( ![D:$i]:
% 1.61/1.79         ( ( r2_hidden @ D @ C ) <=>
% 1.61/1.79           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.61/1.79  thf('8', plain,
% 1.61/1.79      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.61/1.79         (~ (r2_hidden @ X4 @ X3)
% 1.61/1.79          | ~ (r2_hidden @ X4 @ X2)
% 1.61/1.79          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 1.61/1.79      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.61/1.79  thf('9', plain,
% 1.61/1.79      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.61/1.79         (~ (r2_hidden @ X4 @ X2)
% 1.61/1.79          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 1.61/1.79      inference('simplify', [status(thm)], ['8'])).
% 1.61/1.79  thf('10', plain,
% 1.61/1.79      ((![X0 : $i]:
% 1.61/1.79          (~ (r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))))
% 1.61/1.79         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.61/1.79      inference('sup-', [status(thm)], ['7', '9'])).
% 1.61/1.79  thf('11', plain,
% 1.61/1.79      ((~ (r2_hidden @ sk_B @ sk_A))
% 1.61/1.79         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.61/1.79      inference('sup-', [status(thm)], ['6', '10'])).
% 1.61/1.79  thf('12', plain,
% 1.61/1.79      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) | 
% 1.61/1.79       ~ ((r2_hidden @ sk_B @ sk_A))),
% 1.61/1.79      inference('sup-', [status(thm)], ['4', '11'])).
% 1.61/1.79  thf('13', plain, (~ ((r2_hidden @ sk_B @ sk_A))),
% 1.61/1.79      inference('sat_resolution*', [status(thm)], ['2', '12'])).
% 1.61/1.79  thf('14', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 1.61/1.79      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 1.61/1.79  thf('15', plain,
% 1.61/1.79      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.61/1.79         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 1.61/1.79          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 1.61/1.79          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.61/1.79      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.61/1.79  thf('16', plain,
% 1.61/1.79      (![X0 : $i, X1 : $i]:
% 1.61/1.79         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.61/1.79          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.61/1.79      inference('eq_fact', [status(thm)], ['15'])).
% 1.61/1.79  thf('17', plain,
% 1.61/1.79      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.61/1.79         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 1.61/1.79          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 1.61/1.79          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 1.61/1.79          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.61/1.79      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.61/1.79  thf('18', plain,
% 1.61/1.79      (![X0 : $i, X1 : $i]:
% 1.61/1.79         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 1.61/1.79          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.61/1.79          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 1.61/1.79          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.61/1.79      inference('sup-', [status(thm)], ['16', '17'])).
% 1.61/1.79  thf('19', plain,
% 1.61/1.79      (![X0 : $i, X1 : $i]:
% 1.61/1.79         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 1.61/1.79          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.61/1.79          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.61/1.79      inference('simplify', [status(thm)], ['18'])).
% 1.61/1.79  thf('20', plain,
% 1.61/1.79      (![X0 : $i, X1 : $i]:
% 1.61/1.79         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.61/1.79          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.61/1.79      inference('eq_fact', [status(thm)], ['15'])).
% 1.61/1.79  thf('21', plain,
% 1.61/1.79      (![X0 : $i, X1 : $i]:
% 1.61/1.79         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 1.61/1.79          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 1.61/1.79      inference('clc', [status(thm)], ['19', '20'])).
% 1.61/1.79  thf('22', plain,
% 1.61/1.79      (![X15 : $i, X17 : $i, X18 : $i]:
% 1.61/1.79         (~ (r2_hidden @ X18 @ X17)
% 1.61/1.79          | ((X18) = (X15))
% 1.61/1.79          | ((X17) != (k1_tarski @ X15)))),
% 1.61/1.79      inference('cnf', [status(esa)], [d1_tarski])).
% 1.61/1.79  thf('23', plain,
% 1.61/1.79      (![X15 : $i, X18 : $i]:
% 1.61/1.79         (((X18) = (X15)) | ~ (r2_hidden @ X18 @ (k1_tarski @ X15)))),
% 1.61/1.79      inference('simplify', [status(thm)], ['22'])).
% 1.61/1.79  thf('24', plain,
% 1.61/1.79      (![X0 : $i, X1 : $i]:
% 1.61/1.79         (((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 1.61/1.79          | ((sk_D @ X1 @ (k1_tarski @ X0) @ X1) = (X0)))),
% 1.61/1.79      inference('sup-', [status(thm)], ['21', '23'])).
% 1.61/1.79  thf('25', plain,
% 1.61/1.79      (![X0 : $i, X1 : $i]:
% 1.61/1.79         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.61/1.79          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.61/1.79      inference('eq_fact', [status(thm)], ['15'])).
% 1.61/1.79  thf('26', plain,
% 1.61/1.79      (![X0 : $i, X1 : $i]:
% 1.61/1.79         ((r2_hidden @ X0 @ X1)
% 1.61/1.79          | ((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 1.61/1.79          | ((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 1.61/1.79      inference('sup+', [status(thm)], ['24', '25'])).
% 1.61/1.79  thf('27', plain,
% 1.61/1.79      (![X0 : $i, X1 : $i]:
% 1.61/1.79         (((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 1.61/1.79          | (r2_hidden @ X0 @ X1))),
% 1.61/1.79      inference('simplify', [status(thm)], ['26'])).
% 1.61/1.79  thf('28', plain,
% 1.61/1.79      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))
% 1.61/1.79         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.61/1.79      inference('split', [status(esa)], ['3'])).
% 1.61/1.79  thf('29', plain,
% 1.61/1.79      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) | 
% 1.61/1.79       ((r2_hidden @ sk_B @ sk_A))),
% 1.61/1.79      inference('split', [status(esa)], ['3'])).
% 1.61/1.79  thf('30', plain, (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 1.61/1.79      inference('sat_resolution*', [status(thm)], ['2', '12', '29'])).
% 1.61/1.79  thf('31', plain, (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A))),
% 1.61/1.79      inference('simpl_trail', [status(thm)], ['28', '30'])).
% 1.61/1.79  thf('32', plain, ((((sk_A) != (sk_A)) | (r2_hidden @ sk_B @ sk_A))),
% 1.61/1.79      inference('sup-', [status(thm)], ['27', '31'])).
% 1.61/1.79  thf('33', plain, ((r2_hidden @ sk_B @ sk_A)),
% 1.61/1.79      inference('simplify', [status(thm)], ['32'])).
% 1.61/1.79  thf('34', plain, ($false), inference('demod', [status(thm)], ['14', '33'])).
% 1.61/1.79  
% 1.61/1.79  % SZS output end Refutation
% 1.61/1.79  
% 1.61/1.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

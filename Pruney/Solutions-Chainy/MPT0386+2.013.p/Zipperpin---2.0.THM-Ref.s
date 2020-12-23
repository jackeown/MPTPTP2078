%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OPlpbEXE6u

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:33 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   37 (  45 expanded)
%              Number of leaves         :   13 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :  248 ( 329 expanded)
%              Number of equality atoms :   17 (  22 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t4_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t4_setfam_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_A @ sk_B ),
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

thf(d1_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( A = k1_xboole_0 )
       => ( ( B
            = ( k1_setfam_1 @ A ) )
        <=> ( B = k1_xboole_0 ) ) )
      & ( ( A != k1_xboole_0 )
       => ( ( B
            = ( k1_setfam_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ! [D: $i] :
                  ( ( r2_hidden @ D @ A )
                 => ( r2_hidden @ C @ D ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X27: $i,X28: $i,X30: $i,X31: $i] :
      ( ( X27
       != ( k1_setfam_1 @ X28 ) )
      | ~ ( r2_hidden @ X30 @ X28 )
      | ( r2_hidden @ X31 @ X30 )
      | ~ ( r2_hidden @ X31 @ X27 )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('4',plain,(
    ! [X28: $i,X30: $i,X31: $i] :
      ( ( X28 = k1_xboole_0 )
      | ~ ( r2_hidden @ X31 @ ( k1_setfam_1 @ X28 ) )
      | ( r2_hidden @ X31 @ X30 )
      | ~ ( r2_hidden @ X30 @ X28 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_setfam_1 @ X0 ) ) @ X2 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_setfam_1 @ sk_B ) ) @ sk_A )
      | ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('7',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,
    ( ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ sk_A ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ~ ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X28: $i,X33: $i] :
      ( ( X33
       != ( k1_setfam_1 @ X28 ) )
      | ( X33 = k1_xboole_0 )
      | ( X28 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('13',plain,
    ( ( k1_setfam_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['12'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('14',plain,(
    ! [X9: $i] :
      ( r1_xboole_0 @ X9 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('15',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

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

thf('17',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,(
    $false ),
    inference(demod,[status(thm)],['0','11','13','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OPlpbEXE6u
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:59:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.40/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.60  % Solved by: fo/fo7.sh
% 0.40/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.60  % done 252 iterations in 0.143s
% 0.40/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.60  % SZS output start Refutation
% 0.40/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.60  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.40/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.60  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.40/0.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.40/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.60  thf(t4_setfam_1, conjecture,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 0.40/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.60    (~( ![A:$i,B:$i]:
% 0.40/0.60        ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )),
% 0.40/0.60    inference('cnf.neg', [status(esa)], [t4_setfam_1])).
% 0.40/0.60  thf('0', plain, (~ (r1_tarski @ (k1_setfam_1 @ sk_B) @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('1', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf(d3_tarski, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( r1_tarski @ A @ B ) <=>
% 0.40/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.40/0.60  thf('2', plain,
% 0.40/0.60      (![X1 : $i, X3 : $i]:
% 0.40/0.60         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.40/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.60  thf(d1_setfam_1, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( ( ( A ) = ( k1_xboole_0 ) ) =>
% 0.40/0.60         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=> ( ( B ) = ( k1_xboole_0 ) ) ) ) & 
% 0.40/0.60       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.40/0.60         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=>
% 0.40/0.60           ( ![C:$i]:
% 0.40/0.60             ( ( r2_hidden @ C @ B ) <=>
% 0.40/0.60               ( ![D:$i]: ( ( r2_hidden @ D @ A ) => ( r2_hidden @ C @ D ) ) ) ) ) ) ) ))).
% 0.40/0.60  thf('3', plain,
% 0.40/0.60      (![X27 : $i, X28 : $i, X30 : $i, X31 : $i]:
% 0.40/0.60         (((X27) != (k1_setfam_1 @ X28))
% 0.40/0.60          | ~ (r2_hidden @ X30 @ X28)
% 0.40/0.60          | (r2_hidden @ X31 @ X30)
% 0.40/0.60          | ~ (r2_hidden @ X31 @ X27)
% 0.40/0.60          | ((X28) = (k1_xboole_0)))),
% 0.40/0.60      inference('cnf', [status(esa)], [d1_setfam_1])).
% 0.40/0.60  thf('4', plain,
% 0.40/0.60      (![X28 : $i, X30 : $i, X31 : $i]:
% 0.40/0.60         (((X28) = (k1_xboole_0))
% 0.40/0.60          | ~ (r2_hidden @ X31 @ (k1_setfam_1 @ X28))
% 0.40/0.60          | (r2_hidden @ X31 @ X30)
% 0.40/0.60          | ~ (r2_hidden @ X30 @ X28))),
% 0.40/0.60      inference('simplify', [status(thm)], ['3'])).
% 0.40/0.60  thf('5', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.60         ((r1_tarski @ (k1_setfam_1 @ X0) @ X1)
% 0.40/0.60          | ~ (r2_hidden @ X2 @ X0)
% 0.40/0.60          | (r2_hidden @ (sk_C @ X1 @ (k1_setfam_1 @ X0)) @ X2)
% 0.40/0.60          | ((X0) = (k1_xboole_0)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['2', '4'])).
% 0.40/0.60  thf('6', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (((sk_B) = (k1_xboole_0))
% 0.40/0.60          | (r2_hidden @ (sk_C @ X0 @ (k1_setfam_1 @ sk_B)) @ sk_A)
% 0.40/0.60          | (r1_tarski @ (k1_setfam_1 @ sk_B) @ X0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['1', '5'])).
% 0.40/0.60  thf('7', plain,
% 0.40/0.60      (![X1 : $i, X3 : $i]:
% 0.40/0.60         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.40/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.60  thf('8', plain,
% 0.40/0.60      (((r1_tarski @ (k1_setfam_1 @ sk_B) @ sk_A)
% 0.40/0.60        | ((sk_B) = (k1_xboole_0))
% 0.40/0.60        | (r1_tarski @ (k1_setfam_1 @ sk_B) @ sk_A))),
% 0.40/0.60      inference('sup-', [status(thm)], ['6', '7'])).
% 0.40/0.60  thf('9', plain,
% 0.40/0.60      ((((sk_B) = (k1_xboole_0)) | (r1_tarski @ (k1_setfam_1 @ sk_B) @ sk_A))),
% 0.40/0.60      inference('simplify', [status(thm)], ['8'])).
% 0.40/0.60  thf('10', plain, (~ (r1_tarski @ (k1_setfam_1 @ sk_B) @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('11', plain, (((sk_B) = (k1_xboole_0))),
% 0.40/0.60      inference('clc', [status(thm)], ['9', '10'])).
% 0.40/0.60  thf('12', plain,
% 0.40/0.60      (![X28 : $i, X33 : $i]:
% 0.40/0.60         (((X33) != (k1_setfam_1 @ X28))
% 0.40/0.60          | ((X33) = (k1_xboole_0))
% 0.40/0.60          | ((X28) != (k1_xboole_0)))),
% 0.40/0.60      inference('cnf', [status(esa)], [d1_setfam_1])).
% 0.40/0.60  thf('13', plain, (((k1_setfam_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.60      inference('simplify', [status(thm)], ['12'])).
% 0.40/0.60  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.40/0.60  thf('14', plain, (![X9 : $i]: (r1_xboole_0 @ X9 @ k1_xboole_0)),
% 0.40/0.60      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.40/0.60  thf('15', plain,
% 0.40/0.60      (![X1 : $i, X3 : $i]:
% 0.40/0.60         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.40/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.60  thf('16', plain,
% 0.40/0.60      (![X1 : $i, X3 : $i]:
% 0.40/0.60         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.40/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.60  thf(t3_xboole_0, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.40/0.60            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.40/0.60       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.40/0.60            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.40/0.60  thf('17', plain,
% 0.40/0.60      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.40/0.60         (~ (r2_hidden @ X6 @ X4)
% 0.40/0.60          | ~ (r2_hidden @ X6 @ X7)
% 0.40/0.60          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.40/0.60      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.40/0.60  thf('18', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.60         ((r1_tarski @ X0 @ X1)
% 0.40/0.60          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.40/0.60          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.40/0.60      inference('sup-', [status(thm)], ['16', '17'])).
% 0.40/0.60  thf('19', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         ((r1_tarski @ X0 @ X1)
% 0.40/0.60          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.40/0.60          | (r1_tarski @ X0 @ X1))),
% 0.40/0.60      inference('sup-', [status(thm)], ['15', '18'])).
% 0.40/0.60  thf('20', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | (r1_tarski @ X0 @ X1))),
% 0.40/0.60      inference('simplify', [status(thm)], ['19'])).
% 0.40/0.60  thf('21', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.40/0.60      inference('sup-', [status(thm)], ['14', '20'])).
% 0.40/0.60  thf('22', plain, ($false),
% 0.40/0.60      inference('demod', [status(thm)], ['0', '11', '13', '21'])).
% 0.40/0.60  
% 0.40/0.60  % SZS output end Refutation
% 0.40/0.60  
% 0.40/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BUGOxTfTMj

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:16 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   45 (  72 expanded)
%              Number of leaves         :   15 (  26 expanded)
%              Depth                    :   13
%              Number of atoms          :  327 ( 666 expanded)
%              Number of equality atoms :   51 ( 119 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('0',plain,(
    ! [X6: $i,X9: $i,X11: $i] :
      ( ( X11
        = ( k2_tarski @ X9 @ X6 ) )
      | ( ( sk_D @ X11 @ X6 @ X9 )
        = X6 )
      | ( ( sk_D @ X11 @ X6 @ X9 )
        = X9 )
      | ( r2_hidden @ ( sk_D @ X11 @ X6 @ X9 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf(t41_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( A
           != ( k1_tarski @ B ) )
          & ( A != k1_xboole_0 )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( C != B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t41_zfmisc_1])).

thf('1',plain,(
    ! [X40: $i] :
      ( ~ ( r2_hidden @ X40 @ sk_A )
      | ( X40 = sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ sk_A @ X1 @ X0 )
        = X0 )
      | ( ( sk_D @ sk_A @ X1 @ X0 )
        = X1 )
      | ( sk_A
        = ( k2_tarski @ X0 @ X1 ) )
      | ( ( sk_D @ sk_A @ X1 @ X0 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_B )
      | ( ( sk_D @ sk_A @ X1 @ X0 )
        = sk_B )
      | ( sk_A
        = ( k2_tarski @ X0 @ X1 ) )
      | ( ( sk_D @ sk_A @ X1 @ X0 )
        = X1 ) ) ),
    inference(eq_fact,[status(thm)],['2'])).

thf('4',plain,(
    ! [X1: $i] :
      ( ( ( sk_D @ sk_A @ X1 @ sk_B )
        = X1 )
      | ( sk_A
        = ( k2_tarski @ sk_B @ X1 ) )
      | ( ( sk_D @ sk_A @ X1 @ sk_B )
        = sk_B ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( sk_B != X0 )
      | ( sk_A
        = ( k2_tarski @ sk_B @ X0 ) )
      | ( ( sk_D @ sk_A @ X0 @ sk_B )
        = X0 ) ) ),
    inference(eq_fact,[status(thm)],['4'])).

thf('6',plain,
    ( ( ( sk_D @ sk_A @ sk_B @ sk_B )
      = sk_B )
    | ( sk_A
      = ( k2_tarski @ sk_B @ sk_B ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('7',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('8',plain,
    ( ( ( sk_D @ sk_A @ sk_B @ sk_B )
      = sk_B )
    | ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( sk_D @ sk_A @ sk_B @ sk_B )
    = sk_B ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X6: $i,X9: $i,X11: $i] :
      ( ( X11
        = ( k2_tarski @ X9 @ X6 ) )
      | ( ( sk_D @ X11 @ X6 @ X9 )
       != X6 )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X6 @ X9 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('12',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( sk_D @ sk_A @ sk_B @ sk_B )
     != sk_B )
    | ( sk_A
      = ( k2_tarski @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X40: $i] :
      ( ~ ( r2_hidden @ X40 @ sk_A )
      | ( X40 = sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( ( sk_C @ X0 @ sk_A )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ sk_A )
      | ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('19',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('20',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_D @ sk_A @ sk_B @ sk_B )
    = sk_B ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('24',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('25',plain,
    ( ( sk_B != sk_B )
    | ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','22','23','24'])).

thf('26',plain,
    ( sk_A
    = ( k1_tarski @ sk_B ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['26','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BUGOxTfTMj
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:40:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.59/0.79  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.79  % Solved by: fo/fo7.sh
% 0.59/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.79  % done 475 iterations in 0.339s
% 0.59/0.79  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.79  % SZS output start Refutation
% 0.59/0.79  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.79  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.79  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.79  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.59/0.79  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.59/0.79  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.79  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.59/0.79  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.59/0.79  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.59/0.79  thf(d2_tarski, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i]:
% 0.59/0.79     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.59/0.79       ( ![D:$i]:
% 0.59/0.79         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.59/0.79  thf('0', plain,
% 0.59/0.79      (![X6 : $i, X9 : $i, X11 : $i]:
% 0.59/0.79         (((X11) = (k2_tarski @ X9 @ X6))
% 0.59/0.79          | ((sk_D @ X11 @ X6 @ X9) = (X6))
% 0.59/0.79          | ((sk_D @ X11 @ X6 @ X9) = (X9))
% 0.59/0.79          | (r2_hidden @ (sk_D @ X11 @ X6 @ X9) @ X11))),
% 0.59/0.79      inference('cnf', [status(esa)], [d2_tarski])).
% 0.59/0.79  thf(t41_zfmisc_1, conjecture,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.59/0.79          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 0.59/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.79    (~( ![A:$i,B:$i]:
% 0.59/0.79        ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.59/0.79             ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ) )),
% 0.59/0.79    inference('cnf.neg', [status(esa)], [t41_zfmisc_1])).
% 0.59/0.79  thf('1', plain,
% 0.59/0.79      (![X40 : $i]: (~ (r2_hidden @ X40 @ sk_A) | ((X40) = (sk_B)))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('2', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         (((sk_D @ sk_A @ X1 @ X0) = (X0))
% 0.59/0.79          | ((sk_D @ sk_A @ X1 @ X0) = (X1))
% 0.59/0.79          | ((sk_A) = (k2_tarski @ X0 @ X1))
% 0.59/0.79          | ((sk_D @ sk_A @ X1 @ X0) = (sk_B)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['0', '1'])).
% 0.59/0.79  thf('3', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         (((X0) != (sk_B))
% 0.59/0.79          | ((sk_D @ sk_A @ X1 @ X0) = (sk_B))
% 0.59/0.79          | ((sk_A) = (k2_tarski @ X0 @ X1))
% 0.59/0.79          | ((sk_D @ sk_A @ X1 @ X0) = (X1)))),
% 0.59/0.79      inference('eq_fact', [status(thm)], ['2'])).
% 0.59/0.79  thf('4', plain,
% 0.59/0.79      (![X1 : $i]:
% 0.59/0.79         (((sk_D @ sk_A @ X1 @ sk_B) = (X1))
% 0.59/0.79          | ((sk_A) = (k2_tarski @ sk_B @ X1))
% 0.59/0.79          | ((sk_D @ sk_A @ X1 @ sk_B) = (sk_B)))),
% 0.59/0.79      inference('simplify', [status(thm)], ['3'])).
% 0.59/0.79  thf('5', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (((sk_B) != (X0))
% 0.59/0.79          | ((sk_A) = (k2_tarski @ sk_B @ X0))
% 0.59/0.79          | ((sk_D @ sk_A @ X0 @ sk_B) = (X0)))),
% 0.59/0.79      inference('eq_fact', [status(thm)], ['4'])).
% 0.59/0.79  thf('6', plain,
% 0.59/0.79      ((((sk_D @ sk_A @ sk_B @ sk_B) = (sk_B))
% 0.59/0.79        | ((sk_A) = (k2_tarski @ sk_B @ sk_B)))),
% 0.59/0.79      inference('simplify', [status(thm)], ['5'])).
% 0.59/0.79  thf(t69_enumset1, axiom,
% 0.59/0.79    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.59/0.79  thf('7', plain, (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.59/0.79      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.59/0.79  thf('8', plain,
% 0.59/0.79      ((((sk_D @ sk_A @ sk_B @ sk_B) = (sk_B)) | ((sk_A) = (k1_tarski @ sk_B)))),
% 0.59/0.79      inference('demod', [status(thm)], ['6', '7'])).
% 0.59/0.79  thf('9', plain, (((sk_A) != (k1_tarski @ sk_B))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('10', plain, (((sk_D @ sk_A @ sk_B @ sk_B) = (sk_B))),
% 0.59/0.79      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.59/0.79  thf('11', plain,
% 0.59/0.79      (![X6 : $i, X9 : $i, X11 : $i]:
% 0.59/0.79         (((X11) = (k2_tarski @ X9 @ X6))
% 0.59/0.79          | ((sk_D @ X11 @ X6 @ X9) != (X6))
% 0.59/0.79          | ~ (r2_hidden @ (sk_D @ X11 @ X6 @ X9) @ X11))),
% 0.59/0.79      inference('cnf', [status(esa)], [d2_tarski])).
% 0.59/0.79  thf('12', plain,
% 0.59/0.79      ((~ (r2_hidden @ sk_B @ sk_A)
% 0.59/0.79        | ((sk_D @ sk_A @ sk_B @ sk_B) != (sk_B))
% 0.59/0.79        | ((sk_A) = (k2_tarski @ sk_B @ sk_B)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['10', '11'])).
% 0.59/0.79  thf(d3_tarski, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( r1_tarski @ A @ B ) <=>
% 0.59/0.79       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.59/0.79  thf('13', plain,
% 0.59/0.79      (![X1 : $i, X3 : $i]:
% 0.59/0.79         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.59/0.79      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.79  thf('14', plain,
% 0.59/0.79      (![X40 : $i]: (~ (r2_hidden @ X40 @ sk_A) | ((X40) = (sk_B)))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('15', plain,
% 0.59/0.79      (![X0 : $i]: ((r1_tarski @ sk_A @ X0) | ((sk_C @ X0 @ sk_A) = (sk_B)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['13', '14'])).
% 0.59/0.79  thf('16', plain,
% 0.59/0.79      (![X1 : $i, X3 : $i]:
% 0.59/0.79         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.59/0.79      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.79  thf('17', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         ((r2_hidden @ sk_B @ sk_A)
% 0.59/0.79          | (r1_tarski @ sk_A @ X0)
% 0.59/0.79          | (r1_tarski @ sk_A @ X0))),
% 0.59/0.79      inference('sup+', [status(thm)], ['15', '16'])).
% 0.59/0.79  thf('18', plain,
% 0.59/0.79      (![X0 : $i]: ((r1_tarski @ sk_A @ X0) | (r2_hidden @ sk_B @ sk_A))),
% 0.59/0.79      inference('simplify', [status(thm)], ['17'])).
% 0.59/0.79  thf(t38_xboole_1, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.59/0.79       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.59/0.79  thf('19', plain,
% 0.59/0.79      (![X4 : $i, X5 : $i]:
% 0.59/0.79         (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ (k4_xboole_0 @ X5 @ X4)))),
% 0.59/0.79      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.59/0.79  thf('20', plain, (((r2_hidden @ sk_B @ sk_A) | ((sk_A) = (k1_xboole_0)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['18', '19'])).
% 0.59/0.79  thf('21', plain, (((sk_A) != (k1_xboole_0))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('22', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.59/0.79      inference('simplify_reflect-', [status(thm)], ['20', '21'])).
% 0.59/0.79  thf('23', plain, (((sk_D @ sk_A @ sk_B @ sk_B) = (sk_B))),
% 0.59/0.79      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.59/0.79  thf('24', plain,
% 0.59/0.79      (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.59/0.79      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.59/0.79  thf('25', plain, ((((sk_B) != (sk_B)) | ((sk_A) = (k1_tarski @ sk_B)))),
% 0.59/0.79      inference('demod', [status(thm)], ['12', '22', '23', '24'])).
% 0.59/0.79  thf('26', plain, (((sk_A) = (k1_tarski @ sk_B))),
% 0.59/0.79      inference('simplify', [status(thm)], ['25'])).
% 0.59/0.79  thf('27', plain, (((sk_A) != (k1_tarski @ sk_B))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('28', plain, ($false),
% 0.59/0.79      inference('simplify_reflect-', [status(thm)], ['26', '27'])).
% 0.59/0.79  
% 0.59/0.79  % SZS output end Refutation
% 0.59/0.79  
% 0.59/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

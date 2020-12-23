%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.s8Eo3Pxpd0

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:47 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :   38 (  51 expanded)
%              Number of leaves         :   12 (  20 expanded)
%              Depth                    :   10
%              Number of atoms          :  263 ( 389 expanded)
%              Number of equality atoms :    7 (  10 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t86_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_xboole_0 @ A @ C ) )
       => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t86_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('2',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ( r2_hidden @ X4 @ X7 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('7',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) @ X0 )
      | ( r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
      | ( r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('17',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_C_1 )
      | ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','18'])).

thf('20',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_C_1 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) )
    | ( r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['11','21'])).

thf('23',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    $false ),
    inference(demod,[status(thm)],['0','23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.s8Eo3Pxpd0
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:58:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.53/0.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.53/0.77  % Solved by: fo/fo7.sh
% 0.53/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.77  % done 332 iterations in 0.265s
% 0.53/0.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.53/0.77  % SZS output start Refutation
% 0.53/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.77  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.53/0.77  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.53/0.77  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.53/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.77  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.53/0.77  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.53/0.77  thf(t86_xboole_1, conjecture,
% 0.53/0.77    (![A:$i,B:$i,C:$i]:
% 0.53/0.77     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.53/0.77       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.53/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.77    (~( ![A:$i,B:$i,C:$i]:
% 0.53/0.77        ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.53/0.77          ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )),
% 0.53/0.77    inference('cnf.neg', [status(esa)], [t86_xboole_1])).
% 0.53/0.77  thf('0', plain, (~ (r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1))),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf(d3_tarski, axiom,
% 0.53/0.77    (![A:$i,B:$i]:
% 0.53/0.77     ( ( r1_tarski @ A @ B ) <=>
% 0.53/0.77       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.53/0.77  thf('1', plain,
% 0.53/0.77      (![X1 : $i, X3 : $i]:
% 0.53/0.77         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.53/0.77      inference('cnf', [status(esa)], [d3_tarski])).
% 0.53/0.77  thf('2', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('3', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.77         (~ (r2_hidden @ X0 @ X1)
% 0.53/0.77          | (r2_hidden @ X0 @ X2)
% 0.53/0.77          | ~ (r1_tarski @ X1 @ X2))),
% 0.53/0.77      inference('cnf', [status(esa)], [d3_tarski])).
% 0.53/0.77  thf('4', plain,
% 0.53/0.77      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.53/0.77      inference('sup-', [status(thm)], ['2', '3'])).
% 0.53/0.77  thf('5', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         ((r1_tarski @ sk_A @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B))),
% 0.53/0.77      inference('sup-', [status(thm)], ['1', '4'])).
% 0.53/0.77  thf(d5_xboole_0, axiom,
% 0.53/0.77    (![A:$i,B:$i,C:$i]:
% 0.53/0.77     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.53/0.77       ( ![D:$i]:
% 0.53/0.77         ( ( r2_hidden @ D @ C ) <=>
% 0.53/0.77           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.53/0.77  thf('6', plain,
% 0.53/0.77      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.53/0.77         (~ (r2_hidden @ X4 @ X5)
% 0.53/0.77          | (r2_hidden @ X4 @ X6)
% 0.53/0.77          | (r2_hidden @ X4 @ X7)
% 0.53/0.77          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.53/0.77      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.53/0.77  thf('7', plain,
% 0.53/0.77      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.53/0.77         ((r2_hidden @ X4 @ (k4_xboole_0 @ X5 @ X6))
% 0.53/0.77          | (r2_hidden @ X4 @ X6)
% 0.53/0.77          | ~ (r2_hidden @ X4 @ X5))),
% 0.53/0.77      inference('simplify', [status(thm)], ['6'])).
% 0.53/0.77  thf('8', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]:
% 0.53/0.77         ((r1_tarski @ sk_A @ X0)
% 0.53/0.77          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ X1)
% 0.53/0.77          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ (k4_xboole_0 @ sk_B @ X1)))),
% 0.53/0.77      inference('sup-', [status(thm)], ['5', '7'])).
% 0.53/0.77  thf('9', plain,
% 0.53/0.77      (![X1 : $i, X3 : $i]:
% 0.53/0.77         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.53/0.77      inference('cnf', [status(esa)], [d3_tarski])).
% 0.53/0.77  thf('10', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         ((r2_hidden @ (sk_C @ (k4_xboole_0 @ sk_B @ X0) @ sk_A) @ X0)
% 0.53/0.77          | (r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 0.53/0.77          | (r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ X0)))),
% 0.53/0.77      inference('sup-', [status(thm)], ['8', '9'])).
% 0.53/0.77  thf('11', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 0.53/0.77          | (r2_hidden @ (sk_C @ (k4_xboole_0 @ sk_B @ X0) @ sk_A) @ X0))),
% 0.53/0.77      inference('simplify', [status(thm)], ['10'])).
% 0.53/0.77  thf('12', plain, ((r1_xboole_0 @ sk_A @ sk_C_1)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf(t83_xboole_1, axiom,
% 0.53/0.77    (![A:$i,B:$i]:
% 0.53/0.77     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.53/0.77  thf('13', plain,
% 0.53/0.77      (![X10 : $i, X11 : $i]:
% 0.53/0.77         (((k4_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_xboole_0 @ X10 @ X11))),
% 0.53/0.77      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.53/0.77  thf('14', plain, (((k4_xboole_0 @ sk_A @ sk_C_1) = (sk_A))),
% 0.53/0.77      inference('sup-', [status(thm)], ['12', '13'])).
% 0.53/0.77  thf('15', plain,
% 0.53/0.77      (![X1 : $i, X3 : $i]:
% 0.53/0.77         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.53/0.77      inference('cnf', [status(esa)], [d3_tarski])).
% 0.53/0.77  thf('16', plain,
% 0.53/0.77      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.53/0.77         (~ (r2_hidden @ X8 @ X7)
% 0.53/0.77          | ~ (r2_hidden @ X8 @ X6)
% 0.53/0.77          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.53/0.77      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.53/0.77  thf('17', plain,
% 0.53/0.77      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.53/0.77         (~ (r2_hidden @ X8 @ X6)
% 0.53/0.77          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.53/0.77      inference('simplify', [status(thm)], ['16'])).
% 0.53/0.77  thf('18', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.77         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.53/0.77          | ~ (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.53/0.77      inference('sup-', [status(thm)], ['15', '17'])).
% 0.53/0.77  thf('19', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         (~ (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_C_1)
% 0.53/0.77          | (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C_1) @ X0))),
% 0.53/0.77      inference('sup-', [status(thm)], ['14', '18'])).
% 0.53/0.77  thf('20', plain, (((k4_xboole_0 @ sk_A @ sk_C_1) = (sk_A))),
% 0.53/0.77      inference('sup-', [status(thm)], ['12', '13'])).
% 0.53/0.77  thf('21', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         (~ (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_C_1) | (r1_tarski @ sk_A @ X0))),
% 0.53/0.77      inference('demod', [status(thm)], ['19', '20'])).
% 0.53/0.77  thf('22', plain,
% 0.53/0.77      (((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1))
% 0.53/0.77        | (r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1)))),
% 0.53/0.77      inference('sup-', [status(thm)], ['11', '21'])).
% 0.53/0.77  thf('23', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1))),
% 0.53/0.77      inference('simplify', [status(thm)], ['22'])).
% 0.53/0.77  thf('24', plain, ($false), inference('demod', [status(thm)], ['0', '23'])).
% 0.53/0.77  
% 0.53/0.77  % SZS output end Refutation
% 0.53/0.77  
% 0.63/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

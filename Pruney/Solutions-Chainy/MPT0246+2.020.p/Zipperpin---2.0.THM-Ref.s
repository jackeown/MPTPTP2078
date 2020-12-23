%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uKDL8S5nEn

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   41 (  70 expanded)
%              Number of leaves         :   12 (  24 expanded)
%              Depth                    :   13
%              Number of atoms          :  297 ( 659 expanded)
%              Number of equality atoms :   55 ( 130 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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
    ! [X1: $i,X4: $i,X6: $i] :
      ( ( X6
        = ( k2_tarski @ X4 @ X1 ) )
      | ( ( sk_D @ X6 @ X1 @ X4 )
        = X1 )
      | ( ( sk_D @ X6 @ X1 @ X4 )
        = X4 )
      | ( r2_hidden @ ( sk_D @ X6 @ X1 @ X4 ) @ X6 ) ) ),
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
    ! [X35: $i] :
      ( ~ ( r2_hidden @ X35 @ sk_A )
      | ( X35 = sk_B_1 ) ) ),
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
        = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_B_1 )
      | ( ( sk_D @ sk_A @ X1 @ X0 )
        = sk_B_1 )
      | ( sk_A
        = ( k2_tarski @ X0 @ X1 ) )
      | ( ( sk_D @ sk_A @ X1 @ X0 )
        = X1 ) ) ),
    inference(eq_fact,[status(thm)],['2'])).

thf('4',plain,(
    ! [X1: $i] :
      ( ( ( sk_D @ sk_A @ X1 @ sk_B_1 )
        = X1 )
      | ( sk_A
        = ( k2_tarski @ sk_B_1 @ X1 ) )
      | ( ( sk_D @ sk_A @ X1 @ sk_B_1 )
        = sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 != X0 )
      | ( sk_A
        = ( k2_tarski @ sk_B_1 @ X0 ) )
      | ( ( sk_D @ sk_A @ X0 @ sk_B_1 )
        = X0 ) ) ),
    inference(eq_fact,[status(thm)],['4'])).

thf('6',plain,
    ( ( ( sk_D @ sk_A @ sk_B_1 @ sk_B_1 )
      = sk_B_1 )
    | ( sk_A
      = ( k2_tarski @ sk_B_1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('7',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('8',plain,
    ( ( ( sk_D @ sk_A @ sk_B_1 @ sk_B_1 )
      = sk_B_1 )
    | ( sk_A
      = ( k1_tarski @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    sk_A
 != ( k1_tarski @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( sk_D @ sk_A @ sk_B_1 @ sk_B_1 )
    = sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X1: $i,X4: $i,X6: $i] :
      ( ( X6
        = ( k2_tarski @ X4 @ X1 ) )
      | ( ( sk_D @ X6 @ X1 @ X4 )
       != X1 )
      | ~ ( r2_hidden @ ( sk_D @ X6 @ X1 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('12',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( sk_D @ sk_A @ sk_B_1 @ sk_B_1 )
     != sk_B_1 )
    | ( sk_A
      = ( k2_tarski @ sk_B_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('14',plain,(
    ! [X35: $i] :
      ( ~ ( r2_hidden @ X35 @ sk_A )
      | ( X35 = sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( sk_B @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( sk_B @ sk_A )
    = sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('19',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    r2_hidden @ sk_B_1 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_D @ sk_A @ sk_B_1 @ sk_B_1 )
    = sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('23',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('24',plain,
    ( ( sk_B_1 != sk_B_1 )
    | ( sk_A
      = ( k1_tarski @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['12','21','22','23'])).

thf('25',plain,
    ( sk_A
    = ( k1_tarski @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    sk_A
 != ( k1_tarski @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uKDL8S5nEn
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:32:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 40 iterations in 0.031s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.48  thf(d2_tarski, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.21/0.48       ( ![D:$i]:
% 0.21/0.48         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      (![X1 : $i, X4 : $i, X6 : $i]:
% 0.21/0.48         (((X6) = (k2_tarski @ X4 @ X1))
% 0.21/0.48          | ((sk_D @ X6 @ X1 @ X4) = (X1))
% 0.21/0.48          | ((sk_D @ X6 @ X1 @ X4) = (X4))
% 0.21/0.48          | (r2_hidden @ (sk_D @ X6 @ X1 @ X4) @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [d2_tarski])).
% 0.21/0.48  thf(t41_zfmisc_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.48          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i]:
% 0.21/0.48        ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.48             ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t41_zfmisc_1])).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X35 : $i]: (~ (r2_hidden @ X35 @ sk_A) | ((X35) = (sk_B_1)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (((sk_D @ sk_A @ X1 @ X0) = (X0))
% 0.21/0.48          | ((sk_D @ sk_A @ X1 @ X0) = (X1))
% 0.21/0.48          | ((sk_A) = (k2_tarski @ X0 @ X1))
% 0.21/0.48          | ((sk_D @ sk_A @ X1 @ X0) = (sk_B_1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (((X0) != (sk_B_1))
% 0.21/0.49          | ((sk_D @ sk_A @ X1 @ X0) = (sk_B_1))
% 0.21/0.49          | ((sk_A) = (k2_tarski @ X0 @ X1))
% 0.21/0.49          | ((sk_D @ sk_A @ X1 @ X0) = (X1)))),
% 0.21/0.49      inference('eq_fact', [status(thm)], ['2'])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X1 : $i]:
% 0.21/0.49         (((sk_D @ sk_A @ X1 @ sk_B_1) = (X1))
% 0.21/0.49          | ((sk_A) = (k2_tarski @ sk_B_1 @ X1))
% 0.21/0.49          | ((sk_D @ sk_A @ X1 @ sk_B_1) = (sk_B_1)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((sk_B_1) != (X0))
% 0.21/0.49          | ((sk_A) = (k2_tarski @ sk_B_1 @ X0))
% 0.21/0.49          | ((sk_D @ sk_A @ X0 @ sk_B_1) = (X0)))),
% 0.21/0.49      inference('eq_fact', [status(thm)], ['4'])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      ((((sk_D @ sk_A @ sk_B_1 @ sk_B_1) = (sk_B_1))
% 0.21/0.49        | ((sk_A) = (k2_tarski @ sk_B_1 @ sk_B_1)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.49  thf(t69_enumset1, axiom,
% 0.21/0.49    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.49  thf('7', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      ((((sk_D @ sk_A @ sk_B_1 @ sk_B_1) = (sk_B_1))
% 0.21/0.49        | ((sk_A) = (k1_tarski @ sk_B_1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.49  thf('9', plain, (((sk_A) != (k1_tarski @ sk_B_1))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('10', plain, (((sk_D @ sk_A @ sk_B_1 @ sk_B_1) = (sk_B_1))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X1 : $i, X4 : $i, X6 : $i]:
% 0.21/0.49         (((X6) = (k2_tarski @ X4 @ X1))
% 0.21/0.49          | ((sk_D @ X6 @ X1 @ X4) != (X1))
% 0.21/0.49          | ~ (r2_hidden @ (sk_D @ X6 @ X1 @ X4) @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [d2_tarski])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      ((~ (r2_hidden @ sk_B_1 @ sk_A)
% 0.21/0.49        | ((sk_D @ sk_A @ sk_B_1 @ sk_B_1) != (sk_B_1))
% 0.21/0.49        | ((sk_A) = (k2_tarski @ sk_B_1 @ sk_B_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.49  thf(t7_xboole_0, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X35 : $i]: (~ (r2_hidden @ X35 @ sk_A) | ((X35) = (sk_B_1)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('15', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B @ sk_A) = (sk_B_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.49  thf('16', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('17', plain, (((sk_B @ sk_A) = (sk_B_1))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['15', '16'])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.49  thf('19', plain, (((r2_hidden @ sk_B_1 @ sk_A) | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['17', '18'])).
% 0.21/0.49  thf('20', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('21', plain, ((r2_hidden @ sk_B_1 @ sk_A)),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.21/0.49  thf('22', plain, (((sk_D @ sk_A @ sk_B_1 @ sk_B_1) = (sk_B_1))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.21/0.49  thf('23', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      ((((sk_B_1) != (sk_B_1)) | ((sk_A) = (k1_tarski @ sk_B_1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['12', '21', '22', '23'])).
% 0.21/0.49  thf('25', plain, (((sk_A) = (k1_tarski @ sk_B_1))),
% 0.21/0.49      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.49  thf('26', plain, (((sk_A) != (k1_tarski @ sk_B_1))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('27', plain, ($false),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

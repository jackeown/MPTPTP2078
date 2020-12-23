%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.geE5wrUITh

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   29 (  33 expanded)
%              Number of leaves         :   10 (  13 expanded)
%              Depth                    :    7
%              Number of atoms          :  172 ( 216 expanded)
%              Number of equality atoms :   19 (  26 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t21_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = k1_xboole_0 )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = k1_xboole_0 )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t21_zfmisc_1])).

thf('0',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( X10 != X9 )
      | ( r2_hidden @ X10 @ X11 )
      | ( X11
       != ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('2',plain,(
    ! [X9: $i] :
      ( r2_hidden @ X9 @ ( k1_tarski @ X9 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,
    ( ( r2_hidden @ sk_A @ k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['0','5'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('7',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

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

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['10'])).

thf('12',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['6','11'])).

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
    sk_A = sk_B ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['15','16'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.geE5wrUITh
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:38:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 50 iterations in 0.029s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(t21_zfmisc_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.49         ( k1_xboole_0 ) ) =>
% 0.21/0.49       ( ( A ) = ( B ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i]:
% 0.21/0.49        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.49            ( k1_xboole_0 ) ) =>
% 0.21/0.49          ( ( A ) = ( B ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t21_zfmisc_1])).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(d1_tarski, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.49         (((X10) != (X9))
% 0.21/0.49          | (r2_hidden @ X10 @ X11)
% 0.21/0.49          | ((X11) != (k1_tarski @ X9)))),
% 0.21/0.49      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.49  thf('2', plain, (![X9 : $i]: (r2_hidden @ X9 @ (k1_tarski @ X9))),
% 0.21/0.49      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.49  thf(d5_xboole_0, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.21/0.49       ( ![D:$i]:
% 0.21/0.49         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.49           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.49          | (r2_hidden @ X0 @ X2)
% 0.21/0.49          | (r2_hidden @ X0 @ X3)
% 0.21/0.49          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.21/0.49      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.21/0.49          | (r2_hidden @ X0 @ X2)
% 0.21/0.49          | ~ (r2_hidden @ X0 @ X1))),
% 0.21/0.49      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((r2_hidden @ X0 @ X1)
% 0.21/0.49          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['2', '4'])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (((r2_hidden @ sk_A @ k1_xboole_0)
% 0.21/0.49        | (r2_hidden @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['0', '5'])).
% 0.21/0.49  thf(t4_boole, axiom,
% 0.21/0.49    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X8 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X8) = (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t4_boole])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X4 @ X3)
% 0.21/0.49          | ~ (r2_hidden @ X4 @ X2)
% 0.21/0.49          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.21/0.49      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X4 @ X2)
% 0.21/0.49          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['7', '9'])).
% 0.21/0.49  thf('11', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.49      inference('condensation', [status(thm)], ['10'])).
% 0.21/0.49  thf('12', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.21/0.49      inference('clc', [status(thm)], ['6', '11'])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X12 @ X11)
% 0.21/0.49          | ((X12) = (X9))
% 0.21/0.49          | ((X11) != (k1_tarski @ X9)))),
% 0.21/0.49      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X9 : $i, X12 : $i]:
% 0.21/0.49         (((X12) = (X9)) | ~ (r2_hidden @ X12 @ (k1_tarski @ X9)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.49  thf('15', plain, (((sk_A) = (sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['12', '14'])).
% 0.21/0.49  thf('16', plain, (((sk_A) != (sk_B))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('17', plain, ($false),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['15', '16'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

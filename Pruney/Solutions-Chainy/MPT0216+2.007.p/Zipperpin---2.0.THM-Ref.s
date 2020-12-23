%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GKQ1hbKtS9

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   29 (  41 expanded)
%              Number of leaves         :    9 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :  159 ( 284 expanded)
%              Number of equality atoms :   27 (  53 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t9_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k1_tarski @ A )
        = ( k2_tarski @ B @ C ) )
     => ( B = C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k1_tarski @ A )
          = ( k2_tarski @ B @ C ) )
       => ( B = C ) ) ),
    inference('cnf.neg',[status(esa)],[t9_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('2',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    r2_hidden @ sk_C @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf('4',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X3 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('6',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X3 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('8',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('9',plain,(
    ! [X0: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( X4 = X3 )
      | ( X4 = X0 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('10',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    r2_hidden @ sk_C @ ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['3','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('16',plain,(
    sk_C = sk_B ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    sk_B != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GKQ1hbKtS9
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:39:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.44  % Solved by: fo/fo7.sh
% 0.20/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.44  % done 22 iterations in 0.014s
% 0.20/0.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.44  % SZS output start Refutation
% 0.20/0.44  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.44  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.44  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.44  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.44  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.44  thf(t9_zfmisc_1, conjecture,
% 0.20/0.44    (![A:$i,B:$i,C:$i]:
% 0.20/0.44     ( ( ( k1_tarski @ A ) = ( k2_tarski @ B @ C ) ) => ( ( B ) = ( C ) ) ))).
% 0.20/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.44    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.44        ( ( ( k1_tarski @ A ) = ( k2_tarski @ B @ C ) ) => ( ( B ) = ( C ) ) ) )),
% 0.20/0.44    inference('cnf.neg', [status(esa)], [t9_zfmisc_1])).
% 0.20/0.44  thf('0', plain, (((k1_tarski @ sk_A) = (k2_tarski @ sk_B @ sk_C))),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf(d2_tarski, axiom,
% 0.20/0.44    (![A:$i,B:$i,C:$i]:
% 0.20/0.44     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.20/0.44       ( ![D:$i]:
% 0.20/0.44         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.20/0.44  thf('1', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.44         (((X1) != (X0))
% 0.20/0.44          | (r2_hidden @ X1 @ X2)
% 0.20/0.44          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.20/0.44      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.44  thf('2', plain,
% 0.20/0.44      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.20/0.44      inference('simplify', [status(thm)], ['1'])).
% 0.20/0.44  thf('3', plain, ((r2_hidden @ sk_C @ (k1_tarski @ sk_A))),
% 0.20/0.44      inference('sup+', [status(thm)], ['0', '2'])).
% 0.20/0.44  thf('4', plain, (((k1_tarski @ sk_A) = (k2_tarski @ sk_B @ sk_C))),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('5', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.44         (((X1) != (X3))
% 0.20/0.44          | (r2_hidden @ X1 @ X2)
% 0.20/0.44          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.20/0.44      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.44  thf('6', plain,
% 0.20/0.44      (![X0 : $i, X3 : $i]: (r2_hidden @ X3 @ (k2_tarski @ X3 @ X0))),
% 0.20/0.44      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.44  thf('7', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 0.20/0.44      inference('sup+', [status(thm)], ['4', '6'])).
% 0.20/0.44  thf(t69_enumset1, axiom,
% 0.20/0.44    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.44  thf('8', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.20/0.44      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.44  thf('9', plain,
% 0.20/0.44      (![X0 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.44         (~ (r2_hidden @ X4 @ X2)
% 0.20/0.44          | ((X4) = (X3))
% 0.20/0.44          | ((X4) = (X0))
% 0.20/0.44          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.20/0.44      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.44  thf('10', plain,
% 0.20/0.44      (![X0 : $i, X3 : $i, X4 : $i]:
% 0.20/0.44         (((X4) = (X0))
% 0.20/0.44          | ((X4) = (X3))
% 0.20/0.44          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 0.20/0.44      inference('simplify', [status(thm)], ['9'])).
% 0.20/0.44  thf('11', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i]:
% 0.20/0.44         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.20/0.44      inference('sup-', [status(thm)], ['8', '10'])).
% 0.20/0.44  thf('12', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i]:
% 0.20/0.44         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.20/0.44      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.44  thf('13', plain, (((sk_B) = (sk_A))),
% 0.20/0.44      inference('sup-', [status(thm)], ['7', '12'])).
% 0.20/0.44  thf('14', plain, ((r2_hidden @ sk_C @ (k1_tarski @ sk_B))),
% 0.20/0.44      inference('demod', [status(thm)], ['3', '13'])).
% 0.20/0.44  thf('15', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i]:
% 0.20/0.44         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.20/0.44      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.44  thf('16', plain, (((sk_C) = (sk_B))),
% 0.20/0.44      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.44  thf('17', plain, (((sk_B) != (sk_C))),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('18', plain, ($false),
% 0.20/0.44      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 0.20/0.44  
% 0.20/0.44  % SZS output end Refutation
% 0.20/0.44  
% 0.20/0.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

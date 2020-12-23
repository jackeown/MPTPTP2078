%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Yk7Ps1pePE

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   20 (  23 expanded)
%              Number of leaves         :    8 (  10 expanded)
%              Depth                    :    6
%              Number of atoms          :   99 ( 125 expanded)
%              Number of equality atoms :   11 (  15 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( X5 != X4 )
      | ( r2_hidden @ X5 @ X6 )
      | ( X6
       != ( k1_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('1',plain,(
    ! [X4: $i] :
      ( r2_hidden @ X4 @ ( k1_tarski @ X4 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t6_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t6_zfmisc_1])).

thf('2',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( X7 = X4 )
      | ( X6
       != ( k1_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('7',plain,(
    ! [X4: $i,X7: $i] :
      ( ( X7 = X4 )
      | ~ ( r2_hidden @ X7 @ ( k1_tarski @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    sk_A = sk_B ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Yk7Ps1pePE
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:50:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.44  % Solved by: fo/fo7.sh
% 0.21/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.44  % done 20 iterations in 0.016s
% 0.21/0.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.44  % SZS output start Refutation
% 0.21/0.44  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.44  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.44  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.44  thf(d1_tarski, axiom,
% 0.21/0.44    (![A:$i,B:$i]:
% 0.21/0.44     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.44       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.44  thf('0', plain,
% 0.21/0.44      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.44         (((X5) != (X4)) | (r2_hidden @ X5 @ X6) | ((X6) != (k1_tarski @ X4)))),
% 0.21/0.44      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.44  thf('1', plain, (![X4 : $i]: (r2_hidden @ X4 @ (k1_tarski @ X4))),
% 0.21/0.44      inference('simplify', [status(thm)], ['0'])).
% 0.21/0.44  thf(t6_zfmisc_1, conjecture,
% 0.21/0.44    (![A:$i,B:$i]:
% 0.21/0.44     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.21/0.44       ( ( A ) = ( B ) ) ))).
% 0.21/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.44    (~( ![A:$i,B:$i]:
% 0.21/0.44        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.21/0.44          ( ( A ) = ( B ) ) ) )),
% 0.21/0.44    inference('cnf.neg', [status(esa)], [t6_zfmisc_1])).
% 0.21/0.44  thf('2', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf(d3_tarski, axiom,
% 0.21/0.44    (![A:$i,B:$i]:
% 0.21/0.44     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.44       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.44  thf('3', plain,
% 0.21/0.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.44         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.44          | (r2_hidden @ X0 @ X2)
% 0.21/0.44          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.44      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.44  thf('4', plain,
% 0.21/0.44      (![X0 : $i]:
% 0.21/0.44         ((r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.21/0.44          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.21/0.44      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.44  thf('5', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.21/0.44      inference('sup-', [status(thm)], ['1', '4'])).
% 0.21/0.44  thf('6', plain,
% 0.21/0.44      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.21/0.44         (~ (r2_hidden @ X7 @ X6) | ((X7) = (X4)) | ((X6) != (k1_tarski @ X4)))),
% 0.21/0.44      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.44  thf('7', plain,
% 0.21/0.44      (![X4 : $i, X7 : $i]:
% 0.21/0.44         (((X7) = (X4)) | ~ (r2_hidden @ X7 @ (k1_tarski @ X4)))),
% 0.21/0.44      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.44  thf('8', plain, (((sk_A) = (sk_B))),
% 0.21/0.44      inference('sup-', [status(thm)], ['5', '7'])).
% 0.21/0.44  thf('9', plain, (((sk_A) != (sk_B))),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf('10', plain, ($false),
% 0.21/0.44      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.21/0.44  
% 0.21/0.44  % SZS output end Refutation
% 0.21/0.44  
% 0.21/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

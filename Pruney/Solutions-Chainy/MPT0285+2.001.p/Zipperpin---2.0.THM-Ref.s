%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.C3iM24pFCp

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:50 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   21 (  24 expanded)
%              Number of leaves         :    9 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :  116 ( 139 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t92_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t92_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ ( k3_tarski @ sk_B ) ) ),
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

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( r2_hidden @ X6 @ X7 )
      | ( X7
       != ( k3_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('4',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ ( k3_tarski @ X5 ) )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_tarski @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k3_tarski @ sk_B ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('7',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,
    ( ( r1_tarski @ sk_A @ ( k3_tarski @ sk_B ) )
    | ( r1_tarski @ sk_A @ ( k3_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ sk_A @ ( k3_tarski @ sk_B ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    $false ),
    inference(demod,[status(thm)],['0','9'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.C3iM24pFCp
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:46:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.46  % Solved by: fo/fo7.sh
% 0.22/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.46  % done 19 iterations in 0.013s
% 0.22/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.46  % SZS output start Refutation
% 0.22/0.46  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.46  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.22/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.46  thf(t92_zfmisc_1, conjecture,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.22/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.46    (~( ![A:$i,B:$i]:
% 0.22/0.46        ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )),
% 0.22/0.46    inference('cnf.neg', [status(esa)], [t92_zfmisc_1])).
% 0.22/0.46  thf('0', plain, (~ (r1_tarski @ sk_A @ (k3_tarski @ sk_B))),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('1', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf(d3_tarski, axiom,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.46       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.46  thf('2', plain,
% 0.22/0.46      (![X1 : $i, X3 : $i]:
% 0.22/0.46         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.22/0.46      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.46  thf(d4_tarski, axiom,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 0.22/0.46       ( ![C:$i]:
% 0.22/0.46         ( ( r2_hidden @ C @ B ) <=>
% 0.22/0.46           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 0.22/0.46  thf('3', plain,
% 0.22/0.46      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.46         (~ (r2_hidden @ X4 @ X5)
% 0.22/0.46          | ~ (r2_hidden @ X6 @ X4)
% 0.22/0.46          | (r2_hidden @ X6 @ X7)
% 0.22/0.46          | ((X7) != (k3_tarski @ X5)))),
% 0.22/0.46      inference('cnf', [status(esa)], [d4_tarski])).
% 0.22/0.46  thf('4', plain,
% 0.22/0.46      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.46         ((r2_hidden @ X6 @ (k3_tarski @ X5))
% 0.22/0.46          | ~ (r2_hidden @ X6 @ X4)
% 0.22/0.46          | ~ (r2_hidden @ X4 @ X5))),
% 0.22/0.46      inference('simplify', [status(thm)], ['3'])).
% 0.22/0.46  thf('5', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.46         ((r1_tarski @ X0 @ X1)
% 0.22/0.46          | ~ (r2_hidden @ X0 @ X2)
% 0.22/0.46          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_tarski @ X2)))),
% 0.22/0.46      inference('sup-', [status(thm)], ['2', '4'])).
% 0.22/0.46  thf('6', plain,
% 0.22/0.46      (![X0 : $i]:
% 0.22/0.46         ((r2_hidden @ (sk_C @ X0 @ sk_A) @ (k3_tarski @ sk_B))
% 0.22/0.46          | (r1_tarski @ sk_A @ X0))),
% 0.22/0.46      inference('sup-', [status(thm)], ['1', '5'])).
% 0.22/0.46  thf('7', plain,
% 0.22/0.46      (![X1 : $i, X3 : $i]:
% 0.22/0.46         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.22/0.46      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.46  thf('8', plain,
% 0.22/0.46      (((r1_tarski @ sk_A @ (k3_tarski @ sk_B))
% 0.22/0.46        | (r1_tarski @ sk_A @ (k3_tarski @ sk_B)))),
% 0.22/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.46  thf('9', plain, ((r1_tarski @ sk_A @ (k3_tarski @ sk_B))),
% 0.22/0.46      inference('simplify', [status(thm)], ['8'])).
% 0.22/0.46  thf('10', plain, ($false), inference('demod', [status(thm)], ['0', '9'])).
% 0.22/0.46  
% 0.22/0.46  % SZS output end Refutation
% 0.22/0.46  
% 0.22/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

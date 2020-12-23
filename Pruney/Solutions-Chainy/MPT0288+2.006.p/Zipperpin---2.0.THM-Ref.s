%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DDK0gfUKIQ

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   33 (  40 expanded)
%              Number of leaves         :   10 (  16 expanded)
%              Depth                    :    9
%              Number of atoms          :  250 ( 319 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t95_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t95_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ sk_B ) ) ),
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

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ ( sk_D_1 @ X8 @ X5 ) @ X5 )
      | ( X7
       != ( k3_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('3',plain,(
    ! [X5: $i,X8: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X8 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k3_tarski @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X1 @ ( k3_tarski @ X0 ) ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X0 @ ( k3_tarski @ sk_A ) ) @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ ( sk_D_1 @ X8 @ X5 ) )
      | ( X7
       != ( k3_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('11',plain,(
    ! [X5: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ ( sk_D_1 @ X8 @ X5 ) )
      | ~ ( r2_hidden @ X8 @ ( k3_tarski @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k3_tarski @ X0 ) ) @ ( sk_D_1 @ ( sk_C @ X1 @ ( k3_tarski @ X0 ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( r2_hidden @ X6 @ X7 )
      | ( X7
       != ( k3_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('14',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ ( k3_tarski @ X5 ) )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X1 @ ( k3_tarski @ X0 ) ) @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k3_tarski @ X0 ) ) @ ( k3_tarski @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k3_tarski @ sk_A ) ) @ ( k3_tarski @ sk_B ) )
      | ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k3_tarski @ sk_A ) ) @ ( k3_tarski @ sk_B ) )
      | ( r1_tarski @ ( k3_tarski @ sk_A ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,
    ( ( r1_tarski @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ sk_B ) )
    | ( r1_tarski @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ sk_B ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    $false ),
    inference(demod,[status(thm)],['0','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DDK0gfUKIQ
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:31:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 40 iterations in 0.052s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.21/0.51  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(t95_zfmisc_1, conjecture,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( r1_tarski @ A @ B ) =>
% 0.21/0.51       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i]:
% 0.21/0.51        ( ( r1_tarski @ A @ B ) =>
% 0.21/0.51          ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t95_zfmisc_1])).
% 0.21/0.51  thf('0', plain, (~ (r1_tarski @ (k3_tarski @ sk_A) @ (k3_tarski @ sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(d3_tarski, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (![X1 : $i, X3 : $i]:
% 0.21/0.51         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.51  thf(d4_tarski, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 0.21/0.51       ( ![C:$i]:
% 0.21/0.51         ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.51           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X8 @ X7)
% 0.21/0.51          | (r2_hidden @ (sk_D_1 @ X8 @ X5) @ X5)
% 0.21/0.51          | ((X7) != (k3_tarski @ X5)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d4_tarski])).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X5 : $i, X8 : $i]:
% 0.21/0.51         ((r2_hidden @ (sk_D_1 @ X8 @ X5) @ X5)
% 0.21/0.51          | ~ (r2_hidden @ X8 @ (k3_tarski @ X5)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((r1_tarski @ (k3_tarski @ X0) @ X1)
% 0.21/0.51          | (r2_hidden @ (sk_D_1 @ (sk_C @ X1 @ (k3_tarski @ X0)) @ X0) @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['1', '3'])).
% 0.21/0.51  thf('5', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.51          | (r2_hidden @ X0 @ X2)
% 0.21/0.51          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r1_tarski @ (k3_tarski @ sk_A) @ X0)
% 0.21/0.51          | (r2_hidden @ (sk_D_1 @ (sk_C @ X0 @ (k3_tarski @ sk_A)) @ sk_A) @ 
% 0.21/0.51             sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['4', '7'])).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (![X1 : $i, X3 : $i]:
% 0.21/0.51         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X8 @ X7)
% 0.21/0.51          | (r2_hidden @ X8 @ (sk_D_1 @ X8 @ X5))
% 0.21/0.51          | ((X7) != (k3_tarski @ X5)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d4_tarski])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (![X5 : $i, X8 : $i]:
% 0.21/0.51         ((r2_hidden @ X8 @ (sk_D_1 @ X8 @ X5))
% 0.21/0.51          | ~ (r2_hidden @ X8 @ (k3_tarski @ X5)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((r1_tarski @ (k3_tarski @ X0) @ X1)
% 0.21/0.51          | (r2_hidden @ (sk_C @ X1 @ (k3_tarski @ X0)) @ 
% 0.21/0.51             (sk_D_1 @ (sk_C @ X1 @ (k3_tarski @ X0)) @ X0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['9', '11'])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X4 @ X5)
% 0.21/0.51          | ~ (r2_hidden @ X6 @ X4)
% 0.21/0.51          | (r2_hidden @ X6 @ X7)
% 0.21/0.51          | ((X7) != (k3_tarski @ X5)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d4_tarski])).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.51         ((r2_hidden @ X6 @ (k3_tarski @ X5))
% 0.21/0.51          | ~ (r2_hidden @ X6 @ X4)
% 0.21/0.51          | ~ (r2_hidden @ X4 @ X5))),
% 0.21/0.51      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         ((r1_tarski @ (k3_tarski @ X0) @ X1)
% 0.21/0.51          | ~ (r2_hidden @ (sk_D_1 @ (sk_C @ X1 @ (k3_tarski @ X0)) @ X0) @ X2)
% 0.21/0.51          | (r2_hidden @ (sk_C @ X1 @ (k3_tarski @ X0)) @ (k3_tarski @ X2)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['12', '14'])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r1_tarski @ (k3_tarski @ sk_A) @ X0)
% 0.21/0.51          | (r2_hidden @ (sk_C @ X0 @ (k3_tarski @ sk_A)) @ (k3_tarski @ sk_B))
% 0.21/0.51          | (r1_tarski @ (k3_tarski @ sk_A) @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['8', '15'])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r2_hidden @ (sk_C @ X0 @ (k3_tarski @ sk_A)) @ (k3_tarski @ sk_B))
% 0.21/0.51          | (r1_tarski @ (k3_tarski @ sk_A) @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['16'])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (![X1 : $i, X3 : $i]:
% 0.21/0.51         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (((r1_tarski @ (k3_tarski @ sk_A) @ (k3_tarski @ sk_B))
% 0.21/0.51        | (r1_tarski @ (k3_tarski @ sk_A) @ (k3_tarski @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.51  thf('20', plain, ((r1_tarski @ (k3_tarski @ sk_A) @ (k3_tarski @ sk_B))),
% 0.21/0.51      inference('simplify', [status(thm)], ['19'])).
% 0.21/0.51  thf('21', plain, ($false), inference('demod', [status(thm)], ['0', '20'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

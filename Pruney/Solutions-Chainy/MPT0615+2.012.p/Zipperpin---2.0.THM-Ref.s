%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IGLbMPMk0T

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:18 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 108 expanded)
%              Number of leaves         :   13 (  34 expanded)
%              Depth                    :   17
%              Number of atoms          :  360 (1003 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t219_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
          <=> ( r1_tarski @ A @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( r1_tarski @ A @ B )
            <=> ( r1_tarski @ A @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t219_relat_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) )
    | ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) )
   <= ~ ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) )
    | ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,
    ( ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) )
   <= ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) )
        | ~ ( r2_hidden @ X0 @ sk_A ) )
   <= ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) ) )
   <= ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X7 @ X8 ) @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B )
        | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_A @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) )
   <= ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ( r1_tarski @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
   <= ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('19',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['2','19'])).

thf('21',plain,(
    ~ ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','20'])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('22',plain,(
    ! [X9: $i] :
      ( ( ( k7_relat_1 @ X9 @ ( k1_relat_1 @ X9 ) )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('23',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('24',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('25',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['2','19','24'])).

thf('26',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simpl_trail,[status(thm)],['23','25'])).

thf(t105_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ ( k7_relat_1 @ C @ A ) ) ) ) ) )).

thf('27',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( r1_tarski @ ( k7_relat_1 @ X5 @ X6 ) @ ( k7_relat_1 @ X4 @ X6 ) )
      | ~ ( r1_tarski @ X5 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t105_relat_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ( r1_tarski @ ( k7_relat_1 @ sk_A @ X0 ) @ ( k7_relat_1 @ sk_B @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k7_relat_1 @ sk_A @ X0 ) @ ( k7_relat_1 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,
    ( ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['22','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['21','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IGLbMPMk0T
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:54:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 48 iterations in 0.030s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(t219_relat_1, conjecture,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ A ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( v1_relat_1 @ B ) =>
% 0.20/0.49           ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.49             ( r1_tarski @ A @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]:
% 0.20/0.49        ( ( v1_relat_1 @ A ) =>
% 0.20/0.49          ( ![B:$i]:
% 0.20/0.49            ( ( v1_relat_1 @ B ) =>
% 0.20/0.49              ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.49                ( r1_tarski @ A @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t219_relat_1])).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      ((~ (r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))
% 0.20/0.49        | ~ (r1_tarski @ sk_A @ sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      ((~ (r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A))))
% 0.20/0.49         <= (~ ((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (~ ((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))) | 
% 0.20/0.49       ~ ((r1_tarski @ sk_A @ sk_B))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf(d3_tarski, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X1 : $i, X3 : $i]:
% 0.20/0.49         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))
% 0.20/0.49        | (r1_tarski @ sk_A @ sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A))))
% 0.20/0.49         <= (((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))))),
% 0.20/0.49      inference('split', [status(esa)], ['4'])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.49          | (r2_hidden @ X0 @ X2)
% 0.20/0.49          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      ((![X0 : $i]:
% 0.20/0.49          ((r2_hidden @ X0 @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))
% 0.20/0.49           | ~ (r2_hidden @ X0 @ sk_A)))
% 0.20/0.49         <= (((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      ((![X0 : $i]:
% 0.20/0.49          ((r1_tarski @ sk_A @ X0)
% 0.20/0.49           | (r2_hidden @ (sk_C @ X0 @ sk_A) @ 
% 0.20/0.49              (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))))
% 0.20/0.49         <= (((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['3', '7'])).
% 0.20/0.49  thf(t88_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X7 : $i, X8 : $i]:
% 0.20/0.49         ((r1_tarski @ (k7_relat_1 @ X7 @ X8) @ X7) | ~ (v1_relat_1 @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.49          | (r2_hidden @ X0 @ X2)
% 0.20/0.49          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X0)
% 0.20/0.49          | (r2_hidden @ X2 @ X0)
% 0.20/0.49          | ~ (r2_hidden @ X2 @ (k7_relat_1 @ X0 @ X1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      ((![X0 : $i]:
% 0.20/0.49          ((r1_tarski @ sk_A @ X0)
% 0.20/0.49           | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B)
% 0.20/0.49           | ~ (v1_relat_1 @ sk_B)))
% 0.20/0.49         <= (((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['8', '11'])).
% 0.20/0.49  thf('13', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      ((![X0 : $i]:
% 0.20/0.49          ((r1_tarski @ sk_A @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B)))
% 0.20/0.49         <= (((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))))),
% 0.20/0.49      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X1 : $i, X3 : $i]:
% 0.20/0.49         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      ((((r1_tarski @ sk_A @ sk_B) | (r1_tarski @ sk_A @ sk_B)))
% 0.20/0.49         <= (((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (((r1_tarski @ sk_A @ sk_B))
% 0.20/0.49         <= (((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))))),
% 0.20/0.49      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      ((~ (r1_tarski @ sk_A @ sk_B)) <= (~ ((r1_tarski @ sk_A @ sk_B)))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (((r1_tarski @ sk_A @ sk_B)) | 
% 0.20/0.49       ~ ((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (~ ((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A))))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['2', '19'])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (~ (r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['1', '20'])).
% 0.20/0.49  thf(t98_relat_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ A ) =>
% 0.20/0.49       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (![X9 : $i]:
% 0.20/0.49         (((k7_relat_1 @ X9 @ (k1_relat_1 @ X9)) = (X9)) | ~ (v1_relat_1 @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (((r1_tarski @ sk_A @ sk_B)) <= (((r1_tarski @ sk_A @ sk_B)))),
% 0.20/0.49      inference('split', [status(esa)], ['4'])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (((r1_tarski @ sk_A @ sk_B)) | 
% 0.20/0.49       ((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A))))),
% 0.20/0.49      inference('split', [status(esa)], ['4'])).
% 0.20/0.49  thf('25', plain, (((r1_tarski @ sk_A @ sk_B))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['2', '19', '24'])).
% 0.20/0.49  thf('26', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['23', '25'])).
% 0.20/0.49  thf(t105_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ B ) =>
% 0.20/0.49       ( ![C:$i]:
% 0.20/0.49         ( ( v1_relat_1 @ C ) =>
% 0.20/0.49           ( ( r1_tarski @ B @ C ) =>
% 0.20/0.49             ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ ( k7_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X4)
% 0.20/0.49          | (r1_tarski @ (k7_relat_1 @ X5 @ X6) @ (k7_relat_1 @ X4 @ X6))
% 0.20/0.49          | ~ (r1_tarski @ X5 @ X4)
% 0.20/0.49          | ~ (v1_relat_1 @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [t105_relat_1])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ sk_A)
% 0.20/0.49          | (r1_tarski @ (k7_relat_1 @ sk_A @ X0) @ (k7_relat_1 @ sk_B @ X0))
% 0.20/0.49          | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.49  thf('29', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (r1_tarski @ (k7_relat_1 @ sk_A @ X0) @ (k7_relat_1 @ sk_B @ X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      (((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))
% 0.20/0.49        | ~ (v1_relat_1 @ sk_A))),
% 0.20/0.49      inference('sup+', [status(thm)], ['22', '31'])).
% 0.20/0.49  thf('33', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      ((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))),
% 0.20/0.49      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.49  thf('35', plain, ($false), inference('demod', [status(thm)], ['21', '34'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

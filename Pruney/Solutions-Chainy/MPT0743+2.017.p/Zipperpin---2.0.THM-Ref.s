%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yJv6EKzURH

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:54 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 309 expanded)
%              Number of leaves         :   14 (  84 expanded)
%              Depth                    :   17
%              Number of atoms          :  362 (2503 expanded)
%              Number of equality atoms :    9 (  26 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(t33_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ B )
          <=> ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r2_hidden @ A @ B )
            <=> ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_ordinal1])).

thf('0',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('3',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ ( k1_ordinal1 @ X11 ) )
      | ( X10 != X11 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('7',plain,(
    ! [X11: $i] :
      ( r2_hidden @ X11 @ ( k1_ordinal1 @ X11 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('8',plain,(
    ! [X14: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X14 ) )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('9',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v3_ordinal1 @ X7 )
      | ~ ( v3_ordinal1 @ X8 )
      | ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_ordinal1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('11',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('17',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_B )
        | ~ ( r2_hidden @ X0 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['7','18'])).

thf('20',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('21',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('23',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['5','21','22'])).

thf('24',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['3','23'])).

thf('25',plain,(
    ! [X14: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X14 ) )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('26',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v3_ordinal1 @ X12 )
      | ( r1_ordinal1 @ X13 @ X12 )
      | ( r2_hidden @ X12 @ X13 )
      | ~ ( v3_ordinal1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('27',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X10 = X9 )
      | ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ ( k1_ordinal1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X0 ) @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('31',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['5','21'])).

thf('32',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r2_hidden @ sk_B @ sk_A )
    | ( sk_B = sk_A )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( sk_B = sk_A ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['3','23'])).

thf('38',plain,(
    sk_B = sk_A ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( r2_hidden @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['24','38'])).

thf('40',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('41',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['5','21','22'])).

thf('42',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(simpl_trail,[status(thm)],['40','41'])).

thf('43',plain,(
    sk_B = sk_A ),
    inference(clc,[status(thm)],['36','37'])).

thf('44',plain,(
    r2_hidden @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['39','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yJv6EKzURH
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:31:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.42/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.42/0.62  % Solved by: fo/fo7.sh
% 0.42/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.62  % done 406 iterations in 0.165s
% 0.42/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.42/0.62  % SZS output start Refutation
% 0.42/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.62  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.42/0.62  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.42/0.62  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.42/0.62  thf(t33_ordinal1, conjecture,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( v3_ordinal1 @ A ) =>
% 0.42/0.62       ( ![B:$i]:
% 0.42/0.62         ( ( v3_ordinal1 @ B ) =>
% 0.42/0.62           ( ( r2_hidden @ A @ B ) <=>
% 0.42/0.62             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 0.42/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.62    (~( ![A:$i]:
% 0.42/0.62        ( ( v3_ordinal1 @ A ) =>
% 0.42/0.62          ( ![B:$i]:
% 0.42/0.62            ( ( v3_ordinal1 @ B ) =>
% 0.42/0.62              ( ( r2_hidden @ A @ B ) <=>
% 0.42/0.62                ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ) )),
% 0.42/0.62    inference('cnf.neg', [status(esa)], [t33_ordinal1])).
% 0.42/0.62  thf('0', plain,
% 0.42/0.62      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('1', plain,
% 0.42/0.62      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.42/0.62      inference('split', [status(esa)], ['0'])).
% 0.42/0.62  thf(antisymmetry_r2_hidden, axiom,
% 0.42/0.62    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.42/0.62  thf('2', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.42/0.62      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.42/0.62  thf('3', plain,
% 0.42/0.62      ((~ (r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.42/0.62  thf('4', plain,
% 0.42/0.62      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.42/0.62        | ~ (r2_hidden @ sk_A @ sk_B))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('5', plain,
% 0.42/0.62      (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 0.42/0.62       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.42/0.62      inference('split', [status(esa)], ['4'])).
% 0.42/0.62  thf(t13_ordinal1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.42/0.62       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.42/0.62  thf('6', plain,
% 0.42/0.62      (![X10 : $i, X11 : $i]:
% 0.42/0.62         ((r2_hidden @ X10 @ (k1_ordinal1 @ X11)) | ((X10) != (X11)))),
% 0.42/0.62      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.42/0.62  thf('7', plain, (![X11 : $i]: (r2_hidden @ X11 @ (k1_ordinal1 @ X11))),
% 0.42/0.62      inference('simplify', [status(thm)], ['6'])).
% 0.42/0.62  thf(t29_ordinal1, axiom,
% 0.42/0.62    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 0.42/0.62  thf('8', plain,
% 0.42/0.62      (![X14 : $i]:
% 0.42/0.62         ((v3_ordinal1 @ (k1_ordinal1 @ X14)) | ~ (v3_ordinal1 @ X14))),
% 0.42/0.62      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.42/0.62  thf('9', plain,
% 0.42/0.62      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.42/0.62         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.42/0.62      inference('split', [status(esa)], ['0'])).
% 0.42/0.62  thf(redefinition_r1_ordinal1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.42/0.62       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.42/0.62  thf('10', plain,
% 0.42/0.62      (![X7 : $i, X8 : $i]:
% 0.42/0.62         (~ (v3_ordinal1 @ X7)
% 0.42/0.62          | ~ (v3_ordinal1 @ X8)
% 0.42/0.62          | (r1_tarski @ X7 @ X8)
% 0.42/0.62          | ~ (r1_ordinal1 @ X7 @ X8))),
% 0.42/0.62      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.42/0.62  thf('11', plain,
% 0.42/0.62      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.42/0.62         | ~ (v3_ordinal1 @ sk_B)
% 0.42/0.62         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.42/0.62         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['9', '10'])).
% 0.42/0.62  thf('12', plain, ((v3_ordinal1 @ sk_B)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('13', plain,
% 0.42/0.62      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.42/0.62         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.42/0.62         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.42/0.62      inference('demod', [status(thm)], ['11', '12'])).
% 0.42/0.62  thf('14', plain,
% 0.42/0.62      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 0.42/0.62         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['8', '13'])).
% 0.42/0.62  thf('15', plain, ((v3_ordinal1 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('16', plain,
% 0.42/0.62      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.42/0.62         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.42/0.62      inference('demod', [status(thm)], ['14', '15'])).
% 0.42/0.62  thf(d3_tarski, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( r1_tarski @ A @ B ) <=>
% 0.42/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.42/0.62  thf('17', plain,
% 0.42/0.62      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X2 @ X3)
% 0.42/0.62          | (r2_hidden @ X2 @ X4)
% 0.42/0.62          | ~ (r1_tarski @ X3 @ X4))),
% 0.42/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.42/0.62  thf('18', plain,
% 0.42/0.62      ((![X0 : $i]:
% 0.42/0.62          ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k1_ordinal1 @ sk_A))))
% 0.42/0.62         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['16', '17'])).
% 0.42/0.62  thf('19', plain,
% 0.42/0.62      (((r2_hidden @ sk_A @ sk_B))
% 0.42/0.62         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['7', '18'])).
% 0.42/0.62  thf('20', plain,
% 0.42/0.62      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.42/0.62      inference('split', [status(esa)], ['4'])).
% 0.42/0.62  thf('21', plain,
% 0.42/0.62      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.42/0.62       ~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.42/0.62      inference('sup-', [status(thm)], ['19', '20'])).
% 0.42/0.62  thf('22', plain,
% 0.42/0.62      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.42/0.62       ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.42/0.62      inference('split', [status(esa)], ['0'])).
% 0.42/0.62  thf('23', plain, (((r2_hidden @ sk_A @ sk_B))),
% 0.42/0.62      inference('sat_resolution*', [status(thm)], ['5', '21', '22'])).
% 0.42/0.62  thf('24', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 0.42/0.62      inference('simpl_trail', [status(thm)], ['3', '23'])).
% 0.42/0.62  thf('25', plain,
% 0.42/0.62      (![X14 : $i]:
% 0.42/0.62         ((v3_ordinal1 @ (k1_ordinal1 @ X14)) | ~ (v3_ordinal1 @ X14))),
% 0.42/0.62      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.42/0.62  thf(t26_ordinal1, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( v3_ordinal1 @ A ) =>
% 0.42/0.62       ( ![B:$i]:
% 0.42/0.62         ( ( v3_ordinal1 @ B ) =>
% 0.42/0.62           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.42/0.62  thf('26', plain,
% 0.42/0.62      (![X12 : $i, X13 : $i]:
% 0.42/0.62         (~ (v3_ordinal1 @ X12)
% 0.42/0.62          | (r1_ordinal1 @ X13 @ X12)
% 0.42/0.62          | (r2_hidden @ X12 @ X13)
% 0.42/0.62          | ~ (v3_ordinal1 @ X13))),
% 0.42/0.62      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.42/0.62  thf('27', plain,
% 0.42/0.62      (![X9 : $i, X10 : $i]:
% 0.42/0.62         (((X10) = (X9))
% 0.42/0.62          | (r2_hidden @ X10 @ X9)
% 0.42/0.62          | ~ (r2_hidden @ X10 @ (k1_ordinal1 @ X9)))),
% 0.42/0.62      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.42/0.62  thf('28', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (~ (v3_ordinal1 @ (k1_ordinal1 @ X0))
% 0.42/0.62          | (r1_ordinal1 @ (k1_ordinal1 @ X0) @ X1)
% 0.42/0.62          | ~ (v3_ordinal1 @ X1)
% 0.42/0.62          | (r2_hidden @ X1 @ X0)
% 0.42/0.62          | ((X1) = (X0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['26', '27'])).
% 0.42/0.62  thf('29', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (~ (v3_ordinal1 @ X0)
% 0.42/0.62          | ((X1) = (X0))
% 0.42/0.62          | (r2_hidden @ X1 @ X0)
% 0.42/0.62          | ~ (v3_ordinal1 @ X1)
% 0.42/0.62          | (r1_ordinal1 @ (k1_ordinal1 @ X0) @ X1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['25', '28'])).
% 0.42/0.62  thf('30', plain,
% 0.42/0.62      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.42/0.62         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.42/0.62      inference('split', [status(esa)], ['4'])).
% 0.42/0.62  thf('31', plain, (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.42/0.62      inference('sat_resolution*', [status(thm)], ['5', '21'])).
% 0.42/0.62  thf('32', plain, (~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 0.42/0.62      inference('simpl_trail', [status(thm)], ['30', '31'])).
% 0.42/0.62  thf('33', plain,
% 0.42/0.62      ((~ (v3_ordinal1 @ sk_B)
% 0.42/0.62        | (r2_hidden @ sk_B @ sk_A)
% 0.42/0.62        | ((sk_B) = (sk_A))
% 0.42/0.62        | ~ (v3_ordinal1 @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['29', '32'])).
% 0.42/0.62  thf('34', plain, ((v3_ordinal1 @ sk_B)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('35', plain, ((v3_ordinal1 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('36', plain, (((r2_hidden @ sk_B @ sk_A) | ((sk_B) = (sk_A)))),
% 0.42/0.62      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.42/0.62  thf('37', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 0.42/0.62      inference('simpl_trail', [status(thm)], ['3', '23'])).
% 0.42/0.62  thf('38', plain, (((sk_B) = (sk_A))),
% 0.42/0.62      inference('clc', [status(thm)], ['36', '37'])).
% 0.42/0.62  thf('39', plain, (~ (r2_hidden @ sk_A @ sk_A)),
% 0.42/0.62      inference('demod', [status(thm)], ['24', '38'])).
% 0.42/0.62  thf('40', plain,
% 0.42/0.62      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.42/0.62      inference('split', [status(esa)], ['0'])).
% 0.42/0.62  thf('41', plain, (((r2_hidden @ sk_A @ sk_B))),
% 0.42/0.62      inference('sat_resolution*', [status(thm)], ['5', '21', '22'])).
% 0.42/0.62  thf('42', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.42/0.62      inference('simpl_trail', [status(thm)], ['40', '41'])).
% 0.42/0.62  thf('43', plain, (((sk_B) = (sk_A))),
% 0.42/0.62      inference('clc', [status(thm)], ['36', '37'])).
% 0.42/0.62  thf('44', plain, ((r2_hidden @ sk_A @ sk_A)),
% 0.42/0.62      inference('demod', [status(thm)], ['42', '43'])).
% 0.42/0.62  thf('45', plain, ($false), inference('demod', [status(thm)], ['39', '44'])).
% 0.42/0.62  
% 0.42/0.62  % SZS output end Refutation
% 0.42/0.62  
% 0.42/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

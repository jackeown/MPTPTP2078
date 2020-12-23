%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rOyLVBTUUB

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:56 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 194 expanded)
%              Number of leaves         :   16 (  56 expanded)
%              Depth                    :   18
%              Number of atoms          :  477 (1530 expanded)
%              Number of equality atoms :   11 (  16 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( r1_tarski @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('3',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_A )
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
    ! [X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ ( k1_ordinal1 @ X14 ) )
      | ( X13 != X14 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('7',plain,(
    ! [X14: $i] :
      ( r2_hidden @ X14 @ ( k1_ordinal1 @ X14 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('8',plain,(
    ! [X17: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X17 ) )
      | ~ ( v3_ordinal1 @ X17 ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ~ ( v3_ordinal1 @ X10 )
      | ~ ( v3_ordinal1 @ X11 )
      | ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_ordinal1 @ X10 @ X11 ) ) ),
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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
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
    ~ ( r1_tarski @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['3','23'])).

thf('25',plain,(
    ! [X17: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X17 ) )
      | ~ ( v3_ordinal1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('26',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v3_ordinal1 @ X15 )
      | ( r1_ordinal1 @ X16 @ X15 )
      | ( r2_hidden @ X15 @ X16 )
      | ~ ( v3_ordinal1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('27',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X13 = X12 )
      | ( r2_hidden @ X13 @ X12 )
      | ~ ( r2_hidden @ X13 @ ( k1_ordinal1 @ X12 ) ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( r1_tarski @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('38',plain,
    ( ( sk_B = sk_A )
    | ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(connectedness_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
        | ( r1_ordinal1 @ B @ A ) ) ) )).

thf('40',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v3_ordinal1 @ X7 )
      | ~ ( v3_ordinal1 @ X8 )
      | ( r1_ordinal1 @ X7 @ X8 )
      | ( r1_ordinal1 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v3_ordinal1 @ X10 )
      | ~ ( v3_ordinal1 @ X11 )
      | ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_ordinal1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ~ ( r1_tarski @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['3','23'])).

thf('48',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    r1_ordinal1 @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v3_ordinal1 @ X10 )
      | ~ ( v3_ordinal1 @ X11 )
      | ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_ordinal1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('52',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    sk_B = sk_A ),
    inference(demod,[status(thm)],['38','55'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('57',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('58',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    $false ),
    inference(demod,[status(thm)],['24','56','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rOyLVBTUUB
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:45:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.40/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.63  % Solved by: fo/fo7.sh
% 0.40/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.63  % done 324 iterations in 0.166s
% 0.40/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.63  % SZS output start Refutation
% 0.40/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.63  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.40/0.63  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.40/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.63  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.40/0.63  thf(t33_ordinal1, conjecture,
% 0.40/0.63    (![A:$i]:
% 0.40/0.63     ( ( v3_ordinal1 @ A ) =>
% 0.40/0.63       ( ![B:$i]:
% 0.40/0.63         ( ( v3_ordinal1 @ B ) =>
% 0.40/0.63           ( ( r2_hidden @ A @ B ) <=>
% 0.40/0.63             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 0.40/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.63    (~( ![A:$i]:
% 0.40/0.63        ( ( v3_ordinal1 @ A ) =>
% 0.40/0.63          ( ![B:$i]:
% 0.40/0.63            ( ( v3_ordinal1 @ B ) =>
% 0.40/0.63              ( ( r2_hidden @ A @ B ) <=>
% 0.40/0.63                ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ) )),
% 0.40/0.63    inference('cnf.neg', [status(esa)], [t33_ordinal1])).
% 0.40/0.63  thf('0', plain,
% 0.40/0.63      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('1', plain,
% 0.40/0.63      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.40/0.63      inference('split', [status(esa)], ['0'])).
% 0.40/0.63  thf(t7_ordinal1, axiom,
% 0.40/0.63    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.40/0.63  thf('2', plain,
% 0.40/0.63      (![X18 : $i, X19 : $i]:
% 0.40/0.63         (~ (r2_hidden @ X18 @ X19) | ~ (r1_tarski @ X19 @ X18))),
% 0.40/0.63      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.40/0.63  thf('3', plain,
% 0.40/0.63      ((~ (r1_tarski @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.63  thf('4', plain,
% 0.40/0.63      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.40/0.63        | ~ (r2_hidden @ sk_A @ sk_B))),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('5', plain,
% 0.40/0.63      (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 0.40/0.63       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.40/0.63      inference('split', [status(esa)], ['4'])).
% 0.40/0.63  thf(t13_ordinal1, axiom,
% 0.40/0.63    (![A:$i,B:$i]:
% 0.40/0.63     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.40/0.63       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.40/0.63  thf('6', plain,
% 0.40/0.63      (![X13 : $i, X14 : $i]:
% 0.40/0.63         ((r2_hidden @ X13 @ (k1_ordinal1 @ X14)) | ((X13) != (X14)))),
% 0.40/0.63      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.40/0.63  thf('7', plain, (![X14 : $i]: (r2_hidden @ X14 @ (k1_ordinal1 @ X14))),
% 0.40/0.63      inference('simplify', [status(thm)], ['6'])).
% 0.40/0.63  thf(t29_ordinal1, axiom,
% 0.40/0.63    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 0.40/0.63  thf('8', plain,
% 0.40/0.63      (![X17 : $i]:
% 0.40/0.63         ((v3_ordinal1 @ (k1_ordinal1 @ X17)) | ~ (v3_ordinal1 @ X17))),
% 0.40/0.63      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.40/0.63  thf('9', plain,
% 0.40/0.63      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.40/0.63         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.40/0.63      inference('split', [status(esa)], ['0'])).
% 0.40/0.63  thf(redefinition_r1_ordinal1, axiom,
% 0.40/0.63    (![A:$i,B:$i]:
% 0.40/0.63     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.40/0.63       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.40/0.63  thf('10', plain,
% 0.40/0.63      (![X10 : $i, X11 : $i]:
% 0.40/0.63         (~ (v3_ordinal1 @ X10)
% 0.40/0.63          | ~ (v3_ordinal1 @ X11)
% 0.40/0.63          | (r1_tarski @ X10 @ X11)
% 0.40/0.63          | ~ (r1_ordinal1 @ X10 @ X11))),
% 0.40/0.63      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.40/0.63  thf('11', plain,
% 0.40/0.63      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.40/0.63         | ~ (v3_ordinal1 @ sk_B)
% 0.40/0.63         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.40/0.63         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['9', '10'])).
% 0.40/0.63  thf('12', plain, ((v3_ordinal1 @ sk_B)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('13', plain,
% 0.40/0.63      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.40/0.63         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.40/0.63         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.40/0.63      inference('demod', [status(thm)], ['11', '12'])).
% 0.40/0.63  thf('14', plain,
% 0.40/0.63      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 0.40/0.63         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['8', '13'])).
% 0.40/0.63  thf('15', plain, ((v3_ordinal1 @ sk_A)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('16', plain,
% 0.40/0.63      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.40/0.63         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.40/0.63      inference('demod', [status(thm)], ['14', '15'])).
% 0.40/0.63  thf(d3_tarski, axiom,
% 0.40/0.63    (![A:$i,B:$i]:
% 0.40/0.63     ( ( r1_tarski @ A @ B ) <=>
% 0.40/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.40/0.63  thf('17', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.63         (~ (r2_hidden @ X0 @ X1)
% 0.40/0.63          | (r2_hidden @ X0 @ X2)
% 0.40/0.63          | ~ (r1_tarski @ X1 @ X2))),
% 0.40/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.63  thf('18', plain,
% 0.40/0.63      ((![X0 : $i]:
% 0.40/0.63          ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k1_ordinal1 @ sk_A))))
% 0.40/0.63         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['16', '17'])).
% 0.40/0.63  thf('19', plain,
% 0.40/0.63      (((r2_hidden @ sk_A @ sk_B))
% 0.40/0.63         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['7', '18'])).
% 0.40/0.63  thf('20', plain,
% 0.40/0.63      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.40/0.63      inference('split', [status(esa)], ['4'])).
% 0.40/0.63  thf('21', plain,
% 0.40/0.63      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.40/0.63       ~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.40/0.63      inference('sup-', [status(thm)], ['19', '20'])).
% 0.40/0.63  thf('22', plain,
% 0.40/0.63      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.40/0.63       ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.40/0.63      inference('split', [status(esa)], ['0'])).
% 0.40/0.63  thf('23', plain, (((r2_hidden @ sk_A @ sk_B))),
% 0.40/0.63      inference('sat_resolution*', [status(thm)], ['5', '21', '22'])).
% 0.40/0.63  thf('24', plain, (~ (r1_tarski @ sk_B @ sk_A)),
% 0.40/0.63      inference('simpl_trail', [status(thm)], ['3', '23'])).
% 0.40/0.63  thf('25', plain,
% 0.40/0.63      (![X17 : $i]:
% 0.40/0.63         ((v3_ordinal1 @ (k1_ordinal1 @ X17)) | ~ (v3_ordinal1 @ X17))),
% 0.40/0.63      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.40/0.63  thf(t26_ordinal1, axiom,
% 0.40/0.63    (![A:$i]:
% 0.40/0.63     ( ( v3_ordinal1 @ A ) =>
% 0.40/0.63       ( ![B:$i]:
% 0.40/0.63         ( ( v3_ordinal1 @ B ) =>
% 0.40/0.63           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.40/0.63  thf('26', plain,
% 0.40/0.63      (![X15 : $i, X16 : $i]:
% 0.40/0.63         (~ (v3_ordinal1 @ X15)
% 0.40/0.63          | (r1_ordinal1 @ X16 @ X15)
% 0.40/0.63          | (r2_hidden @ X15 @ X16)
% 0.40/0.63          | ~ (v3_ordinal1 @ X16))),
% 0.40/0.63      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.40/0.63  thf('27', plain,
% 0.40/0.63      (![X12 : $i, X13 : $i]:
% 0.40/0.63         (((X13) = (X12))
% 0.40/0.63          | (r2_hidden @ X13 @ X12)
% 0.40/0.63          | ~ (r2_hidden @ X13 @ (k1_ordinal1 @ X12)))),
% 0.40/0.63      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.40/0.63  thf('28', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i]:
% 0.40/0.63         (~ (v3_ordinal1 @ (k1_ordinal1 @ X0))
% 0.40/0.63          | (r1_ordinal1 @ (k1_ordinal1 @ X0) @ X1)
% 0.40/0.63          | ~ (v3_ordinal1 @ X1)
% 0.40/0.63          | (r2_hidden @ X1 @ X0)
% 0.40/0.63          | ((X1) = (X0)))),
% 0.40/0.63      inference('sup-', [status(thm)], ['26', '27'])).
% 0.40/0.63  thf('29', plain,
% 0.40/0.63      (![X0 : $i, X1 : $i]:
% 0.40/0.63         (~ (v3_ordinal1 @ X0)
% 0.40/0.63          | ((X1) = (X0))
% 0.40/0.63          | (r2_hidden @ X1 @ X0)
% 0.40/0.63          | ~ (v3_ordinal1 @ X1)
% 0.40/0.63          | (r1_ordinal1 @ (k1_ordinal1 @ X0) @ X1))),
% 0.40/0.63      inference('sup-', [status(thm)], ['25', '28'])).
% 0.40/0.63  thf('30', plain,
% 0.40/0.63      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.40/0.63         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.40/0.63      inference('split', [status(esa)], ['4'])).
% 0.40/0.63  thf('31', plain, (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.40/0.63      inference('sat_resolution*', [status(thm)], ['5', '21'])).
% 0.40/0.63  thf('32', plain, (~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 0.40/0.63      inference('simpl_trail', [status(thm)], ['30', '31'])).
% 0.40/0.63  thf('33', plain,
% 0.40/0.63      ((~ (v3_ordinal1 @ sk_B)
% 0.40/0.63        | (r2_hidden @ sk_B @ sk_A)
% 0.40/0.63        | ((sk_B) = (sk_A))
% 0.40/0.63        | ~ (v3_ordinal1 @ sk_A))),
% 0.40/0.63      inference('sup-', [status(thm)], ['29', '32'])).
% 0.40/0.63  thf('34', plain, ((v3_ordinal1 @ sk_B)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('35', plain, ((v3_ordinal1 @ sk_A)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('36', plain, (((r2_hidden @ sk_B @ sk_A) | ((sk_B) = (sk_A)))),
% 0.40/0.63      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.40/0.63  thf('37', plain,
% 0.40/0.63      (![X18 : $i, X19 : $i]:
% 0.40/0.63         (~ (r2_hidden @ X18 @ X19) | ~ (r1_tarski @ X19 @ X18))),
% 0.40/0.63      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.40/0.63  thf('38', plain, ((((sk_B) = (sk_A)) | ~ (r1_tarski @ sk_A @ sk_B))),
% 0.40/0.63      inference('sup-', [status(thm)], ['36', '37'])).
% 0.40/0.63  thf('39', plain, ((v3_ordinal1 @ sk_A)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf(connectedness_r1_ordinal1, axiom,
% 0.40/0.63    (![A:$i,B:$i]:
% 0.40/0.63     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.40/0.63       ( ( r1_ordinal1 @ A @ B ) | ( r1_ordinal1 @ B @ A ) ) ))).
% 0.40/0.63  thf('40', plain,
% 0.40/0.63      (![X7 : $i, X8 : $i]:
% 0.40/0.63         (~ (v3_ordinal1 @ X7)
% 0.40/0.63          | ~ (v3_ordinal1 @ X8)
% 0.40/0.63          | (r1_ordinal1 @ X7 @ X8)
% 0.40/0.63          | (r1_ordinal1 @ X8 @ X7))),
% 0.40/0.63      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.40/0.63  thf('41', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         ((r1_ordinal1 @ X0 @ sk_A)
% 0.40/0.63          | (r1_ordinal1 @ sk_A @ X0)
% 0.40/0.63          | ~ (v3_ordinal1 @ X0))),
% 0.40/0.63      inference('sup-', [status(thm)], ['39', '40'])).
% 0.40/0.63  thf('42', plain,
% 0.40/0.63      (![X10 : $i, X11 : $i]:
% 0.40/0.63         (~ (v3_ordinal1 @ X10)
% 0.40/0.63          | ~ (v3_ordinal1 @ X11)
% 0.40/0.63          | (r1_tarski @ X10 @ X11)
% 0.40/0.63          | ~ (r1_ordinal1 @ X10 @ X11))),
% 0.40/0.63      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.40/0.63  thf('43', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         (~ (v3_ordinal1 @ X0)
% 0.40/0.63          | (r1_ordinal1 @ sk_A @ X0)
% 0.40/0.63          | (r1_tarski @ X0 @ sk_A)
% 0.40/0.63          | ~ (v3_ordinal1 @ sk_A)
% 0.40/0.63          | ~ (v3_ordinal1 @ X0))),
% 0.40/0.63      inference('sup-', [status(thm)], ['41', '42'])).
% 0.40/0.63  thf('44', plain, ((v3_ordinal1 @ sk_A)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('45', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         (~ (v3_ordinal1 @ X0)
% 0.40/0.63          | (r1_ordinal1 @ sk_A @ X0)
% 0.40/0.63          | (r1_tarski @ X0 @ sk_A)
% 0.40/0.63          | ~ (v3_ordinal1 @ X0))),
% 0.40/0.63      inference('demod', [status(thm)], ['43', '44'])).
% 0.40/0.63  thf('46', plain,
% 0.40/0.63      (![X0 : $i]:
% 0.40/0.63         ((r1_tarski @ X0 @ sk_A)
% 0.40/0.63          | (r1_ordinal1 @ sk_A @ X0)
% 0.40/0.63          | ~ (v3_ordinal1 @ X0))),
% 0.40/0.63      inference('simplify', [status(thm)], ['45'])).
% 0.40/0.63  thf('47', plain, (~ (r1_tarski @ sk_B @ sk_A)),
% 0.40/0.63      inference('simpl_trail', [status(thm)], ['3', '23'])).
% 0.40/0.63  thf('48', plain, ((~ (v3_ordinal1 @ sk_B) | (r1_ordinal1 @ sk_A @ sk_B))),
% 0.40/0.63      inference('sup-', [status(thm)], ['46', '47'])).
% 0.40/0.63  thf('49', plain, ((v3_ordinal1 @ sk_B)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('50', plain, ((r1_ordinal1 @ sk_A @ sk_B)),
% 0.40/0.63      inference('demod', [status(thm)], ['48', '49'])).
% 0.40/0.63  thf('51', plain,
% 0.40/0.63      (![X10 : $i, X11 : $i]:
% 0.40/0.63         (~ (v3_ordinal1 @ X10)
% 0.40/0.63          | ~ (v3_ordinal1 @ X11)
% 0.40/0.63          | (r1_tarski @ X10 @ X11)
% 0.40/0.63          | ~ (r1_ordinal1 @ X10 @ X11))),
% 0.40/0.63      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.40/0.63  thf('52', plain,
% 0.40/0.63      (((r1_tarski @ sk_A @ sk_B)
% 0.40/0.63        | ~ (v3_ordinal1 @ sk_B)
% 0.40/0.63        | ~ (v3_ordinal1 @ sk_A))),
% 0.40/0.63      inference('sup-', [status(thm)], ['50', '51'])).
% 0.40/0.63  thf('53', plain, ((v3_ordinal1 @ sk_B)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('54', plain, ((v3_ordinal1 @ sk_A)),
% 0.40/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.63  thf('55', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.40/0.63      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.40/0.63  thf('56', plain, (((sk_B) = (sk_A))),
% 0.40/0.63      inference('demod', [status(thm)], ['38', '55'])).
% 0.40/0.63  thf(d10_xboole_0, axiom,
% 0.40/0.63    (![A:$i,B:$i]:
% 0.40/0.63     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.40/0.63  thf('57', plain,
% 0.40/0.63      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.40/0.63      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.40/0.63  thf('58', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.40/0.63      inference('simplify', [status(thm)], ['57'])).
% 0.40/0.63  thf('59', plain, ($false),
% 0.40/0.63      inference('demod', [status(thm)], ['24', '56', '58'])).
% 0.40/0.63  
% 0.40/0.63  % SZS output end Refutation
% 0.40/0.63  
% 0.45/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

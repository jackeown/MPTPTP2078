%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.20KasmABkS

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 303 expanded)
%              Number of leaves         :   16 (  87 expanded)
%              Depth                    :   24
%              Number of atoms          :  514 (2635 expanded)
%              Number of equality atoms :   21 (  59 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('1',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v3_ordinal1 @ X6 )
      | ~ ( v3_ordinal1 @ X7 )
      | ( r1_ordinal1 @ X6 @ X7 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t34_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
          <=> ( r1_ordinal1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
            <=> ( r1_ordinal1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_ordinal1])).

thf('7',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v3_ordinal1 @ X12 )
      | ( r2_hidden @ X13 @ X12 )
      | ( X13 = X12 )
      | ( r2_hidden @ X12 @ X13 )
      | ~ ( v3_ordinal1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('11',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v3_ordinal1 @ X6 )
      | ~ ( v3_ordinal1 @ X7 )
      | ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_ordinal1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('14',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_B )
        | ~ ( r2_hidden @ X0 @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ~ ( v3_ordinal1 @ X0 )
        | ( r2_hidden @ sk_A @ X0 )
        | ( X0 = sk_A )
        | ~ ( v3_ordinal1 @ sk_A )
        | ( r2_hidden @ X0 @ sk_B ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['10','19'])).

thf('21',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ! [X0: $i] :
        ( ~ ( v3_ordinal1 @ X0 )
        | ( r2_hidden @ sk_A @ X0 )
        | ( X0 = sk_A )
        | ( r2_hidden @ X0 @ sk_B ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ~ ( v3_ordinal1 @ X0 )
        | ( r2_hidden @ sk_A @ X0 )
        | ( X0 = sk_A )
        | ( r2_hidden @ X0 @ sk_B ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('25',plain,
    ( ! [X0: $i] :
        ( ( X0 = sk_A )
        | ( r2_hidden @ sk_A @ X0 )
        | ~ ( v3_ordinal1 @ X0 )
        | ~ ( r2_hidden @ sk_B @ X0 ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( sk_B = sk_A )
      | ( r2_hidden @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ( r2_hidden @ sk_A @ sk_B )
      | ( sk_B = sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( sk_B = sk_A )
      | ( r2_hidden @ sk_A @ sk_B )
      | ( r2_hidden @ sk_A @ sk_B )
      | ( sk_B = sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ( sk_B = sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['29'])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('31',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ ( k1_ordinal1 @ X11 ) )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('32',plain,
    ( ( ( sk_B = sk_A )
      | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf('34',plain,
    ( ( sk_B = sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf('36',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('37',plain,(
    ! [X8: $i] :
      ( r2_hidden @ X8 @ ( k1_ordinal1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('38',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
    | ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['9','38'])).

thf('40',plain,(
    ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['8','39'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('41',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v3_ordinal1 @ X14 )
      | ( r1_ordinal1 @ X15 @ X14 )
      | ( r2_hidden @ X14 @ X15 )
      | ~ ( v3_ordinal1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('42',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['11'])).

thf('43',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X10 = X9 )
      | ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ ( k1_ordinal1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('44',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ( sk_A = sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('46',plain,
    ( ( ( sk_A = sk_B )
      | ~ ( r2_hidden @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['11'])).

thf('48',plain,(
    r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['9','38','47'])).

thf('49',plain,
    ( ( sk_A = sk_B )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['46','48'])).

thf('50',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['41','49'])).

thf('51',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( sk_A = sk_B ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['8','39'])).

thf('55',plain,(
    sk_A = sk_B ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( r1_ordinal1 @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['40','55'])).

thf('57',plain,(
    ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','56'])).

thf('58',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    $false ),
    inference(demod,[status(thm)],['57','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.20KasmABkS
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:23:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 154 iterations in 0.062s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.20/0.51  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.20/0.51  thf(d3_tarski, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      (![X3 : $i, X5 : $i]:
% 0.20/0.51         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (![X3 : $i, X5 : $i]:
% 0.20/0.51         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.51  thf('3', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.20/0.51      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.51  thf(redefinition_r1_ordinal1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.20/0.51       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (![X6 : $i, X7 : $i]:
% 0.20/0.51         (~ (v3_ordinal1 @ X6)
% 0.20/0.51          | ~ (v3_ordinal1 @ X7)
% 0.20/0.51          | (r1_ordinal1 @ X6 @ X7)
% 0.20/0.51          | ~ (r1_tarski @ X6 @ X7))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r1_ordinal1 @ X0 @ X0) | ~ (v3_ordinal1 @ X0) | ~ (v3_ordinal1 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (![X0 : $i]: (~ (v3_ordinal1 @ X0) | (r1_ordinal1 @ X0 @ X0))),
% 0.20/0.51      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.51  thf(t34_ordinal1, conjecture,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v3_ordinal1 @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( v3_ordinal1 @ B ) =>
% 0.20/0.51           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.20/0.51             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i]:
% 0.20/0.51        ( ( v3_ordinal1 @ A ) =>
% 0.20/0.51          ( ![B:$i]:
% 0.20/0.51            ( ( v3_ordinal1 @ B ) =>
% 0.20/0.51              ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.20/0.51                ( r1_ordinal1 @ A @ B ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t34_ordinal1])).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      ((~ (r1_ordinal1 @ sk_A @ sk_B)
% 0.20/0.51        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('split', [status(esa)], ['7'])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.20/0.51       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.20/0.51      inference('split', [status(esa)], ['7'])).
% 0.20/0.51  thf(t24_ordinal1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v3_ordinal1 @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( v3_ordinal1 @ B ) =>
% 0.20/0.51           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.20/0.51                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i]:
% 0.20/0.51         (~ (v3_ordinal1 @ X12)
% 0.20/0.51          | (r2_hidden @ X13 @ X12)
% 0.20/0.51          | ((X13) = (X12))
% 0.20/0.51          | (r2_hidden @ X12 @ X13)
% 0.20/0.51          | ~ (v3_ordinal1 @ X13))),
% 0.20/0.51      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (((r1_ordinal1 @ sk_A @ sk_B) | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (((r1_ordinal1 @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('split', [status(esa)], ['11'])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X6 : $i, X7 : $i]:
% 0.20/0.51         (~ (v3_ordinal1 @ X6)
% 0.20/0.51          | ~ (v3_ordinal1 @ X7)
% 0.20/0.51          | (r1_tarski @ X6 @ X7)
% 0.20/0.51          | ~ (r1_ordinal1 @ X6 @ X7))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      ((((r1_tarski @ sk_A @ sk_B)
% 0.20/0.51         | ~ (v3_ordinal1 @ sk_B)
% 0.20/0.51         | ~ (v3_ordinal1 @ sk_A))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.51  thf('15', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('16', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (((r1_tarski @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X2 @ X3)
% 0.20/0.51          | (r2_hidden @ X2 @ X4)
% 0.20/0.51          | ~ (r1_tarski @ X3 @ X4))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      ((![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A)))
% 0.20/0.51         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          (~ (v3_ordinal1 @ X0)
% 0.20/0.51           | (r2_hidden @ sk_A @ X0)
% 0.20/0.51           | ((X0) = (sk_A))
% 0.20/0.51           | ~ (v3_ordinal1 @ sk_A)
% 0.20/0.51           | (r2_hidden @ X0 @ sk_B)))
% 0.20/0.51         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['10', '19'])).
% 0.20/0.51  thf('21', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          (~ (v3_ordinal1 @ X0)
% 0.20/0.51           | (r2_hidden @ sk_A @ X0)
% 0.20/0.51           | ((X0) = (sk_A))
% 0.20/0.51           | (r2_hidden @ X0 @ sk_B)))
% 0.20/0.51         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          (~ (v3_ordinal1 @ X0)
% 0.20/0.51           | (r2_hidden @ sk_A @ X0)
% 0.20/0.51           | ((X0) = (sk_A))
% 0.20/0.51           | (r2_hidden @ X0 @ sk_B)))
% 0.20/0.51         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.51  thf(antisymmetry_r2_hidden, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.51      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          (((X0) = (sk_A))
% 0.20/0.51           | (r2_hidden @ sk_A @ X0)
% 0.20/0.51           | ~ (v3_ordinal1 @ X0)
% 0.20/0.51           | ~ (r2_hidden @ sk_B @ X0)))
% 0.20/0.51         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      (((((sk_B) = (sk_A))
% 0.20/0.51         | (r2_hidden @ sk_A @ sk_B)
% 0.20/0.51         | ~ (v3_ordinal1 @ sk_B)
% 0.20/0.51         | ~ (v3_ordinal1 @ sk_B)
% 0.20/0.51         | (r2_hidden @ sk_A @ sk_B)
% 0.20/0.51         | ((sk_B) = (sk_A)))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['22', '25'])).
% 0.20/0.51  thf('27', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('28', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      (((((sk_B) = (sk_A))
% 0.20/0.51         | (r2_hidden @ sk_A @ sk_B)
% 0.20/0.51         | (r2_hidden @ sk_A @ sk_B)
% 0.20/0.51         | ((sk_B) = (sk_A)))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      ((((r2_hidden @ sk_A @ sk_B) | ((sk_B) = (sk_A))))
% 0.20/0.51         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['29'])).
% 0.20/0.51  thf(t13_ordinal1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.20/0.51       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      (![X10 : $i, X11 : $i]:
% 0.20/0.51         ((r2_hidden @ X10 @ (k1_ordinal1 @ X11)) | ~ (r2_hidden @ X10 @ X11))),
% 0.20/0.51      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      (((((sk_B) = (sk_A)) | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))
% 0.20/0.51         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.20/0.51         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.51      inference('split', [status(esa)], ['7'])).
% 0.20/0.51  thf('34', plain,
% 0.20/0.51      ((((sk_B) = (sk_A)))
% 0.20/0.51         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.20/0.51             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.20/0.51         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.51      inference('split', [status(esa)], ['7'])).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 0.20/0.51         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.20/0.51             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.51  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.20/0.51  thf('37', plain, (![X8 : $i]: (r2_hidden @ X8 @ (k1_ordinal1 @ X8))),
% 0.20/0.51      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) | 
% 0.20/0.51       ~ ((r1_ordinal1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.51  thf('39', plain, (~ ((r1_ordinal1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['9', '38'])).
% 0.20/0.51  thf('40', plain, (~ (r1_ordinal1 @ sk_A @ sk_B)),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['8', '39'])).
% 0.20/0.51  thf(t26_ordinal1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v3_ordinal1 @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( v3_ordinal1 @ B ) =>
% 0.20/0.51           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.51  thf('41', plain,
% 0.20/0.51      (![X14 : $i, X15 : $i]:
% 0.20/0.51         (~ (v3_ordinal1 @ X14)
% 0.20/0.51          | (r1_ordinal1 @ X15 @ X14)
% 0.20/0.51          | (r2_hidden @ X14 @ X15)
% 0.20/0.51          | ~ (v3_ordinal1 @ X15))),
% 0.20/0.51      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.20/0.51  thf('42', plain,
% 0.20/0.51      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.20/0.51         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.51      inference('split', [status(esa)], ['11'])).
% 0.20/0.51  thf('43', plain,
% 0.20/0.51      (![X9 : $i, X10 : $i]:
% 0.20/0.51         (((X10) = (X9))
% 0.20/0.51          | (r2_hidden @ X10 @ X9)
% 0.20/0.51          | ~ (r2_hidden @ X10 @ (k1_ordinal1 @ X9)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.20/0.51  thf('44', plain,
% 0.20/0.51      ((((r2_hidden @ sk_A @ sk_B) | ((sk_A) = (sk_B))))
% 0.20/0.51         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.51  thf('45', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.51      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.20/0.51  thf('46', plain,
% 0.20/0.51      (((((sk_A) = (sk_B)) | ~ (r2_hidden @ sk_B @ sk_A)))
% 0.20/0.51         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.51  thf('47', plain,
% 0.20/0.51      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) | 
% 0.20/0.51       ((r1_ordinal1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('split', [status(esa)], ['11'])).
% 0.20/0.51  thf('48', plain, (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['9', '38', '47'])).
% 0.20/0.51  thf('49', plain, ((((sk_A) = (sk_B)) | ~ (r2_hidden @ sk_B @ sk_A))),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['46', '48'])).
% 0.20/0.51  thf('50', plain,
% 0.20/0.51      ((~ (v3_ordinal1 @ sk_A)
% 0.20/0.51        | (r1_ordinal1 @ sk_A @ sk_B)
% 0.20/0.51        | ~ (v3_ordinal1 @ sk_B)
% 0.20/0.51        | ((sk_A) = (sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['41', '49'])).
% 0.20/0.51  thf('51', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('52', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('53', plain, (((r1_ordinal1 @ sk_A @ sk_B) | ((sk_A) = (sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.20/0.51  thf('54', plain, (~ (r1_ordinal1 @ sk_A @ sk_B)),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['8', '39'])).
% 0.20/0.51  thf('55', plain, (((sk_A) = (sk_B))),
% 0.20/0.51      inference('clc', [status(thm)], ['53', '54'])).
% 0.20/0.51  thf('56', plain, (~ (r1_ordinal1 @ sk_A @ sk_A)),
% 0.20/0.51      inference('demod', [status(thm)], ['40', '55'])).
% 0.20/0.51  thf('57', plain, (~ (v3_ordinal1 @ sk_A)),
% 0.20/0.51      inference('sup-', [status(thm)], ['6', '56'])).
% 0.20/0.51  thf('58', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('59', plain, ($false), inference('demod', [status(thm)], ['57', '58'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.34/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

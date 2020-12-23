%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4OFOz6qtXU

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:54 EST 2020

% Result     : Theorem 1.74s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 167 expanded)
%              Number of leaves         :   17 (  50 expanded)
%              Depth                    :   16
%              Number of atoms          :  396 (1313 expanded)
%              Number of equality atoms :    8 (  13 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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
    ! [X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ~ ( r1_tarski @ X25 @ X24 ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ( r2_hidden @ X20 @ ( k1_ordinal1 @ X21 ) )
      | ( X20 != X21 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('7',plain,(
    ! [X21: $i] :
      ( r2_hidden @ X21 @ ( k1_ordinal1 @ X21 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(fc2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ~ ( v1_xboole_0 @ ( k1_ordinal1 @ A ) )
        & ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) ) )).

thf('8',plain,(
    ! [X16: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X16 ) )
      | ~ ( v3_ordinal1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc2_ordinal1])).

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
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_ordinal1 @ X17 )
      | ~ ( v3_ordinal1 @ X18 )
      | ( r1_tarski @ X17 @ X18 )
      | ~ ( r1_ordinal1 @ X17 @ X18 ) ) ),
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
    ~ ( r1_tarski @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['3','23'])).

thf('25',plain,(
    ! [X16: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X16 ) )
      | ~ ( v3_ordinal1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc2_ordinal1])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('26',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v3_ordinal1 @ X22 )
      | ( r1_ordinal1 @ X23 @ X22 )
      | ( r2_hidden @ X22 @ X23 )
      | ~ ( v3_ordinal1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('27',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X20 = X19 )
      | ( r2_hidden @ X20 @ X19 )
      | ~ ( r2_hidden @ X20 @ ( k1_ordinal1 @ X19 ) ) ) ),
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

thf('37',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('39',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['5','21','22'])).

thf('41',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['39','40'])).

thf('42',plain,(
    sk_B = sk_A ),
    inference(clc,[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('44',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['24','42','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4OFOz6qtXU
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:17:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.74/1.94  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.74/1.94  % Solved by: fo/fo7.sh
% 1.74/1.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.74/1.94  % done 2394 iterations in 1.496s
% 1.74/1.94  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.74/1.94  % SZS output start Refutation
% 1.74/1.94  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.74/1.94  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 1.74/1.94  thf(sk_A_type, type, sk_A: $i).
% 1.74/1.94  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.74/1.94  thf(sk_B_type, type, sk_B: $i).
% 1.74/1.94  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.74/1.94  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 1.74/1.94  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.74/1.94  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 1.74/1.94  thf(t33_ordinal1, conjecture,
% 1.74/1.94    (![A:$i]:
% 1.74/1.94     ( ( v3_ordinal1 @ A ) =>
% 1.74/1.94       ( ![B:$i]:
% 1.74/1.94         ( ( v3_ordinal1 @ B ) =>
% 1.74/1.94           ( ( r2_hidden @ A @ B ) <=>
% 1.74/1.94             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 1.74/1.94  thf(zf_stmt_0, negated_conjecture,
% 1.74/1.94    (~( ![A:$i]:
% 1.74/1.94        ( ( v3_ordinal1 @ A ) =>
% 1.74/1.94          ( ![B:$i]:
% 1.74/1.94            ( ( v3_ordinal1 @ B ) =>
% 1.74/1.94              ( ( r2_hidden @ A @ B ) <=>
% 1.74/1.94                ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ) )),
% 1.74/1.94    inference('cnf.neg', [status(esa)], [t33_ordinal1])).
% 1.74/1.94  thf('0', plain,
% 1.74/1.94      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 1.74/1.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.94  thf('1', plain,
% 1.74/1.94      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.74/1.94      inference('split', [status(esa)], ['0'])).
% 1.74/1.94  thf(t7_ordinal1, axiom,
% 1.74/1.94    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.74/1.94  thf('2', plain,
% 1.74/1.94      (![X24 : $i, X25 : $i]:
% 1.74/1.94         (~ (r2_hidden @ X24 @ X25) | ~ (r1_tarski @ X25 @ X24))),
% 1.74/1.94      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.74/1.94  thf('3', plain,
% 1.74/1.94      ((~ (r1_tarski @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.74/1.94      inference('sup-', [status(thm)], ['1', '2'])).
% 1.74/1.94  thf('4', plain,
% 1.74/1.94      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 1.74/1.94        | ~ (r2_hidden @ sk_A @ sk_B))),
% 1.74/1.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.95  thf('5', plain,
% 1.74/1.95      (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 1.74/1.95       ~ ((r2_hidden @ sk_A @ sk_B))),
% 1.74/1.95      inference('split', [status(esa)], ['4'])).
% 1.74/1.95  thf(t13_ordinal1, axiom,
% 1.74/1.95    (![A:$i,B:$i]:
% 1.74/1.95     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 1.74/1.95       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 1.74/1.95  thf('6', plain,
% 1.74/1.95      (![X20 : $i, X21 : $i]:
% 1.74/1.95         ((r2_hidden @ X20 @ (k1_ordinal1 @ X21)) | ((X20) != (X21)))),
% 1.74/1.95      inference('cnf', [status(esa)], [t13_ordinal1])).
% 1.74/1.95  thf('7', plain, (![X21 : $i]: (r2_hidden @ X21 @ (k1_ordinal1 @ X21))),
% 1.74/1.95      inference('simplify', [status(thm)], ['6'])).
% 1.74/1.95  thf(fc2_ordinal1, axiom,
% 1.74/1.95    (![A:$i]:
% 1.74/1.95     ( ( v3_ordinal1 @ A ) =>
% 1.74/1.95       ( ( ~( v1_xboole_0 @ ( k1_ordinal1 @ A ) ) ) & 
% 1.74/1.95         ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) ))).
% 1.74/1.95  thf('8', plain,
% 1.74/1.95      (![X16 : $i]:
% 1.74/1.95         ((v3_ordinal1 @ (k1_ordinal1 @ X16)) | ~ (v3_ordinal1 @ X16))),
% 1.74/1.95      inference('cnf', [status(esa)], [fc2_ordinal1])).
% 1.74/1.95  thf('9', plain,
% 1.74/1.95      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 1.74/1.95         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 1.74/1.95      inference('split', [status(esa)], ['0'])).
% 1.74/1.95  thf(redefinition_r1_ordinal1, axiom,
% 1.74/1.95    (![A:$i,B:$i]:
% 1.74/1.95     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 1.74/1.95       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 1.74/1.95  thf('10', plain,
% 1.74/1.95      (![X17 : $i, X18 : $i]:
% 1.74/1.95         (~ (v3_ordinal1 @ X17)
% 1.74/1.95          | ~ (v3_ordinal1 @ X18)
% 1.74/1.95          | (r1_tarski @ X17 @ X18)
% 1.74/1.95          | ~ (r1_ordinal1 @ X17 @ X18))),
% 1.74/1.95      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 1.74/1.95  thf('11', plain,
% 1.74/1.95      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 1.74/1.95         | ~ (v3_ordinal1 @ sk_B)
% 1.74/1.95         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 1.74/1.95         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 1.74/1.95      inference('sup-', [status(thm)], ['9', '10'])).
% 1.74/1.95  thf('12', plain, ((v3_ordinal1 @ sk_B)),
% 1.74/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.95  thf('13', plain,
% 1.74/1.95      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 1.74/1.95         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 1.74/1.95         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 1.74/1.95      inference('demod', [status(thm)], ['11', '12'])).
% 1.74/1.95  thf('14', plain,
% 1.74/1.95      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 1.74/1.95         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 1.74/1.95      inference('sup-', [status(thm)], ['8', '13'])).
% 1.74/1.95  thf('15', plain, ((v3_ordinal1 @ sk_A)),
% 1.74/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.95  thf('16', plain,
% 1.74/1.95      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 1.74/1.95         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 1.74/1.95      inference('demod', [status(thm)], ['14', '15'])).
% 1.74/1.95  thf(d3_tarski, axiom,
% 1.74/1.95    (![A:$i,B:$i]:
% 1.74/1.95     ( ( r1_tarski @ A @ B ) <=>
% 1.74/1.95       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.74/1.95  thf('17', plain,
% 1.74/1.95      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.74/1.95         (~ (r2_hidden @ X2 @ X3)
% 1.74/1.95          | (r2_hidden @ X2 @ X4)
% 1.74/1.95          | ~ (r1_tarski @ X3 @ X4))),
% 1.74/1.95      inference('cnf', [status(esa)], [d3_tarski])).
% 1.74/1.95  thf('18', plain,
% 1.74/1.95      ((![X0 : $i]:
% 1.74/1.95          ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k1_ordinal1 @ sk_A))))
% 1.74/1.95         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 1.74/1.95      inference('sup-', [status(thm)], ['16', '17'])).
% 1.74/1.95  thf('19', plain,
% 1.74/1.95      (((r2_hidden @ sk_A @ sk_B))
% 1.74/1.95         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 1.74/1.95      inference('sup-', [status(thm)], ['7', '18'])).
% 1.74/1.95  thf('20', plain,
% 1.74/1.95      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 1.74/1.95      inference('split', [status(esa)], ['4'])).
% 1.74/1.95  thf('21', plain,
% 1.74/1.95      (((r2_hidden @ sk_A @ sk_B)) | 
% 1.74/1.95       ~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 1.74/1.95      inference('sup-', [status(thm)], ['19', '20'])).
% 1.74/1.95  thf('22', plain,
% 1.74/1.95      (((r2_hidden @ sk_A @ sk_B)) | 
% 1.74/1.95       ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 1.74/1.95      inference('split', [status(esa)], ['0'])).
% 1.74/1.95  thf('23', plain, (((r2_hidden @ sk_A @ sk_B))),
% 1.74/1.95      inference('sat_resolution*', [status(thm)], ['5', '21', '22'])).
% 1.74/1.95  thf('24', plain, (~ (r1_tarski @ sk_B @ sk_A)),
% 1.74/1.95      inference('simpl_trail', [status(thm)], ['3', '23'])).
% 1.74/1.95  thf('25', plain,
% 1.74/1.95      (![X16 : $i]:
% 1.74/1.95         ((v3_ordinal1 @ (k1_ordinal1 @ X16)) | ~ (v3_ordinal1 @ X16))),
% 1.74/1.95      inference('cnf', [status(esa)], [fc2_ordinal1])).
% 1.74/1.95  thf(t26_ordinal1, axiom,
% 1.74/1.95    (![A:$i]:
% 1.74/1.95     ( ( v3_ordinal1 @ A ) =>
% 1.74/1.95       ( ![B:$i]:
% 1.74/1.95         ( ( v3_ordinal1 @ B ) =>
% 1.74/1.95           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 1.74/1.95  thf('26', plain,
% 1.74/1.95      (![X22 : $i, X23 : $i]:
% 1.74/1.95         (~ (v3_ordinal1 @ X22)
% 1.74/1.95          | (r1_ordinal1 @ X23 @ X22)
% 1.74/1.95          | (r2_hidden @ X22 @ X23)
% 1.74/1.95          | ~ (v3_ordinal1 @ X23))),
% 1.74/1.95      inference('cnf', [status(esa)], [t26_ordinal1])).
% 1.74/1.95  thf('27', plain,
% 1.74/1.95      (![X19 : $i, X20 : $i]:
% 1.74/1.95         (((X20) = (X19))
% 1.74/1.95          | (r2_hidden @ X20 @ X19)
% 1.74/1.95          | ~ (r2_hidden @ X20 @ (k1_ordinal1 @ X19)))),
% 1.74/1.95      inference('cnf', [status(esa)], [t13_ordinal1])).
% 1.74/1.95  thf('28', plain,
% 1.74/1.95      (![X0 : $i, X1 : $i]:
% 1.74/1.95         (~ (v3_ordinal1 @ (k1_ordinal1 @ X0))
% 1.74/1.95          | (r1_ordinal1 @ (k1_ordinal1 @ X0) @ X1)
% 1.74/1.95          | ~ (v3_ordinal1 @ X1)
% 1.74/1.95          | (r2_hidden @ X1 @ X0)
% 1.74/1.95          | ((X1) = (X0)))),
% 1.74/1.95      inference('sup-', [status(thm)], ['26', '27'])).
% 1.74/1.95  thf('29', plain,
% 1.74/1.95      (![X0 : $i, X1 : $i]:
% 1.74/1.95         (~ (v3_ordinal1 @ X0)
% 1.74/1.95          | ((X1) = (X0))
% 1.74/1.95          | (r2_hidden @ X1 @ X0)
% 1.74/1.95          | ~ (v3_ordinal1 @ X1)
% 1.74/1.95          | (r1_ordinal1 @ (k1_ordinal1 @ X0) @ X1))),
% 1.74/1.95      inference('sup-', [status(thm)], ['25', '28'])).
% 1.74/1.95  thf('30', plain,
% 1.74/1.95      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 1.74/1.95         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 1.74/1.95      inference('split', [status(esa)], ['4'])).
% 1.74/1.95  thf('31', plain, (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 1.74/1.95      inference('sat_resolution*', [status(thm)], ['5', '21'])).
% 1.74/1.95  thf('32', plain, (~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 1.74/1.95      inference('simpl_trail', [status(thm)], ['30', '31'])).
% 1.74/1.95  thf('33', plain,
% 1.74/1.95      ((~ (v3_ordinal1 @ sk_B)
% 1.74/1.95        | (r2_hidden @ sk_B @ sk_A)
% 1.74/1.95        | ((sk_B) = (sk_A))
% 1.74/1.95        | ~ (v3_ordinal1 @ sk_A))),
% 1.74/1.95      inference('sup-', [status(thm)], ['29', '32'])).
% 1.74/1.95  thf('34', plain, ((v3_ordinal1 @ sk_B)),
% 1.74/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.95  thf('35', plain, ((v3_ordinal1 @ sk_A)),
% 1.74/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.95  thf('36', plain, (((r2_hidden @ sk_B @ sk_A) | ((sk_B) = (sk_A)))),
% 1.74/1.95      inference('demod', [status(thm)], ['33', '34', '35'])).
% 1.74/1.95  thf('37', plain,
% 1.74/1.95      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.74/1.95      inference('split', [status(esa)], ['0'])).
% 1.74/1.95  thf(antisymmetry_r2_hidden, axiom,
% 1.74/1.95    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 1.74/1.95  thf('38', plain,
% 1.74/1.95      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 1.74/1.95      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 1.74/1.95  thf('39', plain,
% 1.74/1.95      ((~ (r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.74/1.95      inference('sup-', [status(thm)], ['37', '38'])).
% 1.74/1.95  thf('40', plain, (((r2_hidden @ sk_A @ sk_B))),
% 1.74/1.95      inference('sat_resolution*', [status(thm)], ['5', '21', '22'])).
% 1.74/1.95  thf('41', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 1.74/1.95      inference('simpl_trail', [status(thm)], ['39', '40'])).
% 1.74/1.95  thf('42', plain, (((sk_B) = (sk_A))),
% 1.74/1.95      inference('clc', [status(thm)], ['36', '41'])).
% 1.74/1.95  thf('43', plain,
% 1.74/1.95      (![X3 : $i, X5 : $i]:
% 1.74/1.95         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 1.74/1.95      inference('cnf', [status(esa)], [d3_tarski])).
% 1.74/1.95  thf('44', plain,
% 1.74/1.95      (![X3 : $i, X5 : $i]:
% 1.74/1.95         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 1.74/1.95      inference('cnf', [status(esa)], [d3_tarski])).
% 1.74/1.95  thf('45', plain,
% 1.74/1.95      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 1.74/1.95      inference('sup-', [status(thm)], ['43', '44'])).
% 1.74/1.95  thf('46', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.74/1.95      inference('simplify', [status(thm)], ['45'])).
% 1.74/1.95  thf('47', plain, ($false),
% 1.74/1.95      inference('demod', [status(thm)], ['24', '42', '46'])).
% 1.74/1.95  
% 1.74/1.95  % SZS output end Refutation
% 1.74/1.95  
% 1.74/1.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

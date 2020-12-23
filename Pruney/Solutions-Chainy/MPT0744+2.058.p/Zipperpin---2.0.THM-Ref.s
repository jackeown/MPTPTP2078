%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.D0s5fdZFIu

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:08 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 195 expanded)
%              Number of leaves         :   13 (  59 expanded)
%              Depth                    :   21
%              Number of atoms          :  487 (1580 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf('0',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('3',plain,
    ( ~ ( r1_tarski @ ( k1_ordinal1 @ sk_B ) @ sk_A )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_ordinal1 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('8',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('12',plain,(
    ! [X4: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X4 ) )
      | ~ ( v3_ordinal1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('13',plain,(
    ! [X4: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X4 ) )
      | ~ ( v3_ordinal1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v3_ordinal1 @ X2 )
      | ( r1_ordinal1 @ X3 @ X2 )
      | ( r2_hidden @ X2 @ X3 )
      | ~ ( v3_ordinal1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_ordinal1 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['4'])).

thf('20',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_B ) @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_B ) @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('25',plain,
    ( ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_B ) @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_B ) ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_B ) @ sk_A )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_B ) ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_B ) @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','27'])).

thf('29',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_B ) @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(t33_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ B )
          <=> ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) )).

thf('31',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v3_ordinal1 @ X5 )
      | ~ ( r1_ordinal1 @ ( k1_ordinal1 @ X6 ) @ X5 )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( v3_ordinal1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t33_ordinal1])).

thf('32',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( r2_hidden @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('37',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
    | ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['11','37'])).

thf('39',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,(
    r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['5','38','39'])).

thf('41',plain,(
    ~ ( r1_tarski @ ( k1_ordinal1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['3','40'])).

thf('42',plain,(
    ! [X4: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X4 ) )
      | ~ ( v3_ordinal1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('43',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v3_ordinal1 @ X2 )
      | ( r1_ordinal1 @ X3 @ X2 )
      | ( r2_hidden @ X2 @ X3 )
      | ~ ( v3_ordinal1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('44',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('45',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r2_hidden @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v3_ordinal1 @ X5 )
      | ~ ( r2_hidden @ X6 @ X5 )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X6 ) @ X5 )
      | ~ ( v3_ordinal1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t33_ordinal1])).

thf('50',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_B ) @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_B ) @ sk_A )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['5','38'])).

thf('55',plain,(
    r1_ordinal1 @ ( k1_ordinal1 @ sk_B ) @ sk_A ),
    inference(simpl_trail,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_ordinal1 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('57',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_B ) @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_B ) @ sk_A )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r1_tarski @ ( k1_ordinal1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['42','59'])).

thf('61',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    r1_tarski @ ( k1_ordinal1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    $false ),
    inference(demod,[status(thm)],['41','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.D0s5fdZFIu
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:36:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 57 iterations in 0.028s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.49  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.22/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.49  thf(t34_ordinal1, conjecture,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( v3_ordinal1 @ A ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( v3_ordinal1 @ B ) =>
% 0.22/0.49           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.22/0.49             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i]:
% 0.22/0.49        ( ( v3_ordinal1 @ A ) =>
% 0.22/0.49          ( ![B:$i]:
% 0.22/0.49            ( ( v3_ordinal1 @ B ) =>
% 0.22/0.49              ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.22/0.49                ( r1_ordinal1 @ A @ B ) ) ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t34_ordinal1])).
% 0.22/0.49  thf('0', plain,
% 0.22/0.49      (((r1_ordinal1 @ sk_A @ sk_B) | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.22/0.49         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf(t7_ordinal1, axiom,
% 0.22/0.49    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      (![X7 : $i, X8 : $i]: (~ (r2_hidden @ X7 @ X8) | ~ (r1_tarski @ X8 @ X7))),
% 0.22/0.49      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      ((~ (r1_tarski @ (k1_ordinal1 @ sk_B) @ sk_A))
% 0.22/0.49         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      ((~ (r1_ordinal1 @ sk_A @ sk_B)
% 0.22/0.49        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.22/0.49       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.22/0.49      inference('split', [status(esa)], ['4'])).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      (((r1_ordinal1 @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf(redefinition_r1_ordinal1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.22/0.49       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (v3_ordinal1 @ X0)
% 0.22/0.49          | ~ (v3_ordinal1 @ X1)
% 0.22/0.49          | (r1_tarski @ X0 @ X1)
% 0.22/0.49          | ~ (r1_ordinal1 @ X0 @ X1))),
% 0.22/0.49      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      ((((r1_tarski @ sk_A @ sk_B)
% 0.22/0.49         | ~ (v3_ordinal1 @ sk_B)
% 0.22/0.49         | ~ (v3_ordinal1 @ sk_A))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.49  thf('9', plain, ((v3_ordinal1 @ sk_B)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('10', plain, ((v3_ordinal1 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      (((r1_tarski @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.22/0.49      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.22/0.49  thf(t29_ordinal1, axiom,
% 0.22/0.49    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      (![X4 : $i]: ((v3_ordinal1 @ (k1_ordinal1 @ X4)) | ~ (v3_ordinal1 @ X4))),
% 0.22/0.49      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.22/0.49  thf('13', plain,
% 0.22/0.49      (![X4 : $i]: ((v3_ordinal1 @ (k1_ordinal1 @ X4)) | ~ (v3_ordinal1 @ X4))),
% 0.22/0.49      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.22/0.49  thf(t26_ordinal1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( v3_ordinal1 @ A ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( v3_ordinal1 @ B ) =>
% 0.22/0.49           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.22/0.49  thf('14', plain,
% 0.22/0.49      (![X2 : $i, X3 : $i]:
% 0.22/0.49         (~ (v3_ordinal1 @ X2)
% 0.22/0.49          | (r1_ordinal1 @ X3 @ X2)
% 0.22/0.49          | (r2_hidden @ X2 @ X3)
% 0.22/0.49          | ~ (v3_ordinal1 @ X3))),
% 0.22/0.49      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.22/0.49  thf('15', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (v3_ordinal1 @ X0)
% 0.22/0.49          | ~ (v3_ordinal1 @ X1)
% 0.22/0.49          | (r1_tarski @ X0 @ X1)
% 0.22/0.49          | ~ (r1_ordinal1 @ X0 @ X1))),
% 0.22/0.49      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.22/0.49  thf('16', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (v3_ordinal1 @ X1)
% 0.22/0.49          | (r2_hidden @ X0 @ X1)
% 0.22/0.49          | ~ (v3_ordinal1 @ X0)
% 0.22/0.49          | (r1_tarski @ X1 @ X0)
% 0.22/0.49          | ~ (v3_ordinal1 @ X0)
% 0.22/0.49          | ~ (v3_ordinal1 @ X1))),
% 0.22/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.49  thf('17', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((r1_tarski @ X1 @ X0)
% 0.22/0.49          | ~ (v3_ordinal1 @ X0)
% 0.22/0.49          | (r2_hidden @ X0 @ X1)
% 0.22/0.49          | ~ (v3_ordinal1 @ X1))),
% 0.22/0.49      inference('simplify', [status(thm)], ['16'])).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (v3_ordinal1 @ X0)
% 0.22/0.49          | (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.22/0.49          | ~ (v3_ordinal1 @ X1)
% 0.22/0.49          | (r1_tarski @ (k1_ordinal1 @ X0) @ X1))),
% 0.22/0.49      inference('sup-', [status(thm)], ['13', '17'])).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.22/0.49         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.22/0.49      inference('split', [status(esa)], ['4'])).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      ((((r1_tarski @ (k1_ordinal1 @ sk_B) @ sk_A)
% 0.22/0.49         | ~ (v3_ordinal1 @ sk_A)
% 0.22/0.49         | ~ (v3_ordinal1 @ sk_B)))
% 0.22/0.49         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.49  thf('21', plain, ((v3_ordinal1 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('22', plain, ((v3_ordinal1 @ sk_B)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('23', plain,
% 0.22/0.49      (((r1_tarski @ (k1_ordinal1 @ sk_B) @ sk_A))
% 0.22/0.49         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.22/0.49      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.22/0.49  thf('24', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (v3_ordinal1 @ X0)
% 0.22/0.49          | ~ (v3_ordinal1 @ X1)
% 0.22/0.49          | (r1_ordinal1 @ X0 @ X1)
% 0.22/0.49          | ~ (r1_tarski @ X0 @ X1))),
% 0.22/0.49      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.22/0.49  thf('25', plain,
% 0.22/0.49      ((((r1_ordinal1 @ (k1_ordinal1 @ sk_B) @ sk_A)
% 0.22/0.49         | ~ (v3_ordinal1 @ sk_A)
% 0.22/0.49         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_B))))
% 0.22/0.49         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.49  thf('26', plain, ((v3_ordinal1 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('27', plain,
% 0.22/0.49      ((((r1_ordinal1 @ (k1_ordinal1 @ sk_B) @ sk_A)
% 0.22/0.49         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_B))))
% 0.22/0.49         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.22/0.49      inference('demod', [status(thm)], ['25', '26'])).
% 0.22/0.49  thf('28', plain,
% 0.22/0.49      (((~ (v3_ordinal1 @ sk_B) | (r1_ordinal1 @ (k1_ordinal1 @ sk_B) @ sk_A)))
% 0.22/0.49         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['12', '27'])).
% 0.22/0.49  thf('29', plain, ((v3_ordinal1 @ sk_B)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('30', plain,
% 0.22/0.49      (((r1_ordinal1 @ (k1_ordinal1 @ sk_B) @ sk_A))
% 0.22/0.49         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.22/0.49      inference('demod', [status(thm)], ['28', '29'])).
% 0.22/0.49  thf(t33_ordinal1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( v3_ordinal1 @ A ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( v3_ordinal1 @ B ) =>
% 0.22/0.49           ( ( r2_hidden @ A @ B ) <=>
% 0.22/0.49             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 0.22/0.49  thf('31', plain,
% 0.22/0.49      (![X5 : $i, X6 : $i]:
% 0.22/0.49         (~ (v3_ordinal1 @ X5)
% 0.22/0.49          | ~ (r1_ordinal1 @ (k1_ordinal1 @ X6) @ X5)
% 0.22/0.49          | (r2_hidden @ X6 @ X5)
% 0.22/0.49          | ~ (v3_ordinal1 @ X6))),
% 0.22/0.49      inference('cnf', [status(esa)], [t33_ordinal1])).
% 0.22/0.49  thf('32', plain,
% 0.22/0.49      (((~ (v3_ordinal1 @ sk_B)
% 0.22/0.49         | (r2_hidden @ sk_B @ sk_A)
% 0.22/0.49         | ~ (v3_ordinal1 @ sk_A)))
% 0.22/0.49         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['30', '31'])).
% 0.22/0.49  thf('33', plain, ((v3_ordinal1 @ sk_B)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('34', plain, ((v3_ordinal1 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('35', plain,
% 0.22/0.49      (((r2_hidden @ sk_B @ sk_A))
% 0.22/0.49         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.22/0.49      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.22/0.49  thf('36', plain,
% 0.22/0.49      (![X7 : $i, X8 : $i]: (~ (r2_hidden @ X7 @ X8) | ~ (r1_tarski @ X8 @ X7))),
% 0.22/0.49      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.22/0.49  thf('37', plain,
% 0.22/0.49      ((~ (r1_tarski @ sk_A @ sk_B))
% 0.22/0.49         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.49  thf('38', plain,
% 0.22/0.49      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) | 
% 0.22/0.49       ~ ((r1_ordinal1 @ sk_A @ sk_B))),
% 0.22/0.49      inference('sup-', [status(thm)], ['11', '37'])).
% 0.22/0.49  thf('39', plain,
% 0.22/0.49      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) | 
% 0.22/0.49       ((r1_ordinal1 @ sk_A @ sk_B))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('40', plain, (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.22/0.49      inference('sat_resolution*', [status(thm)], ['5', '38', '39'])).
% 0.22/0.49  thf('41', plain, (~ (r1_tarski @ (k1_ordinal1 @ sk_B) @ sk_A)),
% 0.22/0.49      inference('simpl_trail', [status(thm)], ['3', '40'])).
% 0.22/0.49  thf('42', plain,
% 0.22/0.49      (![X4 : $i]: ((v3_ordinal1 @ (k1_ordinal1 @ X4)) | ~ (v3_ordinal1 @ X4))),
% 0.22/0.49      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.22/0.49  thf('43', plain,
% 0.22/0.49      (![X2 : $i, X3 : $i]:
% 0.22/0.49         (~ (v3_ordinal1 @ X2)
% 0.22/0.49          | (r1_ordinal1 @ X3 @ X2)
% 0.22/0.49          | (r2_hidden @ X2 @ X3)
% 0.22/0.49          | ~ (v3_ordinal1 @ X3))),
% 0.22/0.49      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.22/0.49  thf('44', plain,
% 0.22/0.49      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.22/0.49      inference('split', [status(esa)], ['4'])).
% 0.22/0.49  thf('45', plain,
% 0.22/0.49      (((~ (v3_ordinal1 @ sk_A)
% 0.22/0.49         | (r2_hidden @ sk_B @ sk_A)
% 0.22/0.49         | ~ (v3_ordinal1 @ sk_B))) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['43', '44'])).
% 0.22/0.49  thf('46', plain, ((v3_ordinal1 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('47', plain, ((v3_ordinal1 @ sk_B)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('48', plain,
% 0.22/0.49      (((r2_hidden @ sk_B @ sk_A)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.22/0.49      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.22/0.49  thf('49', plain,
% 0.22/0.49      (![X5 : $i, X6 : $i]:
% 0.22/0.49         (~ (v3_ordinal1 @ X5)
% 0.22/0.49          | ~ (r2_hidden @ X6 @ X5)
% 0.22/0.49          | (r1_ordinal1 @ (k1_ordinal1 @ X6) @ X5)
% 0.22/0.49          | ~ (v3_ordinal1 @ X6))),
% 0.22/0.49      inference('cnf', [status(esa)], [t33_ordinal1])).
% 0.22/0.49  thf('50', plain,
% 0.22/0.49      (((~ (v3_ordinal1 @ sk_B)
% 0.22/0.49         | (r1_ordinal1 @ (k1_ordinal1 @ sk_B) @ sk_A)
% 0.22/0.49         | ~ (v3_ordinal1 @ sk_A))) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['48', '49'])).
% 0.22/0.49  thf('51', plain, ((v3_ordinal1 @ sk_B)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('52', plain, ((v3_ordinal1 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('53', plain,
% 0.22/0.49      (((r1_ordinal1 @ (k1_ordinal1 @ sk_B) @ sk_A))
% 0.22/0.49         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.22/0.49      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.22/0.49  thf('54', plain, (~ ((r1_ordinal1 @ sk_A @ sk_B))),
% 0.22/0.49      inference('sat_resolution*', [status(thm)], ['5', '38'])).
% 0.22/0.49  thf('55', plain, ((r1_ordinal1 @ (k1_ordinal1 @ sk_B) @ sk_A)),
% 0.22/0.49      inference('simpl_trail', [status(thm)], ['53', '54'])).
% 0.22/0.49  thf('56', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (v3_ordinal1 @ X0)
% 0.22/0.49          | ~ (v3_ordinal1 @ X1)
% 0.22/0.49          | (r1_tarski @ X0 @ X1)
% 0.22/0.49          | ~ (r1_ordinal1 @ X0 @ X1))),
% 0.22/0.49      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.22/0.49  thf('57', plain,
% 0.22/0.49      (((r1_tarski @ (k1_ordinal1 @ sk_B) @ sk_A)
% 0.22/0.49        | ~ (v3_ordinal1 @ sk_A)
% 0.22/0.49        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_B)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['55', '56'])).
% 0.22/0.49  thf('58', plain, ((v3_ordinal1 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('59', plain,
% 0.22/0.49      (((r1_tarski @ (k1_ordinal1 @ sk_B) @ sk_A)
% 0.22/0.49        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_B)))),
% 0.22/0.49      inference('demod', [status(thm)], ['57', '58'])).
% 0.22/0.49  thf('60', plain,
% 0.22/0.49      ((~ (v3_ordinal1 @ sk_B) | (r1_tarski @ (k1_ordinal1 @ sk_B) @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['42', '59'])).
% 0.22/0.49  thf('61', plain, ((v3_ordinal1 @ sk_B)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('62', plain, ((r1_tarski @ (k1_ordinal1 @ sk_B) @ sk_A)),
% 0.22/0.49      inference('demod', [status(thm)], ['60', '61'])).
% 0.22/0.49  thf('63', plain, ($false), inference('demod', [status(thm)], ['41', '62'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

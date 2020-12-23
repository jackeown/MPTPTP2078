%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KOCB8jwukv

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:56 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 189 expanded)
%              Number of leaves         :   16 (  56 expanded)
%              Depth                    :   28
%              Number of atoms          :  486 (1484 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('0',plain,(
    ! [X14: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X14 ) )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X10 = X9 )
      | ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ ( k1_ordinal1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_ordinal1 @ X0 ) ) @ X0 )
      | ( ( sk_C @ X1 @ ( k1_ordinal1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v3_ordinal1 @ X12 )
      | ( r1_ordinal1 @ X13 @ X12 )
      | ( r2_hidden @ X12 @ X13 )
      | ~ ( v3_ordinal1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

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

thf('5',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('8',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['9'])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('11',plain,(
    ! [X8: $i] :
      ( r2_hidden @ X8 @ ( k1_ordinal1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('12',plain,(
    ! [X14: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X14 ) )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('13',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v3_ordinal1 @ X6 )
      | ~ ( v3_ordinal1 @ X7 )
      | ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_ordinal1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('15',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_B )
        | ~ ( r2_hidden @ X0 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['11','22'])).

thf('24',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['9'])).

thf('25',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('27',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['10','25','26'])).

thf('28',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['8','27'])).

thf('29',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','28'])).

thf('30',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    r1_ordinal1 @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v3_ordinal1 @ X6 )
      | ~ ( v3_ordinal1 @ X7 )
      | ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_ordinal1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('34',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ ( k1_ordinal1 @ sk_A ) )
        = sk_A )
      | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_ordinal1 @ sk_A ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','39'])).

thf('41',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('42',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ( ( sk_C @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      = sk_A )
    | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( sk_C @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      = sk_A )
    | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('45',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('47',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['10','25','26'])).

thf('48',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(simpl_trail,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,(
    r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v3_ordinal1 @ X6 )
      | ~ ( v3_ordinal1 @ X7 )
      | ( r1_ordinal1 @ X6 @ X7 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('52',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['9'])).

thf('56',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['10','25'])).

thf('57',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['54','57'])).

thf('59',plain,(
    ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','58'])).

thf('60',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    $false ),
    inference(demod,[status(thm)],['59','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KOCB8jwukv
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:39:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.57  % Solved by: fo/fo7.sh
% 0.20/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.57  % done 342 iterations in 0.115s
% 0.20/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.57  % SZS output start Refutation
% 0.20/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.57  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.20/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.57  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.20/0.57  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.20/0.57  thf(t29_ordinal1, axiom,
% 0.20/0.57    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 0.20/0.57  thf('0', plain,
% 0.20/0.57      (![X14 : $i]:
% 0.20/0.57         ((v3_ordinal1 @ (k1_ordinal1 @ X14)) | ~ (v3_ordinal1 @ X14))),
% 0.20/0.57      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.20/0.57  thf(d3_tarski, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.57  thf('1', plain,
% 0.20/0.57      (![X3 : $i, X5 : $i]:
% 0.20/0.57         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.20/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.57  thf(t13_ordinal1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.20/0.57       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.20/0.57  thf('2', plain,
% 0.20/0.57      (![X9 : $i, X10 : $i]:
% 0.20/0.57         (((X10) = (X9))
% 0.20/0.57          | (r2_hidden @ X10 @ X9)
% 0.20/0.57          | ~ (r2_hidden @ X10 @ (k1_ordinal1 @ X9)))),
% 0.20/0.57      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.20/0.57  thf('3', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((r1_tarski @ (k1_ordinal1 @ X0) @ X1)
% 0.20/0.57          | (r2_hidden @ (sk_C @ X1 @ (k1_ordinal1 @ X0)) @ X0)
% 0.20/0.57          | ((sk_C @ X1 @ (k1_ordinal1 @ X0)) = (X0)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.57  thf(t26_ordinal1, axiom,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( v3_ordinal1 @ A ) =>
% 0.20/0.57       ( ![B:$i]:
% 0.20/0.57         ( ( v3_ordinal1 @ B ) =>
% 0.20/0.57           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.57  thf('4', plain,
% 0.20/0.57      (![X12 : $i, X13 : $i]:
% 0.20/0.57         (~ (v3_ordinal1 @ X12)
% 0.20/0.57          | (r1_ordinal1 @ X13 @ X12)
% 0.20/0.57          | (r2_hidden @ X12 @ X13)
% 0.20/0.57          | ~ (v3_ordinal1 @ X13))),
% 0.20/0.57      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.20/0.57  thf(t33_ordinal1, conjecture,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( v3_ordinal1 @ A ) =>
% 0.20/0.57       ( ![B:$i]:
% 0.20/0.57         ( ( v3_ordinal1 @ B ) =>
% 0.20/0.57           ( ( r2_hidden @ A @ B ) <=>
% 0.20/0.57             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 0.20/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.57    (~( ![A:$i]:
% 0.20/0.57        ( ( v3_ordinal1 @ A ) =>
% 0.20/0.57          ( ![B:$i]:
% 0.20/0.57            ( ( v3_ordinal1 @ B ) =>
% 0.20/0.57              ( ( r2_hidden @ A @ B ) <=>
% 0.20/0.57                ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ) )),
% 0.20/0.57    inference('cnf.neg', [status(esa)], [t33_ordinal1])).
% 0.20/0.57  thf('5', plain,
% 0.20/0.57      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('6', plain,
% 0.20/0.57      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.20/0.57      inference('split', [status(esa)], ['5'])).
% 0.20/0.57  thf(antisymmetry_r2_hidden, axiom,
% 0.20/0.57    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.20/0.57  thf('7', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.57      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.20/0.57  thf('8', plain,
% 0.20/0.57      ((~ (r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.57  thf('9', plain,
% 0.20/0.57      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.20/0.57        | ~ (r2_hidden @ sk_A @ sk_B))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('10', plain,
% 0.20/0.57      (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 0.20/0.57       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.20/0.57      inference('split', [status(esa)], ['9'])).
% 0.20/0.57  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.20/0.57  thf('11', plain, (![X8 : $i]: (r2_hidden @ X8 @ (k1_ordinal1 @ X8))),
% 0.20/0.57      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.20/0.57  thf('12', plain,
% 0.20/0.57      (![X14 : $i]:
% 0.20/0.57         ((v3_ordinal1 @ (k1_ordinal1 @ X14)) | ~ (v3_ordinal1 @ X14))),
% 0.20/0.57      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.20/0.57  thf('13', plain,
% 0.20/0.57      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.20/0.57         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.20/0.57      inference('split', [status(esa)], ['5'])).
% 0.20/0.57  thf(redefinition_r1_ordinal1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.20/0.57       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.20/0.57  thf('14', plain,
% 0.20/0.57      (![X6 : $i, X7 : $i]:
% 0.20/0.57         (~ (v3_ordinal1 @ X6)
% 0.20/0.57          | ~ (v3_ordinal1 @ X7)
% 0.20/0.57          | (r1_tarski @ X6 @ X7)
% 0.20/0.57          | ~ (r1_ordinal1 @ X6 @ X7))),
% 0.20/0.57      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.20/0.57  thf('15', plain,
% 0.20/0.57      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.20/0.57         | ~ (v3_ordinal1 @ sk_B)
% 0.20/0.57         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.20/0.57         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.57  thf('16', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('17', plain,
% 0.20/0.57      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.20/0.57         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.20/0.57         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.20/0.57      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.57  thf('18', plain,
% 0.20/0.57      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 0.20/0.57         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['12', '17'])).
% 0.20/0.57  thf('19', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('20', plain,
% 0.20/0.57      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.20/0.57         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.20/0.57      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.57  thf('21', plain,
% 0.20/0.57      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.57         (~ (r2_hidden @ X2 @ X3)
% 0.20/0.57          | (r2_hidden @ X2 @ X4)
% 0.20/0.57          | ~ (r1_tarski @ X3 @ X4))),
% 0.20/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.57  thf('22', plain,
% 0.20/0.57      ((![X0 : $i]:
% 0.20/0.57          ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k1_ordinal1 @ sk_A))))
% 0.20/0.57         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.57  thf('23', plain,
% 0.20/0.57      (((r2_hidden @ sk_A @ sk_B))
% 0.20/0.57         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['11', '22'])).
% 0.20/0.57  thf('24', plain,
% 0.20/0.57      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.20/0.57      inference('split', [status(esa)], ['9'])).
% 0.20/0.57  thf('25', plain,
% 0.20/0.57      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.20/0.57       ~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.20/0.57      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.57  thf('26', plain,
% 0.20/0.57      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.20/0.57       ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.20/0.57      inference('split', [status(esa)], ['5'])).
% 0.20/0.57  thf('27', plain, (((r2_hidden @ sk_A @ sk_B))),
% 0.20/0.57      inference('sat_resolution*', [status(thm)], ['10', '25', '26'])).
% 0.20/0.57  thf('28', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 0.20/0.57      inference('simpl_trail', [status(thm)], ['8', '27'])).
% 0.20/0.57  thf('29', plain,
% 0.20/0.57      ((~ (v3_ordinal1 @ sk_A)
% 0.20/0.57        | (r1_ordinal1 @ sk_A @ sk_B)
% 0.20/0.57        | ~ (v3_ordinal1 @ sk_B))),
% 0.20/0.57      inference('sup-', [status(thm)], ['4', '28'])).
% 0.20/0.57  thf('30', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('31', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('32', plain, ((r1_ordinal1 @ sk_A @ sk_B)),
% 0.20/0.57      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.20/0.57  thf('33', plain,
% 0.20/0.57      (![X6 : $i, X7 : $i]:
% 0.20/0.57         (~ (v3_ordinal1 @ X6)
% 0.20/0.57          | ~ (v3_ordinal1 @ X7)
% 0.20/0.57          | (r1_tarski @ X6 @ X7)
% 0.20/0.57          | ~ (r1_ordinal1 @ X6 @ X7))),
% 0.20/0.57      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.20/0.57  thf('34', plain,
% 0.20/0.57      (((r1_tarski @ sk_A @ sk_B)
% 0.20/0.57        | ~ (v3_ordinal1 @ sk_B)
% 0.20/0.57        | ~ (v3_ordinal1 @ sk_A))),
% 0.20/0.57      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.57  thf('35', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('36', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('37', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.20/0.57      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.20/0.57  thf('38', plain,
% 0.20/0.57      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.57         (~ (r2_hidden @ X2 @ X3)
% 0.20/0.57          | (r2_hidden @ X2 @ X4)
% 0.20/0.57          | ~ (r1_tarski @ X3 @ X4))),
% 0.20/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.57  thf('39', plain,
% 0.20/0.57      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.57      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.57  thf('40', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (((sk_C @ X0 @ (k1_ordinal1 @ sk_A)) = (sk_A))
% 0.20/0.57          | (r1_tarski @ (k1_ordinal1 @ sk_A) @ X0)
% 0.20/0.57          | (r2_hidden @ (sk_C @ X0 @ (k1_ordinal1 @ sk_A)) @ sk_B))),
% 0.20/0.57      inference('sup-', [status(thm)], ['3', '39'])).
% 0.20/0.57  thf('41', plain,
% 0.20/0.57      (![X3 : $i, X5 : $i]:
% 0.20/0.57         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.20/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.57  thf('42', plain,
% 0.20/0.57      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.20/0.57        | ((sk_C @ sk_B @ (k1_ordinal1 @ sk_A)) = (sk_A))
% 0.20/0.57        | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.20/0.57      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.57  thf('43', plain,
% 0.20/0.57      ((((sk_C @ sk_B @ (k1_ordinal1 @ sk_A)) = (sk_A))
% 0.20/0.57        | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.20/0.57      inference('simplify', [status(thm)], ['42'])).
% 0.20/0.57  thf('44', plain,
% 0.20/0.57      (![X3 : $i, X5 : $i]:
% 0.20/0.57         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.20/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.57  thf('45', plain,
% 0.20/0.57      ((~ (r2_hidden @ sk_A @ sk_B)
% 0.20/0.57        | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.20/0.57        | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.20/0.57      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.57  thf('46', plain,
% 0.20/0.57      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.20/0.57      inference('split', [status(esa)], ['5'])).
% 0.20/0.57  thf('47', plain, (((r2_hidden @ sk_A @ sk_B))),
% 0.20/0.57      inference('sat_resolution*', [status(thm)], ['10', '25', '26'])).
% 0.20/0.57  thf('48', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.20/0.57      inference('simpl_trail', [status(thm)], ['46', '47'])).
% 0.20/0.57  thf('49', plain,
% 0.20/0.57      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.20/0.57        | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.20/0.57      inference('demod', [status(thm)], ['45', '48'])).
% 0.20/0.57  thf('50', plain, ((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 0.20/0.57      inference('simplify', [status(thm)], ['49'])).
% 0.20/0.57  thf('51', plain,
% 0.20/0.57      (![X6 : $i, X7 : $i]:
% 0.20/0.57         (~ (v3_ordinal1 @ X6)
% 0.20/0.57          | ~ (v3_ordinal1 @ X7)
% 0.20/0.57          | (r1_ordinal1 @ X6 @ X7)
% 0.20/0.57          | ~ (r1_tarski @ X6 @ X7))),
% 0.20/0.57      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.20/0.57  thf('52', plain,
% 0.20/0.57      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.20/0.57        | ~ (v3_ordinal1 @ sk_B)
% 0.20/0.57        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.57  thf('53', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('54', plain,
% 0.20/0.57      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.20/0.57        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A)))),
% 0.20/0.57      inference('demod', [status(thm)], ['52', '53'])).
% 0.20/0.57  thf('55', plain,
% 0.20/0.57      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.20/0.57         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.20/0.57      inference('split', [status(esa)], ['9'])).
% 0.20/0.57  thf('56', plain, (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.20/0.57      inference('sat_resolution*', [status(thm)], ['10', '25'])).
% 0.20/0.57  thf('57', plain, (~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 0.20/0.57      inference('simpl_trail', [status(thm)], ['55', '56'])).
% 0.20/0.57  thf('58', plain, (~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))),
% 0.20/0.57      inference('clc', [status(thm)], ['54', '57'])).
% 0.20/0.57  thf('59', plain, (~ (v3_ordinal1 @ sk_A)),
% 0.20/0.57      inference('sup-', [status(thm)], ['0', '58'])).
% 0.20/0.57  thf('60', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('61', plain, ($false), inference('demod', [status(thm)], ['59', '60'])).
% 0.20/0.57  
% 0.20/0.57  % SZS output end Refutation
% 0.20/0.57  
% 0.20/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0yzG2VhqWe

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:59 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 196 expanded)
%              Number of leaves         :   16 (  57 expanded)
%              Depth                    :   26
%              Number of atoms          :  552 (1560 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('0',plain,(
    ! [X13: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X13 ) )
      | ~ ( v3_ordinal1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

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

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X11 = X10 )
      | ( r2_hidden @ X11 @ X10 )
      | ~ ( r2_hidden @ X11 @ ( k1_ordinal1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_ordinal1 @ X0 ) ) @ X0 )
      | ( ( sk_C @ X1 @ ( k1_ordinal1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

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

thf('4',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(connectedness_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
        | ( r1_ordinal1 @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v3_ordinal1 @ X4 )
      | ~ ( v3_ordinal1 @ X5 )
      | ( r1_ordinal1 @ X4 @ X5 )
      | ( r1_ordinal1 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v3_ordinal1 @ X7 )
      | ~ ( v3_ordinal1 @ X8 )
      | ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_ordinal1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v3_ordinal1 @ X7 )
      | ~ ( v3_ordinal1 @ X8 )
      | ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_ordinal1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ( r1_tarski @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ( r1_tarski @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['17'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('19',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('20',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['21'])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('23',plain,(
    ! [X9: $i] :
      ( r2_hidden @ X9 @ ( k1_ordinal1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('24',plain,(
    ! [X13: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X13 ) )
      | ~ ( v3_ordinal1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('25',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['17'])).

thf('26',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v3_ordinal1 @ X7 )
      | ~ ( v3_ordinal1 @ X8 )
      | ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_ordinal1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('27',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_B )
        | ~ ( r2_hidden @ X0 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['23','34'])).

thf('36',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['21'])).

thf('37',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['17'])).

thf('39',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['22','37','38'])).

thf('40',plain,(
    ~ ( r1_tarski @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['20','39'])).

thf('41',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['16','40'])).

thf('42',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ ( k1_ordinal1 @ sk_A ) )
        = sk_A )
      | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_ordinal1 @ sk_A ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','45'])).

thf('47',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('48',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ( ( sk_C @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      = sk_A )
    | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( sk_C @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      = sk_A )
    | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('51',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['17'])).

thf('53',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['22','37','38'])).

thf('54',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(simpl_trail,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('56',plain,(
    r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v3_ordinal1 @ X7 )
      | ~ ( v3_ordinal1 @ X8 )
      | ( r1_ordinal1 @ X7 @ X8 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('58',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['21'])).

thf('62',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['22','37'])).

thf('63',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['61','62'])).

thf('64',plain,(
    ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['60','63'])).

thf('65',plain,(
    ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','64'])).

thf('66',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['65','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0yzG2VhqWe
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:26:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.44/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.68  % Solved by: fo/fo7.sh
% 0.44/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.68  % done 437 iterations in 0.222s
% 0.44/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.68  % SZS output start Refutation
% 0.44/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.68  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.44/0.68  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.44/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.68  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.44/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.68  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.44/0.68  thf(t29_ordinal1, axiom,
% 0.44/0.68    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 0.44/0.68  thf('0', plain,
% 0.44/0.68      (![X13 : $i]:
% 0.44/0.68         ((v3_ordinal1 @ (k1_ordinal1 @ X13)) | ~ (v3_ordinal1 @ X13))),
% 0.44/0.68      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.44/0.68  thf(d3_tarski, axiom,
% 0.44/0.68    (![A:$i,B:$i]:
% 0.44/0.68     ( ( r1_tarski @ A @ B ) <=>
% 0.44/0.68       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.44/0.68  thf('1', plain,
% 0.44/0.68      (![X1 : $i, X3 : $i]:
% 0.44/0.68         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.44/0.68      inference('cnf', [status(esa)], [d3_tarski])).
% 0.44/0.68  thf(t13_ordinal1, axiom,
% 0.44/0.68    (![A:$i,B:$i]:
% 0.44/0.68     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.44/0.68       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.44/0.68  thf('2', plain,
% 0.44/0.68      (![X10 : $i, X11 : $i]:
% 0.44/0.68         (((X11) = (X10))
% 0.44/0.68          | (r2_hidden @ X11 @ X10)
% 0.44/0.68          | ~ (r2_hidden @ X11 @ (k1_ordinal1 @ X10)))),
% 0.44/0.68      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.44/0.68  thf('3', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i]:
% 0.44/0.68         ((r1_tarski @ (k1_ordinal1 @ X0) @ X1)
% 0.44/0.68          | (r2_hidden @ (sk_C @ X1 @ (k1_ordinal1 @ X0)) @ X0)
% 0.44/0.68          | ((sk_C @ X1 @ (k1_ordinal1 @ X0)) = (X0)))),
% 0.44/0.68      inference('sup-', [status(thm)], ['1', '2'])).
% 0.44/0.68  thf(t33_ordinal1, conjecture,
% 0.44/0.68    (![A:$i]:
% 0.44/0.68     ( ( v3_ordinal1 @ A ) =>
% 0.44/0.68       ( ![B:$i]:
% 0.44/0.68         ( ( v3_ordinal1 @ B ) =>
% 0.44/0.68           ( ( r2_hidden @ A @ B ) <=>
% 0.44/0.68             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 0.44/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.68    (~( ![A:$i]:
% 0.44/0.68        ( ( v3_ordinal1 @ A ) =>
% 0.44/0.68          ( ![B:$i]:
% 0.44/0.68            ( ( v3_ordinal1 @ B ) =>
% 0.44/0.68              ( ( r2_hidden @ A @ B ) <=>
% 0.44/0.68                ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ) )),
% 0.44/0.68    inference('cnf.neg', [status(esa)], [t33_ordinal1])).
% 0.44/0.68  thf('4', plain, ((v3_ordinal1 @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf(connectedness_r1_ordinal1, axiom,
% 0.44/0.68    (![A:$i,B:$i]:
% 0.44/0.68     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.44/0.68       ( ( r1_ordinal1 @ A @ B ) | ( r1_ordinal1 @ B @ A ) ) ))).
% 0.44/0.68  thf('5', plain,
% 0.44/0.68      (![X4 : $i, X5 : $i]:
% 0.44/0.68         (~ (v3_ordinal1 @ X4)
% 0.44/0.68          | ~ (v3_ordinal1 @ X5)
% 0.44/0.68          | (r1_ordinal1 @ X4 @ X5)
% 0.44/0.68          | (r1_ordinal1 @ X5 @ X4))),
% 0.44/0.68      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.44/0.68  thf('6', plain,
% 0.44/0.68      (![X0 : $i]:
% 0.44/0.68         ((r1_ordinal1 @ X0 @ sk_A)
% 0.44/0.68          | (r1_ordinal1 @ sk_A @ X0)
% 0.44/0.68          | ~ (v3_ordinal1 @ X0))),
% 0.44/0.68      inference('sup-', [status(thm)], ['4', '5'])).
% 0.44/0.68  thf(redefinition_r1_ordinal1, axiom,
% 0.44/0.68    (![A:$i,B:$i]:
% 0.44/0.68     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.44/0.68       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.44/0.68  thf('7', plain,
% 0.44/0.68      (![X7 : $i, X8 : $i]:
% 0.44/0.68         (~ (v3_ordinal1 @ X7)
% 0.44/0.68          | ~ (v3_ordinal1 @ X8)
% 0.44/0.68          | (r1_tarski @ X7 @ X8)
% 0.44/0.68          | ~ (r1_ordinal1 @ X7 @ X8))),
% 0.44/0.68      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.44/0.68  thf('8', plain,
% 0.44/0.68      (![X0 : $i]:
% 0.44/0.68         (~ (v3_ordinal1 @ X0)
% 0.44/0.68          | (r1_ordinal1 @ sk_A @ X0)
% 0.44/0.68          | (r1_tarski @ X0 @ sk_A)
% 0.44/0.68          | ~ (v3_ordinal1 @ sk_A)
% 0.44/0.68          | ~ (v3_ordinal1 @ X0))),
% 0.44/0.68      inference('sup-', [status(thm)], ['6', '7'])).
% 0.44/0.68  thf('9', plain, ((v3_ordinal1 @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('10', plain,
% 0.44/0.68      (![X0 : $i]:
% 0.44/0.68         (~ (v3_ordinal1 @ X0)
% 0.44/0.68          | (r1_ordinal1 @ sk_A @ X0)
% 0.44/0.68          | (r1_tarski @ X0 @ sk_A)
% 0.44/0.68          | ~ (v3_ordinal1 @ X0))),
% 0.44/0.68      inference('demod', [status(thm)], ['8', '9'])).
% 0.44/0.68  thf('11', plain,
% 0.44/0.68      (![X0 : $i]:
% 0.44/0.68         ((r1_tarski @ X0 @ sk_A)
% 0.44/0.68          | (r1_ordinal1 @ sk_A @ X0)
% 0.44/0.68          | ~ (v3_ordinal1 @ X0))),
% 0.44/0.68      inference('simplify', [status(thm)], ['10'])).
% 0.44/0.68  thf('12', plain,
% 0.44/0.68      (![X7 : $i, X8 : $i]:
% 0.44/0.68         (~ (v3_ordinal1 @ X7)
% 0.44/0.68          | ~ (v3_ordinal1 @ X8)
% 0.44/0.68          | (r1_tarski @ X7 @ X8)
% 0.44/0.68          | ~ (r1_ordinal1 @ X7 @ X8))),
% 0.44/0.68      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.44/0.68  thf('13', plain,
% 0.44/0.68      (![X0 : $i]:
% 0.44/0.68         (~ (v3_ordinal1 @ X0)
% 0.44/0.68          | (r1_tarski @ X0 @ sk_A)
% 0.44/0.68          | (r1_tarski @ sk_A @ X0)
% 0.44/0.68          | ~ (v3_ordinal1 @ X0)
% 0.44/0.68          | ~ (v3_ordinal1 @ sk_A))),
% 0.44/0.68      inference('sup-', [status(thm)], ['11', '12'])).
% 0.44/0.68  thf('14', plain, ((v3_ordinal1 @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('15', plain,
% 0.44/0.68      (![X0 : $i]:
% 0.44/0.68         (~ (v3_ordinal1 @ X0)
% 0.44/0.68          | (r1_tarski @ X0 @ sk_A)
% 0.44/0.68          | (r1_tarski @ sk_A @ X0)
% 0.44/0.68          | ~ (v3_ordinal1 @ X0))),
% 0.44/0.68      inference('demod', [status(thm)], ['13', '14'])).
% 0.44/0.68  thf('16', plain,
% 0.44/0.68      (![X0 : $i]:
% 0.44/0.68         ((r1_tarski @ sk_A @ X0)
% 0.44/0.68          | (r1_tarski @ X0 @ sk_A)
% 0.44/0.68          | ~ (v3_ordinal1 @ X0))),
% 0.44/0.68      inference('simplify', [status(thm)], ['15'])).
% 0.44/0.68  thf('17', plain,
% 0.44/0.68      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('18', plain,
% 0.44/0.68      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.44/0.68      inference('split', [status(esa)], ['17'])).
% 0.44/0.68  thf(t7_ordinal1, axiom,
% 0.44/0.68    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.44/0.68  thf('19', plain,
% 0.44/0.68      (![X14 : $i, X15 : $i]:
% 0.44/0.68         (~ (r2_hidden @ X14 @ X15) | ~ (r1_tarski @ X15 @ X14))),
% 0.44/0.68      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.44/0.68  thf('20', plain,
% 0.44/0.68      ((~ (r1_tarski @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.44/0.68      inference('sup-', [status(thm)], ['18', '19'])).
% 0.44/0.68  thf('21', plain,
% 0.44/0.68      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.44/0.68        | ~ (r2_hidden @ sk_A @ sk_B))),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('22', plain,
% 0.44/0.68      (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 0.44/0.68       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.44/0.68      inference('split', [status(esa)], ['21'])).
% 0.44/0.68  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.44/0.68  thf('23', plain, (![X9 : $i]: (r2_hidden @ X9 @ (k1_ordinal1 @ X9))),
% 0.44/0.68      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.44/0.68  thf('24', plain,
% 0.44/0.68      (![X13 : $i]:
% 0.44/0.68         ((v3_ordinal1 @ (k1_ordinal1 @ X13)) | ~ (v3_ordinal1 @ X13))),
% 0.44/0.68      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.44/0.68  thf('25', plain,
% 0.44/0.68      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.44/0.68         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.44/0.68      inference('split', [status(esa)], ['17'])).
% 0.44/0.68  thf('26', plain,
% 0.44/0.68      (![X7 : $i, X8 : $i]:
% 0.44/0.68         (~ (v3_ordinal1 @ X7)
% 0.44/0.68          | ~ (v3_ordinal1 @ X8)
% 0.44/0.68          | (r1_tarski @ X7 @ X8)
% 0.44/0.68          | ~ (r1_ordinal1 @ X7 @ X8))),
% 0.44/0.68      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.44/0.68  thf('27', plain,
% 0.44/0.68      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.44/0.68         | ~ (v3_ordinal1 @ sk_B)
% 0.44/0.68         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.44/0.68         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.44/0.68      inference('sup-', [status(thm)], ['25', '26'])).
% 0.44/0.68  thf('28', plain, ((v3_ordinal1 @ sk_B)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('29', plain,
% 0.44/0.68      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.44/0.68         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.44/0.68         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.44/0.68      inference('demod', [status(thm)], ['27', '28'])).
% 0.44/0.68  thf('30', plain,
% 0.44/0.68      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 0.44/0.68         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.44/0.68      inference('sup-', [status(thm)], ['24', '29'])).
% 0.44/0.68  thf('31', plain, ((v3_ordinal1 @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('32', plain,
% 0.44/0.68      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.44/0.68         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.44/0.68      inference('demod', [status(thm)], ['30', '31'])).
% 0.44/0.68  thf('33', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.68         (~ (r2_hidden @ X0 @ X1)
% 0.44/0.68          | (r2_hidden @ X0 @ X2)
% 0.44/0.68          | ~ (r1_tarski @ X1 @ X2))),
% 0.44/0.68      inference('cnf', [status(esa)], [d3_tarski])).
% 0.44/0.68  thf('34', plain,
% 0.44/0.68      ((![X0 : $i]:
% 0.44/0.68          ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k1_ordinal1 @ sk_A))))
% 0.44/0.68         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.44/0.68      inference('sup-', [status(thm)], ['32', '33'])).
% 0.44/0.68  thf('35', plain,
% 0.44/0.68      (((r2_hidden @ sk_A @ sk_B))
% 0.44/0.68         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.44/0.68      inference('sup-', [status(thm)], ['23', '34'])).
% 0.44/0.68  thf('36', plain,
% 0.44/0.68      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.44/0.68      inference('split', [status(esa)], ['21'])).
% 0.44/0.68  thf('37', plain,
% 0.44/0.68      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.44/0.68       ~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.44/0.68      inference('sup-', [status(thm)], ['35', '36'])).
% 0.44/0.68  thf('38', plain,
% 0.44/0.68      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.44/0.68       ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.44/0.68      inference('split', [status(esa)], ['17'])).
% 0.44/0.68  thf('39', plain, (((r2_hidden @ sk_A @ sk_B))),
% 0.44/0.68      inference('sat_resolution*', [status(thm)], ['22', '37', '38'])).
% 0.44/0.68  thf('40', plain, (~ (r1_tarski @ sk_B @ sk_A)),
% 0.44/0.68      inference('simpl_trail', [status(thm)], ['20', '39'])).
% 0.44/0.68  thf('41', plain, ((~ (v3_ordinal1 @ sk_B) | (r1_tarski @ sk_A @ sk_B))),
% 0.44/0.68      inference('sup-', [status(thm)], ['16', '40'])).
% 0.44/0.68  thf('42', plain, ((v3_ordinal1 @ sk_B)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('43', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.44/0.68      inference('demod', [status(thm)], ['41', '42'])).
% 0.44/0.68  thf('44', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.68         (~ (r2_hidden @ X0 @ X1)
% 0.44/0.68          | (r2_hidden @ X0 @ X2)
% 0.44/0.68          | ~ (r1_tarski @ X1 @ X2))),
% 0.44/0.68      inference('cnf', [status(esa)], [d3_tarski])).
% 0.44/0.68  thf('45', plain,
% 0.44/0.68      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.44/0.68      inference('sup-', [status(thm)], ['43', '44'])).
% 0.44/0.68  thf('46', plain,
% 0.44/0.68      (![X0 : $i]:
% 0.44/0.68         (((sk_C @ X0 @ (k1_ordinal1 @ sk_A)) = (sk_A))
% 0.44/0.68          | (r1_tarski @ (k1_ordinal1 @ sk_A) @ X0)
% 0.44/0.68          | (r2_hidden @ (sk_C @ X0 @ (k1_ordinal1 @ sk_A)) @ sk_B))),
% 0.44/0.68      inference('sup-', [status(thm)], ['3', '45'])).
% 0.44/0.68  thf('47', plain,
% 0.44/0.68      (![X1 : $i, X3 : $i]:
% 0.44/0.68         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.44/0.68      inference('cnf', [status(esa)], [d3_tarski])).
% 0.44/0.68  thf('48', plain,
% 0.44/0.68      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.44/0.68        | ((sk_C @ sk_B @ (k1_ordinal1 @ sk_A)) = (sk_A))
% 0.44/0.68        | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.44/0.68      inference('sup-', [status(thm)], ['46', '47'])).
% 0.44/0.68  thf('49', plain,
% 0.44/0.68      ((((sk_C @ sk_B @ (k1_ordinal1 @ sk_A)) = (sk_A))
% 0.44/0.68        | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.44/0.68      inference('simplify', [status(thm)], ['48'])).
% 0.44/0.68  thf('50', plain,
% 0.44/0.68      (![X1 : $i, X3 : $i]:
% 0.44/0.68         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.44/0.68      inference('cnf', [status(esa)], [d3_tarski])).
% 0.44/0.68  thf('51', plain,
% 0.44/0.68      ((~ (r2_hidden @ sk_A @ sk_B)
% 0.44/0.68        | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.44/0.68        | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.44/0.68      inference('sup-', [status(thm)], ['49', '50'])).
% 0.44/0.68  thf('52', plain,
% 0.44/0.68      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.44/0.68      inference('split', [status(esa)], ['17'])).
% 0.44/0.68  thf('53', plain, (((r2_hidden @ sk_A @ sk_B))),
% 0.44/0.68      inference('sat_resolution*', [status(thm)], ['22', '37', '38'])).
% 0.44/0.68  thf('54', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.44/0.68      inference('simpl_trail', [status(thm)], ['52', '53'])).
% 0.44/0.68  thf('55', plain,
% 0.44/0.68      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.44/0.68        | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.44/0.68      inference('demod', [status(thm)], ['51', '54'])).
% 0.44/0.68  thf('56', plain, ((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 0.44/0.68      inference('simplify', [status(thm)], ['55'])).
% 0.44/0.68  thf('57', plain,
% 0.44/0.68      (![X7 : $i, X8 : $i]:
% 0.44/0.68         (~ (v3_ordinal1 @ X7)
% 0.44/0.68          | ~ (v3_ordinal1 @ X8)
% 0.44/0.68          | (r1_ordinal1 @ X7 @ X8)
% 0.44/0.68          | ~ (r1_tarski @ X7 @ X8))),
% 0.44/0.68      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.44/0.68  thf('58', plain,
% 0.44/0.68      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.44/0.68        | ~ (v3_ordinal1 @ sk_B)
% 0.44/0.68        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A)))),
% 0.44/0.68      inference('sup-', [status(thm)], ['56', '57'])).
% 0.44/0.68  thf('59', plain, ((v3_ordinal1 @ sk_B)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('60', plain,
% 0.44/0.68      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.44/0.68        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A)))),
% 0.44/0.68      inference('demod', [status(thm)], ['58', '59'])).
% 0.44/0.68  thf('61', plain,
% 0.44/0.68      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.44/0.68         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.44/0.68      inference('split', [status(esa)], ['21'])).
% 0.44/0.68  thf('62', plain, (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.44/0.68      inference('sat_resolution*', [status(thm)], ['22', '37'])).
% 0.44/0.68  thf('63', plain, (~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 0.44/0.68      inference('simpl_trail', [status(thm)], ['61', '62'])).
% 0.44/0.68  thf('64', plain, (~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))),
% 0.44/0.68      inference('clc', [status(thm)], ['60', '63'])).
% 0.44/0.68  thf('65', plain, (~ (v3_ordinal1 @ sk_A)),
% 0.44/0.68      inference('sup-', [status(thm)], ['0', '64'])).
% 0.44/0.68  thf('66', plain, ((v3_ordinal1 @ sk_A)),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf('67', plain, ($false), inference('demod', [status(thm)], ['65', '66'])).
% 0.44/0.68  
% 0.44/0.68  % SZS output end Refutation
% 0.44/0.68  
% 0.44/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

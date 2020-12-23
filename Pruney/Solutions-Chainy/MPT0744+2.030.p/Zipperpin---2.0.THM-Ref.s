%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.m9B3g0yQnm

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 222 expanded)
%              Number of leaves         :   16 (  66 expanded)
%              Depth                    :   15
%              Number of atoms          :  458 (1795 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

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
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v3_ordinal1 @ X3 )
      | ~ ( v3_ordinal1 @ X4 )
      | ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_ordinal1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('6',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf(fc2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ~ ( v1_xboole_0 @ ( k1_ordinal1 @ A ) )
        & ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) ) )).

thf('10',plain,(
    ! [X2: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X2 ) )
      | ~ ( v3_ordinal1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc2_ordinal1])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v3_ordinal1 @ X9 )
      | ( r1_ordinal1 @ X10 @ X9 )
      | ( r2_hidden @ X9 @ X10 )
      | ~ ( v3_ordinal1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('12',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('13',plain,
    ( ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_B ) )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_B ) @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_B ) )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_B ) @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_B ) @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_B ) @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t33_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ B )
          <=> ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) )).

thf('19',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v3_ordinal1 @ X11 )
      | ~ ( r1_ordinal1 @ ( k1_ordinal1 @ X12 ) @ X11 )
      | ( r2_hidden @ X12 @ X11 )
      | ~ ( v3_ordinal1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t33_ordinal1])).

thf('20',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( r2_hidden @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('24',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('25',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
    | ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['9','25'])).

thf('27',plain,(
    ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','26'])).

thf('28',plain,(
    ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','27'])).

thf('29',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v3_ordinal1 @ X9 )
      | ( r1_ordinal1 @ X10 @ X9 )
      | ( r2_hidden @ X9 @ X10 )
      | ~ ( v3_ordinal1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('30',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('31',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X7 = X6 )
      | ( r2_hidden @ X7 @ X6 )
      | ~ ( r2_hidden @ X7 @ ( k1_ordinal1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('32',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ( sk_A = sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('34',plain,
    ( ( ( sk_A = sk_B )
      | ~ ( r2_hidden @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ( sk_A = sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( ( r1_ordinal1 @ sk_A @ sk_B )
      | ( sk_A = sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','26'])).

thf('42',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('43',plain,(
    r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','26','42'])).

thf('44',plain,(
    sk_A = sk_B ),
    inference(simpl_trail,[status(thm)],['40','41','43'])).

thf('45',plain,(
    ~ ( r1_ordinal1 @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['28','44'])).

thf('46',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v3_ordinal1 @ X9 )
      | ( r1_ordinal1 @ X10 @ X9 )
      | ( r2_hidden @ X9 @ X10 )
      | ~ ( v3_ordinal1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ sk_A @ X0 )
      | ( r1_ordinal1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ sk_A @ X0 )
      | ( r1_ordinal1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    r1_ordinal1 @ sk_A @ sk_A ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['45','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.m9B3g0yQnm
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:47:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 196 iterations in 0.050s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.51  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.22/0.51  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.51  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.22/0.51  thf(t34_ordinal1, conjecture,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( v3_ordinal1 @ A ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( v3_ordinal1 @ B ) =>
% 0.22/0.51           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.22/0.51             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.51    (~( ![A:$i]:
% 0.22/0.51        ( ( v3_ordinal1 @ A ) =>
% 0.22/0.51          ( ![B:$i]:
% 0.22/0.51            ( ( v3_ordinal1 @ B ) =>
% 0.22/0.51              ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.22/0.51                ( r1_ordinal1 @ A @ B ) ) ) ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t34_ordinal1])).
% 0.22/0.51  thf('0', plain,
% 0.22/0.51      ((~ (r1_ordinal1 @ sk_A @ sk_B)
% 0.22/0.51        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('1', plain,
% 0.22/0.51      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.22/0.51      inference('split', [status(esa)], ['0'])).
% 0.22/0.51  thf('2', plain,
% 0.22/0.51      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.22/0.51       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.22/0.51      inference('split', [status(esa)], ['0'])).
% 0.22/0.51  thf('3', plain,
% 0.22/0.51      (((r1_ordinal1 @ sk_A @ sk_B) | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('4', plain,
% 0.22/0.51      (((r1_ordinal1 @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.22/0.51      inference('split', [status(esa)], ['3'])).
% 0.22/0.51  thf(redefinition_r1_ordinal1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.22/0.51       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.22/0.51  thf('5', plain,
% 0.22/0.51      (![X3 : $i, X4 : $i]:
% 0.22/0.51         (~ (v3_ordinal1 @ X3)
% 0.22/0.51          | ~ (v3_ordinal1 @ X4)
% 0.22/0.51          | (r1_tarski @ X3 @ X4)
% 0.22/0.51          | ~ (r1_ordinal1 @ X3 @ X4))),
% 0.22/0.51      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.22/0.51  thf('6', plain,
% 0.22/0.51      ((((r1_tarski @ sk_A @ sk_B)
% 0.22/0.51         | ~ (v3_ordinal1 @ sk_B)
% 0.22/0.51         | ~ (v3_ordinal1 @ sk_A))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.51  thf('7', plain, ((v3_ordinal1 @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('8', plain, ((v3_ordinal1 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('9', plain,
% 0.22/0.51      (((r1_tarski @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.22/0.51      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.22/0.51  thf(fc2_ordinal1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( v3_ordinal1 @ A ) =>
% 0.22/0.51       ( ( ~( v1_xboole_0 @ ( k1_ordinal1 @ A ) ) ) & 
% 0.22/0.51         ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) ))).
% 0.22/0.51  thf('10', plain,
% 0.22/0.51      (![X2 : $i]: ((v3_ordinal1 @ (k1_ordinal1 @ X2)) | ~ (v3_ordinal1 @ X2))),
% 0.22/0.51      inference('cnf', [status(esa)], [fc2_ordinal1])).
% 0.22/0.51  thf(t26_ordinal1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( v3_ordinal1 @ A ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( v3_ordinal1 @ B ) =>
% 0.22/0.51           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.22/0.51  thf('11', plain,
% 0.22/0.51      (![X9 : $i, X10 : $i]:
% 0.22/0.51         (~ (v3_ordinal1 @ X9)
% 0.22/0.51          | (r1_ordinal1 @ X10 @ X9)
% 0.22/0.51          | (r2_hidden @ X9 @ X10)
% 0.22/0.51          | ~ (v3_ordinal1 @ X10))),
% 0.22/0.51      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.22/0.51  thf('12', plain,
% 0.22/0.51      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.22/0.51         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.22/0.51      inference('split', [status(esa)], ['0'])).
% 0.22/0.51  thf('13', plain,
% 0.22/0.51      (((~ (v3_ordinal1 @ (k1_ordinal1 @ sk_B))
% 0.22/0.51         | (r1_ordinal1 @ (k1_ordinal1 @ sk_B) @ sk_A)
% 0.22/0.51         | ~ (v3_ordinal1 @ sk_A)))
% 0.22/0.51         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.51  thf('14', plain, ((v3_ordinal1 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('15', plain,
% 0.22/0.51      (((~ (v3_ordinal1 @ (k1_ordinal1 @ sk_B))
% 0.22/0.51         | (r1_ordinal1 @ (k1_ordinal1 @ sk_B) @ sk_A)))
% 0.22/0.51         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.22/0.51      inference('demod', [status(thm)], ['13', '14'])).
% 0.22/0.51  thf('16', plain,
% 0.22/0.51      (((~ (v3_ordinal1 @ sk_B) | (r1_ordinal1 @ (k1_ordinal1 @ sk_B) @ sk_A)))
% 0.22/0.51         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['10', '15'])).
% 0.22/0.51  thf('17', plain, ((v3_ordinal1 @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('18', plain,
% 0.22/0.51      (((r1_ordinal1 @ (k1_ordinal1 @ sk_B) @ sk_A))
% 0.22/0.51         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.22/0.51      inference('demod', [status(thm)], ['16', '17'])).
% 0.22/0.51  thf(t33_ordinal1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( v3_ordinal1 @ A ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( v3_ordinal1 @ B ) =>
% 0.22/0.51           ( ( r2_hidden @ A @ B ) <=>
% 0.22/0.51             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 0.22/0.51  thf('19', plain,
% 0.22/0.51      (![X11 : $i, X12 : $i]:
% 0.22/0.51         (~ (v3_ordinal1 @ X11)
% 0.22/0.51          | ~ (r1_ordinal1 @ (k1_ordinal1 @ X12) @ X11)
% 0.22/0.51          | (r2_hidden @ X12 @ X11)
% 0.22/0.51          | ~ (v3_ordinal1 @ X12))),
% 0.22/0.51      inference('cnf', [status(esa)], [t33_ordinal1])).
% 0.22/0.51  thf('20', plain,
% 0.22/0.51      (((~ (v3_ordinal1 @ sk_B)
% 0.22/0.51         | (r2_hidden @ sk_B @ sk_A)
% 0.22/0.51         | ~ (v3_ordinal1 @ sk_A)))
% 0.22/0.51         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.51  thf('21', plain, ((v3_ordinal1 @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('22', plain, ((v3_ordinal1 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('23', plain,
% 0.22/0.51      (((r2_hidden @ sk_B @ sk_A))
% 0.22/0.51         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.22/0.51      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.22/0.51  thf(t7_ordinal1, axiom,
% 0.22/0.51    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.51  thf('24', plain,
% 0.22/0.51      (![X13 : $i, X14 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X13 @ X14) | ~ (r1_tarski @ X14 @ X13))),
% 0.22/0.51      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.22/0.51  thf('25', plain,
% 0.22/0.51      ((~ (r1_tarski @ sk_A @ sk_B))
% 0.22/0.51         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.51  thf('26', plain,
% 0.22/0.51      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) | 
% 0.22/0.51       ~ ((r1_ordinal1 @ sk_A @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['9', '25'])).
% 0.22/0.51  thf('27', plain, (~ ((r1_ordinal1 @ sk_A @ sk_B))),
% 0.22/0.51      inference('sat_resolution*', [status(thm)], ['2', '26'])).
% 0.22/0.51  thf('28', plain, (~ (r1_ordinal1 @ sk_A @ sk_B)),
% 0.22/0.51      inference('simpl_trail', [status(thm)], ['1', '27'])).
% 0.22/0.51  thf('29', plain,
% 0.22/0.51      (![X9 : $i, X10 : $i]:
% 0.22/0.51         (~ (v3_ordinal1 @ X9)
% 0.22/0.51          | (r1_ordinal1 @ X10 @ X9)
% 0.22/0.51          | (r2_hidden @ X9 @ X10)
% 0.22/0.51          | ~ (v3_ordinal1 @ X10))),
% 0.22/0.51      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.22/0.51  thf('30', plain,
% 0.22/0.51      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.22/0.51         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.22/0.51      inference('split', [status(esa)], ['3'])).
% 0.22/0.51  thf(t13_ordinal1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.22/0.51       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.22/0.51  thf('31', plain,
% 0.22/0.51      (![X6 : $i, X7 : $i]:
% 0.22/0.51         (((X7) = (X6))
% 0.22/0.51          | (r2_hidden @ X7 @ X6)
% 0.22/0.51          | ~ (r2_hidden @ X7 @ (k1_ordinal1 @ X6)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.22/0.51  thf('32', plain,
% 0.22/0.51      ((((r2_hidden @ sk_A @ sk_B) | ((sk_A) = (sk_B))))
% 0.22/0.51         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['30', '31'])).
% 0.22/0.51  thf(antisymmetry_r2_hidden, axiom,
% 0.22/0.51    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.22/0.51  thf('33', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.22/0.51      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.22/0.51  thf('34', plain,
% 0.22/0.51      (((((sk_A) = (sk_B)) | ~ (r2_hidden @ sk_B @ sk_A)))
% 0.22/0.51         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.51  thf('35', plain,
% 0.22/0.51      (((~ (v3_ordinal1 @ sk_A)
% 0.22/0.51         | (r1_ordinal1 @ sk_A @ sk_B)
% 0.22/0.51         | ~ (v3_ordinal1 @ sk_B)
% 0.22/0.51         | ((sk_A) = (sk_B)))) <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['29', '34'])).
% 0.22/0.51  thf('36', plain, ((v3_ordinal1 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('37', plain, ((v3_ordinal1 @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('38', plain,
% 0.22/0.51      ((((r1_ordinal1 @ sk_A @ sk_B) | ((sk_A) = (sk_B))))
% 0.22/0.51         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.22/0.51      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.22/0.51  thf('39', plain,
% 0.22/0.51      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.22/0.51      inference('split', [status(esa)], ['0'])).
% 0.22/0.51  thf('40', plain,
% 0.22/0.51      ((((sk_A) = (sk_B)))
% 0.22/0.51         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 0.22/0.51             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['38', '39'])).
% 0.22/0.51  thf('41', plain, (~ ((r1_ordinal1 @ sk_A @ sk_B))),
% 0.22/0.51      inference('sat_resolution*', [status(thm)], ['2', '26'])).
% 0.22/0.51  thf('42', plain,
% 0.22/0.51      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) | 
% 0.22/0.51       ((r1_ordinal1 @ sk_A @ sk_B))),
% 0.22/0.51      inference('split', [status(esa)], ['3'])).
% 0.22/0.51  thf('43', plain, (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.22/0.51      inference('sat_resolution*', [status(thm)], ['2', '26', '42'])).
% 0.22/0.51  thf('44', plain, (((sk_A) = (sk_B))),
% 0.22/0.51      inference('simpl_trail', [status(thm)], ['40', '41', '43'])).
% 0.22/0.51  thf('45', plain, (~ (r1_ordinal1 @ sk_A @ sk_A)),
% 0.22/0.51      inference('demod', [status(thm)], ['28', '44'])).
% 0.22/0.51  thf('46', plain, ((v3_ordinal1 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('47', plain,
% 0.22/0.51      (![X9 : $i, X10 : $i]:
% 0.22/0.51         (~ (v3_ordinal1 @ X9)
% 0.22/0.51          | (r1_ordinal1 @ X10 @ X9)
% 0.22/0.51          | (r2_hidden @ X9 @ X10)
% 0.22/0.51          | ~ (v3_ordinal1 @ X10))),
% 0.22/0.51      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.22/0.51  thf('48', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (v3_ordinal1 @ X0)
% 0.22/0.51          | (r2_hidden @ sk_A @ X0)
% 0.22/0.51          | (r1_ordinal1 @ X0 @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['46', '47'])).
% 0.22/0.51  thf('49', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (v3_ordinal1 @ X0)
% 0.22/0.51          | (r2_hidden @ sk_A @ X0)
% 0.22/0.51          | (r1_ordinal1 @ X0 @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['46', '47'])).
% 0.22/0.51  thf('50', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.22/0.51      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.22/0.51  thf('51', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((r1_ordinal1 @ X0 @ sk_A)
% 0.22/0.51          | ~ (v3_ordinal1 @ X0)
% 0.22/0.51          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['49', '50'])).
% 0.22/0.51  thf('52', plain,
% 0.22/0.51      (((r1_ordinal1 @ sk_A @ sk_A)
% 0.22/0.51        | ~ (v3_ordinal1 @ sk_A)
% 0.22/0.51        | ~ (v3_ordinal1 @ sk_A)
% 0.22/0.51        | (r1_ordinal1 @ sk_A @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['48', '51'])).
% 0.22/0.51  thf('53', plain, ((v3_ordinal1 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('54', plain, ((v3_ordinal1 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('55', plain,
% 0.22/0.51      (((r1_ordinal1 @ sk_A @ sk_A) | (r1_ordinal1 @ sk_A @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.22/0.51  thf('56', plain, ((r1_ordinal1 @ sk_A @ sk_A)),
% 0.22/0.51      inference('simplify', [status(thm)], ['55'])).
% 0.22/0.51  thf('57', plain, ($false), inference('demod', [status(thm)], ['45', '56'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

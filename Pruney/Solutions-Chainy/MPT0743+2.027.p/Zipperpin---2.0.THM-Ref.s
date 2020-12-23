%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wsDgtUy9fF

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:56 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 375 expanded)
%              Number of leaves         :   19 ( 112 expanded)
%              Depth                    :   21
%              Number of atoms          :  601 (3031 expanded)
%              Number of equality atoms :   13 (  25 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

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
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('3',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_A )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 )
    | ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 )
    | ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['4'])).

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('6',plain,(
    ! [X16: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X16 ) )
      | ~ ( v3_ordinal1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('7',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v3_ordinal1 @ X8 )
      | ~ ( v3_ordinal1 @ X9 )
      | ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_ordinal1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('9',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_B_1 )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('15',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v3_ordinal1 @ X14 )
      | ( r1_ordinal1 @ X15 @ X14 )
      | ( r2_hidden @ X14 @ X15 )
      | ~ ( v3_ordinal1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('16',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ ( k1_ordinal1 @ X13 ) )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_B_1 ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v3_ordinal1 @ X8 )
      | ~ ( v3_ordinal1 @ X9 )
      | ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_ordinal1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('25',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( r1_tarski @ sk_A @ sk_B_1 )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v3_ordinal1 @ X14 )
      | ( r1_ordinal1 @ X15 @ X14 )
      | ( r2_hidden @ X14 @ X15 )
      | ~ ( v3_ordinal1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('30',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
   <= ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('31',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B_1 )
      | ( r1_ordinal1 @ sk_B_1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( r1_ordinal1 @ sk_B_1 @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v3_ordinal1 @ X8 )
      | ~ ( v3_ordinal1 @ X9 )
      | ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_ordinal1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('36',plain,
    ( ( ( r1_tarski @ sk_B_1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('40',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,
    ( ( ~ ( r1_tarski @ sk_A @ sk_B_1 )
      | ( sk_A = sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( sk_A = sk_B_1 )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['28','41'])).

thf('43',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('44',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('45',plain,(
    ! [X10: $i] :
      ( r2_hidden @ X10 @ ( k1_ordinal1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('46',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('47',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('50',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['5','48','49'])).

thf('51',plain,(
    ~ ( r1_tarski @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['3','50'])).

thf('52',plain,(
    ! [X16: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X16 ) )
      | ~ ( v3_ordinal1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('53',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v3_ordinal1 @ X14 )
      | ( r1_ordinal1 @ X15 @ X14 )
      | ( r2_hidden @ X14 @ X15 )
      | ~ ( v3_ordinal1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('54',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X12 = X11 )
      | ( r2_hidden @ X12 @ X11 )
      | ~ ( r2_hidden @ X12 @ ( k1_ordinal1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X0 ) @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('58',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['5','48'])).

thf('59',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( v3_ordinal1 @ sk_B_1 )
    | ( r2_hidden @ sk_B_1 @ sk_A )
    | ( sk_B_1 = sk_A )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
    | ( sk_B_1 = sk_A ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('65',plain,
    ( ( sk_B_1 = sk_A )
    | ~ ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf(d2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
    <=> ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( r1_tarski @ B @ A ) ) ) )).

thf('67',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r1_tarski @ X5 @ X6 )
      | ~ ( v1_ordinal1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('68',plain,
    ( ( ~ ( v1_ordinal1 @ sk_B_1 )
      | ( r1_tarski @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('70',plain,(
    ! [X3: $i] :
      ( ( v1_ordinal1 @ X3 )
      | ~ ( v3_ordinal1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('71',plain,(
    v1_ordinal1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( r1_tarski @ sk_A @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['68','71'])).

thf('73',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['5','48','49'])).

thf('74',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(simpl_trail,[status(thm)],['72','73'])).

thf('75',plain,(
    sk_B_1 = sk_A ),
    inference(demod,[status(thm)],['65','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('77',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    $false ),
    inference(demod,[status(thm)],['51','75','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wsDgtUy9fF
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:36:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.61  % Solved by: fo/fo7.sh
% 0.39/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.61  % done 343 iterations in 0.156s
% 0.39/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.61  % SZS output start Refutation
% 0.39/0.61  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 0.39/0.61  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 0.39/0.61  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.39/0.61  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.39/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.61  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.39/0.61  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.39/0.61  thf(t33_ordinal1, conjecture,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ( v3_ordinal1 @ A ) =>
% 0.39/0.61       ( ![B:$i]:
% 0.39/0.61         ( ( v3_ordinal1 @ B ) =>
% 0.39/0.61           ( ( r2_hidden @ A @ B ) <=>
% 0.39/0.61             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 0.39/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.61    (~( ![A:$i]:
% 0.39/0.61        ( ( v3_ordinal1 @ A ) =>
% 0.39/0.61          ( ![B:$i]:
% 0.39/0.61            ( ( v3_ordinal1 @ B ) =>
% 0.39/0.61              ( ( r2_hidden @ A @ B ) <=>
% 0.39/0.61                ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ) )),
% 0.39/0.61    inference('cnf.neg', [status(esa)], [t33_ordinal1])).
% 0.39/0.61  thf('0', plain,
% 0.39/0.61      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B_1)
% 0.39/0.61        | (r2_hidden @ sk_A @ sk_B_1))),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('1', plain,
% 0.39/0.61      (((r2_hidden @ sk_A @ sk_B_1)) <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.39/0.61      inference('split', [status(esa)], ['0'])).
% 0.39/0.61  thf(t7_ordinal1, axiom,
% 0.39/0.61    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.39/0.61  thf('2', plain,
% 0.39/0.61      (![X17 : $i, X18 : $i]:
% 0.39/0.61         (~ (r2_hidden @ X17 @ X18) | ~ (r1_tarski @ X18 @ X17))),
% 0.39/0.61      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.39/0.61  thf('3', plain,
% 0.39/0.61      ((~ (r1_tarski @ sk_B_1 @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.61  thf('4', plain,
% 0.39/0.61      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B_1)
% 0.39/0.61        | ~ (r2_hidden @ sk_A @ sk_B_1))),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('5', plain,
% 0.39/0.61      (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B_1)) | 
% 0.39/0.61       ~ ((r2_hidden @ sk_A @ sk_B_1))),
% 0.39/0.61      inference('split', [status(esa)], ['4'])).
% 0.39/0.61  thf(t29_ordinal1, axiom,
% 0.39/0.61    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 0.39/0.61  thf('6', plain,
% 0.39/0.61      (![X16 : $i]:
% 0.39/0.61         ((v3_ordinal1 @ (k1_ordinal1 @ X16)) | ~ (v3_ordinal1 @ X16))),
% 0.39/0.61      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.39/0.61  thf('7', plain,
% 0.39/0.61      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B_1))
% 0.39/0.61         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B_1)))),
% 0.39/0.61      inference('split', [status(esa)], ['0'])).
% 0.39/0.61  thf(redefinition_r1_ordinal1, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.39/0.61       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.39/0.61  thf('8', plain,
% 0.39/0.61      (![X8 : $i, X9 : $i]:
% 0.39/0.61         (~ (v3_ordinal1 @ X8)
% 0.39/0.61          | ~ (v3_ordinal1 @ X9)
% 0.39/0.61          | (r1_tarski @ X8 @ X9)
% 0.39/0.61          | ~ (r1_ordinal1 @ X8 @ X9))),
% 0.39/0.61      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.39/0.61  thf('9', plain,
% 0.39/0.61      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B_1)
% 0.39/0.61         | ~ (v3_ordinal1 @ sk_B_1)
% 0.39/0.61         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.39/0.61         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B_1)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['7', '8'])).
% 0.39/0.61  thf('10', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('11', plain,
% 0.39/0.61      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B_1)
% 0.39/0.61         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.39/0.61         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B_1)))),
% 0.39/0.61      inference('demod', [status(thm)], ['9', '10'])).
% 0.39/0.61  thf('12', plain,
% 0.39/0.61      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B_1)))
% 0.39/0.61         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B_1)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['6', '11'])).
% 0.39/0.61  thf('13', plain, ((v3_ordinal1 @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('14', plain,
% 0.39/0.61      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B_1))
% 0.39/0.61         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B_1)))),
% 0.39/0.61      inference('demod', [status(thm)], ['12', '13'])).
% 0.39/0.61  thf(t26_ordinal1, axiom,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ( v3_ordinal1 @ A ) =>
% 0.39/0.61       ( ![B:$i]:
% 0.39/0.61         ( ( v3_ordinal1 @ B ) =>
% 0.39/0.61           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.39/0.61  thf('15', plain,
% 0.39/0.61      (![X14 : $i, X15 : $i]:
% 0.39/0.61         (~ (v3_ordinal1 @ X14)
% 0.39/0.61          | (r1_ordinal1 @ X15 @ X14)
% 0.39/0.61          | (r2_hidden @ X14 @ X15)
% 0.39/0.61          | ~ (v3_ordinal1 @ X15))),
% 0.39/0.61      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.39/0.61  thf(t13_ordinal1, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.39/0.61       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.39/0.61  thf('16', plain,
% 0.39/0.61      (![X12 : $i, X13 : $i]:
% 0.39/0.61         ((r2_hidden @ X12 @ (k1_ordinal1 @ X13)) | ~ (r2_hidden @ X12 @ X13))),
% 0.39/0.61      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.39/0.61  thf('17', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         (~ (v3_ordinal1 @ X0)
% 0.39/0.61          | (r1_ordinal1 @ X0 @ X1)
% 0.39/0.61          | ~ (v3_ordinal1 @ X1)
% 0.39/0.61          | (r2_hidden @ X1 @ (k1_ordinal1 @ X0)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['15', '16'])).
% 0.39/0.61  thf('18', plain,
% 0.39/0.61      (![X17 : $i, X18 : $i]:
% 0.39/0.61         (~ (r2_hidden @ X17 @ X18) | ~ (r1_tarski @ X18 @ X17))),
% 0.39/0.61      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.39/0.61  thf('19', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         (~ (v3_ordinal1 @ X1)
% 0.39/0.61          | (r1_ordinal1 @ X0 @ X1)
% 0.39/0.61          | ~ (v3_ordinal1 @ X0)
% 0.39/0.61          | ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X1))),
% 0.39/0.61      inference('sup-', [status(thm)], ['17', '18'])).
% 0.39/0.61  thf('20', plain,
% 0.39/0.61      (((~ (v3_ordinal1 @ sk_A)
% 0.39/0.61         | (r1_ordinal1 @ sk_A @ sk_B_1)
% 0.39/0.61         | ~ (v3_ordinal1 @ sk_B_1)))
% 0.39/0.61         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B_1)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['14', '19'])).
% 0.39/0.61  thf('21', plain, ((v3_ordinal1 @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('22', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('23', plain,
% 0.39/0.61      (((r1_ordinal1 @ sk_A @ sk_B_1))
% 0.39/0.61         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B_1)))),
% 0.39/0.61      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.39/0.61  thf('24', plain,
% 0.39/0.61      (![X8 : $i, X9 : $i]:
% 0.39/0.61         (~ (v3_ordinal1 @ X8)
% 0.39/0.61          | ~ (v3_ordinal1 @ X9)
% 0.39/0.61          | (r1_tarski @ X8 @ X9)
% 0.39/0.61          | ~ (r1_ordinal1 @ X8 @ X9))),
% 0.39/0.61      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.39/0.61  thf('25', plain,
% 0.39/0.61      ((((r1_tarski @ sk_A @ sk_B_1)
% 0.39/0.61         | ~ (v3_ordinal1 @ sk_B_1)
% 0.39/0.61         | ~ (v3_ordinal1 @ sk_A)))
% 0.39/0.61         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B_1)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['23', '24'])).
% 0.39/0.61  thf('26', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('27', plain, ((v3_ordinal1 @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('28', plain,
% 0.39/0.61      (((r1_tarski @ sk_A @ sk_B_1))
% 0.39/0.61         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B_1)))),
% 0.39/0.61      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.39/0.61  thf('29', plain,
% 0.39/0.61      (![X14 : $i, X15 : $i]:
% 0.39/0.61         (~ (v3_ordinal1 @ X14)
% 0.39/0.61          | (r1_ordinal1 @ X15 @ X14)
% 0.39/0.61          | (r2_hidden @ X14 @ X15)
% 0.39/0.61          | ~ (v3_ordinal1 @ X15))),
% 0.39/0.61      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.39/0.61  thf('30', plain,
% 0.39/0.61      ((~ (r2_hidden @ sk_A @ sk_B_1)) <= (~ ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.39/0.61      inference('split', [status(esa)], ['4'])).
% 0.39/0.61  thf('31', plain,
% 0.39/0.61      (((~ (v3_ordinal1 @ sk_B_1)
% 0.39/0.61         | (r1_ordinal1 @ sk_B_1 @ sk_A)
% 0.39/0.61         | ~ (v3_ordinal1 @ sk_A))) <= (~ ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['29', '30'])).
% 0.39/0.61  thf('32', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('33', plain, ((v3_ordinal1 @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('34', plain,
% 0.39/0.61      (((r1_ordinal1 @ sk_B_1 @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.39/0.61      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.39/0.61  thf('35', plain,
% 0.39/0.61      (![X8 : $i, X9 : $i]:
% 0.39/0.61         (~ (v3_ordinal1 @ X8)
% 0.39/0.61          | ~ (v3_ordinal1 @ X9)
% 0.39/0.61          | (r1_tarski @ X8 @ X9)
% 0.39/0.61          | ~ (r1_ordinal1 @ X8 @ X9))),
% 0.39/0.61      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.39/0.61  thf('36', plain,
% 0.39/0.61      ((((r1_tarski @ sk_B_1 @ sk_A)
% 0.39/0.61         | ~ (v3_ordinal1 @ sk_A)
% 0.39/0.61         | ~ (v3_ordinal1 @ sk_B_1))) <= (~ ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['34', '35'])).
% 0.39/0.61  thf('37', plain, ((v3_ordinal1 @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('38', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('39', plain,
% 0.39/0.61      (((r1_tarski @ sk_B_1 @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.39/0.61      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.39/0.61  thf(d10_xboole_0, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.39/0.61  thf('40', plain,
% 0.39/0.61      (![X0 : $i, X2 : $i]:
% 0.39/0.61         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.39/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.61  thf('41', plain,
% 0.39/0.61      (((~ (r1_tarski @ sk_A @ sk_B_1) | ((sk_A) = (sk_B_1))))
% 0.39/0.61         <= (~ ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['39', '40'])).
% 0.39/0.61  thf('42', plain,
% 0.39/0.61      ((((sk_A) = (sk_B_1)))
% 0.39/0.61         <= (~ ((r2_hidden @ sk_A @ sk_B_1)) & 
% 0.39/0.61             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B_1)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['28', '41'])).
% 0.39/0.61  thf('43', plain,
% 0.39/0.61      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B_1))
% 0.39/0.61         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B_1)))),
% 0.39/0.61      inference('demod', [status(thm)], ['12', '13'])).
% 0.39/0.61  thf('44', plain,
% 0.39/0.61      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_A))
% 0.39/0.61         <= (~ ((r2_hidden @ sk_A @ sk_B_1)) & 
% 0.39/0.61             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B_1)))),
% 0.39/0.61      inference('sup+', [status(thm)], ['42', '43'])).
% 0.39/0.61  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.39/0.61  thf('45', plain, (![X10 : $i]: (r2_hidden @ X10 @ (k1_ordinal1 @ X10))),
% 0.39/0.61      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.39/0.61  thf('46', plain,
% 0.39/0.61      (![X17 : $i, X18 : $i]:
% 0.39/0.61         (~ (r2_hidden @ X17 @ X18) | ~ (r1_tarski @ X18 @ X17))),
% 0.39/0.61      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.39/0.61  thf('47', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X0)),
% 0.39/0.61      inference('sup-', [status(thm)], ['45', '46'])).
% 0.39/0.61  thf('48', plain,
% 0.39/0.61      (((r2_hidden @ sk_A @ sk_B_1)) | 
% 0.39/0.61       ~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B_1))),
% 0.39/0.61      inference('sup-', [status(thm)], ['44', '47'])).
% 0.39/0.61  thf('49', plain,
% 0.39/0.61      (((r2_hidden @ sk_A @ sk_B_1)) | 
% 0.39/0.61       ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B_1))),
% 0.39/0.61      inference('split', [status(esa)], ['0'])).
% 0.39/0.61  thf('50', plain, (((r2_hidden @ sk_A @ sk_B_1))),
% 0.39/0.61      inference('sat_resolution*', [status(thm)], ['5', '48', '49'])).
% 0.39/0.61  thf('51', plain, (~ (r1_tarski @ sk_B_1 @ sk_A)),
% 0.39/0.61      inference('simpl_trail', [status(thm)], ['3', '50'])).
% 0.39/0.61  thf('52', plain,
% 0.39/0.61      (![X16 : $i]:
% 0.39/0.61         ((v3_ordinal1 @ (k1_ordinal1 @ X16)) | ~ (v3_ordinal1 @ X16))),
% 0.39/0.61      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.39/0.61  thf('53', plain,
% 0.39/0.61      (![X14 : $i, X15 : $i]:
% 0.39/0.61         (~ (v3_ordinal1 @ X14)
% 0.39/0.61          | (r1_ordinal1 @ X15 @ X14)
% 0.39/0.61          | (r2_hidden @ X14 @ X15)
% 0.39/0.61          | ~ (v3_ordinal1 @ X15))),
% 0.39/0.61      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.39/0.61  thf('54', plain,
% 0.39/0.61      (![X11 : $i, X12 : $i]:
% 0.39/0.61         (((X12) = (X11))
% 0.39/0.61          | (r2_hidden @ X12 @ X11)
% 0.39/0.61          | ~ (r2_hidden @ X12 @ (k1_ordinal1 @ X11)))),
% 0.39/0.61      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.39/0.61  thf('55', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         (~ (v3_ordinal1 @ (k1_ordinal1 @ X0))
% 0.39/0.61          | (r1_ordinal1 @ (k1_ordinal1 @ X0) @ X1)
% 0.39/0.61          | ~ (v3_ordinal1 @ X1)
% 0.39/0.61          | (r2_hidden @ X1 @ X0)
% 0.39/0.61          | ((X1) = (X0)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['53', '54'])).
% 0.39/0.61  thf('56', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         (~ (v3_ordinal1 @ X0)
% 0.39/0.61          | ((X1) = (X0))
% 0.39/0.61          | (r2_hidden @ X1 @ X0)
% 0.39/0.61          | ~ (v3_ordinal1 @ X1)
% 0.39/0.61          | (r1_ordinal1 @ (k1_ordinal1 @ X0) @ X1))),
% 0.39/0.61      inference('sup-', [status(thm)], ['52', '55'])).
% 0.39/0.61  thf('57', plain,
% 0.39/0.61      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B_1))
% 0.39/0.61         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B_1)))),
% 0.39/0.61      inference('split', [status(esa)], ['4'])).
% 0.39/0.61  thf('58', plain, (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B_1))),
% 0.39/0.61      inference('sat_resolution*', [status(thm)], ['5', '48'])).
% 0.39/0.61  thf('59', plain, (~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B_1)),
% 0.39/0.61      inference('simpl_trail', [status(thm)], ['57', '58'])).
% 0.39/0.61  thf('60', plain,
% 0.39/0.61      ((~ (v3_ordinal1 @ sk_B_1)
% 0.39/0.61        | (r2_hidden @ sk_B_1 @ sk_A)
% 0.39/0.61        | ((sk_B_1) = (sk_A))
% 0.39/0.61        | ~ (v3_ordinal1 @ sk_A))),
% 0.39/0.61      inference('sup-', [status(thm)], ['56', '59'])).
% 0.39/0.61  thf('61', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('62', plain, ((v3_ordinal1 @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('63', plain, (((r2_hidden @ sk_B_1 @ sk_A) | ((sk_B_1) = (sk_A)))),
% 0.39/0.61      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.39/0.61  thf('64', plain,
% 0.39/0.61      (![X17 : $i, X18 : $i]:
% 0.39/0.61         (~ (r2_hidden @ X17 @ X18) | ~ (r1_tarski @ X18 @ X17))),
% 0.39/0.61      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.39/0.61  thf('65', plain, ((((sk_B_1) = (sk_A)) | ~ (r1_tarski @ sk_A @ sk_B_1))),
% 0.39/0.61      inference('sup-', [status(thm)], ['63', '64'])).
% 0.39/0.61  thf('66', plain,
% 0.39/0.61      (((r2_hidden @ sk_A @ sk_B_1)) <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.39/0.61      inference('split', [status(esa)], ['0'])).
% 0.39/0.61  thf(d2_ordinal1, axiom,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ( v1_ordinal1 @ A ) <=>
% 0.39/0.61       ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( r1_tarski @ B @ A ) ) ) ))).
% 0.39/0.61  thf('67', plain,
% 0.39/0.61      (![X5 : $i, X6 : $i]:
% 0.39/0.61         (~ (r2_hidden @ X5 @ X6)
% 0.39/0.61          | (r1_tarski @ X5 @ X6)
% 0.39/0.61          | ~ (v1_ordinal1 @ X6))),
% 0.39/0.61      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.39/0.61  thf('68', plain,
% 0.39/0.61      (((~ (v1_ordinal1 @ sk_B_1) | (r1_tarski @ sk_A @ sk_B_1)))
% 0.39/0.61         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['66', '67'])).
% 0.39/0.61  thf('69', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf(cc1_ordinal1, axiom,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 0.39/0.61  thf('70', plain, (![X3 : $i]: ((v1_ordinal1 @ X3) | ~ (v3_ordinal1 @ X3))),
% 0.39/0.61      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.39/0.61  thf('71', plain, ((v1_ordinal1 @ sk_B_1)),
% 0.39/0.61      inference('sup-', [status(thm)], ['69', '70'])).
% 0.39/0.61  thf('72', plain,
% 0.39/0.61      (((r1_tarski @ sk_A @ sk_B_1)) <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.39/0.61      inference('demod', [status(thm)], ['68', '71'])).
% 0.39/0.61  thf('73', plain, (((r2_hidden @ sk_A @ sk_B_1))),
% 0.39/0.61      inference('sat_resolution*', [status(thm)], ['5', '48', '49'])).
% 0.39/0.61  thf('74', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.39/0.61      inference('simpl_trail', [status(thm)], ['72', '73'])).
% 0.39/0.61  thf('75', plain, (((sk_B_1) = (sk_A))),
% 0.39/0.61      inference('demod', [status(thm)], ['65', '74'])).
% 0.39/0.61  thf('76', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.39/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.61  thf('77', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.39/0.61      inference('simplify', [status(thm)], ['76'])).
% 0.39/0.61  thf('78', plain, ($false),
% 0.39/0.61      inference('demod', [status(thm)], ['51', '75', '77'])).
% 0.39/0.61  
% 0.39/0.61  % SZS output end Refutation
% 0.39/0.61  
% 0.39/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

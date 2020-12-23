%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.713vdud33S

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:55 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 256 expanded)
%              Number of leaves         :   15 (  75 expanded)
%              Depth                    :   16
%              Number of atoms          :  546 (2050 expanded)
%              Number of equality atoms :    8 (  13 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( r1_tarski @ X21 @ X20 ) ) ),
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

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_ordinal1 @ X17 )
      | ( r1_ordinal1 @ X18 @ X17 )
      | ( r2_hidden @ X17 @ X18 )
      | ~ ( v3_ordinal1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('7',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('8',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( r1_ordinal1 @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v3_ordinal1 @ X12 )
      | ~ ( v3_ordinal1 @ X13 )
      | ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_ordinal1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('13',plain,
    ( ( ( r1_tarski @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('17',plain,(
    ! [X19: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X19 ) )
      | ~ ( v3_ordinal1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('18',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('19',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v3_ordinal1 @ X12 )
      | ~ ( v3_ordinal1 @ X13 )
      | ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_ordinal1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('20',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('26',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('27',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ X0 )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','27'])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('29',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r2_hidden @ X15 @ ( k1_ordinal1 @ X16 ) )
      | ( X15 != X16 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('30',plain,(
    ! [X16: $i] :
      ( r2_hidden @ X16 @ ( k1_ordinal1 @ X16 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( r1_tarski @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('32',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['28','32'])).

thf('34',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('35',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['5','33','34'])).

thf('36',plain,(
    ~ ( r1_tarski @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['3','35'])).

thf('37',plain,(
    ! [X19: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X19 ) )
      | ~ ( v3_ordinal1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('38',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_ordinal1 @ X17 )
      | ( r1_ordinal1 @ X18 @ X17 )
      | ( r2_hidden @ X17 @ X18 )
      | ~ ( v3_ordinal1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('39',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X15 = X14 )
      | ( r2_hidden @ X15 @ X14 )
      | ~ ( r2_hidden @ X15 @ ( k1_ordinal1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X0 ) @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('43',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['5','33'])).

thf('44',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r2_hidden @ sk_B @ sk_A )
    | ( sk_B = sk_A )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( sk_B = sk_A ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('51',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['5','33','34'])).

thf('53',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['51','52'])).

thf('54',plain,(
    sk_B = sk_A ),
    inference(clc,[status(thm)],['48','53'])).

thf('55',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_ordinal1 @ X17 )
      | ( r1_ordinal1 @ X18 @ X17 )
      | ( r2_hidden @ X17 @ X18 )
      | ~ ( v3_ordinal1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('57',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_ordinal1 @ X17 )
      | ( r1_ordinal1 @ X18 @ X17 )
      | ( r2_hidden @ X17 @ X18 )
      | ~ ( v3_ordinal1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','61'])).

thf('63',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference(eq_fact,[status(thm)],['62'])).

thf('64',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    r1_ordinal1 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v3_ordinal1 @ X12 )
      | ~ ( v3_ordinal1 @ X13 )
      | ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_ordinal1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('67',plain,
    ( ( r1_tarski @ sk_A @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    r1_tarski @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    $false ),
    inference(demod,[status(thm)],['36','54','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.713vdud33S
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:29:33 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.41/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.60  % Solved by: fo/fo7.sh
% 0.41/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.60  % done 361 iterations in 0.141s
% 0.41/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.60  % SZS output start Refutation
% 0.41/0.60  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.41/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.60  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.41/0.60  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.41/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.60  thf(t33_ordinal1, conjecture,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( v3_ordinal1 @ A ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( v3_ordinal1 @ B ) =>
% 0.41/0.60           ( ( r2_hidden @ A @ B ) <=>
% 0.41/0.60             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 0.41/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.60    (~( ![A:$i]:
% 0.41/0.60        ( ( v3_ordinal1 @ A ) =>
% 0.41/0.60          ( ![B:$i]:
% 0.41/0.60            ( ( v3_ordinal1 @ B ) =>
% 0.41/0.60              ( ( r2_hidden @ A @ B ) <=>
% 0.41/0.60                ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ) )),
% 0.41/0.60    inference('cnf.neg', [status(esa)], [t33_ordinal1])).
% 0.41/0.60  thf('0', plain,
% 0.41/0.60      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('1', plain,
% 0.41/0.60      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.41/0.60      inference('split', [status(esa)], ['0'])).
% 0.41/0.60  thf(t7_ordinal1, axiom,
% 0.41/0.60    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.41/0.60  thf('2', plain,
% 0.41/0.60      (![X20 : $i, X21 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X20 @ X21) | ~ (r1_tarski @ X21 @ X20))),
% 0.41/0.60      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.41/0.60  thf('3', plain,
% 0.41/0.60      ((~ (r1_tarski @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.41/0.60  thf('4', plain,
% 0.41/0.60      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.41/0.60        | ~ (r2_hidden @ sk_A @ sk_B))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('5', plain,
% 0.41/0.60      (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 0.41/0.60       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.41/0.60      inference('split', [status(esa)], ['4'])).
% 0.41/0.60  thf(t26_ordinal1, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( v3_ordinal1 @ A ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( v3_ordinal1 @ B ) =>
% 0.41/0.60           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.41/0.60  thf('6', plain,
% 0.41/0.60      (![X17 : $i, X18 : $i]:
% 0.41/0.60         (~ (v3_ordinal1 @ X17)
% 0.41/0.60          | (r1_ordinal1 @ X18 @ X17)
% 0.41/0.60          | (r2_hidden @ X17 @ X18)
% 0.41/0.60          | ~ (v3_ordinal1 @ X18))),
% 0.41/0.60      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.41/0.60  thf('7', plain,
% 0.41/0.60      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.41/0.60      inference('split', [status(esa)], ['4'])).
% 0.41/0.60  thf('8', plain,
% 0.41/0.60      (((~ (v3_ordinal1 @ sk_B)
% 0.41/0.60         | (r1_ordinal1 @ sk_B @ sk_A)
% 0.41/0.60         | ~ (v3_ordinal1 @ sk_A))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['6', '7'])).
% 0.41/0.60  thf('9', plain, ((v3_ordinal1 @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('10', plain, ((v3_ordinal1 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('11', plain,
% 0.41/0.60      (((r1_ordinal1 @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.41/0.60      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.41/0.60  thf(redefinition_r1_ordinal1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.41/0.60       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.41/0.60  thf('12', plain,
% 0.41/0.60      (![X12 : $i, X13 : $i]:
% 0.41/0.60         (~ (v3_ordinal1 @ X12)
% 0.41/0.60          | ~ (v3_ordinal1 @ X13)
% 0.41/0.60          | (r1_tarski @ X12 @ X13)
% 0.41/0.60          | ~ (r1_ordinal1 @ X12 @ X13))),
% 0.41/0.60      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.41/0.60  thf('13', plain,
% 0.41/0.60      ((((r1_tarski @ sk_B @ sk_A)
% 0.41/0.60         | ~ (v3_ordinal1 @ sk_A)
% 0.41/0.60         | ~ (v3_ordinal1 @ sk_B))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.41/0.60  thf('14', plain, ((v3_ordinal1 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('15', plain, ((v3_ordinal1 @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('16', plain,
% 0.41/0.60      (((r1_tarski @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.41/0.60      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.41/0.60  thf(t29_ordinal1, axiom,
% 0.41/0.60    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 0.41/0.60  thf('17', plain,
% 0.41/0.60      (![X19 : $i]:
% 0.41/0.60         ((v3_ordinal1 @ (k1_ordinal1 @ X19)) | ~ (v3_ordinal1 @ X19))),
% 0.41/0.60      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.41/0.60  thf('18', plain,
% 0.41/0.60      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.41/0.60         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.41/0.60      inference('split', [status(esa)], ['0'])).
% 0.41/0.60  thf('19', plain,
% 0.41/0.60      (![X12 : $i, X13 : $i]:
% 0.41/0.60         (~ (v3_ordinal1 @ X12)
% 0.41/0.60          | ~ (v3_ordinal1 @ X13)
% 0.41/0.60          | (r1_tarski @ X12 @ X13)
% 0.41/0.60          | ~ (r1_ordinal1 @ X12 @ X13))),
% 0.41/0.60      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.41/0.60  thf('20', plain,
% 0.41/0.60      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.41/0.60         | ~ (v3_ordinal1 @ sk_B)
% 0.41/0.60         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.41/0.60         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['18', '19'])).
% 0.41/0.60  thf('21', plain, ((v3_ordinal1 @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('22', plain,
% 0.41/0.60      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.41/0.60         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.41/0.60         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.41/0.60      inference('demod', [status(thm)], ['20', '21'])).
% 0.41/0.60  thf('23', plain,
% 0.41/0.60      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 0.41/0.60         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['17', '22'])).
% 0.41/0.60  thf('24', plain, ((v3_ordinal1 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('25', plain,
% 0.41/0.60      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.41/0.60         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.41/0.60      inference('demod', [status(thm)], ['23', '24'])).
% 0.41/0.60  thf(t1_xboole_1, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.41/0.60       ( r1_tarski @ A @ C ) ))).
% 0.41/0.60  thf('26', plain,
% 0.41/0.60      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.41/0.60         (~ (r1_tarski @ X2 @ X3)
% 0.41/0.60          | ~ (r1_tarski @ X3 @ X4)
% 0.41/0.60          | (r1_tarski @ X2 @ X4))),
% 0.41/0.60      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.41/0.60  thf('27', plain,
% 0.41/0.60      ((![X0 : $i]:
% 0.41/0.60          ((r1_tarski @ (k1_ordinal1 @ sk_A) @ X0) | ~ (r1_tarski @ sk_B @ X0)))
% 0.41/0.60         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['25', '26'])).
% 0.41/0.60  thf('28', plain,
% 0.41/0.60      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_A))
% 0.41/0.60         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.41/0.60             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['16', '27'])).
% 0.41/0.60  thf(t13_ordinal1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.41/0.60       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.41/0.60  thf('29', plain,
% 0.41/0.60      (![X15 : $i, X16 : $i]:
% 0.41/0.60         ((r2_hidden @ X15 @ (k1_ordinal1 @ X16)) | ((X15) != (X16)))),
% 0.41/0.60      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.41/0.60  thf('30', plain, (![X16 : $i]: (r2_hidden @ X16 @ (k1_ordinal1 @ X16))),
% 0.41/0.60      inference('simplify', [status(thm)], ['29'])).
% 0.41/0.60  thf('31', plain,
% 0.41/0.60      (![X20 : $i, X21 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X20 @ X21) | ~ (r1_tarski @ X21 @ X20))),
% 0.41/0.60      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.41/0.60  thf('32', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X0)),
% 0.41/0.60      inference('sup-', [status(thm)], ['30', '31'])).
% 0.41/0.60  thf('33', plain,
% 0.41/0.60      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.41/0.60       ~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.41/0.60      inference('sup-', [status(thm)], ['28', '32'])).
% 0.41/0.60  thf('34', plain,
% 0.41/0.60      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.41/0.60       ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.41/0.60      inference('split', [status(esa)], ['0'])).
% 0.41/0.60  thf('35', plain, (((r2_hidden @ sk_A @ sk_B))),
% 0.41/0.60      inference('sat_resolution*', [status(thm)], ['5', '33', '34'])).
% 0.41/0.60  thf('36', plain, (~ (r1_tarski @ sk_B @ sk_A)),
% 0.41/0.60      inference('simpl_trail', [status(thm)], ['3', '35'])).
% 0.41/0.60  thf('37', plain,
% 0.41/0.60      (![X19 : $i]:
% 0.41/0.60         ((v3_ordinal1 @ (k1_ordinal1 @ X19)) | ~ (v3_ordinal1 @ X19))),
% 0.41/0.60      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.41/0.60  thf('38', plain,
% 0.41/0.60      (![X17 : $i, X18 : $i]:
% 0.41/0.60         (~ (v3_ordinal1 @ X17)
% 0.41/0.60          | (r1_ordinal1 @ X18 @ X17)
% 0.41/0.60          | (r2_hidden @ X17 @ X18)
% 0.41/0.60          | ~ (v3_ordinal1 @ X18))),
% 0.41/0.60      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.41/0.60  thf('39', plain,
% 0.41/0.60      (![X14 : $i, X15 : $i]:
% 0.41/0.60         (((X15) = (X14))
% 0.41/0.60          | (r2_hidden @ X15 @ X14)
% 0.41/0.60          | ~ (r2_hidden @ X15 @ (k1_ordinal1 @ X14)))),
% 0.41/0.60      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.41/0.60  thf('40', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         (~ (v3_ordinal1 @ (k1_ordinal1 @ X0))
% 0.41/0.60          | (r1_ordinal1 @ (k1_ordinal1 @ X0) @ X1)
% 0.41/0.60          | ~ (v3_ordinal1 @ X1)
% 0.41/0.60          | (r2_hidden @ X1 @ X0)
% 0.41/0.60          | ((X1) = (X0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['38', '39'])).
% 0.41/0.60  thf('41', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         (~ (v3_ordinal1 @ X0)
% 0.41/0.60          | ((X1) = (X0))
% 0.41/0.60          | (r2_hidden @ X1 @ X0)
% 0.41/0.60          | ~ (v3_ordinal1 @ X1)
% 0.41/0.60          | (r1_ordinal1 @ (k1_ordinal1 @ X0) @ X1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['37', '40'])).
% 0.41/0.60  thf('42', plain,
% 0.41/0.60      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.41/0.60         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.41/0.60      inference('split', [status(esa)], ['4'])).
% 0.41/0.60  thf('43', plain, (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.41/0.60      inference('sat_resolution*', [status(thm)], ['5', '33'])).
% 0.41/0.60  thf('44', plain, (~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 0.41/0.60      inference('simpl_trail', [status(thm)], ['42', '43'])).
% 0.41/0.60  thf('45', plain,
% 0.41/0.60      ((~ (v3_ordinal1 @ sk_B)
% 0.41/0.60        | (r2_hidden @ sk_B @ sk_A)
% 0.41/0.60        | ((sk_B) = (sk_A))
% 0.41/0.60        | ~ (v3_ordinal1 @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['41', '44'])).
% 0.41/0.60  thf('46', plain, ((v3_ordinal1 @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('47', plain, ((v3_ordinal1 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('48', plain, (((r2_hidden @ sk_B @ sk_A) | ((sk_B) = (sk_A)))),
% 0.41/0.60      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.41/0.60  thf('49', plain,
% 0.41/0.60      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.41/0.60      inference('split', [status(esa)], ['0'])).
% 0.41/0.60  thf(antisymmetry_r2_hidden, axiom,
% 0.41/0.60    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.41/0.60  thf('50', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.41/0.60      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.41/0.60  thf('51', plain,
% 0.41/0.60      ((~ (r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['49', '50'])).
% 0.41/0.60  thf('52', plain, (((r2_hidden @ sk_A @ sk_B))),
% 0.41/0.60      inference('sat_resolution*', [status(thm)], ['5', '33', '34'])).
% 0.41/0.60  thf('53', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 0.41/0.60      inference('simpl_trail', [status(thm)], ['51', '52'])).
% 0.41/0.60  thf('54', plain, (((sk_B) = (sk_A))),
% 0.41/0.60      inference('clc', [status(thm)], ['48', '53'])).
% 0.41/0.60  thf('55', plain, ((v3_ordinal1 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('56', plain,
% 0.41/0.60      (![X17 : $i, X18 : $i]:
% 0.41/0.60         (~ (v3_ordinal1 @ X17)
% 0.41/0.60          | (r1_ordinal1 @ X18 @ X17)
% 0.41/0.60          | (r2_hidden @ X17 @ X18)
% 0.41/0.60          | ~ (v3_ordinal1 @ X18))),
% 0.41/0.60      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.41/0.60  thf('57', plain,
% 0.41/0.60      (![X17 : $i, X18 : $i]:
% 0.41/0.60         (~ (v3_ordinal1 @ X17)
% 0.41/0.60          | (r1_ordinal1 @ X18 @ X17)
% 0.41/0.60          | (r2_hidden @ X17 @ X18)
% 0.41/0.60          | ~ (v3_ordinal1 @ X18))),
% 0.41/0.60      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.41/0.60  thf('58', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.41/0.60      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.41/0.60  thf('59', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         (~ (v3_ordinal1 @ X0)
% 0.41/0.60          | (r1_ordinal1 @ X0 @ X1)
% 0.41/0.60          | ~ (v3_ordinal1 @ X1)
% 0.41/0.60          | ~ (r2_hidden @ X0 @ X1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['57', '58'])).
% 0.41/0.60  thf('60', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         (~ (v3_ordinal1 @ X0)
% 0.41/0.60          | (r1_ordinal1 @ X0 @ X1)
% 0.41/0.60          | ~ (v3_ordinal1 @ X1)
% 0.41/0.60          | ~ (v3_ordinal1 @ X0)
% 0.41/0.60          | (r1_ordinal1 @ X1 @ X0)
% 0.41/0.60          | ~ (v3_ordinal1 @ X1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['56', '59'])).
% 0.41/0.60  thf('61', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((r1_ordinal1 @ X1 @ X0)
% 0.41/0.60          | ~ (v3_ordinal1 @ X1)
% 0.41/0.60          | (r1_ordinal1 @ X0 @ X1)
% 0.41/0.60          | ~ (v3_ordinal1 @ X0))),
% 0.41/0.60      inference('simplify', [status(thm)], ['60'])).
% 0.41/0.60  thf('62', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (v3_ordinal1 @ X0)
% 0.41/0.60          | (r1_ordinal1 @ X0 @ sk_A)
% 0.41/0.60          | (r1_ordinal1 @ sk_A @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['55', '61'])).
% 0.41/0.60  thf('63', plain, (((r1_ordinal1 @ sk_A @ sk_A) | ~ (v3_ordinal1 @ sk_A))),
% 0.41/0.60      inference('eq_fact', [status(thm)], ['62'])).
% 0.41/0.60  thf('64', plain, ((v3_ordinal1 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('65', plain, ((r1_ordinal1 @ sk_A @ sk_A)),
% 0.41/0.60      inference('demod', [status(thm)], ['63', '64'])).
% 0.41/0.60  thf('66', plain,
% 0.41/0.60      (![X12 : $i, X13 : $i]:
% 0.41/0.60         (~ (v3_ordinal1 @ X12)
% 0.41/0.60          | ~ (v3_ordinal1 @ X13)
% 0.41/0.60          | (r1_tarski @ X12 @ X13)
% 0.41/0.60          | ~ (r1_ordinal1 @ X12 @ X13))),
% 0.41/0.60      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.41/0.60  thf('67', plain,
% 0.41/0.60      (((r1_tarski @ sk_A @ sk_A)
% 0.41/0.60        | ~ (v3_ordinal1 @ sk_A)
% 0.41/0.60        | ~ (v3_ordinal1 @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['65', '66'])).
% 0.41/0.60  thf('68', plain, ((v3_ordinal1 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('69', plain, ((v3_ordinal1 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('70', plain, ((r1_tarski @ sk_A @ sk_A)),
% 0.41/0.60      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.41/0.60  thf('71', plain, ($false),
% 0.41/0.60      inference('demod', [status(thm)], ['36', '54', '70'])).
% 0.41/0.60  
% 0.41/0.60  % SZS output end Refutation
% 0.41/0.60  
% 0.41/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

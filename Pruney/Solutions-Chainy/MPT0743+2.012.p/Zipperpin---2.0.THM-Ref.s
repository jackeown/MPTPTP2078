%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.i7ObExJYET

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 599 expanded)
%              Number of leaves         :   20 ( 178 expanded)
%              Depth                    :   21
%              Number of atoms          :  627 (4996 expanded)
%              Number of equality atoms :   21 (  66 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('6',plain,(
    ! [X17: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X17 ) )
      | ~ ( v3_ordinal1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('7',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v3_ordinal1 @ X9 )
      | ~ ( v3_ordinal1 @ X10 )
      | ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_ordinal1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('9',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('15',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v3_ordinal1 @ X15 )
      | ( r1_ordinal1 @ X16 @ X15 )
      | ( r2_hidden @ X15 @ X16 )
      | ~ ( v3_ordinal1 @ X16 ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( r1_tarski @ X19 @ X18 ) ) ),
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
      | ( r1_ordinal1 @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v3_ordinal1 @ X9 )
      | ~ ( v3_ordinal1 @ X10 )
      | ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_ordinal1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('25',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v3_ordinal1 @ X15 )
      | ( r1_ordinal1 @ X16 @ X15 )
      | ( r2_hidden @ X15 @ X16 )
      | ~ ( v3_ordinal1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('30',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('31',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( r1_ordinal1 @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v3_ordinal1 @ X9 )
      | ~ ( v3_ordinal1 @ X10 )
      | ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_ordinal1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('36',plain,
    ( ( ( r1_tarski @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('40',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,
    ( ( ~ ( r1_tarski @ sk_A @ sk_B )
      | ( sk_A = sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','41'])).

thf('43',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('44',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('45',plain,
    ( ( ~ ( r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ~ ( r1_tarski @ sk_A @ ( k1_ordinal1 @ sk_A ) )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('47',plain,(
    ! [X8: $i] :
      ( ( k1_ordinal1 @ X8 )
      = ( k2_xboole_0 @ X8 @ ( k1_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('48',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','41'])).

thf('51',plain,
    ( ( sk_A
      = ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['46','49','50'])).

thf(t14_ordinal1,axiom,(
    ! [A: $i] :
      ( A
     != ( k1_ordinal1 @ A ) ) )).

thf('52',plain,(
    ! [X14: $i] :
      ( X14
     != ( k1_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t14_ordinal1])).

thf('53',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('55',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['5','53','54'])).

thf('56',plain,(
    ~ ( r1_tarski @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['3','55'])).

thf('57',plain,(
    ! [X17: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X17 ) )
      | ~ ( v3_ordinal1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('58',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v3_ordinal1 @ X15 )
      | ( r1_ordinal1 @ X16 @ X15 )
      | ( r2_hidden @ X15 @ X16 )
      | ~ ( v3_ordinal1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('59',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X12 = X11 )
      | ( r2_hidden @ X12 @ X11 )
      | ~ ( r2_hidden @ X12 @ ( k1_ordinal1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X0 ) @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('63',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['5','53'])).

thf('64',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['62','63'])).

thf('65',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r2_hidden @ sk_B @ sk_A )
    | ( sk_B = sk_A )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( sk_B = sk_A ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('71',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['5','53','54'])).

thf('73',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['71','72'])).

thf('74',plain,(
    sk_B = sk_A ),
    inference(clc,[status(thm)],['68','73'])).

thf('75',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('76',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    $false ),
    inference(demod,[status(thm)],['56','74','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.i7ObExJYET
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:01:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.58  % Solved by: fo/fo7.sh
% 0.22/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.58  % done 342 iterations in 0.119s
% 0.22/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.58  % SZS output start Refutation
% 0.22/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.58  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.22/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.58  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.22/0.58  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.22/0.58  thf(t33_ordinal1, conjecture,
% 0.22/0.58    (![A:$i]:
% 0.22/0.58     ( ( v3_ordinal1 @ A ) =>
% 0.22/0.58       ( ![B:$i]:
% 0.22/0.58         ( ( v3_ordinal1 @ B ) =>
% 0.22/0.58           ( ( r2_hidden @ A @ B ) <=>
% 0.22/0.58             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 0.22/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.58    (~( ![A:$i]:
% 0.22/0.58        ( ( v3_ordinal1 @ A ) =>
% 0.22/0.58          ( ![B:$i]:
% 0.22/0.58            ( ( v3_ordinal1 @ B ) =>
% 0.22/0.58              ( ( r2_hidden @ A @ B ) <=>
% 0.22/0.58                ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ) )),
% 0.22/0.58    inference('cnf.neg', [status(esa)], [t33_ordinal1])).
% 0.22/0.58  thf('0', plain,
% 0.22/0.58      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('1', plain,
% 0.22/0.58      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.22/0.58      inference('split', [status(esa)], ['0'])).
% 0.22/0.58  thf(t7_ordinal1, axiom,
% 0.22/0.58    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.58  thf('2', plain,
% 0.22/0.58      (![X18 : $i, X19 : $i]:
% 0.22/0.58         (~ (r2_hidden @ X18 @ X19) | ~ (r1_tarski @ X19 @ X18))),
% 0.22/0.58      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.22/0.58  thf('3', plain,
% 0.22/0.58      ((~ (r1_tarski @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.58  thf('4', plain,
% 0.22/0.58      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.22/0.58        | ~ (r2_hidden @ sk_A @ sk_B))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('5', plain,
% 0.22/0.58      (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 0.22/0.58       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.22/0.58      inference('split', [status(esa)], ['4'])).
% 0.22/0.58  thf(t29_ordinal1, axiom,
% 0.22/0.58    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 0.22/0.58  thf('6', plain,
% 0.22/0.58      (![X17 : $i]:
% 0.22/0.58         ((v3_ordinal1 @ (k1_ordinal1 @ X17)) | ~ (v3_ordinal1 @ X17))),
% 0.22/0.58      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.22/0.58  thf('7', plain,
% 0.22/0.58      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.22/0.58         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.22/0.58      inference('split', [status(esa)], ['0'])).
% 0.22/0.58  thf(redefinition_r1_ordinal1, axiom,
% 0.22/0.58    (![A:$i,B:$i]:
% 0.22/0.58     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.22/0.58       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.22/0.58  thf('8', plain,
% 0.22/0.58      (![X9 : $i, X10 : $i]:
% 0.22/0.58         (~ (v3_ordinal1 @ X9)
% 0.22/0.58          | ~ (v3_ordinal1 @ X10)
% 0.22/0.58          | (r1_tarski @ X9 @ X10)
% 0.22/0.58          | ~ (r1_ordinal1 @ X9 @ X10))),
% 0.22/0.58      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.22/0.58  thf('9', plain,
% 0.22/0.58      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.22/0.58         | ~ (v3_ordinal1 @ sk_B)
% 0.22/0.58         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.22/0.58         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.58  thf('10', plain, ((v3_ordinal1 @ sk_B)),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('11', plain,
% 0.22/0.58      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.22/0.58         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.22/0.58         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.22/0.58      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.58  thf('12', plain,
% 0.22/0.58      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 0.22/0.58         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['6', '11'])).
% 0.22/0.58  thf('13', plain, ((v3_ordinal1 @ sk_A)),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('14', plain,
% 0.22/0.58      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.22/0.58         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.22/0.58      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.58  thf(t26_ordinal1, axiom,
% 0.22/0.58    (![A:$i]:
% 0.22/0.58     ( ( v3_ordinal1 @ A ) =>
% 0.22/0.58       ( ![B:$i]:
% 0.22/0.58         ( ( v3_ordinal1 @ B ) =>
% 0.22/0.58           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.22/0.58  thf('15', plain,
% 0.22/0.58      (![X15 : $i, X16 : $i]:
% 0.22/0.58         (~ (v3_ordinal1 @ X15)
% 0.22/0.58          | (r1_ordinal1 @ X16 @ X15)
% 0.22/0.58          | (r2_hidden @ X15 @ X16)
% 0.22/0.58          | ~ (v3_ordinal1 @ X16))),
% 0.22/0.58      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.22/0.58  thf(t13_ordinal1, axiom,
% 0.22/0.58    (![A:$i,B:$i]:
% 0.22/0.58     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.22/0.58       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.22/0.58  thf('16', plain,
% 0.22/0.58      (![X12 : $i, X13 : $i]:
% 0.22/0.58         ((r2_hidden @ X12 @ (k1_ordinal1 @ X13)) | ~ (r2_hidden @ X12 @ X13))),
% 0.22/0.58      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.22/0.58  thf('17', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         (~ (v3_ordinal1 @ X0)
% 0.22/0.58          | (r1_ordinal1 @ X0 @ X1)
% 0.22/0.58          | ~ (v3_ordinal1 @ X1)
% 0.22/0.58          | (r2_hidden @ X1 @ (k1_ordinal1 @ X0)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.58  thf('18', plain,
% 0.22/0.58      (![X18 : $i, X19 : $i]:
% 0.22/0.58         (~ (r2_hidden @ X18 @ X19) | ~ (r1_tarski @ X19 @ X18))),
% 0.22/0.58      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.22/0.58  thf('19', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         (~ (v3_ordinal1 @ X1)
% 0.22/0.58          | (r1_ordinal1 @ X0 @ X1)
% 0.22/0.58          | ~ (v3_ordinal1 @ X0)
% 0.22/0.58          | ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X1))),
% 0.22/0.58      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.58  thf('20', plain,
% 0.22/0.58      (((~ (v3_ordinal1 @ sk_A)
% 0.22/0.58         | (r1_ordinal1 @ sk_A @ sk_B)
% 0.22/0.58         | ~ (v3_ordinal1 @ sk_B)))
% 0.22/0.58         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['14', '19'])).
% 0.22/0.58  thf('21', plain, ((v3_ordinal1 @ sk_A)),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('22', plain, ((v3_ordinal1 @ sk_B)),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('23', plain,
% 0.22/0.58      (((r1_ordinal1 @ sk_A @ sk_B))
% 0.22/0.58         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.22/0.58      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.22/0.58  thf('24', plain,
% 0.22/0.58      (![X9 : $i, X10 : $i]:
% 0.22/0.58         (~ (v3_ordinal1 @ X9)
% 0.22/0.58          | ~ (v3_ordinal1 @ X10)
% 0.22/0.58          | (r1_tarski @ X9 @ X10)
% 0.22/0.58          | ~ (r1_ordinal1 @ X9 @ X10))),
% 0.22/0.58      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.22/0.58  thf('25', plain,
% 0.22/0.58      ((((r1_tarski @ sk_A @ sk_B)
% 0.22/0.58         | ~ (v3_ordinal1 @ sk_B)
% 0.22/0.58         | ~ (v3_ordinal1 @ sk_A)))
% 0.22/0.58         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.58  thf('26', plain, ((v3_ordinal1 @ sk_B)),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('27', plain, ((v3_ordinal1 @ sk_A)),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('28', plain,
% 0.22/0.58      (((r1_tarski @ sk_A @ sk_B))
% 0.22/0.58         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.22/0.58      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.22/0.58  thf('29', plain,
% 0.22/0.58      (![X15 : $i, X16 : $i]:
% 0.22/0.58         (~ (v3_ordinal1 @ X15)
% 0.22/0.58          | (r1_ordinal1 @ X16 @ X15)
% 0.22/0.58          | (r2_hidden @ X15 @ X16)
% 0.22/0.58          | ~ (v3_ordinal1 @ X16))),
% 0.22/0.58      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.22/0.58  thf('30', plain,
% 0.22/0.58      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.22/0.58      inference('split', [status(esa)], ['4'])).
% 0.22/0.58  thf('31', plain,
% 0.22/0.58      (((~ (v3_ordinal1 @ sk_B)
% 0.22/0.58         | (r1_ordinal1 @ sk_B @ sk_A)
% 0.22/0.58         | ~ (v3_ordinal1 @ sk_A))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.58  thf('32', plain, ((v3_ordinal1 @ sk_B)),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('33', plain, ((v3_ordinal1 @ sk_A)),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('34', plain,
% 0.22/0.58      (((r1_ordinal1 @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.22/0.58      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.22/0.58  thf('35', plain,
% 0.22/0.58      (![X9 : $i, X10 : $i]:
% 0.22/0.58         (~ (v3_ordinal1 @ X9)
% 0.22/0.58          | ~ (v3_ordinal1 @ X10)
% 0.22/0.58          | (r1_tarski @ X9 @ X10)
% 0.22/0.58          | ~ (r1_ordinal1 @ X9 @ X10))),
% 0.22/0.58      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.22/0.58  thf('36', plain,
% 0.22/0.58      ((((r1_tarski @ sk_B @ sk_A)
% 0.22/0.58         | ~ (v3_ordinal1 @ sk_A)
% 0.22/0.58         | ~ (v3_ordinal1 @ sk_B))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['34', '35'])).
% 0.22/0.58  thf('37', plain, ((v3_ordinal1 @ sk_A)),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('38', plain, ((v3_ordinal1 @ sk_B)),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('39', plain,
% 0.22/0.58      (((r1_tarski @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.22/0.58      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.22/0.58  thf(d10_xboole_0, axiom,
% 0.22/0.58    (![A:$i,B:$i]:
% 0.22/0.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.58  thf('40', plain,
% 0.22/0.58      (![X2 : $i, X4 : $i]:
% 0.22/0.58         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.22/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.58  thf('41', plain,
% 0.22/0.58      (((~ (r1_tarski @ sk_A @ sk_B) | ((sk_A) = (sk_B))))
% 0.22/0.58         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['39', '40'])).
% 0.22/0.58  thf('42', plain,
% 0.22/0.58      ((((sk_A) = (sk_B)))
% 0.22/0.58         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.22/0.58             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['28', '41'])).
% 0.22/0.58  thf('43', plain,
% 0.22/0.58      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.22/0.58         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.22/0.58      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.58  thf('44', plain,
% 0.22/0.58      (![X2 : $i, X4 : $i]:
% 0.22/0.58         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.22/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.58  thf('45', plain,
% 0.22/0.58      (((~ (r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.22/0.58         | ((sk_B) = (k1_ordinal1 @ sk_A))))
% 0.22/0.58         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['43', '44'])).
% 0.22/0.58  thf('46', plain,
% 0.22/0.58      (((~ (r1_tarski @ sk_A @ (k1_ordinal1 @ sk_A))
% 0.22/0.58         | ((sk_B) = (k1_ordinal1 @ sk_A))))
% 0.22/0.58         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.22/0.58             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['42', '45'])).
% 0.22/0.58  thf(d1_ordinal1, axiom,
% 0.22/0.58    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.22/0.58  thf('47', plain,
% 0.22/0.58      (![X8 : $i]: ((k1_ordinal1 @ X8) = (k2_xboole_0 @ X8 @ (k1_tarski @ X8)))),
% 0.22/0.58      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.22/0.58  thf(t7_xboole_1, axiom,
% 0.22/0.58    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.58  thf('48', plain,
% 0.22/0.58      (![X5 : $i, X6 : $i]: (r1_tarski @ X5 @ (k2_xboole_0 @ X5 @ X6))),
% 0.22/0.58      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.22/0.58  thf('49', plain, (![X0 : $i]: (r1_tarski @ X0 @ (k1_ordinal1 @ X0))),
% 0.22/0.58      inference('sup+', [status(thm)], ['47', '48'])).
% 0.22/0.58  thf('50', plain,
% 0.22/0.58      ((((sk_A) = (sk_B)))
% 0.22/0.58         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.22/0.58             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['28', '41'])).
% 0.22/0.58  thf('51', plain,
% 0.22/0.58      ((((sk_A) = (k1_ordinal1 @ sk_A)))
% 0.22/0.58         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.22/0.58             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.22/0.58      inference('demod', [status(thm)], ['46', '49', '50'])).
% 0.22/0.58  thf(t14_ordinal1, axiom, (![A:$i]: ( ( A ) != ( k1_ordinal1 @ A ) ))).
% 0.22/0.58  thf('52', plain, (![X14 : $i]: ((X14) != (k1_ordinal1 @ X14))),
% 0.22/0.58      inference('cnf', [status(esa)], [t14_ordinal1])).
% 0.22/0.58  thf('53', plain,
% 0.22/0.58      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.22/0.58       ~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.22/0.58      inference('simplify_reflect-', [status(thm)], ['51', '52'])).
% 0.22/0.58  thf('54', plain,
% 0.22/0.58      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.22/0.58       ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.22/0.58      inference('split', [status(esa)], ['0'])).
% 0.22/0.58  thf('55', plain, (((r2_hidden @ sk_A @ sk_B))),
% 0.22/0.58      inference('sat_resolution*', [status(thm)], ['5', '53', '54'])).
% 0.22/0.58  thf('56', plain, (~ (r1_tarski @ sk_B @ sk_A)),
% 0.22/0.58      inference('simpl_trail', [status(thm)], ['3', '55'])).
% 0.22/0.58  thf('57', plain,
% 0.22/0.58      (![X17 : $i]:
% 0.22/0.58         ((v3_ordinal1 @ (k1_ordinal1 @ X17)) | ~ (v3_ordinal1 @ X17))),
% 0.22/0.58      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.22/0.58  thf('58', plain,
% 0.22/0.58      (![X15 : $i, X16 : $i]:
% 0.22/0.58         (~ (v3_ordinal1 @ X15)
% 0.22/0.58          | (r1_ordinal1 @ X16 @ X15)
% 0.22/0.58          | (r2_hidden @ X15 @ X16)
% 0.22/0.58          | ~ (v3_ordinal1 @ X16))),
% 0.22/0.58      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.22/0.58  thf('59', plain,
% 0.22/0.58      (![X11 : $i, X12 : $i]:
% 0.22/0.58         (((X12) = (X11))
% 0.22/0.58          | (r2_hidden @ X12 @ X11)
% 0.22/0.58          | ~ (r2_hidden @ X12 @ (k1_ordinal1 @ X11)))),
% 0.22/0.58      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.22/0.58  thf('60', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         (~ (v3_ordinal1 @ (k1_ordinal1 @ X0))
% 0.22/0.58          | (r1_ordinal1 @ (k1_ordinal1 @ X0) @ X1)
% 0.22/0.58          | ~ (v3_ordinal1 @ X1)
% 0.22/0.58          | (r2_hidden @ X1 @ X0)
% 0.22/0.58          | ((X1) = (X0)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['58', '59'])).
% 0.22/0.58  thf('61', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         (~ (v3_ordinal1 @ X0)
% 0.22/0.58          | ((X1) = (X0))
% 0.22/0.58          | (r2_hidden @ X1 @ X0)
% 0.22/0.58          | ~ (v3_ordinal1 @ X1)
% 0.22/0.58          | (r1_ordinal1 @ (k1_ordinal1 @ X0) @ X1))),
% 0.22/0.58      inference('sup-', [status(thm)], ['57', '60'])).
% 0.22/0.58  thf('62', plain,
% 0.22/0.58      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.22/0.58         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.22/0.58      inference('split', [status(esa)], ['4'])).
% 0.22/0.58  thf('63', plain, (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.22/0.58      inference('sat_resolution*', [status(thm)], ['5', '53'])).
% 0.22/0.58  thf('64', plain, (~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 0.22/0.58      inference('simpl_trail', [status(thm)], ['62', '63'])).
% 0.22/0.58  thf('65', plain,
% 0.22/0.58      ((~ (v3_ordinal1 @ sk_B)
% 0.22/0.58        | (r2_hidden @ sk_B @ sk_A)
% 0.22/0.58        | ((sk_B) = (sk_A))
% 0.22/0.58        | ~ (v3_ordinal1 @ sk_A))),
% 0.22/0.58      inference('sup-', [status(thm)], ['61', '64'])).
% 0.22/0.58  thf('66', plain, ((v3_ordinal1 @ sk_B)),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('67', plain, ((v3_ordinal1 @ sk_A)),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('68', plain, (((r2_hidden @ sk_B @ sk_A) | ((sk_B) = (sk_A)))),
% 0.22/0.58      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.22/0.58  thf('69', plain,
% 0.22/0.58      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.22/0.58      inference('split', [status(esa)], ['0'])).
% 0.22/0.58  thf(antisymmetry_r2_hidden, axiom,
% 0.22/0.58    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.22/0.58  thf('70', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.22/0.58      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.22/0.58  thf('71', plain,
% 0.22/0.58      ((~ (r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['69', '70'])).
% 0.22/0.58  thf('72', plain, (((r2_hidden @ sk_A @ sk_B))),
% 0.22/0.58      inference('sat_resolution*', [status(thm)], ['5', '53', '54'])).
% 0.22/0.58  thf('73', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 0.22/0.58      inference('simpl_trail', [status(thm)], ['71', '72'])).
% 0.22/0.58  thf('74', plain, (((sk_B) = (sk_A))),
% 0.22/0.58      inference('clc', [status(thm)], ['68', '73'])).
% 0.22/0.58  thf('75', plain,
% 0.22/0.58      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.22/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.58  thf('76', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.22/0.58      inference('simplify', [status(thm)], ['75'])).
% 0.22/0.58  thf('77', plain, ($false),
% 0.22/0.58      inference('demod', [status(thm)], ['56', '74', '76'])).
% 0.22/0.58  
% 0.22/0.58  % SZS output end Refutation
% 0.22/0.58  
% 0.22/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0PSoy4yAnH

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:53 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 543 expanded)
%              Number of leaves         :   21 ( 161 expanded)
%              Depth                    :   20
%              Number of atoms          :  619 (4366 expanded)
%              Number of equality atoms :   24 ( 111 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('26',plain,(
    ! [X8: $i] :
      ( ( k2_tarski @ X8 @ X8 )
      = ( k1_tarski @ X8 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('27',plain,(
    ! [X11: $i] :
      ( ( k1_ordinal1 @ X11 )
      = ( k2_xboole_0 @ X11 @ ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k1_ordinal1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('29',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X5 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X1 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('32',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('33',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_A )
      | ( sk_B = sk_A ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_B = sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','33'])).

thf('35',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('36',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('37',plain,
    ( ( ~ ( r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ~ ( r1_tarski @ sk_A @ ( k1_ordinal1 @ sk_A ) )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k1_ordinal1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('40',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X5 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','43'])).

thf('45',plain,
    ( ( sk_B = sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','33'])).

thf('46',plain,
    ( ( sk_A
      = ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','44','45'])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('47',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r2_hidden @ X15 @ ( k1_ordinal1 @ X16 ) )
      | ( X15 != X16 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('48',plain,(
    ! [X16: $i] :
      ( r2_hidden @ X16 @ ( k1_ordinal1 @ X16 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( r1_tarski @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('50',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','50'])).

thf('52',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['40'])).

thf('53',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['51','52'])).

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
    ! [X19: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X19 ) )
      | ~ ( v3_ordinal1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('58',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_ordinal1 @ X17 )
      | ( r1_ordinal1 @ X18 @ X17 )
      | ( r2_hidden @ X17 @ X18 )
      | ~ ( v3_ordinal1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('59',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X15 = X14 )
      | ( r2_hidden @ X15 @ X14 )
      | ~ ( r2_hidden @ X15 @ ( k1_ordinal1 @ X14 ) ) ) ),
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
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['40'])).

thf('76',plain,(
    $false ),
    inference(demod,[status(thm)],['56','74','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0PSoy4yAnH
% 0.14/0.36  % Computer   : n021.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 15:05:34 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.45/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.71  % Solved by: fo/fo7.sh
% 0.45/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.71  % done 494 iterations in 0.232s
% 0.45/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.71  % SZS output start Refutation
% 0.45/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.71  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.71  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.45/0.71  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.71  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.45/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.71  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.45/0.71  thf(t33_ordinal1, conjecture,
% 0.45/0.71    (![A:$i]:
% 0.45/0.71     ( ( v3_ordinal1 @ A ) =>
% 0.45/0.71       ( ![B:$i]:
% 0.45/0.71         ( ( v3_ordinal1 @ B ) =>
% 0.45/0.71           ( ( r2_hidden @ A @ B ) <=>
% 0.45/0.71             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 0.45/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.71    (~( ![A:$i]:
% 0.45/0.71        ( ( v3_ordinal1 @ A ) =>
% 0.45/0.71          ( ![B:$i]:
% 0.45/0.71            ( ( v3_ordinal1 @ B ) =>
% 0.45/0.71              ( ( r2_hidden @ A @ B ) <=>
% 0.45/0.71                ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ) )),
% 0.45/0.71    inference('cnf.neg', [status(esa)], [t33_ordinal1])).
% 0.45/0.71  thf('0', plain,
% 0.45/0.71      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('1', plain,
% 0.45/0.71      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.45/0.71      inference('split', [status(esa)], ['0'])).
% 0.45/0.71  thf(t7_ordinal1, axiom,
% 0.45/0.71    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.71  thf('2', plain,
% 0.45/0.71      (![X20 : $i, X21 : $i]:
% 0.45/0.71         (~ (r2_hidden @ X20 @ X21) | ~ (r1_tarski @ X21 @ X20))),
% 0.45/0.71      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.45/0.71  thf('3', plain,
% 0.45/0.71      ((~ (r1_tarski @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.45/0.71      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.71  thf('4', plain,
% 0.45/0.71      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.45/0.71        | ~ (r2_hidden @ sk_A @ sk_B))),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('5', plain,
% 0.45/0.71      (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 0.45/0.71       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.45/0.71      inference('split', [status(esa)], ['4'])).
% 0.45/0.71  thf(t26_ordinal1, axiom,
% 0.45/0.71    (![A:$i]:
% 0.45/0.71     ( ( v3_ordinal1 @ A ) =>
% 0.45/0.71       ( ![B:$i]:
% 0.45/0.71         ( ( v3_ordinal1 @ B ) =>
% 0.45/0.71           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.45/0.71  thf('6', plain,
% 0.45/0.71      (![X17 : $i, X18 : $i]:
% 0.45/0.71         (~ (v3_ordinal1 @ X17)
% 0.45/0.71          | (r1_ordinal1 @ X18 @ X17)
% 0.45/0.71          | (r2_hidden @ X17 @ X18)
% 0.45/0.71          | ~ (v3_ordinal1 @ X18))),
% 0.45/0.71      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.45/0.71  thf('7', plain,
% 0.45/0.71      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.45/0.71      inference('split', [status(esa)], ['4'])).
% 0.45/0.71  thf('8', plain,
% 0.45/0.71      (((~ (v3_ordinal1 @ sk_B)
% 0.45/0.71         | (r1_ordinal1 @ sk_B @ sk_A)
% 0.45/0.71         | ~ (v3_ordinal1 @ sk_A))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.45/0.71      inference('sup-', [status(thm)], ['6', '7'])).
% 0.45/0.71  thf('9', plain, ((v3_ordinal1 @ sk_B)),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('10', plain, ((v3_ordinal1 @ sk_A)),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('11', plain,
% 0.45/0.71      (((r1_ordinal1 @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.45/0.71      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.45/0.71  thf(redefinition_r1_ordinal1, axiom,
% 0.45/0.71    (![A:$i,B:$i]:
% 0.45/0.71     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.45/0.71       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.45/0.71  thf('12', plain,
% 0.45/0.71      (![X12 : $i, X13 : $i]:
% 0.45/0.71         (~ (v3_ordinal1 @ X12)
% 0.45/0.71          | ~ (v3_ordinal1 @ X13)
% 0.45/0.71          | (r1_tarski @ X12 @ X13)
% 0.45/0.71          | ~ (r1_ordinal1 @ X12 @ X13))),
% 0.45/0.71      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.45/0.71  thf('13', plain,
% 0.45/0.71      ((((r1_tarski @ sk_B @ sk_A)
% 0.45/0.71         | ~ (v3_ordinal1 @ sk_A)
% 0.45/0.71         | ~ (v3_ordinal1 @ sk_B))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.45/0.71      inference('sup-', [status(thm)], ['11', '12'])).
% 0.45/0.71  thf('14', plain, ((v3_ordinal1 @ sk_A)),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('15', plain, ((v3_ordinal1 @ sk_B)),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('16', plain,
% 0.45/0.71      (((r1_tarski @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.45/0.71      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.45/0.71  thf(t29_ordinal1, axiom,
% 0.45/0.71    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 0.45/0.71  thf('17', plain,
% 0.45/0.71      (![X19 : $i]:
% 0.45/0.71         ((v3_ordinal1 @ (k1_ordinal1 @ X19)) | ~ (v3_ordinal1 @ X19))),
% 0.45/0.71      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.45/0.71  thf('18', plain,
% 0.45/0.71      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.45/0.71         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.45/0.71      inference('split', [status(esa)], ['0'])).
% 0.45/0.71  thf('19', plain,
% 0.45/0.71      (![X12 : $i, X13 : $i]:
% 0.45/0.71         (~ (v3_ordinal1 @ X12)
% 0.45/0.71          | ~ (v3_ordinal1 @ X13)
% 0.45/0.71          | (r1_tarski @ X12 @ X13)
% 0.45/0.71          | ~ (r1_ordinal1 @ X12 @ X13))),
% 0.45/0.71      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.45/0.71  thf('20', plain,
% 0.45/0.71      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.45/0.71         | ~ (v3_ordinal1 @ sk_B)
% 0.45/0.71         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.45/0.71         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.45/0.71      inference('sup-', [status(thm)], ['18', '19'])).
% 0.45/0.71  thf('21', plain, ((v3_ordinal1 @ sk_B)),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('22', plain,
% 0.45/0.71      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.45/0.71         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.45/0.71         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.45/0.71      inference('demod', [status(thm)], ['20', '21'])).
% 0.45/0.71  thf('23', plain,
% 0.45/0.71      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 0.45/0.71         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.45/0.71      inference('sup-', [status(thm)], ['17', '22'])).
% 0.45/0.71  thf('24', plain, ((v3_ordinal1 @ sk_A)),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('25', plain,
% 0.45/0.71      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.45/0.71         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.45/0.71      inference('demod', [status(thm)], ['23', '24'])).
% 0.45/0.71  thf(t69_enumset1, axiom,
% 0.45/0.71    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.45/0.71  thf('26', plain, (![X8 : $i]: ((k2_tarski @ X8 @ X8) = (k1_tarski @ X8))),
% 0.45/0.71      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.71  thf(d1_ordinal1, axiom,
% 0.45/0.71    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.45/0.71  thf('27', plain,
% 0.45/0.71      (![X11 : $i]:
% 0.45/0.71         ((k1_ordinal1 @ X11) = (k2_xboole_0 @ X11 @ (k1_tarski @ X11)))),
% 0.45/0.71      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.45/0.71  thf('28', plain,
% 0.45/0.71      (![X0 : $i]:
% 0.45/0.71         ((k1_ordinal1 @ X0) = (k2_xboole_0 @ X0 @ (k2_tarski @ X0 @ X0)))),
% 0.45/0.71      inference('sup+', [status(thm)], ['26', '27'])).
% 0.45/0.71  thf(t11_xboole_1, axiom,
% 0.45/0.71    (![A:$i,B:$i,C:$i]:
% 0.45/0.71     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.45/0.71  thf('29', plain,
% 0.45/0.71      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.71         ((r1_tarski @ X5 @ X6) | ~ (r1_tarski @ (k2_xboole_0 @ X5 @ X7) @ X6))),
% 0.45/0.71      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.45/0.71  thf('30', plain,
% 0.45/0.71      (![X0 : $i, X1 : $i]:
% 0.45/0.71         (~ (r1_tarski @ (k1_ordinal1 @ X0) @ X1) | (r1_tarski @ X0 @ X1))),
% 0.45/0.71      inference('sup-', [status(thm)], ['28', '29'])).
% 0.45/0.71  thf('31', plain,
% 0.45/0.71      (((r1_tarski @ sk_A @ sk_B))
% 0.45/0.71         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.45/0.71      inference('sup-', [status(thm)], ['25', '30'])).
% 0.45/0.71  thf(d10_xboole_0, axiom,
% 0.45/0.71    (![A:$i,B:$i]:
% 0.45/0.71     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.71  thf('32', plain,
% 0.45/0.71      (![X2 : $i, X4 : $i]:
% 0.45/0.71         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.45/0.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.71  thf('33', plain,
% 0.45/0.71      (((~ (r1_tarski @ sk_B @ sk_A) | ((sk_B) = (sk_A))))
% 0.45/0.71         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.45/0.71      inference('sup-', [status(thm)], ['31', '32'])).
% 0.45/0.71  thf('34', plain,
% 0.45/0.71      ((((sk_B) = (sk_A)))
% 0.45/0.71         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.45/0.71             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.45/0.71      inference('sup-', [status(thm)], ['16', '33'])).
% 0.45/0.71  thf('35', plain,
% 0.45/0.71      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.45/0.71         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.45/0.71      inference('demod', [status(thm)], ['23', '24'])).
% 0.45/0.71  thf('36', plain,
% 0.45/0.71      (![X2 : $i, X4 : $i]:
% 0.45/0.71         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.45/0.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.71  thf('37', plain,
% 0.45/0.71      (((~ (r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.45/0.71         | ((sk_B) = (k1_ordinal1 @ sk_A))))
% 0.45/0.71         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.45/0.71      inference('sup-', [status(thm)], ['35', '36'])).
% 0.45/0.71  thf('38', plain,
% 0.45/0.71      (((~ (r1_tarski @ sk_A @ (k1_ordinal1 @ sk_A))
% 0.45/0.71         | ((sk_B) = (k1_ordinal1 @ sk_A))))
% 0.45/0.71         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.45/0.71             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.45/0.71      inference('sup-', [status(thm)], ['34', '37'])).
% 0.45/0.71  thf('39', plain,
% 0.45/0.71      (![X0 : $i]:
% 0.45/0.71         ((k1_ordinal1 @ X0) = (k2_xboole_0 @ X0 @ (k2_tarski @ X0 @ X0)))),
% 0.45/0.71      inference('sup+', [status(thm)], ['26', '27'])).
% 0.45/0.71  thf('40', plain,
% 0.45/0.71      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.45/0.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.71  thf('41', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.45/0.71      inference('simplify', [status(thm)], ['40'])).
% 0.45/0.71  thf('42', plain,
% 0.45/0.71      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.71         ((r1_tarski @ X5 @ X6) | ~ (r1_tarski @ (k2_xboole_0 @ X5 @ X7) @ X6))),
% 0.45/0.71      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.45/0.71  thf('43', plain,
% 0.45/0.71      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.45/0.71      inference('sup-', [status(thm)], ['41', '42'])).
% 0.45/0.71  thf('44', plain, (![X0 : $i]: (r1_tarski @ X0 @ (k1_ordinal1 @ X0))),
% 0.45/0.71      inference('sup+', [status(thm)], ['39', '43'])).
% 0.45/0.71  thf('45', plain,
% 0.45/0.71      ((((sk_B) = (sk_A)))
% 0.45/0.71         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.45/0.71             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.45/0.71      inference('sup-', [status(thm)], ['16', '33'])).
% 0.45/0.71  thf('46', plain,
% 0.45/0.71      ((((sk_A) = (k1_ordinal1 @ sk_A)))
% 0.45/0.71         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.45/0.71             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.45/0.71      inference('demod', [status(thm)], ['38', '44', '45'])).
% 0.45/0.71  thf(t13_ordinal1, axiom,
% 0.45/0.71    (![A:$i,B:$i]:
% 0.45/0.71     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.45/0.71       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.45/0.71  thf('47', plain,
% 0.45/0.71      (![X15 : $i, X16 : $i]:
% 0.45/0.71         ((r2_hidden @ X15 @ (k1_ordinal1 @ X16)) | ((X15) != (X16)))),
% 0.45/0.71      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.45/0.71  thf('48', plain, (![X16 : $i]: (r2_hidden @ X16 @ (k1_ordinal1 @ X16))),
% 0.45/0.71      inference('simplify', [status(thm)], ['47'])).
% 0.45/0.71  thf('49', plain,
% 0.45/0.71      (![X20 : $i, X21 : $i]:
% 0.45/0.71         (~ (r2_hidden @ X20 @ X21) | ~ (r1_tarski @ X21 @ X20))),
% 0.45/0.71      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.45/0.71  thf('50', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X0)),
% 0.45/0.71      inference('sup-', [status(thm)], ['48', '49'])).
% 0.45/0.71  thf('51', plain,
% 0.45/0.71      ((~ (r1_tarski @ sk_A @ sk_A))
% 0.45/0.71         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.45/0.71             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.45/0.71      inference('sup-', [status(thm)], ['46', '50'])).
% 0.45/0.71  thf('52', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.45/0.71      inference('simplify', [status(thm)], ['40'])).
% 0.45/0.71  thf('53', plain,
% 0.45/0.71      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.45/0.71       ~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.45/0.71      inference('demod', [status(thm)], ['51', '52'])).
% 0.45/0.71  thf('54', plain,
% 0.45/0.71      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.45/0.71       ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.45/0.71      inference('split', [status(esa)], ['0'])).
% 0.45/0.71  thf('55', plain, (((r2_hidden @ sk_A @ sk_B))),
% 0.45/0.71      inference('sat_resolution*', [status(thm)], ['5', '53', '54'])).
% 0.45/0.71  thf('56', plain, (~ (r1_tarski @ sk_B @ sk_A)),
% 0.45/0.71      inference('simpl_trail', [status(thm)], ['3', '55'])).
% 0.45/0.71  thf('57', plain,
% 0.45/0.71      (![X19 : $i]:
% 0.45/0.71         ((v3_ordinal1 @ (k1_ordinal1 @ X19)) | ~ (v3_ordinal1 @ X19))),
% 0.45/0.71      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.45/0.71  thf('58', plain,
% 0.45/0.71      (![X17 : $i, X18 : $i]:
% 0.45/0.71         (~ (v3_ordinal1 @ X17)
% 0.45/0.71          | (r1_ordinal1 @ X18 @ X17)
% 0.45/0.71          | (r2_hidden @ X17 @ X18)
% 0.45/0.71          | ~ (v3_ordinal1 @ X18))),
% 0.45/0.71      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.45/0.71  thf('59', plain,
% 0.45/0.71      (![X14 : $i, X15 : $i]:
% 0.45/0.71         (((X15) = (X14))
% 0.45/0.71          | (r2_hidden @ X15 @ X14)
% 0.45/0.71          | ~ (r2_hidden @ X15 @ (k1_ordinal1 @ X14)))),
% 0.45/0.71      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.45/0.71  thf('60', plain,
% 0.45/0.71      (![X0 : $i, X1 : $i]:
% 0.45/0.71         (~ (v3_ordinal1 @ (k1_ordinal1 @ X0))
% 0.45/0.71          | (r1_ordinal1 @ (k1_ordinal1 @ X0) @ X1)
% 0.45/0.71          | ~ (v3_ordinal1 @ X1)
% 0.45/0.71          | (r2_hidden @ X1 @ X0)
% 0.45/0.71          | ((X1) = (X0)))),
% 0.45/0.71      inference('sup-', [status(thm)], ['58', '59'])).
% 0.45/0.71  thf('61', plain,
% 0.45/0.71      (![X0 : $i, X1 : $i]:
% 0.45/0.71         (~ (v3_ordinal1 @ X0)
% 0.45/0.71          | ((X1) = (X0))
% 0.45/0.71          | (r2_hidden @ X1 @ X0)
% 0.45/0.71          | ~ (v3_ordinal1 @ X1)
% 0.45/0.71          | (r1_ordinal1 @ (k1_ordinal1 @ X0) @ X1))),
% 0.45/0.71      inference('sup-', [status(thm)], ['57', '60'])).
% 0.45/0.71  thf('62', plain,
% 0.45/0.71      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.45/0.71         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.45/0.71      inference('split', [status(esa)], ['4'])).
% 0.45/0.71  thf('63', plain, (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.45/0.71      inference('sat_resolution*', [status(thm)], ['5', '53'])).
% 0.45/0.71  thf('64', plain, (~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 0.45/0.71      inference('simpl_trail', [status(thm)], ['62', '63'])).
% 0.45/0.71  thf('65', plain,
% 0.45/0.71      ((~ (v3_ordinal1 @ sk_B)
% 0.45/0.71        | (r2_hidden @ sk_B @ sk_A)
% 0.45/0.71        | ((sk_B) = (sk_A))
% 0.45/0.71        | ~ (v3_ordinal1 @ sk_A))),
% 0.45/0.71      inference('sup-', [status(thm)], ['61', '64'])).
% 0.45/0.71  thf('66', plain, ((v3_ordinal1 @ sk_B)),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('67', plain, ((v3_ordinal1 @ sk_A)),
% 0.45/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.71  thf('68', plain, (((r2_hidden @ sk_B @ sk_A) | ((sk_B) = (sk_A)))),
% 0.45/0.71      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.45/0.71  thf('69', plain,
% 0.45/0.71      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.45/0.71      inference('split', [status(esa)], ['0'])).
% 0.45/0.71  thf(antisymmetry_r2_hidden, axiom,
% 0.45/0.71    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.45/0.71  thf('70', plain,
% 0.45/0.71      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.45/0.71      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.45/0.71  thf('71', plain,
% 0.45/0.71      ((~ (r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.45/0.71      inference('sup-', [status(thm)], ['69', '70'])).
% 0.45/0.71  thf('72', plain, (((r2_hidden @ sk_A @ sk_B))),
% 0.45/0.71      inference('sat_resolution*', [status(thm)], ['5', '53', '54'])).
% 0.45/0.71  thf('73', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 0.45/0.71      inference('simpl_trail', [status(thm)], ['71', '72'])).
% 0.45/0.71  thf('74', plain, (((sk_B) = (sk_A))),
% 0.45/0.71      inference('clc', [status(thm)], ['68', '73'])).
% 0.45/0.71  thf('75', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.45/0.71      inference('simplify', [status(thm)], ['40'])).
% 0.45/0.71  thf('76', plain, ($false),
% 0.45/0.71      inference('demod', [status(thm)], ['56', '74', '75'])).
% 0.45/0.71  
% 0.45/0.71  % SZS output end Refutation
% 0.45/0.71  
% 0.56/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

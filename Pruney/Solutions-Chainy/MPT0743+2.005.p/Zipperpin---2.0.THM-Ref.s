%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xZBCCgr5Ws

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:53 EST 2020

% Result     : Theorem 0.62s
% Output     : Refutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 480 expanded)
%              Number of leaves         :   22 ( 143 expanded)
%              Depth                    :   19
%              Number of atoms          :  566 (3955 expanded)
%              Number of equality atoms :   21 (  71 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

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
    ! [X52: $i,X53: $i] :
      ( ~ ( r2_hidden @ X52 @ X53 )
      | ~ ( r1_tarski @ X53 @ X52 ) ) ),
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
    ! [X50: $i,X51: $i] :
      ( ~ ( v3_ordinal1 @ X50 )
      | ( r1_ordinal1 @ X51 @ X50 )
      | ( r2_hidden @ X50 @ X51 )
      | ~ ( v3_ordinal1 @ X51 ) ) ),
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
    ! [X44: $i,X45: $i] :
      ( ~ ( v3_ordinal1 @ X44 )
      | ~ ( v3_ordinal1 @ X45 )
      | ( r1_tarski @ X44 @ X45 )
      | ~ ( r1_ordinal1 @ X44 @ X45 ) ) ),
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

thf(fc2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ~ ( v1_xboole_0 @ ( k1_ordinal1 @ A ) )
        & ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) ) )).

thf('17',plain,(
    ! [X43: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X43 ) )
      | ~ ( v3_ordinal1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[fc2_ordinal1])).

thf('18',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('19',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( v3_ordinal1 @ X44 )
      | ~ ( v3_ordinal1 @ X45 )
      | ( r1_tarski @ X44 @ X45 )
      | ~ ( r1_ordinal1 @ X44 @ X45 ) ) ),
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

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('26',plain,(
    ! [X42: $i] :
      ( ( k1_ordinal1 @ X42 )
      = ( k2_xboole_0 @ X42 @ ( k1_tarski @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('27',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X5 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X1 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('30',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('31',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_A )
      | ( sk_B = sk_A ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_B = sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','31'])).

thf('33',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('34',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,
    ( ( ~ ( r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ~ ( r1_tarski @ sk_A @ ( k1_ordinal1 @ sk_A ) )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X42: $i] :
      ( ( k1_ordinal1 @ X42 )
      = ( k2_xboole_0 @ X42 @ ( k1_tarski @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('38',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_B = sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','31'])).

thf('41',plain,
    ( ( sk_A
      = ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','39','40'])).

thf(t14_ordinal1,axiom,(
    ! [A: $i] :
      ( A
     != ( k1_ordinal1 @ A ) ) )).

thf('42',plain,(
    ! [X49: $i] :
      ( X49
     != ( k1_ordinal1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t14_ordinal1])).

thf('43',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['5','43','44'])).

thf('46',plain,(
    ~ ( r1_tarski @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['3','45'])).

thf('47',plain,(
    ! [X43: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X43 ) )
      | ~ ( v3_ordinal1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[fc2_ordinal1])).

thf('48',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( v3_ordinal1 @ X50 )
      | ( r1_ordinal1 @ X51 @ X50 )
      | ( r2_hidden @ X50 @ X51 )
      | ~ ( v3_ordinal1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X0 ) @ X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('50',plain,(
    ! [X46: $i,X47: $i] :
      ( ( X47 = X46 )
      | ( r2_hidden @ X47 @ X46 )
      | ~ ( r2_hidden @ X47 @ ( k1_ordinal1 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X0 ) @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('53',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['5','43'])).

thf('54',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( sk_B = sk_A )
    | ( r2_hidden @ sk_B @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( sk_B = sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('61',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['5','43','44'])).

thf('63',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['61','62'])).

thf('64',plain,(
    sk_B = sk_A ),
    inference(clc,[status(thm)],['58','63'])).

thf('65',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('66',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['46','64','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xZBCCgr5Ws
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:10:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.62/0.81  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.62/0.81  % Solved by: fo/fo7.sh
% 0.62/0.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.62/0.81  % done 646 iterations in 0.359s
% 0.62/0.81  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.62/0.81  % SZS output start Refutation
% 0.62/0.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.62/0.81  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.62/0.81  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.62/0.81  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.62/0.81  thf(sk_A_type, type, sk_A: $i).
% 0.62/0.81  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.62/0.81  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.62/0.81  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.62/0.81  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.62/0.81  thf(sk_B_type, type, sk_B: $i).
% 0.62/0.81  thf(t33_ordinal1, conjecture,
% 0.62/0.81    (![A:$i]:
% 0.62/0.81     ( ( v3_ordinal1 @ A ) =>
% 0.62/0.81       ( ![B:$i]:
% 0.62/0.81         ( ( v3_ordinal1 @ B ) =>
% 0.62/0.81           ( ( r2_hidden @ A @ B ) <=>
% 0.62/0.81             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 0.62/0.81  thf(zf_stmt_0, negated_conjecture,
% 0.62/0.81    (~( ![A:$i]:
% 0.62/0.81        ( ( v3_ordinal1 @ A ) =>
% 0.62/0.81          ( ![B:$i]:
% 0.62/0.81            ( ( v3_ordinal1 @ B ) =>
% 0.62/0.81              ( ( r2_hidden @ A @ B ) <=>
% 0.62/0.81                ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ) )),
% 0.62/0.81    inference('cnf.neg', [status(esa)], [t33_ordinal1])).
% 0.62/0.81  thf('0', plain,
% 0.62/0.81      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 0.62/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.81  thf('1', plain,
% 0.62/0.81      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.62/0.81      inference('split', [status(esa)], ['0'])).
% 0.62/0.81  thf(t7_ordinal1, axiom,
% 0.62/0.81    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.62/0.81  thf('2', plain,
% 0.62/0.81      (![X52 : $i, X53 : $i]:
% 0.62/0.81         (~ (r2_hidden @ X52 @ X53) | ~ (r1_tarski @ X53 @ X52))),
% 0.62/0.81      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.62/0.81  thf('3', plain,
% 0.62/0.81      ((~ (r1_tarski @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.62/0.81      inference('sup-', [status(thm)], ['1', '2'])).
% 0.62/0.81  thf('4', plain,
% 0.62/0.81      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.62/0.81        | ~ (r2_hidden @ sk_A @ sk_B))),
% 0.62/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.81  thf('5', plain,
% 0.62/0.81      (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 0.62/0.81       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.62/0.81      inference('split', [status(esa)], ['4'])).
% 0.62/0.81  thf(t26_ordinal1, axiom,
% 0.62/0.81    (![A:$i]:
% 0.62/0.81     ( ( v3_ordinal1 @ A ) =>
% 0.62/0.81       ( ![B:$i]:
% 0.62/0.81         ( ( v3_ordinal1 @ B ) =>
% 0.62/0.81           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.62/0.81  thf('6', plain,
% 0.62/0.81      (![X50 : $i, X51 : $i]:
% 0.62/0.81         (~ (v3_ordinal1 @ X50)
% 0.62/0.81          | (r1_ordinal1 @ X51 @ X50)
% 0.62/0.81          | (r2_hidden @ X50 @ X51)
% 0.62/0.81          | ~ (v3_ordinal1 @ X51))),
% 0.62/0.81      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.62/0.81  thf('7', plain,
% 0.62/0.81      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.62/0.81      inference('split', [status(esa)], ['4'])).
% 0.62/0.81  thf('8', plain,
% 0.62/0.81      (((~ (v3_ordinal1 @ sk_B)
% 0.62/0.81         | (r1_ordinal1 @ sk_B @ sk_A)
% 0.62/0.81         | ~ (v3_ordinal1 @ sk_A))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.62/0.81      inference('sup-', [status(thm)], ['6', '7'])).
% 0.62/0.81  thf('9', plain, ((v3_ordinal1 @ sk_B)),
% 0.62/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.81  thf('10', plain, ((v3_ordinal1 @ sk_A)),
% 0.62/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.81  thf('11', plain,
% 0.62/0.81      (((r1_ordinal1 @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.62/0.81      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.62/0.81  thf(redefinition_r1_ordinal1, axiom,
% 0.62/0.81    (![A:$i,B:$i]:
% 0.62/0.81     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.62/0.81       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.62/0.81  thf('12', plain,
% 0.62/0.81      (![X44 : $i, X45 : $i]:
% 0.62/0.81         (~ (v3_ordinal1 @ X44)
% 0.62/0.81          | ~ (v3_ordinal1 @ X45)
% 0.62/0.81          | (r1_tarski @ X44 @ X45)
% 0.62/0.81          | ~ (r1_ordinal1 @ X44 @ X45))),
% 0.62/0.81      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.62/0.81  thf('13', plain,
% 0.62/0.81      ((((r1_tarski @ sk_B @ sk_A)
% 0.62/0.81         | ~ (v3_ordinal1 @ sk_A)
% 0.62/0.81         | ~ (v3_ordinal1 @ sk_B))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.62/0.81      inference('sup-', [status(thm)], ['11', '12'])).
% 0.62/0.81  thf('14', plain, ((v3_ordinal1 @ sk_A)),
% 0.62/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.81  thf('15', plain, ((v3_ordinal1 @ sk_B)),
% 0.62/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.81  thf('16', plain,
% 0.62/0.81      (((r1_tarski @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.62/0.81      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.62/0.81  thf(fc2_ordinal1, axiom,
% 0.62/0.81    (![A:$i]:
% 0.62/0.81     ( ( v3_ordinal1 @ A ) =>
% 0.62/0.81       ( ( ~( v1_xboole_0 @ ( k1_ordinal1 @ A ) ) ) & 
% 0.62/0.81         ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) ))).
% 0.62/0.81  thf('17', plain,
% 0.62/0.81      (![X43 : $i]:
% 0.62/0.81         ((v3_ordinal1 @ (k1_ordinal1 @ X43)) | ~ (v3_ordinal1 @ X43))),
% 0.62/0.81      inference('cnf', [status(esa)], [fc2_ordinal1])).
% 0.62/0.81  thf('18', plain,
% 0.62/0.81      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.62/0.81         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.62/0.81      inference('split', [status(esa)], ['0'])).
% 0.62/0.81  thf('19', plain,
% 0.62/0.81      (![X44 : $i, X45 : $i]:
% 0.62/0.81         (~ (v3_ordinal1 @ X44)
% 0.62/0.81          | ~ (v3_ordinal1 @ X45)
% 0.62/0.81          | (r1_tarski @ X44 @ X45)
% 0.62/0.81          | ~ (r1_ordinal1 @ X44 @ X45))),
% 0.62/0.81      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.62/0.81  thf('20', plain,
% 0.62/0.81      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.62/0.81         | ~ (v3_ordinal1 @ sk_B)
% 0.62/0.81         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.62/0.81         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.62/0.81      inference('sup-', [status(thm)], ['18', '19'])).
% 0.62/0.81  thf('21', plain, ((v3_ordinal1 @ sk_B)),
% 0.62/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.81  thf('22', plain,
% 0.62/0.81      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.62/0.81         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.62/0.81         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.62/0.81      inference('demod', [status(thm)], ['20', '21'])).
% 0.62/0.81  thf('23', plain,
% 0.62/0.81      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 0.62/0.81         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.62/0.81      inference('sup-', [status(thm)], ['17', '22'])).
% 0.62/0.81  thf('24', plain, ((v3_ordinal1 @ sk_A)),
% 0.62/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.81  thf('25', plain,
% 0.62/0.81      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.62/0.81         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.62/0.81      inference('demod', [status(thm)], ['23', '24'])).
% 0.62/0.81  thf(d1_ordinal1, axiom,
% 0.62/0.81    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.62/0.81  thf('26', plain,
% 0.62/0.81      (![X42 : $i]:
% 0.62/0.81         ((k1_ordinal1 @ X42) = (k2_xboole_0 @ X42 @ (k1_tarski @ X42)))),
% 0.62/0.81      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.62/0.81  thf(t11_xboole_1, axiom,
% 0.62/0.81    (![A:$i,B:$i,C:$i]:
% 0.62/0.81     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.62/0.81  thf('27', plain,
% 0.62/0.81      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.62/0.81         ((r1_tarski @ X5 @ X6) | ~ (r1_tarski @ (k2_xboole_0 @ X5 @ X7) @ X6))),
% 0.62/0.81      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.62/0.81  thf('28', plain,
% 0.62/0.81      (![X0 : $i, X1 : $i]:
% 0.62/0.81         (~ (r1_tarski @ (k1_ordinal1 @ X0) @ X1) | (r1_tarski @ X0 @ X1))),
% 0.62/0.81      inference('sup-', [status(thm)], ['26', '27'])).
% 0.62/0.81  thf('29', plain,
% 0.62/0.81      (((r1_tarski @ sk_A @ sk_B))
% 0.62/0.81         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.62/0.81      inference('sup-', [status(thm)], ['25', '28'])).
% 0.62/0.81  thf(d10_xboole_0, axiom,
% 0.62/0.81    (![A:$i,B:$i]:
% 0.62/0.81     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.62/0.81  thf('30', plain,
% 0.62/0.81      (![X2 : $i, X4 : $i]:
% 0.62/0.81         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.62/0.81      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.62/0.81  thf('31', plain,
% 0.62/0.81      (((~ (r1_tarski @ sk_B @ sk_A) | ((sk_B) = (sk_A))))
% 0.62/0.81         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.62/0.81      inference('sup-', [status(thm)], ['29', '30'])).
% 0.62/0.81  thf('32', plain,
% 0.62/0.81      ((((sk_B) = (sk_A)))
% 0.62/0.81         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.62/0.81             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.62/0.81      inference('sup-', [status(thm)], ['16', '31'])).
% 0.62/0.81  thf('33', plain,
% 0.62/0.81      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.62/0.81         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.62/0.81      inference('demod', [status(thm)], ['23', '24'])).
% 0.62/0.81  thf('34', plain,
% 0.62/0.81      (![X2 : $i, X4 : $i]:
% 0.62/0.81         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.62/0.81      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.62/0.81  thf('35', plain,
% 0.62/0.81      (((~ (r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.62/0.81         | ((sk_B) = (k1_ordinal1 @ sk_A))))
% 0.62/0.81         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.62/0.81      inference('sup-', [status(thm)], ['33', '34'])).
% 0.62/0.81  thf('36', plain,
% 0.62/0.81      (((~ (r1_tarski @ sk_A @ (k1_ordinal1 @ sk_A))
% 0.62/0.81         | ((sk_B) = (k1_ordinal1 @ sk_A))))
% 0.62/0.81         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.62/0.81             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.62/0.81      inference('sup-', [status(thm)], ['32', '35'])).
% 0.62/0.81  thf('37', plain,
% 0.62/0.81      (![X42 : $i]:
% 0.62/0.81         ((k1_ordinal1 @ X42) = (k2_xboole_0 @ X42 @ (k1_tarski @ X42)))),
% 0.62/0.81      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.62/0.81  thf(t7_xboole_1, axiom,
% 0.62/0.81    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.62/0.81  thf('38', plain,
% 0.62/0.81      (![X8 : $i, X9 : $i]: (r1_tarski @ X8 @ (k2_xboole_0 @ X8 @ X9))),
% 0.62/0.81      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.62/0.81  thf('39', plain, (![X0 : $i]: (r1_tarski @ X0 @ (k1_ordinal1 @ X0))),
% 0.62/0.81      inference('sup+', [status(thm)], ['37', '38'])).
% 0.62/0.81  thf('40', plain,
% 0.62/0.81      ((((sk_B) = (sk_A)))
% 0.62/0.81         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.62/0.81             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.62/0.81      inference('sup-', [status(thm)], ['16', '31'])).
% 0.62/0.81  thf('41', plain,
% 0.62/0.81      ((((sk_A) = (k1_ordinal1 @ sk_A)))
% 0.62/0.81         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.62/0.81             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.62/0.81      inference('demod', [status(thm)], ['36', '39', '40'])).
% 0.62/0.81  thf(t14_ordinal1, axiom, (![A:$i]: ( ( A ) != ( k1_ordinal1 @ A ) ))).
% 0.62/0.81  thf('42', plain, (![X49 : $i]: ((X49) != (k1_ordinal1 @ X49))),
% 0.62/0.81      inference('cnf', [status(esa)], [t14_ordinal1])).
% 0.62/0.81  thf('43', plain,
% 0.62/0.81      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.62/0.81       ~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.62/0.81      inference('simplify_reflect-', [status(thm)], ['41', '42'])).
% 0.62/0.81  thf('44', plain,
% 0.62/0.81      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.62/0.81       ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.62/0.81      inference('split', [status(esa)], ['0'])).
% 0.62/0.81  thf('45', plain, (((r2_hidden @ sk_A @ sk_B))),
% 0.62/0.81      inference('sat_resolution*', [status(thm)], ['5', '43', '44'])).
% 0.62/0.81  thf('46', plain, (~ (r1_tarski @ sk_B @ sk_A)),
% 0.62/0.81      inference('simpl_trail', [status(thm)], ['3', '45'])).
% 0.62/0.81  thf('47', plain,
% 0.62/0.81      (![X43 : $i]:
% 0.62/0.81         ((v3_ordinal1 @ (k1_ordinal1 @ X43)) | ~ (v3_ordinal1 @ X43))),
% 0.62/0.81      inference('cnf', [status(esa)], [fc2_ordinal1])).
% 0.62/0.81  thf('48', plain,
% 0.62/0.81      (![X50 : $i, X51 : $i]:
% 0.62/0.81         (~ (v3_ordinal1 @ X50)
% 0.62/0.81          | (r1_ordinal1 @ X51 @ X50)
% 0.62/0.81          | (r2_hidden @ X50 @ X51)
% 0.62/0.81          | ~ (v3_ordinal1 @ X51))),
% 0.62/0.81      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.62/0.81  thf('49', plain,
% 0.62/0.81      (![X0 : $i, X1 : $i]:
% 0.62/0.81         (~ (v3_ordinal1 @ X0)
% 0.62/0.81          | (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.62/0.81          | (r1_ordinal1 @ (k1_ordinal1 @ X0) @ X1)
% 0.62/0.81          | ~ (v3_ordinal1 @ X1))),
% 0.62/0.81      inference('sup-', [status(thm)], ['47', '48'])).
% 0.62/0.81  thf(t13_ordinal1, axiom,
% 0.62/0.81    (![A:$i,B:$i]:
% 0.62/0.81     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.62/0.81       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.62/0.81  thf('50', plain,
% 0.62/0.81      (![X46 : $i, X47 : $i]:
% 0.62/0.81         (((X47) = (X46))
% 0.62/0.81          | (r2_hidden @ X47 @ X46)
% 0.62/0.81          | ~ (r2_hidden @ X47 @ (k1_ordinal1 @ X46)))),
% 0.62/0.81      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.62/0.81  thf('51', plain,
% 0.62/0.81      (![X0 : $i, X1 : $i]:
% 0.62/0.81         (~ (v3_ordinal1 @ X1)
% 0.62/0.81          | (r1_ordinal1 @ (k1_ordinal1 @ X0) @ X1)
% 0.62/0.81          | ~ (v3_ordinal1 @ X0)
% 0.62/0.81          | (r2_hidden @ X1 @ X0)
% 0.62/0.81          | ((X1) = (X0)))),
% 0.62/0.81      inference('sup-', [status(thm)], ['49', '50'])).
% 0.62/0.81  thf('52', plain,
% 0.62/0.81      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.62/0.81         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.62/0.81      inference('split', [status(esa)], ['4'])).
% 0.62/0.81  thf('53', plain, (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.62/0.81      inference('sat_resolution*', [status(thm)], ['5', '43'])).
% 0.62/0.81  thf('54', plain, (~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 0.62/0.81      inference('simpl_trail', [status(thm)], ['52', '53'])).
% 0.62/0.81  thf('55', plain,
% 0.62/0.81      ((((sk_B) = (sk_A))
% 0.62/0.81        | (r2_hidden @ sk_B @ sk_A)
% 0.62/0.81        | ~ (v3_ordinal1 @ sk_A)
% 0.62/0.81        | ~ (v3_ordinal1 @ sk_B))),
% 0.62/0.81      inference('sup-', [status(thm)], ['51', '54'])).
% 0.62/0.81  thf('56', plain, ((v3_ordinal1 @ sk_A)),
% 0.62/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.81  thf('57', plain, ((v3_ordinal1 @ sk_B)),
% 0.62/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.81  thf('58', plain, ((((sk_B) = (sk_A)) | (r2_hidden @ sk_B @ sk_A))),
% 0.62/0.81      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.62/0.81  thf('59', plain,
% 0.62/0.81      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.62/0.81      inference('split', [status(esa)], ['0'])).
% 0.62/0.81  thf(antisymmetry_r2_hidden, axiom,
% 0.62/0.81    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.62/0.81  thf('60', plain,
% 0.62/0.81      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.62/0.81      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.62/0.81  thf('61', plain,
% 0.62/0.81      ((~ (r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.62/0.81      inference('sup-', [status(thm)], ['59', '60'])).
% 0.62/0.81  thf('62', plain, (((r2_hidden @ sk_A @ sk_B))),
% 0.62/0.81      inference('sat_resolution*', [status(thm)], ['5', '43', '44'])).
% 0.62/0.81  thf('63', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 0.62/0.81      inference('simpl_trail', [status(thm)], ['61', '62'])).
% 0.62/0.81  thf('64', plain, (((sk_B) = (sk_A))),
% 0.62/0.81      inference('clc', [status(thm)], ['58', '63'])).
% 0.62/0.81  thf('65', plain,
% 0.62/0.81      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.62/0.81      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.62/0.81  thf('66', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.62/0.81      inference('simplify', [status(thm)], ['65'])).
% 0.62/0.81  thf('67', plain, ($false),
% 0.62/0.81      inference('demod', [status(thm)], ['46', '64', '66'])).
% 0.62/0.81  
% 0.62/0.81  % SZS output end Refutation
% 0.62/0.81  
% 0.62/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

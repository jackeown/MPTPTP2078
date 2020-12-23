%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cEjrMM2Vf7

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:54 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 363 expanded)
%              Number of leaves         :   16 ( 107 expanded)
%              Depth                    :   20
%              Number of atoms          :  563 (2965 expanded)
%              Number of equality atoms :   12 (  24 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

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
    ! [X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
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
    ! [X15: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X15 ) )
      | ~ ( v3_ordinal1 @ X15 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ~ ( v3_ordinal1 @ X7 )
      | ~ ( v3_ordinal1 @ X8 )
      | ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_ordinal1 @ X7 @ X8 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ~ ( v3_ordinal1 @ X13 )
      | ( r1_ordinal1 @ X14 @ X13 )
      | ( r2_hidden @ X13 @ X14 )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('16',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ ( k1_ordinal1 @ X12 ) )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ~ ( v3_ordinal1 @ X7 )
      | ~ ( v3_ordinal1 @ X8 )
      | ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_ordinal1 @ X7 @ X8 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ~ ( v3_ordinal1 @ X13 )
      | ( r1_ordinal1 @ X14 @ X13 )
      | ( r2_hidden @ X13 @ X14 )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ~ ( v3_ordinal1 @ X7 )
      | ~ ( v3_ordinal1 @ X8 )
      | ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_ordinal1 @ X7 @ X8 ) ) ),
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

thf('44',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('45',plain,(
    ! [X9: $i] :
      ( r2_hidden @ X9 @ ( k1_ordinal1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('46',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('47',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('50',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['5','48','49'])).

thf('51',plain,(
    ~ ( r1_tarski @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['3','50'])).

thf('52',plain,(
    ! [X15: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X15 ) )
      | ~ ( v3_ordinal1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('53',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v3_ordinal1 @ X13 )
      | ( r1_ordinal1 @ X14 @ X13 )
      | ( r2_hidden @ X13 @ X14 )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('54',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X11 = X10 )
      | ( r2_hidden @ X11 @ X10 )
      | ~ ( r2_hidden @ X11 @ ( k1_ordinal1 @ X10 ) ) ) ),
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
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('58',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['5','48'])).

thf('59',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r2_hidden @ sk_B @ sk_A )
    | ( sk_B = sk_A )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( sk_B = sk_A ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('66',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['5','48','49'])).

thf('68',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['66','67'])).

thf('69',plain,(
    sk_B = sk_A ),
    inference(clc,[status(thm)],['63','68'])).

thf('70',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('71',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    $false ),
    inference(demod,[status(thm)],['51','69','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cEjrMM2Vf7
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:28:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.46/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.65  % Solved by: fo/fo7.sh
% 0.46/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.65  % done 342 iterations in 0.185s
% 0.46/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.65  % SZS output start Refutation
% 0.46/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.65  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.46/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.65  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.46/0.65  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.46/0.65  thf(t33_ordinal1, conjecture,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( v3_ordinal1 @ A ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( v3_ordinal1 @ B ) =>
% 0.46/0.65           ( ( r2_hidden @ A @ B ) <=>
% 0.46/0.65             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 0.46/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.65    (~( ![A:$i]:
% 0.46/0.65        ( ( v3_ordinal1 @ A ) =>
% 0.46/0.65          ( ![B:$i]:
% 0.46/0.65            ( ( v3_ordinal1 @ B ) =>
% 0.46/0.65              ( ( r2_hidden @ A @ B ) <=>
% 0.46/0.65                ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ) )),
% 0.46/0.65    inference('cnf.neg', [status(esa)], [t33_ordinal1])).
% 0.46/0.65  thf('0', plain,
% 0.46/0.65      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('1', plain,
% 0.46/0.65      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.46/0.65      inference('split', [status(esa)], ['0'])).
% 0.46/0.65  thf(t7_ordinal1, axiom,
% 0.46/0.65    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.65  thf('2', plain,
% 0.46/0.65      (![X16 : $i, X17 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X16 @ X17) | ~ (r1_tarski @ X17 @ X16))),
% 0.46/0.65      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.46/0.65  thf('3', plain,
% 0.46/0.65      ((~ (r1_tarski @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.65  thf('4', plain,
% 0.46/0.65      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.46/0.65        | ~ (r2_hidden @ sk_A @ sk_B))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('5', plain,
% 0.46/0.65      (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 0.46/0.65       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.46/0.65      inference('split', [status(esa)], ['4'])).
% 0.46/0.65  thf(t29_ordinal1, axiom,
% 0.46/0.65    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 0.46/0.65  thf('6', plain,
% 0.46/0.65      (![X15 : $i]:
% 0.46/0.65         ((v3_ordinal1 @ (k1_ordinal1 @ X15)) | ~ (v3_ordinal1 @ X15))),
% 0.46/0.65      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.46/0.65  thf('7', plain,
% 0.46/0.65      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.46/0.65         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.46/0.65      inference('split', [status(esa)], ['0'])).
% 0.46/0.65  thf(redefinition_r1_ordinal1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.46/0.65       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.46/0.65  thf('8', plain,
% 0.46/0.65      (![X7 : $i, X8 : $i]:
% 0.46/0.65         (~ (v3_ordinal1 @ X7)
% 0.46/0.65          | ~ (v3_ordinal1 @ X8)
% 0.46/0.65          | (r1_tarski @ X7 @ X8)
% 0.46/0.65          | ~ (r1_ordinal1 @ X7 @ X8))),
% 0.46/0.65      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.46/0.65  thf('9', plain,
% 0.46/0.65      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.46/0.65         | ~ (v3_ordinal1 @ sk_B)
% 0.46/0.65         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.46/0.65         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['7', '8'])).
% 0.46/0.65  thf('10', plain, ((v3_ordinal1 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('11', plain,
% 0.46/0.65      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.46/0.65         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.46/0.65         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.46/0.65      inference('demod', [status(thm)], ['9', '10'])).
% 0.46/0.65  thf('12', plain,
% 0.46/0.65      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 0.46/0.65         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['6', '11'])).
% 0.46/0.65  thf('13', plain, ((v3_ordinal1 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('14', plain,
% 0.46/0.65      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.46/0.65         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.46/0.65      inference('demod', [status(thm)], ['12', '13'])).
% 0.46/0.65  thf(t26_ordinal1, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( v3_ordinal1 @ A ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( v3_ordinal1 @ B ) =>
% 0.46/0.65           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.46/0.65  thf('15', plain,
% 0.46/0.65      (![X13 : $i, X14 : $i]:
% 0.46/0.65         (~ (v3_ordinal1 @ X13)
% 0.46/0.65          | (r1_ordinal1 @ X14 @ X13)
% 0.46/0.65          | (r2_hidden @ X13 @ X14)
% 0.46/0.65          | ~ (v3_ordinal1 @ X14))),
% 0.46/0.65      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.46/0.65  thf(t13_ordinal1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.46/0.65       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.46/0.65  thf('16', plain,
% 0.46/0.65      (![X11 : $i, X12 : $i]:
% 0.46/0.65         ((r2_hidden @ X11 @ (k1_ordinal1 @ X12)) | ~ (r2_hidden @ X11 @ X12))),
% 0.46/0.65      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.46/0.65  thf('17', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (~ (v3_ordinal1 @ X0)
% 0.46/0.65          | (r1_ordinal1 @ X0 @ X1)
% 0.46/0.65          | ~ (v3_ordinal1 @ X1)
% 0.46/0.65          | (r2_hidden @ X1 @ (k1_ordinal1 @ X0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['15', '16'])).
% 0.46/0.65  thf('18', plain,
% 0.46/0.65      (![X16 : $i, X17 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X16 @ X17) | ~ (r1_tarski @ X17 @ X16))),
% 0.46/0.65      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.46/0.65  thf('19', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (~ (v3_ordinal1 @ X1)
% 0.46/0.65          | (r1_ordinal1 @ X0 @ X1)
% 0.46/0.65          | ~ (v3_ordinal1 @ X0)
% 0.46/0.65          | ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X1))),
% 0.46/0.65      inference('sup-', [status(thm)], ['17', '18'])).
% 0.46/0.65  thf('20', plain,
% 0.46/0.65      (((~ (v3_ordinal1 @ sk_A)
% 0.46/0.65         | (r1_ordinal1 @ sk_A @ sk_B)
% 0.46/0.65         | ~ (v3_ordinal1 @ sk_B)))
% 0.46/0.65         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['14', '19'])).
% 0.46/0.65  thf('21', plain, ((v3_ordinal1 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('22', plain, ((v3_ordinal1 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('23', plain,
% 0.46/0.65      (((r1_ordinal1 @ sk_A @ sk_B))
% 0.46/0.65         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.46/0.65      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.46/0.65  thf('24', plain,
% 0.46/0.65      (![X7 : $i, X8 : $i]:
% 0.46/0.65         (~ (v3_ordinal1 @ X7)
% 0.46/0.65          | ~ (v3_ordinal1 @ X8)
% 0.46/0.65          | (r1_tarski @ X7 @ X8)
% 0.46/0.65          | ~ (r1_ordinal1 @ X7 @ X8))),
% 0.46/0.65      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.46/0.65  thf('25', plain,
% 0.46/0.65      ((((r1_tarski @ sk_A @ sk_B)
% 0.46/0.65         | ~ (v3_ordinal1 @ sk_B)
% 0.46/0.65         | ~ (v3_ordinal1 @ sk_A)))
% 0.46/0.65         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['23', '24'])).
% 0.46/0.65  thf('26', plain, ((v3_ordinal1 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('27', plain, ((v3_ordinal1 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('28', plain,
% 0.46/0.65      (((r1_tarski @ sk_A @ sk_B))
% 0.46/0.65         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.46/0.65      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.46/0.65  thf('29', plain,
% 0.46/0.65      (![X13 : $i, X14 : $i]:
% 0.46/0.65         (~ (v3_ordinal1 @ X13)
% 0.46/0.65          | (r1_ordinal1 @ X14 @ X13)
% 0.46/0.65          | (r2_hidden @ X13 @ X14)
% 0.46/0.65          | ~ (v3_ordinal1 @ X14))),
% 0.46/0.65      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.46/0.65  thf('30', plain,
% 0.46/0.65      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.46/0.65      inference('split', [status(esa)], ['4'])).
% 0.46/0.65  thf('31', plain,
% 0.46/0.65      (((~ (v3_ordinal1 @ sk_B)
% 0.46/0.65         | (r1_ordinal1 @ sk_B @ sk_A)
% 0.46/0.65         | ~ (v3_ordinal1 @ sk_A))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['29', '30'])).
% 0.46/0.65  thf('32', plain, ((v3_ordinal1 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('33', plain, ((v3_ordinal1 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('34', plain,
% 0.46/0.65      (((r1_ordinal1 @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.46/0.65      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.46/0.65  thf('35', plain,
% 0.46/0.65      (![X7 : $i, X8 : $i]:
% 0.46/0.65         (~ (v3_ordinal1 @ X7)
% 0.46/0.65          | ~ (v3_ordinal1 @ X8)
% 0.46/0.65          | (r1_tarski @ X7 @ X8)
% 0.46/0.65          | ~ (r1_ordinal1 @ X7 @ X8))),
% 0.46/0.65      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.46/0.65  thf('36', plain,
% 0.46/0.65      ((((r1_tarski @ sk_B @ sk_A)
% 0.46/0.65         | ~ (v3_ordinal1 @ sk_A)
% 0.46/0.65         | ~ (v3_ordinal1 @ sk_B))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['34', '35'])).
% 0.46/0.65  thf('37', plain, ((v3_ordinal1 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('38', plain, ((v3_ordinal1 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('39', plain,
% 0.46/0.65      (((r1_tarski @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.46/0.65      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.46/0.65  thf(d10_xboole_0, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.65  thf('40', plain,
% 0.46/0.65      (![X2 : $i, X4 : $i]:
% 0.46/0.65         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.46/0.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.65  thf('41', plain,
% 0.46/0.65      (((~ (r1_tarski @ sk_A @ sk_B) | ((sk_A) = (sk_B))))
% 0.46/0.65         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['39', '40'])).
% 0.46/0.65  thf('42', plain,
% 0.46/0.65      ((((sk_A) = (sk_B)))
% 0.46/0.65         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.46/0.65             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['28', '41'])).
% 0.46/0.65  thf('43', plain,
% 0.46/0.65      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.46/0.65         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.46/0.65      inference('demod', [status(thm)], ['12', '13'])).
% 0.46/0.65  thf('44', plain,
% 0.46/0.65      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_A))
% 0.46/0.65         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.46/0.65             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['42', '43'])).
% 0.46/0.65  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.46/0.65  thf('45', plain, (![X9 : $i]: (r2_hidden @ X9 @ (k1_ordinal1 @ X9))),
% 0.46/0.65      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.46/0.65  thf('46', plain,
% 0.46/0.65      (![X16 : $i, X17 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X16 @ X17) | ~ (r1_tarski @ X17 @ X16))),
% 0.46/0.65      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.46/0.65  thf('47', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X0)),
% 0.46/0.65      inference('sup-', [status(thm)], ['45', '46'])).
% 0.46/0.65  thf('48', plain,
% 0.46/0.65      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.46/0.65       ~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.46/0.65      inference('sup-', [status(thm)], ['44', '47'])).
% 0.46/0.65  thf('49', plain,
% 0.46/0.65      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.46/0.65       ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.46/0.65      inference('split', [status(esa)], ['0'])).
% 0.46/0.65  thf('50', plain, (((r2_hidden @ sk_A @ sk_B))),
% 0.46/0.65      inference('sat_resolution*', [status(thm)], ['5', '48', '49'])).
% 0.46/0.65  thf('51', plain, (~ (r1_tarski @ sk_B @ sk_A)),
% 0.46/0.65      inference('simpl_trail', [status(thm)], ['3', '50'])).
% 0.46/0.65  thf('52', plain,
% 0.46/0.65      (![X15 : $i]:
% 0.46/0.65         ((v3_ordinal1 @ (k1_ordinal1 @ X15)) | ~ (v3_ordinal1 @ X15))),
% 0.46/0.65      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.46/0.65  thf('53', plain,
% 0.46/0.65      (![X13 : $i, X14 : $i]:
% 0.46/0.65         (~ (v3_ordinal1 @ X13)
% 0.46/0.65          | (r1_ordinal1 @ X14 @ X13)
% 0.46/0.65          | (r2_hidden @ X13 @ X14)
% 0.46/0.65          | ~ (v3_ordinal1 @ X14))),
% 0.46/0.65      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.46/0.65  thf('54', plain,
% 0.46/0.65      (![X10 : $i, X11 : $i]:
% 0.46/0.65         (((X11) = (X10))
% 0.46/0.65          | (r2_hidden @ X11 @ X10)
% 0.46/0.65          | ~ (r2_hidden @ X11 @ (k1_ordinal1 @ X10)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.46/0.65  thf('55', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (~ (v3_ordinal1 @ (k1_ordinal1 @ X0))
% 0.46/0.65          | (r1_ordinal1 @ (k1_ordinal1 @ X0) @ X1)
% 0.46/0.65          | ~ (v3_ordinal1 @ X1)
% 0.46/0.65          | (r2_hidden @ X1 @ X0)
% 0.46/0.65          | ((X1) = (X0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['53', '54'])).
% 0.46/0.65  thf('56', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (~ (v3_ordinal1 @ X0)
% 0.46/0.65          | ((X1) = (X0))
% 0.46/0.65          | (r2_hidden @ X1 @ X0)
% 0.46/0.65          | ~ (v3_ordinal1 @ X1)
% 0.46/0.65          | (r1_ordinal1 @ (k1_ordinal1 @ X0) @ X1))),
% 0.46/0.65      inference('sup-', [status(thm)], ['52', '55'])).
% 0.46/0.65  thf('57', plain,
% 0.46/0.65      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.46/0.65         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.46/0.65      inference('split', [status(esa)], ['4'])).
% 0.46/0.65  thf('58', plain, (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.46/0.65      inference('sat_resolution*', [status(thm)], ['5', '48'])).
% 0.46/0.65  thf('59', plain, (~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 0.46/0.65      inference('simpl_trail', [status(thm)], ['57', '58'])).
% 0.46/0.65  thf('60', plain,
% 0.46/0.65      ((~ (v3_ordinal1 @ sk_B)
% 0.46/0.65        | (r2_hidden @ sk_B @ sk_A)
% 0.46/0.65        | ((sk_B) = (sk_A))
% 0.46/0.65        | ~ (v3_ordinal1 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['56', '59'])).
% 0.46/0.65  thf('61', plain, ((v3_ordinal1 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('62', plain, ((v3_ordinal1 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('63', plain, (((r2_hidden @ sk_B @ sk_A) | ((sk_B) = (sk_A)))),
% 0.46/0.65      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.46/0.65  thf('64', plain,
% 0.46/0.65      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.46/0.65      inference('split', [status(esa)], ['0'])).
% 0.46/0.65  thf(antisymmetry_r2_hidden, axiom,
% 0.46/0.65    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.46/0.65  thf('65', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.46/0.65      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.46/0.65  thf('66', plain,
% 0.46/0.65      ((~ (r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['64', '65'])).
% 0.46/0.65  thf('67', plain, (((r2_hidden @ sk_A @ sk_B))),
% 0.46/0.65      inference('sat_resolution*', [status(thm)], ['5', '48', '49'])).
% 0.46/0.65  thf('68', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 0.46/0.65      inference('simpl_trail', [status(thm)], ['66', '67'])).
% 0.46/0.65  thf('69', plain, (((sk_B) = (sk_A))),
% 0.46/0.65      inference('clc', [status(thm)], ['63', '68'])).
% 0.46/0.65  thf('70', plain,
% 0.46/0.65      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.65  thf('71', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.46/0.65      inference('simplify', [status(thm)], ['70'])).
% 0.46/0.65  thf('72', plain, ($false),
% 0.46/0.65      inference('demod', [status(thm)], ['51', '69', '71'])).
% 0.46/0.65  
% 0.46/0.65  % SZS output end Refutation
% 0.46/0.65  
% 0.46/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

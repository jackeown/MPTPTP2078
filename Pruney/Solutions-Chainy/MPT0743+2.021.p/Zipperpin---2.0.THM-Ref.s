%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CsErhnow5G

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:55 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 253 expanded)
%              Number of leaves         :   16 (  75 expanded)
%              Depth                    :   16
%              Number of atoms          :  543 (2011 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ~ ( v3_ordinal1 @ X12 )
      | ( r1_ordinal1 @ X13 @ X12 )
      | ( r2_hidden @ X12 @ X13 )
      | ~ ( v3_ordinal1 @ X13 ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ~ ( v3_ordinal1 @ X6 )
      | ~ ( v3_ordinal1 @ X7 )
      | ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_ordinal1 @ X6 @ X7 ) ) ),
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
    ! [X14: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X14 ) )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('18',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('19',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v3_ordinal1 @ X6 )
      | ~ ( v3_ordinal1 @ X7 )
      | ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_ordinal1 @ X6 @ X7 ) ) ),
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

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('29',plain,(
    ! [X8: $i] :
      ( r2_hidden @ X8 @ ( k1_ordinal1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('30',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('31',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['5','32','33'])).

thf('35',plain,(
    ~ ( r1_tarski @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['3','34'])).

thf('36',plain,(
    ! [X14: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X14 ) )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('37',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v3_ordinal1 @ X12 )
      | ( r1_ordinal1 @ X13 @ X12 )
      | ( r2_hidden @ X12 @ X13 )
      | ~ ( v3_ordinal1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('38',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X10 = X9 )
      | ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ ( k1_ordinal1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ X0 ) )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X0 ) @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ ( k1_ordinal1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('42',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['5','32'])).

thf('43',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r2_hidden @ sk_B @ sk_A )
    | ( sk_B = sk_A )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( sk_B = sk_A ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('50',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['5','32','33'])).

thf('52',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['50','51'])).

thf('53',plain,(
    sk_B = sk_A ),
    inference(clc,[status(thm)],['47','52'])).

thf('54',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v3_ordinal1 @ X12 )
      | ( r1_ordinal1 @ X13 @ X12 )
      | ( r2_hidden @ X12 @ X13 )
      | ~ ( v3_ordinal1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('56',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v3_ordinal1 @ X12 )
      | ( r1_ordinal1 @ X13 @ X12 )
      | ( r2_hidden @ X12 @ X13 )
      | ~ ( v3_ordinal1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','60'])).

thf('62',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference(eq_fact,[status(thm)],['61'])).

thf('63',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    r1_ordinal1 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v3_ordinal1 @ X6 )
      | ~ ( v3_ordinal1 @ X7 )
      | ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_ordinal1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('66',plain,
    ( ( r1_tarski @ sk_A @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    r1_tarski @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    $false ),
    inference(demod,[status(thm)],['35','53','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CsErhnow5G
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:10:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.59  % Solved by: fo/fo7.sh
% 0.37/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.59  % done 361 iterations in 0.129s
% 0.37/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.59  % SZS output start Refutation
% 0.37/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.59  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.37/0.59  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.37/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.59  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.37/0.59  thf(t33_ordinal1, conjecture,
% 0.37/0.59    (![A:$i]:
% 0.37/0.59     ( ( v3_ordinal1 @ A ) =>
% 0.37/0.59       ( ![B:$i]:
% 0.37/0.59         ( ( v3_ordinal1 @ B ) =>
% 0.37/0.59           ( ( r2_hidden @ A @ B ) <=>
% 0.37/0.59             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 0.37/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.59    (~( ![A:$i]:
% 0.37/0.59        ( ( v3_ordinal1 @ A ) =>
% 0.37/0.59          ( ![B:$i]:
% 0.37/0.59            ( ( v3_ordinal1 @ B ) =>
% 0.37/0.59              ( ( r2_hidden @ A @ B ) <=>
% 0.37/0.59                ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ) )),
% 0.37/0.59    inference('cnf.neg', [status(esa)], [t33_ordinal1])).
% 0.37/0.59  thf('0', plain,
% 0.37/0.59      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('1', plain,
% 0.37/0.59      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.37/0.59      inference('split', [status(esa)], ['0'])).
% 0.37/0.59  thf(t7_ordinal1, axiom,
% 0.37/0.59    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.59  thf('2', plain,
% 0.37/0.59      (![X15 : $i, X16 : $i]:
% 0.37/0.59         (~ (r2_hidden @ X15 @ X16) | ~ (r1_tarski @ X16 @ X15))),
% 0.37/0.59      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.37/0.59  thf('3', plain,
% 0.37/0.59      ((~ (r1_tarski @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.59  thf('4', plain,
% 0.37/0.59      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.37/0.59        | ~ (r2_hidden @ sk_A @ sk_B))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('5', plain,
% 0.37/0.59      (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 0.37/0.59       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.37/0.59      inference('split', [status(esa)], ['4'])).
% 0.37/0.59  thf(t26_ordinal1, axiom,
% 0.37/0.59    (![A:$i]:
% 0.37/0.59     ( ( v3_ordinal1 @ A ) =>
% 0.37/0.59       ( ![B:$i]:
% 0.37/0.59         ( ( v3_ordinal1 @ B ) =>
% 0.37/0.59           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.37/0.59  thf('6', plain,
% 0.37/0.59      (![X12 : $i, X13 : $i]:
% 0.37/0.59         (~ (v3_ordinal1 @ X12)
% 0.37/0.59          | (r1_ordinal1 @ X13 @ X12)
% 0.37/0.59          | (r2_hidden @ X12 @ X13)
% 0.37/0.59          | ~ (v3_ordinal1 @ X13))),
% 0.37/0.59      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.37/0.59  thf('7', plain,
% 0.37/0.59      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.37/0.59      inference('split', [status(esa)], ['4'])).
% 0.37/0.59  thf('8', plain,
% 0.37/0.59      (((~ (v3_ordinal1 @ sk_B)
% 0.37/0.59         | (r1_ordinal1 @ sk_B @ sk_A)
% 0.37/0.59         | ~ (v3_ordinal1 @ sk_A))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.59  thf('9', plain, ((v3_ordinal1 @ sk_B)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('10', plain, ((v3_ordinal1 @ sk_A)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('11', plain,
% 0.37/0.59      (((r1_ordinal1 @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.37/0.59      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.37/0.59  thf(redefinition_r1_ordinal1, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.37/0.59       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.37/0.59  thf('12', plain,
% 0.37/0.59      (![X6 : $i, X7 : $i]:
% 0.37/0.59         (~ (v3_ordinal1 @ X6)
% 0.37/0.59          | ~ (v3_ordinal1 @ X7)
% 0.37/0.59          | (r1_tarski @ X6 @ X7)
% 0.37/0.59          | ~ (r1_ordinal1 @ X6 @ X7))),
% 0.37/0.59      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.37/0.59  thf('13', plain,
% 0.37/0.59      ((((r1_tarski @ sk_B @ sk_A)
% 0.37/0.59         | ~ (v3_ordinal1 @ sk_A)
% 0.37/0.59         | ~ (v3_ordinal1 @ sk_B))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.59  thf('14', plain, ((v3_ordinal1 @ sk_A)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('15', plain, ((v3_ordinal1 @ sk_B)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('16', plain,
% 0.37/0.59      (((r1_tarski @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.37/0.59      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.37/0.59  thf(t29_ordinal1, axiom,
% 0.37/0.59    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 0.37/0.59  thf('17', plain,
% 0.37/0.59      (![X14 : $i]:
% 0.37/0.59         ((v3_ordinal1 @ (k1_ordinal1 @ X14)) | ~ (v3_ordinal1 @ X14))),
% 0.37/0.59      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.37/0.59  thf('18', plain,
% 0.37/0.59      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.37/0.59         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.37/0.59      inference('split', [status(esa)], ['0'])).
% 0.37/0.59  thf('19', plain,
% 0.37/0.59      (![X6 : $i, X7 : $i]:
% 0.37/0.59         (~ (v3_ordinal1 @ X6)
% 0.37/0.59          | ~ (v3_ordinal1 @ X7)
% 0.37/0.59          | (r1_tarski @ X6 @ X7)
% 0.37/0.59          | ~ (r1_ordinal1 @ X6 @ X7))),
% 0.37/0.59      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.37/0.59  thf('20', plain,
% 0.37/0.59      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.37/0.59         | ~ (v3_ordinal1 @ sk_B)
% 0.37/0.59         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.37/0.59         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['18', '19'])).
% 0.37/0.59  thf('21', plain, ((v3_ordinal1 @ sk_B)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('22', plain,
% 0.37/0.59      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.37/0.59         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.37/0.59         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.37/0.59      inference('demod', [status(thm)], ['20', '21'])).
% 0.37/0.59  thf('23', plain,
% 0.37/0.59      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 0.37/0.59         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['17', '22'])).
% 0.37/0.59  thf('24', plain, ((v3_ordinal1 @ sk_A)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('25', plain,
% 0.37/0.59      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.37/0.59         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.37/0.59      inference('demod', [status(thm)], ['23', '24'])).
% 0.37/0.59  thf(t1_xboole_1, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i]:
% 0.37/0.59     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.37/0.59       ( r1_tarski @ A @ C ) ))).
% 0.37/0.59  thf('26', plain,
% 0.37/0.59      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.37/0.59         (~ (r1_tarski @ X2 @ X3)
% 0.37/0.59          | ~ (r1_tarski @ X3 @ X4)
% 0.37/0.59          | (r1_tarski @ X2 @ X4))),
% 0.37/0.59      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.37/0.59  thf('27', plain,
% 0.37/0.59      ((![X0 : $i]:
% 0.37/0.59          ((r1_tarski @ (k1_ordinal1 @ sk_A) @ X0) | ~ (r1_tarski @ sk_B @ X0)))
% 0.37/0.59         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['25', '26'])).
% 0.37/0.59  thf('28', plain,
% 0.37/0.59      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_A))
% 0.37/0.59         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.37/0.59             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['16', '27'])).
% 0.37/0.59  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.37/0.59  thf('29', plain, (![X8 : $i]: (r2_hidden @ X8 @ (k1_ordinal1 @ X8))),
% 0.37/0.59      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.37/0.59  thf('30', plain,
% 0.37/0.59      (![X15 : $i, X16 : $i]:
% 0.37/0.59         (~ (r2_hidden @ X15 @ X16) | ~ (r1_tarski @ X16 @ X15))),
% 0.37/0.59      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.37/0.59  thf('31', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X0)),
% 0.37/0.59      inference('sup-', [status(thm)], ['29', '30'])).
% 0.37/0.59  thf('32', plain,
% 0.37/0.59      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.37/0.59       ~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.37/0.59      inference('sup-', [status(thm)], ['28', '31'])).
% 0.37/0.59  thf('33', plain,
% 0.37/0.59      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.37/0.59       ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.37/0.59      inference('split', [status(esa)], ['0'])).
% 0.37/0.59  thf('34', plain, (((r2_hidden @ sk_A @ sk_B))),
% 0.37/0.59      inference('sat_resolution*', [status(thm)], ['5', '32', '33'])).
% 0.37/0.59  thf('35', plain, (~ (r1_tarski @ sk_B @ sk_A)),
% 0.37/0.59      inference('simpl_trail', [status(thm)], ['3', '34'])).
% 0.37/0.59  thf('36', plain,
% 0.37/0.59      (![X14 : $i]:
% 0.37/0.59         ((v3_ordinal1 @ (k1_ordinal1 @ X14)) | ~ (v3_ordinal1 @ X14))),
% 0.37/0.59      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.37/0.59  thf('37', plain,
% 0.37/0.59      (![X12 : $i, X13 : $i]:
% 0.37/0.59         (~ (v3_ordinal1 @ X12)
% 0.37/0.59          | (r1_ordinal1 @ X13 @ X12)
% 0.37/0.59          | (r2_hidden @ X12 @ X13)
% 0.37/0.59          | ~ (v3_ordinal1 @ X13))),
% 0.37/0.59      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.37/0.59  thf(t13_ordinal1, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.37/0.59       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.37/0.59  thf('38', plain,
% 0.37/0.59      (![X9 : $i, X10 : $i]:
% 0.37/0.59         (((X10) = (X9))
% 0.37/0.59          | (r2_hidden @ X10 @ X9)
% 0.37/0.59          | ~ (r2_hidden @ X10 @ (k1_ordinal1 @ X9)))),
% 0.37/0.59      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.37/0.59  thf('39', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         (~ (v3_ordinal1 @ (k1_ordinal1 @ X0))
% 0.37/0.59          | (r1_ordinal1 @ (k1_ordinal1 @ X0) @ X1)
% 0.37/0.59          | ~ (v3_ordinal1 @ X1)
% 0.37/0.59          | (r2_hidden @ X1 @ X0)
% 0.37/0.59          | ((X1) = (X0)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['37', '38'])).
% 0.37/0.59  thf('40', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         (~ (v3_ordinal1 @ X0)
% 0.37/0.59          | ((X1) = (X0))
% 0.37/0.59          | (r2_hidden @ X1 @ X0)
% 0.37/0.59          | ~ (v3_ordinal1 @ X1)
% 0.37/0.59          | (r1_ordinal1 @ (k1_ordinal1 @ X0) @ X1))),
% 0.37/0.59      inference('sup-', [status(thm)], ['36', '39'])).
% 0.37/0.59  thf('41', plain,
% 0.37/0.59      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.37/0.59         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.37/0.59      inference('split', [status(esa)], ['4'])).
% 0.37/0.59  thf('42', plain, (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.37/0.59      inference('sat_resolution*', [status(thm)], ['5', '32'])).
% 0.37/0.59  thf('43', plain, (~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 0.37/0.59      inference('simpl_trail', [status(thm)], ['41', '42'])).
% 0.37/0.59  thf('44', plain,
% 0.37/0.59      ((~ (v3_ordinal1 @ sk_B)
% 0.37/0.59        | (r2_hidden @ sk_B @ sk_A)
% 0.37/0.59        | ((sk_B) = (sk_A))
% 0.37/0.59        | ~ (v3_ordinal1 @ sk_A))),
% 0.37/0.59      inference('sup-', [status(thm)], ['40', '43'])).
% 0.37/0.59  thf('45', plain, ((v3_ordinal1 @ sk_B)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('46', plain, ((v3_ordinal1 @ sk_A)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('47', plain, (((r2_hidden @ sk_B @ sk_A) | ((sk_B) = (sk_A)))),
% 0.37/0.59      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.37/0.59  thf('48', plain,
% 0.37/0.59      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.37/0.59      inference('split', [status(esa)], ['0'])).
% 0.37/0.59  thf(antisymmetry_r2_hidden, axiom,
% 0.37/0.59    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.37/0.59  thf('49', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.37/0.59      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.37/0.59  thf('50', plain,
% 0.37/0.59      ((~ (r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['48', '49'])).
% 0.37/0.59  thf('51', plain, (((r2_hidden @ sk_A @ sk_B))),
% 0.37/0.59      inference('sat_resolution*', [status(thm)], ['5', '32', '33'])).
% 0.37/0.59  thf('52', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 0.37/0.59      inference('simpl_trail', [status(thm)], ['50', '51'])).
% 0.37/0.59  thf('53', plain, (((sk_B) = (sk_A))),
% 0.37/0.59      inference('clc', [status(thm)], ['47', '52'])).
% 0.37/0.59  thf('54', plain, ((v3_ordinal1 @ sk_A)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('55', plain,
% 0.37/0.59      (![X12 : $i, X13 : $i]:
% 0.37/0.59         (~ (v3_ordinal1 @ X12)
% 0.37/0.59          | (r1_ordinal1 @ X13 @ X12)
% 0.37/0.59          | (r2_hidden @ X12 @ X13)
% 0.37/0.59          | ~ (v3_ordinal1 @ X13))),
% 0.37/0.59      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.37/0.59  thf('56', plain,
% 0.37/0.59      (![X12 : $i, X13 : $i]:
% 0.37/0.59         (~ (v3_ordinal1 @ X12)
% 0.37/0.59          | (r1_ordinal1 @ X13 @ X12)
% 0.37/0.59          | (r2_hidden @ X12 @ X13)
% 0.37/0.59          | ~ (v3_ordinal1 @ X13))),
% 0.37/0.59      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.37/0.59  thf('57', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.37/0.59      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.37/0.59  thf('58', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         (~ (v3_ordinal1 @ X0)
% 0.37/0.59          | (r1_ordinal1 @ X0 @ X1)
% 0.37/0.59          | ~ (v3_ordinal1 @ X1)
% 0.37/0.59          | ~ (r2_hidden @ X0 @ X1))),
% 0.37/0.59      inference('sup-', [status(thm)], ['56', '57'])).
% 0.37/0.59  thf('59', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         (~ (v3_ordinal1 @ X0)
% 0.37/0.59          | (r1_ordinal1 @ X0 @ X1)
% 0.37/0.59          | ~ (v3_ordinal1 @ X1)
% 0.37/0.59          | ~ (v3_ordinal1 @ X0)
% 0.37/0.59          | (r1_ordinal1 @ X1 @ X0)
% 0.37/0.59          | ~ (v3_ordinal1 @ X1))),
% 0.37/0.59      inference('sup-', [status(thm)], ['55', '58'])).
% 0.37/0.59  thf('60', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         ((r1_ordinal1 @ X1 @ X0)
% 0.37/0.59          | ~ (v3_ordinal1 @ X1)
% 0.37/0.59          | (r1_ordinal1 @ X0 @ X1)
% 0.37/0.59          | ~ (v3_ordinal1 @ X0))),
% 0.37/0.59      inference('simplify', [status(thm)], ['59'])).
% 0.37/0.59  thf('61', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         (~ (v3_ordinal1 @ X0)
% 0.37/0.59          | (r1_ordinal1 @ X0 @ sk_A)
% 0.37/0.59          | (r1_ordinal1 @ sk_A @ X0))),
% 0.37/0.59      inference('sup-', [status(thm)], ['54', '60'])).
% 0.37/0.59  thf('62', plain, (((r1_ordinal1 @ sk_A @ sk_A) | ~ (v3_ordinal1 @ sk_A))),
% 0.37/0.59      inference('eq_fact', [status(thm)], ['61'])).
% 0.37/0.59  thf('63', plain, ((v3_ordinal1 @ sk_A)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('64', plain, ((r1_ordinal1 @ sk_A @ sk_A)),
% 0.37/0.59      inference('demod', [status(thm)], ['62', '63'])).
% 0.37/0.59  thf('65', plain,
% 0.37/0.59      (![X6 : $i, X7 : $i]:
% 0.37/0.59         (~ (v3_ordinal1 @ X6)
% 0.37/0.59          | ~ (v3_ordinal1 @ X7)
% 0.37/0.59          | (r1_tarski @ X6 @ X7)
% 0.37/0.59          | ~ (r1_ordinal1 @ X6 @ X7))),
% 0.37/0.59      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.37/0.59  thf('66', plain,
% 0.37/0.59      (((r1_tarski @ sk_A @ sk_A)
% 0.37/0.59        | ~ (v3_ordinal1 @ sk_A)
% 0.37/0.59        | ~ (v3_ordinal1 @ sk_A))),
% 0.37/0.59      inference('sup-', [status(thm)], ['64', '65'])).
% 0.37/0.59  thf('67', plain, ((v3_ordinal1 @ sk_A)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('68', plain, ((v3_ordinal1 @ sk_A)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('69', plain, ((r1_tarski @ sk_A @ sk_A)),
% 0.37/0.59      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.37/0.59  thf('70', plain, ($false),
% 0.37/0.59      inference('demod', [status(thm)], ['35', '53', '69'])).
% 0.37/0.59  
% 0.37/0.59  % SZS output end Refutation
% 0.37/0.59  
% 0.37/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

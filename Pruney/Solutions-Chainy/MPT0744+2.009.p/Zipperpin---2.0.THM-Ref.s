%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tGO85lu3zr

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:00 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 255 expanded)
%              Number of leaves         :   19 (  75 expanded)
%              Depth                    :   22
%              Number of atoms          :  559 (2083 expanded)
%              Number of equality atoms :   18 (  58 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('3',plain,(
    ! [X16: $i] :
      ( ( k1_ordinal1 @ X16 )
      = ( k2_xboole_0 @ X16 @ ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('4',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_ordinal1 @ X17 )
      | ~ ( v3_ordinal1 @ X18 )
      | ( r1_tarski @ X17 @ X18 )
      | ~ ( r1_ordinal1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('7',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('11',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v3_ordinal1 @ X19 )
      | ( r2_hidden @ X20 @ X19 )
      | ( X20 = X19 )
      | ( r2_hidden @ X19 @ X20 )
      | ~ ( v3_ordinal1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('12',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X23 @ X24 )
      | ~ ( r1_tarski @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( sk_B = sk_A )
      | ( r2_hidden @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( sk_B = sk_A )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('18',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X5 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('19',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X5 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ( sk_B = sk_A )
        | ( r2_hidden @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      | ( sk_B = sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['3','20'])).

thf('22',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('23',plain,
    ( ( sk_B = sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('25',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X16: $i] :
      ( ( k1_ordinal1 @ X16 )
      = ( k2_xboole_0 @ X16 @ ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['27'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('29',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_tarski @ ( k1_tarski @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('32',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','33'])).

thf('35',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
    | ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['25','34'])).

thf('36',plain,(
    ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','35'])).

thf('37',plain,(
    ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','36'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('38',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v3_ordinal1 @ X21 )
      | ( r1_ordinal1 @ X22 @ X21 )
      | ( r2_hidden @ X21 @ X22 )
      | ~ ( v3_ordinal1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('39',plain,(
    ! [X11: $i,X13: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X11 ) @ X13 )
      | ~ ( r2_hidden @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['4'])).

thf('42',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('43',plain,(
    r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','35','42'])).

thf('44',plain,(
    r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['41','43'])).

thf('45',plain,(
    ! [X16: $i] :
      ( ( k1_ordinal1 @ X16 )
      = ( k2_xboole_0 @ X16 @ ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('46',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('47',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['44','48'])).

thf('50',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X23 @ X24 )
      | ~ ( r1_tarski @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('51',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['40','51'])).

thf('53',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','36'])).

thf('57',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v3_ordinal1 @ X21 )
      | ( r1_ordinal1 @ X22 @ X21 )
      | ( r2_hidden @ X21 @ X22 )
      | ~ ( v3_ordinal1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    r1_ordinal1 @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    $false ),
    inference(demod,[status(thm)],['37','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tGO85lu3zr
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 15:34:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.41/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.59  % Solved by: fo/fo7.sh
% 0.41/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.59  % done 347 iterations in 0.128s
% 0.41/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.59  % SZS output start Refutation
% 0.41/0.59  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.41/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.41/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.41/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.59  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.41/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.59  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.41/0.59  thf(t34_ordinal1, conjecture,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( v3_ordinal1 @ A ) =>
% 0.41/0.59       ( ![B:$i]:
% 0.41/0.59         ( ( v3_ordinal1 @ B ) =>
% 0.41/0.59           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.41/0.59             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 0.41/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.59    (~( ![A:$i]:
% 0.41/0.59        ( ( v3_ordinal1 @ A ) =>
% 0.41/0.59          ( ![B:$i]:
% 0.41/0.59            ( ( v3_ordinal1 @ B ) =>
% 0.41/0.59              ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.41/0.59                ( r1_ordinal1 @ A @ B ) ) ) ) ) )),
% 0.41/0.59    inference('cnf.neg', [status(esa)], [t34_ordinal1])).
% 0.41/0.59  thf('0', plain,
% 0.41/0.59      ((~ (r1_ordinal1 @ sk_A @ sk_B)
% 0.41/0.59        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('1', plain,
% 0.41/0.59      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.41/0.59      inference('split', [status(esa)], ['0'])).
% 0.41/0.59  thf('2', plain,
% 0.41/0.59      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.41/0.59       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.41/0.59      inference('split', [status(esa)], ['0'])).
% 0.41/0.59  thf(d1_ordinal1, axiom,
% 0.41/0.59    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.41/0.59  thf('3', plain,
% 0.41/0.59      (![X16 : $i]:
% 0.41/0.59         ((k1_ordinal1 @ X16) = (k2_xboole_0 @ X16 @ (k1_tarski @ X16)))),
% 0.41/0.59      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.41/0.59  thf('4', plain,
% 0.41/0.59      (((r1_ordinal1 @ sk_A @ sk_B) | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('5', plain,
% 0.41/0.59      (((r1_ordinal1 @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.41/0.59      inference('split', [status(esa)], ['4'])).
% 0.41/0.59  thf(redefinition_r1_ordinal1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.41/0.59       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.41/0.59  thf('6', plain,
% 0.41/0.59      (![X17 : $i, X18 : $i]:
% 0.41/0.59         (~ (v3_ordinal1 @ X17)
% 0.41/0.59          | ~ (v3_ordinal1 @ X18)
% 0.41/0.59          | (r1_tarski @ X17 @ X18)
% 0.41/0.59          | ~ (r1_ordinal1 @ X17 @ X18))),
% 0.41/0.59      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.41/0.59  thf('7', plain,
% 0.41/0.59      ((((r1_tarski @ sk_A @ sk_B)
% 0.41/0.59         | ~ (v3_ordinal1 @ sk_B)
% 0.41/0.59         | ~ (v3_ordinal1 @ sk_A))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['5', '6'])).
% 0.41/0.59  thf('8', plain, ((v3_ordinal1 @ sk_B)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('9', plain, ((v3_ordinal1 @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('10', plain,
% 0.41/0.59      (((r1_tarski @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.41/0.59      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.41/0.59  thf(t24_ordinal1, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( v3_ordinal1 @ A ) =>
% 0.41/0.59       ( ![B:$i]:
% 0.41/0.59         ( ( v3_ordinal1 @ B ) =>
% 0.41/0.59           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.41/0.59                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 0.41/0.59  thf('11', plain,
% 0.41/0.59      (![X19 : $i, X20 : $i]:
% 0.41/0.59         (~ (v3_ordinal1 @ X19)
% 0.41/0.59          | (r2_hidden @ X20 @ X19)
% 0.41/0.59          | ((X20) = (X19))
% 0.41/0.59          | (r2_hidden @ X19 @ X20)
% 0.41/0.59          | ~ (v3_ordinal1 @ X20))),
% 0.41/0.59      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.41/0.59  thf(t7_ordinal1, axiom,
% 0.41/0.59    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.41/0.59  thf('12', plain,
% 0.41/0.59      (![X23 : $i, X24 : $i]:
% 0.41/0.59         (~ (r2_hidden @ X23 @ X24) | ~ (r1_tarski @ X24 @ X23))),
% 0.41/0.59      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.41/0.59  thf('13', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         (~ (v3_ordinal1 @ X1)
% 0.41/0.59          | (r2_hidden @ X0 @ X1)
% 0.41/0.59          | ((X1) = (X0))
% 0.41/0.59          | ~ (v3_ordinal1 @ X0)
% 0.41/0.59          | ~ (r1_tarski @ X0 @ X1))),
% 0.41/0.59      inference('sup-', [status(thm)], ['11', '12'])).
% 0.41/0.59  thf('14', plain,
% 0.41/0.59      (((~ (v3_ordinal1 @ sk_A)
% 0.41/0.59         | ((sk_B) = (sk_A))
% 0.41/0.59         | (r2_hidden @ sk_A @ sk_B)
% 0.41/0.59         | ~ (v3_ordinal1 @ sk_B))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['10', '13'])).
% 0.41/0.59  thf('15', plain, ((v3_ordinal1 @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('16', plain, ((v3_ordinal1 @ sk_B)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('17', plain,
% 0.41/0.59      (((((sk_B) = (sk_A)) | (r2_hidden @ sk_A @ sk_B)))
% 0.41/0.59         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.41/0.59      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.41/0.59  thf(d3_xboole_0, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.41/0.59       ( ![D:$i]:
% 0.41/0.59         ( ( r2_hidden @ D @ C ) <=>
% 0.41/0.59           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.41/0.59  thf('18', plain,
% 0.41/0.59      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.41/0.59         (~ (r2_hidden @ X2 @ X5)
% 0.41/0.59          | (r2_hidden @ X2 @ X4)
% 0.41/0.59          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.41/0.59      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.41/0.59  thf('19', plain,
% 0.41/0.59      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.41/0.59         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X5))),
% 0.41/0.59      inference('simplify', [status(thm)], ['18'])).
% 0.41/0.59  thf('20', plain,
% 0.41/0.59      ((![X0 : $i]:
% 0.41/0.59          (((sk_B) = (sk_A)) | (r2_hidden @ sk_A @ (k2_xboole_0 @ sk_B @ X0))))
% 0.41/0.59         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['17', '19'])).
% 0.41/0.59  thf('21', plain,
% 0.41/0.59      ((((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)) | ((sk_B) = (sk_A))))
% 0.41/0.59         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.41/0.59      inference('sup+', [status(thm)], ['3', '20'])).
% 0.41/0.59  thf('22', plain,
% 0.41/0.59      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.41/0.59         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.41/0.59      inference('split', [status(esa)], ['0'])).
% 0.41/0.59  thf('23', plain,
% 0.41/0.59      ((((sk_B) = (sk_A)))
% 0.41/0.59         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.41/0.59             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['21', '22'])).
% 0.41/0.59  thf('24', plain,
% 0.41/0.59      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.41/0.59         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.41/0.59      inference('split', [status(esa)], ['0'])).
% 0.41/0.59  thf('25', plain,
% 0.41/0.59      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 0.41/0.59         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.41/0.59             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['23', '24'])).
% 0.41/0.59  thf('26', plain,
% 0.41/0.59      (![X16 : $i]:
% 0.41/0.59         ((k1_ordinal1 @ X16) = (k2_xboole_0 @ X16 @ (k1_tarski @ X16)))),
% 0.41/0.59      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.41/0.59  thf(d10_xboole_0, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.41/0.59  thf('27', plain,
% 0.41/0.59      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 0.41/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.41/0.59  thf('28', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 0.41/0.59      inference('simplify', [status(thm)], ['27'])).
% 0.41/0.59  thf(l1_zfmisc_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.41/0.59  thf('29', plain,
% 0.41/0.59      (![X11 : $i, X12 : $i]:
% 0.41/0.59         ((r2_hidden @ X11 @ X12) | ~ (r1_tarski @ (k1_tarski @ X11) @ X12))),
% 0.41/0.59      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.41/0.59  thf('30', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.41/0.59      inference('sup-', [status(thm)], ['28', '29'])).
% 0.41/0.59  thf('31', plain,
% 0.41/0.59      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.41/0.59         (~ (r2_hidden @ X2 @ X3)
% 0.41/0.59          | (r2_hidden @ X2 @ X4)
% 0.41/0.59          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.41/0.59      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.41/0.59  thf('32', plain,
% 0.41/0.59      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.41/0.59         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 0.41/0.59      inference('simplify', [status(thm)], ['31'])).
% 0.41/0.59  thf('33', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['30', '32'])).
% 0.41/0.59  thf('34', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_ordinal1 @ X0))),
% 0.41/0.59      inference('sup+', [status(thm)], ['26', '33'])).
% 0.41/0.59  thf('35', plain,
% 0.41/0.59      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) | 
% 0.41/0.59       ~ ((r1_ordinal1 @ sk_A @ sk_B))),
% 0.41/0.59      inference('demod', [status(thm)], ['25', '34'])).
% 0.41/0.59  thf('36', plain, (~ ((r1_ordinal1 @ sk_A @ sk_B))),
% 0.41/0.59      inference('sat_resolution*', [status(thm)], ['2', '35'])).
% 0.41/0.59  thf('37', plain, (~ (r1_ordinal1 @ sk_A @ sk_B)),
% 0.41/0.59      inference('simpl_trail', [status(thm)], ['1', '36'])).
% 0.41/0.59  thf(t26_ordinal1, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( v3_ordinal1 @ A ) =>
% 0.41/0.59       ( ![B:$i]:
% 0.41/0.59         ( ( v3_ordinal1 @ B ) =>
% 0.41/0.59           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.41/0.59  thf('38', plain,
% 0.41/0.59      (![X21 : $i, X22 : $i]:
% 0.41/0.59         (~ (v3_ordinal1 @ X21)
% 0.41/0.59          | (r1_ordinal1 @ X22 @ X21)
% 0.41/0.59          | (r2_hidden @ X21 @ X22)
% 0.41/0.59          | ~ (v3_ordinal1 @ X22))),
% 0.41/0.59      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.41/0.59  thf('39', plain,
% 0.41/0.59      (![X11 : $i, X13 : $i]:
% 0.41/0.59         ((r1_tarski @ (k1_tarski @ X11) @ X13) | ~ (r2_hidden @ X11 @ X13))),
% 0.41/0.59      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.41/0.59  thf('40', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         (~ (v3_ordinal1 @ X0)
% 0.41/0.59          | (r1_ordinal1 @ X0 @ X1)
% 0.41/0.59          | ~ (v3_ordinal1 @ X1)
% 0.41/0.59          | (r1_tarski @ (k1_tarski @ X1) @ X0))),
% 0.41/0.59      inference('sup-', [status(thm)], ['38', '39'])).
% 0.41/0.59  thf('41', plain,
% 0.41/0.59      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.41/0.59         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.41/0.59      inference('split', [status(esa)], ['4'])).
% 0.41/0.59  thf('42', plain,
% 0.41/0.59      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) | 
% 0.41/0.59       ((r1_ordinal1 @ sk_A @ sk_B))),
% 0.41/0.59      inference('split', [status(esa)], ['4'])).
% 0.41/0.59  thf('43', plain, (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.41/0.59      inference('sat_resolution*', [status(thm)], ['2', '35', '42'])).
% 0.41/0.59  thf('44', plain, ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))),
% 0.41/0.59      inference('simpl_trail', [status(thm)], ['41', '43'])).
% 0.41/0.59  thf('45', plain,
% 0.41/0.59      (![X16 : $i]:
% 0.41/0.59         ((k1_ordinal1 @ X16) = (k2_xboole_0 @ X16 @ (k1_tarski @ X16)))),
% 0.41/0.59      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.41/0.59  thf('46', plain,
% 0.41/0.59      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.41/0.59         (~ (r2_hidden @ X6 @ X4)
% 0.41/0.59          | (r2_hidden @ X6 @ X5)
% 0.41/0.59          | (r2_hidden @ X6 @ X3)
% 0.41/0.59          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.41/0.59      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.41/0.59  thf('47', plain,
% 0.41/0.59      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.41/0.59         ((r2_hidden @ X6 @ X3)
% 0.41/0.59          | (r2_hidden @ X6 @ X5)
% 0.41/0.59          | ~ (r2_hidden @ X6 @ (k2_xboole_0 @ X5 @ X3)))),
% 0.41/0.59      inference('simplify', [status(thm)], ['46'])).
% 0.41/0.59  thf('48', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.41/0.59          | (r2_hidden @ X1 @ X0)
% 0.41/0.59          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['45', '47'])).
% 0.41/0.59  thf('49', plain,
% 0.41/0.59      (((r2_hidden @ sk_A @ (k1_tarski @ sk_B)) | (r2_hidden @ sk_A @ sk_B))),
% 0.41/0.59      inference('sup-', [status(thm)], ['44', '48'])).
% 0.41/0.59  thf('50', plain,
% 0.41/0.59      (![X23 : $i, X24 : $i]:
% 0.41/0.59         (~ (r2_hidden @ X23 @ X24) | ~ (r1_tarski @ X24 @ X23))),
% 0.41/0.59      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.41/0.59  thf('51', plain,
% 0.41/0.59      (((r2_hidden @ sk_A @ sk_B) | ~ (r1_tarski @ (k1_tarski @ sk_B) @ sk_A))),
% 0.41/0.59      inference('sup-', [status(thm)], ['49', '50'])).
% 0.41/0.59  thf('52', plain,
% 0.41/0.59      ((~ (v3_ordinal1 @ sk_B)
% 0.41/0.59        | (r1_ordinal1 @ sk_A @ sk_B)
% 0.41/0.59        | ~ (v3_ordinal1 @ sk_A)
% 0.41/0.59        | (r2_hidden @ sk_A @ sk_B))),
% 0.41/0.59      inference('sup-', [status(thm)], ['40', '51'])).
% 0.41/0.59  thf('53', plain, ((v3_ordinal1 @ sk_B)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('54', plain, ((v3_ordinal1 @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('55', plain, (((r1_ordinal1 @ sk_A @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 0.41/0.59      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.41/0.59  thf('56', plain, (~ (r1_ordinal1 @ sk_A @ sk_B)),
% 0.41/0.59      inference('simpl_trail', [status(thm)], ['1', '36'])).
% 0.41/0.59  thf('57', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.41/0.59      inference('clc', [status(thm)], ['55', '56'])).
% 0.41/0.59  thf('58', plain,
% 0.41/0.59      (![X21 : $i, X22 : $i]:
% 0.41/0.59         (~ (v3_ordinal1 @ X21)
% 0.41/0.59          | (r1_ordinal1 @ X22 @ X21)
% 0.41/0.59          | (r2_hidden @ X21 @ X22)
% 0.41/0.59          | ~ (v3_ordinal1 @ X22))),
% 0.41/0.59      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.41/0.59  thf(antisymmetry_r2_hidden, axiom,
% 0.41/0.59    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.41/0.59  thf('59', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.41/0.59      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.41/0.59  thf('60', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         (~ (v3_ordinal1 @ X0)
% 0.41/0.59          | (r1_ordinal1 @ X0 @ X1)
% 0.41/0.59          | ~ (v3_ordinal1 @ X1)
% 0.41/0.59          | ~ (r2_hidden @ X0 @ X1))),
% 0.41/0.59      inference('sup-', [status(thm)], ['58', '59'])).
% 0.41/0.59  thf('61', plain,
% 0.41/0.59      ((~ (v3_ordinal1 @ sk_B)
% 0.41/0.59        | (r1_ordinal1 @ sk_A @ sk_B)
% 0.41/0.59        | ~ (v3_ordinal1 @ sk_A))),
% 0.41/0.59      inference('sup-', [status(thm)], ['57', '60'])).
% 0.41/0.59  thf('62', plain, ((v3_ordinal1 @ sk_B)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('63', plain, ((v3_ordinal1 @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('64', plain, ((r1_ordinal1 @ sk_A @ sk_B)),
% 0.41/0.59      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.41/0.59  thf('65', plain, ($false), inference('demod', [status(thm)], ['37', '64'])).
% 0.41/0.59  
% 0.41/0.59  % SZS output end Refutation
% 0.41/0.59  
% 0.41/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5oHEKIuExh

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:07 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 132 expanded)
%              Number of leaves         :   17 (  41 expanded)
%              Depth                    :   13
%              Number of atoms          :  596 (1080 expanded)
%              Number of equality atoms :   26 (  32 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

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
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(connectedness_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
        | ( r1_ordinal1 @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v3_ordinal1 @ X12 )
      | ~ ( v3_ordinal1 @ X13 )
      | ( r1_ordinal1 @ X12 @ X13 )
      | ( r1_ordinal1 @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v3_ordinal1 @ X15 )
      | ~ ( v3_ordinal1 @ X16 )
      | ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_ordinal1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('11',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( r1_tarski @ sk_B @ sk_A ) )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['14'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('16',plain,(
    ! [X14: $i] :
      ( ( k1_ordinal1 @ X14 )
      = ( k2_xboole_0 @ X14 @ ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('17',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('18',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','19'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('21',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X8 )
      | ( X9 = X6 )
      | ( X8
       != ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('22',plain,(
    ! [X6: $i,X9: $i] :
      ( ( X9 = X6 )
      | ~ ( r2_hidden @ X9 @ ( k1_tarski @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ( sk_A = sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('24',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( r1_tarski @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('25',plain,
    ( ( ( sk_A = sk_B )
      | ~ ( r1_tarski @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','25'])).

thf('27',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('28',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_A )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('30',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_A ) ),
    inference(eq_fact,[status(thm)],['29'])).

thf('31',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    r1_ordinal1 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','32'])).

thf('34',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['14'])).

thf('35',plain,(
    ! [X14: $i] :
      ( ( k1_ordinal1 @ X14 )
      = ( k2_xboole_0 @ X14 @ ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('36',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['14'])).

thf('37',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v3_ordinal1 @ X15 )
      | ~ ( v3_ordinal1 @ X16 )
      | ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_ordinal1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('38',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('42',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_ordinal1 @ X17 )
      | ( r2_hidden @ X18 @ X17 )
      | ( X18 = X17 )
      | ( r2_hidden @ X17 @ X18 )
      | ~ ( v3_ordinal1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('43',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( r1_tarski @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( sk_B = sk_A )
      | ( r2_hidden @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( ( sk_B = sk_A )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ( sk_B = sk_A )
        | ( r2_hidden @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      | ( sk_B = sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['35','51'])).

thf('53',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('54',plain,
    ( ( sk_B = sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('56',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X14: $i] :
      ( ( k1_ordinal1 @ X14 )
      = ( k2_xboole_0 @ X14 @ ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('58',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( X7 != X6 )
      | ( r2_hidden @ X7 @ X8 )
      | ( X8
       != ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('59',plain,(
    ! [X6: $i] :
      ( r2_hidden @ X6 @ ( k1_tarski @ X6 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['57','62'])).

thf('64',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['56','63'])).

thf('65',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','33','34','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5oHEKIuExh
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:17:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.52/0.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.52/0.72  % Solved by: fo/fo7.sh
% 0.52/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.72  % done 380 iterations in 0.243s
% 0.52/0.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.52/0.72  % SZS output start Refutation
% 0.52/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.72  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.52/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.72  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.52/0.72  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.52/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.72  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.52/0.72  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.52/0.72  thf(t34_ordinal1, conjecture,
% 0.52/0.72    (![A:$i]:
% 0.52/0.72     ( ( v3_ordinal1 @ A ) =>
% 0.52/0.72       ( ![B:$i]:
% 0.52/0.72         ( ( v3_ordinal1 @ B ) =>
% 0.52/0.72           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.52/0.72             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 0.52/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.72    (~( ![A:$i]:
% 0.52/0.72        ( ( v3_ordinal1 @ A ) =>
% 0.52/0.72          ( ![B:$i]:
% 0.52/0.72            ( ( v3_ordinal1 @ B ) =>
% 0.52/0.72              ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.52/0.72                ( r1_ordinal1 @ A @ B ) ) ) ) ) )),
% 0.52/0.72    inference('cnf.neg', [status(esa)], [t34_ordinal1])).
% 0.52/0.72  thf('0', plain,
% 0.52/0.72      ((~ (r1_ordinal1 @ sk_A @ sk_B)
% 0.52/0.72        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('1', plain,
% 0.52/0.72      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.52/0.72       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.52/0.72      inference('split', [status(esa)], ['0'])).
% 0.52/0.72  thf('2', plain, ((v3_ordinal1 @ sk_A)),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf(connectedness_r1_ordinal1, axiom,
% 0.52/0.72    (![A:$i,B:$i]:
% 0.52/0.72     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.52/0.72       ( ( r1_ordinal1 @ A @ B ) | ( r1_ordinal1 @ B @ A ) ) ))).
% 0.52/0.72  thf('3', plain,
% 0.52/0.72      (![X12 : $i, X13 : $i]:
% 0.52/0.72         (~ (v3_ordinal1 @ X12)
% 0.52/0.72          | ~ (v3_ordinal1 @ X13)
% 0.52/0.72          | (r1_ordinal1 @ X12 @ X13)
% 0.52/0.72          | (r1_ordinal1 @ X13 @ X12))),
% 0.52/0.72      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.52/0.72  thf('4', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         ((r1_ordinal1 @ X0 @ sk_A)
% 0.52/0.72          | (r1_ordinal1 @ sk_A @ X0)
% 0.52/0.72          | ~ (v3_ordinal1 @ X0))),
% 0.52/0.72      inference('sup-', [status(thm)], ['2', '3'])).
% 0.52/0.72  thf(redefinition_r1_ordinal1, axiom,
% 0.52/0.72    (![A:$i,B:$i]:
% 0.52/0.72     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.52/0.72       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.52/0.72  thf('5', plain,
% 0.52/0.72      (![X15 : $i, X16 : $i]:
% 0.52/0.72         (~ (v3_ordinal1 @ X15)
% 0.52/0.72          | ~ (v3_ordinal1 @ X16)
% 0.52/0.72          | (r1_tarski @ X15 @ X16)
% 0.52/0.72          | ~ (r1_ordinal1 @ X15 @ X16))),
% 0.52/0.72      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.52/0.72  thf('6', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         (~ (v3_ordinal1 @ X0)
% 0.52/0.72          | (r1_ordinal1 @ sk_A @ X0)
% 0.52/0.72          | (r1_tarski @ X0 @ sk_A)
% 0.52/0.72          | ~ (v3_ordinal1 @ sk_A)
% 0.52/0.72          | ~ (v3_ordinal1 @ X0))),
% 0.52/0.72      inference('sup-', [status(thm)], ['4', '5'])).
% 0.52/0.72  thf('7', plain, ((v3_ordinal1 @ sk_A)),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('8', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         (~ (v3_ordinal1 @ X0)
% 0.52/0.72          | (r1_ordinal1 @ sk_A @ X0)
% 0.52/0.72          | (r1_tarski @ X0 @ sk_A)
% 0.52/0.72          | ~ (v3_ordinal1 @ X0))),
% 0.52/0.72      inference('demod', [status(thm)], ['6', '7'])).
% 0.52/0.72  thf('9', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         ((r1_tarski @ X0 @ sk_A)
% 0.52/0.72          | (r1_ordinal1 @ sk_A @ X0)
% 0.52/0.72          | ~ (v3_ordinal1 @ X0))),
% 0.52/0.72      inference('simplify', [status(thm)], ['8'])).
% 0.52/0.72  thf('10', plain,
% 0.52/0.72      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.52/0.72      inference('split', [status(esa)], ['0'])).
% 0.52/0.72  thf('11', plain,
% 0.52/0.72      (((~ (v3_ordinal1 @ sk_B) | (r1_tarski @ sk_B @ sk_A)))
% 0.52/0.72         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.52/0.72      inference('sup-', [status(thm)], ['9', '10'])).
% 0.52/0.72  thf('12', plain, ((v3_ordinal1 @ sk_B)),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('13', plain,
% 0.52/0.72      (((r1_tarski @ sk_B @ sk_A)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.52/0.72      inference('demod', [status(thm)], ['11', '12'])).
% 0.52/0.72  thf('14', plain,
% 0.52/0.72      (((r1_ordinal1 @ sk_A @ sk_B) | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('15', plain,
% 0.52/0.72      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.52/0.72         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.52/0.72      inference('split', [status(esa)], ['14'])).
% 0.52/0.72  thf(d1_ordinal1, axiom,
% 0.52/0.72    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.52/0.72  thf('16', plain,
% 0.52/0.72      (![X14 : $i]:
% 0.52/0.72         ((k1_ordinal1 @ X14) = (k2_xboole_0 @ X14 @ (k1_tarski @ X14)))),
% 0.52/0.72      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.52/0.72  thf(d3_xboole_0, axiom,
% 0.52/0.72    (![A:$i,B:$i,C:$i]:
% 0.52/0.72     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.52/0.72       ( ![D:$i]:
% 0.52/0.72         ( ( r2_hidden @ D @ C ) <=>
% 0.52/0.72           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.52/0.72  thf('17', plain,
% 0.52/0.72      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.52/0.72         (~ (r2_hidden @ X4 @ X2)
% 0.52/0.72          | (r2_hidden @ X4 @ X3)
% 0.52/0.72          | (r2_hidden @ X4 @ X1)
% 0.52/0.72          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.52/0.72      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.52/0.72  thf('18', plain,
% 0.52/0.72      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.52/0.72         ((r2_hidden @ X4 @ X1)
% 0.52/0.72          | (r2_hidden @ X4 @ X3)
% 0.52/0.72          | ~ (r2_hidden @ X4 @ (k2_xboole_0 @ X3 @ X1)))),
% 0.52/0.72      inference('simplify', [status(thm)], ['17'])).
% 0.52/0.72  thf('19', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]:
% 0.52/0.72         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.52/0.72          | (r2_hidden @ X1 @ X0)
% 0.52/0.72          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.52/0.72      inference('sup-', [status(thm)], ['16', '18'])).
% 0.52/0.72  thf('20', plain,
% 0.52/0.72      ((((r2_hidden @ sk_A @ (k1_tarski @ sk_B)) | (r2_hidden @ sk_A @ sk_B)))
% 0.52/0.72         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.52/0.72      inference('sup-', [status(thm)], ['15', '19'])).
% 0.52/0.72  thf(d1_tarski, axiom,
% 0.52/0.72    (![A:$i,B:$i]:
% 0.52/0.72     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.52/0.72       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.52/0.72  thf('21', plain,
% 0.52/0.72      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.52/0.72         (~ (r2_hidden @ X9 @ X8) | ((X9) = (X6)) | ((X8) != (k1_tarski @ X6)))),
% 0.52/0.72      inference('cnf', [status(esa)], [d1_tarski])).
% 0.52/0.72  thf('22', plain,
% 0.52/0.72      (![X6 : $i, X9 : $i]:
% 0.52/0.72         (((X9) = (X6)) | ~ (r2_hidden @ X9 @ (k1_tarski @ X6)))),
% 0.52/0.72      inference('simplify', [status(thm)], ['21'])).
% 0.52/0.72  thf('23', plain,
% 0.52/0.72      ((((r2_hidden @ sk_A @ sk_B) | ((sk_A) = (sk_B))))
% 0.52/0.72         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.52/0.72      inference('sup-', [status(thm)], ['20', '22'])).
% 0.52/0.72  thf(t7_ordinal1, axiom,
% 0.52/0.72    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.52/0.72  thf('24', plain,
% 0.52/0.72      (![X19 : $i, X20 : $i]:
% 0.52/0.72         (~ (r2_hidden @ X19 @ X20) | ~ (r1_tarski @ X20 @ X19))),
% 0.52/0.72      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.52/0.72  thf('25', plain,
% 0.52/0.72      (((((sk_A) = (sk_B)) | ~ (r1_tarski @ sk_B @ sk_A)))
% 0.52/0.72         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.52/0.72      inference('sup-', [status(thm)], ['23', '24'])).
% 0.52/0.72  thf('26', plain,
% 0.52/0.72      ((((sk_A) = (sk_B)))
% 0.52/0.72         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 0.52/0.72             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.52/0.72      inference('sup-', [status(thm)], ['13', '25'])).
% 0.52/0.72  thf('27', plain,
% 0.52/0.72      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.52/0.72      inference('split', [status(esa)], ['0'])).
% 0.52/0.72  thf('28', plain,
% 0.52/0.72      ((~ (r1_ordinal1 @ sk_A @ sk_A))
% 0.52/0.72         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 0.52/0.72             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.52/0.72      inference('sup-', [status(thm)], ['26', '27'])).
% 0.52/0.72  thf('29', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         ((r1_ordinal1 @ X0 @ sk_A)
% 0.52/0.72          | (r1_ordinal1 @ sk_A @ X0)
% 0.52/0.72          | ~ (v3_ordinal1 @ X0))),
% 0.52/0.72      inference('sup-', [status(thm)], ['2', '3'])).
% 0.52/0.72  thf('30', plain, ((~ (v3_ordinal1 @ sk_A) | (r1_ordinal1 @ sk_A @ sk_A))),
% 0.52/0.72      inference('eq_fact', [status(thm)], ['29'])).
% 0.52/0.72  thf('31', plain, ((v3_ordinal1 @ sk_A)),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('32', plain, ((r1_ordinal1 @ sk_A @ sk_A)),
% 0.52/0.72      inference('demod', [status(thm)], ['30', '31'])).
% 0.52/0.72  thf('33', plain,
% 0.52/0.72      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.52/0.72       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.52/0.72      inference('demod', [status(thm)], ['28', '32'])).
% 0.52/0.72  thf('34', plain,
% 0.52/0.72      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.52/0.72       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.52/0.72      inference('split', [status(esa)], ['14'])).
% 0.52/0.72  thf('35', plain,
% 0.52/0.72      (![X14 : $i]:
% 0.52/0.72         ((k1_ordinal1 @ X14) = (k2_xboole_0 @ X14 @ (k1_tarski @ X14)))),
% 0.52/0.72      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.52/0.72  thf('36', plain,
% 0.52/0.72      (((r1_ordinal1 @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.52/0.72      inference('split', [status(esa)], ['14'])).
% 0.52/0.72  thf('37', plain,
% 0.52/0.72      (![X15 : $i, X16 : $i]:
% 0.52/0.72         (~ (v3_ordinal1 @ X15)
% 0.52/0.72          | ~ (v3_ordinal1 @ X16)
% 0.52/0.72          | (r1_tarski @ X15 @ X16)
% 0.52/0.72          | ~ (r1_ordinal1 @ X15 @ X16))),
% 0.52/0.72      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.52/0.72  thf('38', plain,
% 0.52/0.72      ((((r1_tarski @ sk_A @ sk_B)
% 0.52/0.72         | ~ (v3_ordinal1 @ sk_B)
% 0.52/0.72         | ~ (v3_ordinal1 @ sk_A))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.52/0.72      inference('sup-', [status(thm)], ['36', '37'])).
% 0.52/0.72  thf('39', plain, ((v3_ordinal1 @ sk_B)),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('40', plain, ((v3_ordinal1 @ sk_A)),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('41', plain,
% 0.52/0.72      (((r1_tarski @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.52/0.72      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.52/0.72  thf(t24_ordinal1, axiom,
% 0.52/0.72    (![A:$i]:
% 0.52/0.72     ( ( v3_ordinal1 @ A ) =>
% 0.52/0.72       ( ![B:$i]:
% 0.52/0.72         ( ( v3_ordinal1 @ B ) =>
% 0.52/0.72           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.52/0.72                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 0.52/0.72  thf('42', plain,
% 0.52/0.72      (![X17 : $i, X18 : $i]:
% 0.52/0.72         (~ (v3_ordinal1 @ X17)
% 0.52/0.72          | (r2_hidden @ X18 @ X17)
% 0.52/0.72          | ((X18) = (X17))
% 0.52/0.72          | (r2_hidden @ X17 @ X18)
% 0.52/0.72          | ~ (v3_ordinal1 @ X18))),
% 0.52/0.72      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.52/0.72  thf('43', plain,
% 0.52/0.72      (![X19 : $i, X20 : $i]:
% 0.52/0.72         (~ (r2_hidden @ X19 @ X20) | ~ (r1_tarski @ X20 @ X19))),
% 0.52/0.72      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.52/0.72  thf('44', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]:
% 0.52/0.72         (~ (v3_ordinal1 @ X1)
% 0.52/0.72          | (r2_hidden @ X0 @ X1)
% 0.52/0.72          | ((X1) = (X0))
% 0.52/0.72          | ~ (v3_ordinal1 @ X0)
% 0.52/0.72          | ~ (r1_tarski @ X0 @ X1))),
% 0.52/0.72      inference('sup-', [status(thm)], ['42', '43'])).
% 0.52/0.72  thf('45', plain,
% 0.52/0.72      (((~ (v3_ordinal1 @ sk_A)
% 0.52/0.72         | ((sk_B) = (sk_A))
% 0.52/0.72         | (r2_hidden @ sk_A @ sk_B)
% 0.52/0.72         | ~ (v3_ordinal1 @ sk_B))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.52/0.72      inference('sup-', [status(thm)], ['41', '44'])).
% 0.52/0.72  thf('46', plain, ((v3_ordinal1 @ sk_A)),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('47', plain, ((v3_ordinal1 @ sk_B)),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('48', plain,
% 0.52/0.72      (((((sk_B) = (sk_A)) | (r2_hidden @ sk_A @ sk_B)))
% 0.52/0.72         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.52/0.72      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.52/0.72  thf('49', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.52/0.72         (~ (r2_hidden @ X0 @ X3)
% 0.52/0.72          | (r2_hidden @ X0 @ X2)
% 0.52/0.72          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.52/0.72      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.52/0.72  thf('50', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.52/0.72         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 0.52/0.72      inference('simplify', [status(thm)], ['49'])).
% 0.52/0.72  thf('51', plain,
% 0.52/0.72      ((![X0 : $i]:
% 0.52/0.72          (((sk_B) = (sk_A)) | (r2_hidden @ sk_A @ (k2_xboole_0 @ sk_B @ X0))))
% 0.52/0.72         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.52/0.72      inference('sup-', [status(thm)], ['48', '50'])).
% 0.52/0.72  thf('52', plain,
% 0.52/0.72      ((((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)) | ((sk_B) = (sk_A))))
% 0.52/0.72         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.52/0.72      inference('sup+', [status(thm)], ['35', '51'])).
% 0.52/0.72  thf('53', plain,
% 0.52/0.72      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.52/0.72         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.52/0.72      inference('split', [status(esa)], ['0'])).
% 0.52/0.72  thf('54', plain,
% 0.52/0.72      ((((sk_B) = (sk_A)))
% 0.52/0.72         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.52/0.72             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.52/0.72      inference('sup-', [status(thm)], ['52', '53'])).
% 0.52/0.72  thf('55', plain,
% 0.52/0.72      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.52/0.72         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.52/0.72      inference('split', [status(esa)], ['0'])).
% 0.52/0.72  thf('56', plain,
% 0.52/0.72      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 0.52/0.72         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.52/0.72             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.52/0.72      inference('sup-', [status(thm)], ['54', '55'])).
% 0.52/0.72  thf('57', plain,
% 0.52/0.72      (![X14 : $i]:
% 0.52/0.72         ((k1_ordinal1 @ X14) = (k2_xboole_0 @ X14 @ (k1_tarski @ X14)))),
% 0.52/0.72      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.52/0.72  thf('58', plain,
% 0.52/0.72      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.52/0.72         (((X7) != (X6)) | (r2_hidden @ X7 @ X8) | ((X8) != (k1_tarski @ X6)))),
% 0.52/0.72      inference('cnf', [status(esa)], [d1_tarski])).
% 0.52/0.72  thf('59', plain, (![X6 : $i]: (r2_hidden @ X6 @ (k1_tarski @ X6))),
% 0.52/0.72      inference('simplify', [status(thm)], ['58'])).
% 0.52/0.72  thf('60', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.52/0.72         (~ (r2_hidden @ X0 @ X1)
% 0.52/0.72          | (r2_hidden @ X0 @ X2)
% 0.52/0.72          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.52/0.72      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.52/0.72  thf('61', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.52/0.72         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 0.52/0.72      inference('simplify', [status(thm)], ['60'])).
% 0.52/0.72  thf('62', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]:
% 0.52/0.72         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.52/0.72      inference('sup-', [status(thm)], ['59', '61'])).
% 0.52/0.72  thf('63', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_ordinal1 @ X0))),
% 0.52/0.72      inference('sup+', [status(thm)], ['57', '62'])).
% 0.52/0.72  thf('64', plain,
% 0.52/0.72      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.52/0.72       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.52/0.72      inference('demod', [status(thm)], ['56', '63'])).
% 0.52/0.72  thf('65', plain, ($false),
% 0.52/0.72      inference('sat_resolution*', [status(thm)], ['1', '33', '34', '64'])).
% 0.52/0.72  
% 0.52/0.72  % SZS output end Refutation
% 0.52/0.72  
% 0.52/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

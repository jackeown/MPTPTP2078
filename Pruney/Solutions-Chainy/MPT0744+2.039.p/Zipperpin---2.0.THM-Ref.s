%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.znkBxhffJj

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:05 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 131 expanded)
%              Number of leaves         :   21 (  43 expanded)
%              Depth                    :   14
%              Number of atoms          :  572 (1037 expanded)
%              Number of equality atoms :   22 (  24 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v3_ordinal1 @ X19 )
      | ~ ( v3_ordinal1 @ X20 )
      | ( r1_ordinal1 @ X19 @ X20 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['7'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('9',plain,(
    ! [X15: $i] :
      ( ( k1_ordinal1 @ X15 )
      = ( k2_xboole_0 @ X15 @ ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('10',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('11',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ( r2_hidden @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['8','12'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('14',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( X12 = X9 )
      | ( X11
       != ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('15',plain,(
    ! [X9: $i,X12: $i] :
      ( ( X12 = X9 )
      | ~ ( r2_hidden @ X12 @ ( k1_tarski @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B_1 )
      | ( sk_A = sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf(d2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
    <=> ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( r1_tarski @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ( r1_tarski @ X16 @ X17 )
      | ~ ( v1_ordinal1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('18',plain,
    ( ( ( sk_A = sk_B_1 )
      | ~ ( v1_ordinal1 @ sk_B_1 )
      | ( r1_tarski @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('20',plain,(
    ! [X14: $i] :
      ( ( v1_ordinal1 @ X14 )
      | ~ ( v3_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('21',plain,(
    v1_ordinal1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( sk_A = sk_B_1 )
      | ( r1_tarski @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v3_ordinal1 @ X19 )
      | ~ ( v3_ordinal1 @ X20 )
      | ( r1_ordinal1 @ X19 @ X20 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('24',plain,
    ( ( ( sk_A = sk_B_1 )
      | ( r1_ordinal1 @ sk_A @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( ( sk_A = sk_B_1 )
      | ( r1_ordinal1 @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('29',plain,
    ( ( sk_A = sk_B_1 )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_A )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['6','31'])).

thf('33',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['7'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('36',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v3_ordinal1 @ X24 )
      | ( r1_ordinal1 @ X25 @ X24 )
      | ( r2_hidden @ X24 @ X25 )
      | ~ ( v3_ordinal1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('37',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r2_hidden @ X22 @ ( k1_ordinal1 @ X23 ) )
      | ~ ( r2_hidden @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_ordinal1 @ sk_B_1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( r1_ordinal1 @ sk_B_1 @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v3_ordinal1 @ X19 )
      | ~ ( v3_ordinal1 @ X20 )
      | ( r1_tarski @ X19 @ X20 )
      | ~ ( r1_ordinal1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('45',plain,
    ( ( ( r1_tarski @ sk_B_1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['7'])).

thf('50',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v3_ordinal1 @ X19 )
      | ~ ( v3_ordinal1 @ X20 )
      | ( r1_tarski @ X19 @ X20 )
      | ~ ( r1_ordinal1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('51',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( r1_tarski @ sk_A @ sk_B_1 )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('56',plain,
    ( ( ~ ( r1_tarski @ sk_B_1 @ sk_A )
      | ( sk_B_1 = sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( sk_B_1 = sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
      & ( r1_ordinal1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['48','56'])).

thf('58',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('59',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
      & ( r1_ordinal1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r2_hidden @ X22 @ ( k1_ordinal1 @ X23 ) )
      | ( X22 != X23 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('61',plain,(
    ! [X23: $i] :
      ( r2_hidden @ X23 @ ( k1_ordinal1 @ X23 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['59','61'])).

thf('63',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','34','35','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.znkBxhffJj
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:14:18 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.56  % Solved by: fo/fo7.sh
% 0.39/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.56  % done 269 iterations in 0.112s
% 0.39/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.56  % SZS output start Refutation
% 0.39/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.56  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.39/0.56  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 0.39/0.56  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.39/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.39/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.56  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 0.39/0.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.39/0.56  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.39/0.56  thf(t34_ordinal1, conjecture,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( v3_ordinal1 @ A ) =>
% 0.39/0.56       ( ![B:$i]:
% 0.39/0.56         ( ( v3_ordinal1 @ B ) =>
% 0.39/0.56           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.39/0.56             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 0.39/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.56    (~( ![A:$i]:
% 0.39/0.56        ( ( v3_ordinal1 @ A ) =>
% 0.39/0.56          ( ![B:$i]:
% 0.39/0.56            ( ( v3_ordinal1 @ B ) =>
% 0.39/0.56              ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.39/0.56                ( r1_ordinal1 @ A @ B ) ) ) ) ) )),
% 0.39/0.56    inference('cnf.neg', [status(esa)], [t34_ordinal1])).
% 0.39/0.56  thf('0', plain,
% 0.39/0.56      ((~ (r1_ordinal1 @ sk_A @ sk_B_1)
% 0.39/0.56        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('1', plain,
% 0.39/0.56      (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 0.39/0.56       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.39/0.56      inference('split', [status(esa)], ['0'])).
% 0.39/0.56  thf(d10_xboole_0, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.39/0.56  thf('2', plain,
% 0.39/0.56      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 0.39/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.56  thf('3', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.39/0.56      inference('simplify', [status(thm)], ['2'])).
% 0.39/0.56  thf(redefinition_r1_ordinal1, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.39/0.56       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.39/0.56  thf('4', plain,
% 0.39/0.56      (![X19 : $i, X20 : $i]:
% 0.39/0.56         (~ (v3_ordinal1 @ X19)
% 0.39/0.56          | ~ (v3_ordinal1 @ X20)
% 0.39/0.56          | (r1_ordinal1 @ X19 @ X20)
% 0.39/0.56          | ~ (r1_tarski @ X19 @ X20))),
% 0.39/0.56      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.39/0.56  thf('5', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         ((r1_ordinal1 @ X0 @ X0) | ~ (v3_ordinal1 @ X0) | ~ (v3_ordinal1 @ X0))),
% 0.39/0.56      inference('sup-', [status(thm)], ['3', '4'])).
% 0.39/0.56  thf('6', plain,
% 0.39/0.56      (![X0 : $i]: (~ (v3_ordinal1 @ X0) | (r1_ordinal1 @ X0 @ X0))),
% 0.39/0.56      inference('simplify', [status(thm)], ['5'])).
% 0.39/0.56  thf('7', plain,
% 0.39/0.56      (((r1_ordinal1 @ sk_A @ sk_B_1)
% 0.39/0.56        | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('8', plain,
% 0.39/0.56      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))
% 0.39/0.56         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.39/0.56      inference('split', [status(esa)], ['7'])).
% 0.39/0.56  thf(d1_ordinal1, axiom,
% 0.39/0.56    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.39/0.56  thf('9', plain,
% 0.39/0.56      (![X15 : $i]:
% 0.39/0.56         ((k1_ordinal1 @ X15) = (k2_xboole_0 @ X15 @ (k1_tarski @ X15)))),
% 0.39/0.56      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.39/0.56  thf(d3_xboole_0, axiom,
% 0.39/0.56    (![A:$i,B:$i,C:$i]:
% 0.39/0.56     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.39/0.56       ( ![D:$i]:
% 0.39/0.56         ( ( r2_hidden @ D @ C ) <=>
% 0.39/0.56           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.39/0.56  thf('10', plain,
% 0.39/0.56      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.39/0.56         (~ (r2_hidden @ X4 @ X2)
% 0.39/0.56          | (r2_hidden @ X4 @ X3)
% 0.39/0.56          | (r2_hidden @ X4 @ X1)
% 0.39/0.56          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.39/0.56      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.39/0.56  thf('11', plain,
% 0.39/0.56      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.39/0.56         ((r2_hidden @ X4 @ X1)
% 0.39/0.56          | (r2_hidden @ X4 @ X3)
% 0.39/0.56          | ~ (r2_hidden @ X4 @ (k2_xboole_0 @ X3 @ X1)))),
% 0.39/0.56      inference('simplify', [status(thm)], ['10'])).
% 0.39/0.56  thf('12', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.39/0.56          | (r2_hidden @ X1 @ X0)
% 0.39/0.56          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['9', '11'])).
% 0.39/0.56  thf('13', plain,
% 0.39/0.56      ((((r2_hidden @ sk_A @ (k1_tarski @ sk_B_1))
% 0.39/0.56         | (r2_hidden @ sk_A @ sk_B_1)))
% 0.39/0.56         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.39/0.56      inference('sup-', [status(thm)], ['8', '12'])).
% 0.39/0.56  thf(d1_tarski, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.39/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.39/0.56  thf('14', plain,
% 0.39/0.56      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.39/0.56         (~ (r2_hidden @ X12 @ X11)
% 0.39/0.56          | ((X12) = (X9))
% 0.39/0.56          | ((X11) != (k1_tarski @ X9)))),
% 0.39/0.56      inference('cnf', [status(esa)], [d1_tarski])).
% 0.39/0.56  thf('15', plain,
% 0.39/0.56      (![X9 : $i, X12 : $i]:
% 0.39/0.56         (((X12) = (X9)) | ~ (r2_hidden @ X12 @ (k1_tarski @ X9)))),
% 0.39/0.56      inference('simplify', [status(thm)], ['14'])).
% 0.39/0.56  thf('16', plain,
% 0.39/0.56      ((((r2_hidden @ sk_A @ sk_B_1) | ((sk_A) = (sk_B_1))))
% 0.39/0.56         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.39/0.56      inference('sup-', [status(thm)], ['13', '15'])).
% 0.39/0.56  thf(d2_ordinal1, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( v1_ordinal1 @ A ) <=>
% 0.39/0.56       ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( r1_tarski @ B @ A ) ) ) ))).
% 0.39/0.56  thf('17', plain,
% 0.39/0.56      (![X16 : $i, X17 : $i]:
% 0.39/0.56         (~ (r2_hidden @ X16 @ X17)
% 0.39/0.56          | (r1_tarski @ X16 @ X17)
% 0.39/0.56          | ~ (v1_ordinal1 @ X17))),
% 0.39/0.56      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.39/0.56  thf('18', plain,
% 0.39/0.56      (((((sk_A) = (sk_B_1))
% 0.39/0.56         | ~ (v1_ordinal1 @ sk_B_1)
% 0.39/0.56         | (r1_tarski @ sk_A @ sk_B_1)))
% 0.39/0.56         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.39/0.56      inference('sup-', [status(thm)], ['16', '17'])).
% 0.39/0.56  thf('19', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(cc1_ordinal1, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 0.39/0.56  thf('20', plain,
% 0.39/0.56      (![X14 : $i]: ((v1_ordinal1 @ X14) | ~ (v3_ordinal1 @ X14))),
% 0.39/0.56      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.39/0.56  thf('21', plain, ((v1_ordinal1 @ sk_B_1)),
% 0.39/0.56      inference('sup-', [status(thm)], ['19', '20'])).
% 0.39/0.56  thf('22', plain,
% 0.39/0.56      (((((sk_A) = (sk_B_1)) | (r1_tarski @ sk_A @ sk_B_1)))
% 0.39/0.56         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.39/0.56      inference('demod', [status(thm)], ['18', '21'])).
% 0.39/0.56  thf('23', plain,
% 0.39/0.56      (![X19 : $i, X20 : $i]:
% 0.39/0.56         (~ (v3_ordinal1 @ X19)
% 0.39/0.56          | ~ (v3_ordinal1 @ X20)
% 0.39/0.56          | (r1_ordinal1 @ X19 @ X20)
% 0.39/0.56          | ~ (r1_tarski @ X19 @ X20))),
% 0.39/0.56      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.39/0.56  thf('24', plain,
% 0.39/0.56      (((((sk_A) = (sk_B_1))
% 0.39/0.56         | (r1_ordinal1 @ sk_A @ sk_B_1)
% 0.39/0.56         | ~ (v3_ordinal1 @ sk_B_1)
% 0.39/0.56         | ~ (v3_ordinal1 @ sk_A)))
% 0.39/0.56         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.39/0.56      inference('sup-', [status(thm)], ['22', '23'])).
% 0.39/0.56  thf('25', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('26', plain, ((v3_ordinal1 @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('27', plain,
% 0.39/0.56      (((((sk_A) = (sk_B_1)) | (r1_ordinal1 @ sk_A @ sk_B_1)))
% 0.39/0.56         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.39/0.56      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.39/0.56  thf('28', plain,
% 0.39/0.56      ((~ (r1_ordinal1 @ sk_A @ sk_B_1)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.39/0.56      inference('split', [status(esa)], ['0'])).
% 0.39/0.56  thf('29', plain,
% 0.39/0.56      ((((sk_A) = (sk_B_1)))
% 0.39/0.56         <= (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) & 
% 0.39/0.56             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.39/0.56      inference('sup-', [status(thm)], ['27', '28'])).
% 0.39/0.56  thf('30', plain,
% 0.39/0.56      ((~ (r1_ordinal1 @ sk_A @ sk_B_1)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.39/0.56      inference('split', [status(esa)], ['0'])).
% 0.39/0.56  thf('31', plain,
% 0.39/0.56      ((~ (r1_ordinal1 @ sk_A @ sk_A))
% 0.39/0.56         <= (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) & 
% 0.39/0.56             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.39/0.56      inference('sup-', [status(thm)], ['29', '30'])).
% 0.39/0.56  thf('32', plain,
% 0.39/0.56      ((~ (v3_ordinal1 @ sk_A))
% 0.39/0.56         <= (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) & 
% 0.39/0.56             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.39/0.56      inference('sup-', [status(thm)], ['6', '31'])).
% 0.39/0.56  thf('33', plain, ((v3_ordinal1 @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('34', plain,
% 0.39/0.56      (((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 0.39/0.56       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.39/0.56      inference('demod', [status(thm)], ['32', '33'])).
% 0.39/0.56  thf('35', plain,
% 0.39/0.56      (((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 0.39/0.56       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.39/0.56      inference('split', [status(esa)], ['7'])).
% 0.39/0.56  thf(t26_ordinal1, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( v3_ordinal1 @ A ) =>
% 0.39/0.56       ( ![B:$i]:
% 0.39/0.56         ( ( v3_ordinal1 @ B ) =>
% 0.39/0.56           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.39/0.56  thf('36', plain,
% 0.39/0.56      (![X24 : $i, X25 : $i]:
% 0.39/0.56         (~ (v3_ordinal1 @ X24)
% 0.39/0.56          | (r1_ordinal1 @ X25 @ X24)
% 0.39/0.56          | (r2_hidden @ X24 @ X25)
% 0.39/0.56          | ~ (v3_ordinal1 @ X25))),
% 0.39/0.56      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.39/0.56  thf(t13_ordinal1, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.39/0.56       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.39/0.56  thf('37', plain,
% 0.39/0.56      (![X22 : $i, X23 : $i]:
% 0.39/0.56         ((r2_hidden @ X22 @ (k1_ordinal1 @ X23)) | ~ (r2_hidden @ X22 @ X23))),
% 0.39/0.56      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.39/0.56  thf('38', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         (~ (v3_ordinal1 @ X0)
% 0.39/0.56          | (r1_ordinal1 @ X0 @ X1)
% 0.39/0.56          | ~ (v3_ordinal1 @ X1)
% 0.39/0.56          | (r2_hidden @ X1 @ (k1_ordinal1 @ X0)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['36', '37'])).
% 0.39/0.56  thf('39', plain,
% 0.39/0.56      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))
% 0.39/0.56         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.39/0.56      inference('split', [status(esa)], ['0'])).
% 0.39/0.56  thf('40', plain,
% 0.39/0.56      (((~ (v3_ordinal1 @ sk_A)
% 0.39/0.56         | (r1_ordinal1 @ sk_B_1 @ sk_A)
% 0.39/0.56         | ~ (v3_ordinal1 @ sk_B_1)))
% 0.39/0.56         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.39/0.56      inference('sup-', [status(thm)], ['38', '39'])).
% 0.39/0.56  thf('41', plain, ((v3_ordinal1 @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('42', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('43', plain,
% 0.39/0.56      (((r1_ordinal1 @ sk_B_1 @ sk_A))
% 0.39/0.56         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.39/0.56      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.39/0.56  thf('44', plain,
% 0.39/0.56      (![X19 : $i, X20 : $i]:
% 0.39/0.56         (~ (v3_ordinal1 @ X19)
% 0.39/0.56          | ~ (v3_ordinal1 @ X20)
% 0.39/0.56          | (r1_tarski @ X19 @ X20)
% 0.39/0.56          | ~ (r1_ordinal1 @ X19 @ X20))),
% 0.39/0.56      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.39/0.56  thf('45', plain,
% 0.39/0.56      ((((r1_tarski @ sk_B_1 @ sk_A)
% 0.39/0.56         | ~ (v3_ordinal1 @ sk_A)
% 0.39/0.56         | ~ (v3_ordinal1 @ sk_B_1)))
% 0.39/0.56         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.39/0.56      inference('sup-', [status(thm)], ['43', '44'])).
% 0.39/0.56  thf('46', plain, ((v3_ordinal1 @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('47', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('48', plain,
% 0.39/0.56      (((r1_tarski @ sk_B_1 @ sk_A))
% 0.39/0.56         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.39/0.56      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.39/0.56  thf('49', plain,
% 0.39/0.56      (((r1_ordinal1 @ sk_A @ sk_B_1)) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.39/0.56      inference('split', [status(esa)], ['7'])).
% 0.39/0.56  thf('50', plain,
% 0.39/0.56      (![X19 : $i, X20 : $i]:
% 0.39/0.56         (~ (v3_ordinal1 @ X19)
% 0.39/0.56          | ~ (v3_ordinal1 @ X20)
% 0.39/0.56          | (r1_tarski @ X19 @ X20)
% 0.39/0.56          | ~ (r1_ordinal1 @ X19 @ X20))),
% 0.39/0.56      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.39/0.56  thf('51', plain,
% 0.39/0.56      ((((r1_tarski @ sk_A @ sk_B_1)
% 0.39/0.56         | ~ (v3_ordinal1 @ sk_B_1)
% 0.39/0.56         | ~ (v3_ordinal1 @ sk_A))) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['49', '50'])).
% 0.39/0.56  thf('52', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('53', plain, ((v3_ordinal1 @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('54', plain,
% 0.39/0.56      (((r1_tarski @ sk_A @ sk_B_1)) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.39/0.56      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.39/0.56  thf('55', plain,
% 0.39/0.56      (![X6 : $i, X8 : $i]:
% 0.39/0.56         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 0.39/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.56  thf('56', plain,
% 0.39/0.56      (((~ (r1_tarski @ sk_B_1 @ sk_A) | ((sk_B_1) = (sk_A))))
% 0.39/0.56         <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['54', '55'])).
% 0.39/0.56  thf('57', plain,
% 0.39/0.56      ((((sk_B_1) = (sk_A)))
% 0.39/0.56         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))) & 
% 0.39/0.56             ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['48', '56'])).
% 0.39/0.56  thf('58', plain,
% 0.39/0.56      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))
% 0.39/0.56         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.39/0.56      inference('split', [status(esa)], ['0'])).
% 0.39/0.56  thf('59', plain,
% 0.39/0.56      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 0.39/0.56         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))) & 
% 0.39/0.56             ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['57', '58'])).
% 0.39/0.56  thf('60', plain,
% 0.39/0.56      (![X22 : $i, X23 : $i]:
% 0.39/0.56         ((r2_hidden @ X22 @ (k1_ordinal1 @ X23)) | ((X22) != (X23)))),
% 0.39/0.56      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.39/0.56  thf('61', plain, (![X23 : $i]: (r2_hidden @ X23 @ (k1_ordinal1 @ X23))),
% 0.39/0.56      inference('simplify', [status(thm)], ['60'])).
% 0.39/0.56  thf('62', plain,
% 0.39/0.56      (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 0.39/0.56       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.39/0.56      inference('demod', [status(thm)], ['59', '61'])).
% 0.39/0.56  thf('63', plain, ($false),
% 0.39/0.56      inference('sat_resolution*', [status(thm)], ['1', '34', '35', '62'])).
% 0.39/0.56  
% 0.39/0.56  % SZS output end Refutation
% 0.39/0.56  
% 0.44/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

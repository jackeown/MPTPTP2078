%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.X3HBAozWF0

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:59 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 128 expanded)
%              Number of leaves         :   19 (  42 expanded)
%              Depth                    :   13
%              Number of atoms          :  527 ( 998 expanded)
%              Number of equality atoms :   18 (  20 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf(connectedness_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
        | ( r1_ordinal1 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v3_ordinal1 @ X6 )
      | ~ ( v3_ordinal1 @ X7 )
      | ( r1_ordinal1 @ X6 @ X7 )
      | ( r1_ordinal1 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v3_ordinal1 @ X9 )
      | ~ ( v3_ordinal1 @ X10 )
      | ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_ordinal1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('7',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B )
      | ( r1_tarski @ sk_B @ sk_A ) )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('11',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r2_xboole_0 @ X2 @ X4 )
      | ( X2 = X4 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('12',plain,
    ( ( ( sk_B = sk_A )
      | ( r2_xboole_0 @ sk_B @ sk_A ) )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t21_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_xboole_0 @ A @ B )
           => ( r2_hidden @ A @ B ) ) ) ) )).

thf('13',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v3_ordinal1 @ X15 )
      | ( r2_hidden @ X16 @ X15 )
      | ~ ( r2_xboole_0 @ X16 @ X15 )
      | ~ ( v1_ordinal1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t21_ordinal1])).

thf('14',plain,
    ( ( ( sk_B = sk_A )
      | ~ ( v1_ordinal1 @ sk_B )
      | ( r2_hidden @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('16',plain,(
    ! [X5: $i] :
      ( ( v1_ordinal1 @ X5 )
      | ~ ( v3_ordinal1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('17',plain,(
    v1_ordinal1 @ sk_B ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( sk_B = sk_A )
      | ( r2_hidden @ sk_B @ sk_A ) )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['14','17','18'])).

thf('20',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['20'])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('22',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X13 = X12 )
      | ( r2_hidden @ X13 @ X12 )
      | ~ ( r2_hidden @ X13 @ ( k1_ordinal1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('23',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ( sk_A = sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('25',plain,
    ( ( ( sk_A = sk_B )
      | ~ ( r2_hidden @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( sk_B = sk_A )
      | ( sk_A = sk_B ) )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,
    ( ( sk_B = sk_A )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('29',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_A )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v3_ordinal1 @ X6 )
      | ~ ( v3_ordinal1 @ X7 )
      | ( r1_ordinal1 @ X6 @ X7 )
      | ( r1_ordinal1 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_A ) ),
    inference(eq_fact,[status(thm)],['32'])).

thf('34',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    r1_ordinal1 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','35'])).

thf('37',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['20'])).

thf('38',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['20'])).

thf('39',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v3_ordinal1 @ X9 )
      | ~ ( v3_ordinal1 @ X10 )
      | ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_ordinal1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('40',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r2_xboole_0 @ X2 @ X4 )
      | ( X2 = X4 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('45',plain,
    ( ( ( sk_A = sk_B )
      | ( r2_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v3_ordinal1 @ X15 )
      | ( r2_hidden @ X16 @ X15 )
      | ~ ( r2_xboole_0 @ X16 @ X15 )
      | ~ ( v1_ordinal1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t21_ordinal1])).

thf('47',plain,
    ( ( ( sk_A = sk_B )
      | ~ ( v1_ordinal1 @ sk_A )
      | ( r2_hidden @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X5: $i] :
      ( ( v1_ordinal1 @ X5 )
      | ~ ( v3_ordinal1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('50',plain,(
    v1_ordinal1 @ sk_A ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( ( sk_A = sk_B )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['47','50','51'])).

thf('53',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ ( k1_ordinal1 @ X14 ) )
      | ~ ( r2_hidden @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('54',plain,
    ( ( ( sk_A = sk_B )
      | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('56',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('58',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('59',plain,(
    ! [X11: $i] :
      ( r2_hidden @ X11 @ ( k1_ordinal1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('60',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','36','37','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.X3HBAozWF0
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:56:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 134 iterations in 0.063s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.20/0.51  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.20/0.51  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.20/0.51  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(t34_ordinal1, conjecture,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v3_ordinal1 @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( v3_ordinal1 @ B ) =>
% 0.20/0.51           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.20/0.51             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i]:
% 0.20/0.51        ( ( v3_ordinal1 @ A ) =>
% 0.20/0.51          ( ![B:$i]:
% 0.20/0.51            ( ( v3_ordinal1 @ B ) =>
% 0.20/0.51              ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.20/0.51                ( r1_ordinal1 @ A @ B ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t34_ordinal1])).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      ((~ (r1_ordinal1 @ sk_A @ sk_B)
% 0.20/0.51        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.20/0.51       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf(connectedness_r1_ordinal1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.20/0.51       ( ( r1_ordinal1 @ A @ B ) | ( r1_ordinal1 @ B @ A ) ) ))).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X6 : $i, X7 : $i]:
% 0.20/0.51         (~ (v3_ordinal1 @ X6)
% 0.20/0.51          | ~ (v3_ordinal1 @ X7)
% 0.20/0.51          | (r1_ordinal1 @ X6 @ X7)
% 0.20/0.51          | (r1_ordinal1 @ X7 @ X6))),
% 0.20/0.51      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.20/0.51  thf(redefinition_r1_ordinal1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.20/0.51       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X9 : $i, X10 : $i]:
% 0.20/0.51         (~ (v3_ordinal1 @ X9)
% 0.20/0.51          | ~ (v3_ordinal1 @ X10)
% 0.20/0.51          | (r1_tarski @ X9 @ X10)
% 0.20/0.51          | ~ (r1_ordinal1 @ X9 @ X10))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r1_ordinal1 @ X0 @ X1)
% 0.20/0.51          | ~ (v3_ordinal1 @ X0)
% 0.20/0.51          | ~ (v3_ordinal1 @ X1)
% 0.20/0.51          | (r1_tarski @ X1 @ X0)
% 0.20/0.51          | ~ (v3_ordinal1 @ X0)
% 0.20/0.51          | ~ (v3_ordinal1 @ X1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r1_tarski @ X1 @ X0)
% 0.20/0.51          | ~ (v3_ordinal1 @ X1)
% 0.20/0.51          | ~ (v3_ordinal1 @ X0)
% 0.20/0.51          | (r1_ordinal1 @ X0 @ X1))),
% 0.20/0.51      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (((~ (v3_ordinal1 @ sk_A)
% 0.20/0.51         | ~ (v3_ordinal1 @ sk_B)
% 0.20/0.51         | (r1_tarski @ sk_B @ sk_A))) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.51  thf('8', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('9', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (((r1_tarski @ sk_B @ sk_A)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.20/0.51  thf(d8_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.20/0.51       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X2 : $i, X4 : $i]:
% 0.20/0.51         ((r2_xboole_0 @ X2 @ X4) | ((X2) = (X4)) | ~ (r1_tarski @ X2 @ X4))),
% 0.20/0.51      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (((((sk_B) = (sk_A)) | (r2_xboole_0 @ sk_B @ sk_A)))
% 0.20/0.51         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.51  thf(t21_ordinal1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v1_ordinal1 @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( v3_ordinal1 @ B ) =>
% 0.20/0.51           ( ( r2_xboole_0 @ A @ B ) => ( r2_hidden @ A @ B ) ) ) ) ))).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X15 : $i, X16 : $i]:
% 0.20/0.51         (~ (v3_ordinal1 @ X15)
% 0.20/0.51          | (r2_hidden @ X16 @ X15)
% 0.20/0.51          | ~ (r2_xboole_0 @ X16 @ X15)
% 0.20/0.51          | ~ (v1_ordinal1 @ X16))),
% 0.20/0.51      inference('cnf', [status(esa)], [t21_ordinal1])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (((((sk_B) = (sk_A))
% 0.20/0.51         | ~ (v1_ordinal1 @ sk_B)
% 0.20/0.51         | (r2_hidden @ sk_B @ sk_A)
% 0.20/0.51         | ~ (v3_ordinal1 @ sk_A))) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.51  thf('15', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(cc1_ordinal1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 0.20/0.51  thf('16', plain, (![X5 : $i]: ((v1_ordinal1 @ X5) | ~ (v3_ordinal1 @ X5))),
% 0.20/0.51      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.20/0.51  thf('17', plain, ((v1_ordinal1 @ sk_B)),
% 0.20/0.51      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.51  thf('18', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (((((sk_B) = (sk_A)) | (r2_hidden @ sk_B @ sk_A)))
% 0.20/0.51         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['14', '17', '18'])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (((r1_ordinal1 @ sk_A @ sk_B) | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.20/0.51         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.51      inference('split', [status(esa)], ['20'])).
% 0.20/0.51  thf(t13_ordinal1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.20/0.51       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i]:
% 0.20/0.51         (((X13) = (X12))
% 0.20/0.51          | (r2_hidden @ X13 @ X12)
% 0.20/0.51          | ~ (r2_hidden @ X13 @ (k1_ordinal1 @ X12)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      ((((r2_hidden @ sk_A @ sk_B) | ((sk_A) = (sk_B))))
% 0.20/0.51         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.51  thf(antisymmetry_r2_hidden, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.51      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (((((sk_A) = (sk_B)) | ~ (r2_hidden @ sk_B @ sk_A)))
% 0.20/0.51         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      (((((sk_B) = (sk_A)) | ((sk_A) = (sk_B))))
% 0.20/0.51         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 0.20/0.51             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['19', '25'])).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      ((((sk_B) = (sk_A)))
% 0.20/0.51         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 0.20/0.51             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.51      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      ((~ (r1_ordinal1 @ sk_A @ sk_A))
% 0.20/0.51         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 0.20/0.51             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.51  thf('30', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      (![X6 : $i, X7 : $i]:
% 0.20/0.51         (~ (v3_ordinal1 @ X6)
% 0.20/0.51          | ~ (v3_ordinal1 @ X7)
% 0.20/0.51          | (r1_ordinal1 @ X6 @ X7)
% 0.20/0.51          | (r1_ordinal1 @ X7 @ X6))),
% 0.20/0.51      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r1_ordinal1 @ X0 @ sk_A)
% 0.20/0.51          | (r1_ordinal1 @ sk_A @ X0)
% 0.20/0.51          | ~ (v3_ordinal1 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.51  thf('33', plain, ((~ (v3_ordinal1 @ sk_A) | (r1_ordinal1 @ sk_A @ sk_A))),
% 0.20/0.51      inference('eq_fact', [status(thm)], ['32'])).
% 0.20/0.51  thf('34', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('35', plain, ((r1_ordinal1 @ sk_A @ sk_A)),
% 0.20/0.51      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.20/0.51       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['29', '35'])).
% 0.20/0.51  thf('37', plain,
% 0.20/0.51      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.20/0.51       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.20/0.51      inference('split', [status(esa)], ['20'])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      (((r1_ordinal1 @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('split', [status(esa)], ['20'])).
% 0.20/0.51  thf('39', plain,
% 0.20/0.51      (![X9 : $i, X10 : $i]:
% 0.20/0.51         (~ (v3_ordinal1 @ X9)
% 0.20/0.51          | ~ (v3_ordinal1 @ X10)
% 0.20/0.51          | (r1_tarski @ X9 @ X10)
% 0.20/0.51          | ~ (r1_ordinal1 @ X9 @ X10))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      ((((r1_tarski @ sk_A @ sk_B)
% 0.20/0.51         | ~ (v3_ordinal1 @ sk_B)
% 0.20/0.51         | ~ (v3_ordinal1 @ sk_A))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.51  thf('41', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('42', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('43', plain,
% 0.20/0.51      (((r1_tarski @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.20/0.51  thf('44', plain,
% 0.20/0.51      (![X2 : $i, X4 : $i]:
% 0.20/0.51         ((r2_xboole_0 @ X2 @ X4) | ((X2) = (X4)) | ~ (r1_tarski @ X2 @ X4))),
% 0.20/0.51      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.20/0.51  thf('45', plain,
% 0.20/0.51      (((((sk_A) = (sk_B)) | (r2_xboole_0 @ sk_A @ sk_B)))
% 0.20/0.51         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.51  thf('46', plain,
% 0.20/0.51      (![X15 : $i, X16 : $i]:
% 0.20/0.51         (~ (v3_ordinal1 @ X15)
% 0.20/0.51          | (r2_hidden @ X16 @ X15)
% 0.20/0.51          | ~ (r2_xboole_0 @ X16 @ X15)
% 0.20/0.51          | ~ (v1_ordinal1 @ X16))),
% 0.20/0.51      inference('cnf', [status(esa)], [t21_ordinal1])).
% 0.20/0.51  thf('47', plain,
% 0.20/0.51      (((((sk_A) = (sk_B))
% 0.20/0.51         | ~ (v1_ordinal1 @ sk_A)
% 0.20/0.51         | (r2_hidden @ sk_A @ sk_B)
% 0.20/0.51         | ~ (v3_ordinal1 @ sk_B))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.51  thf('48', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('49', plain, (![X5 : $i]: ((v1_ordinal1 @ X5) | ~ (v3_ordinal1 @ X5))),
% 0.20/0.51      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.20/0.51  thf('50', plain, ((v1_ordinal1 @ sk_A)),
% 0.20/0.51      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.51  thf('51', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('52', plain,
% 0.20/0.51      (((((sk_A) = (sk_B)) | (r2_hidden @ sk_A @ sk_B)))
% 0.20/0.51         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['47', '50', '51'])).
% 0.20/0.51  thf('53', plain,
% 0.20/0.51      (![X13 : $i, X14 : $i]:
% 0.20/0.51         ((r2_hidden @ X13 @ (k1_ordinal1 @ X14)) | ~ (r2_hidden @ X13 @ X14))),
% 0.20/0.51      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.20/0.51  thf('54', plain,
% 0.20/0.51      (((((sk_A) = (sk_B)) | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))
% 0.20/0.51         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.51  thf('55', plain,
% 0.20/0.51      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.20/0.51         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('56', plain,
% 0.20/0.51      ((((sk_A) = (sk_B)))
% 0.20/0.51         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.20/0.51             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.51  thf('57', plain,
% 0.20/0.51      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.20/0.51         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('58', plain,
% 0.20/0.51      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 0.20/0.51         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.20/0.51             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['56', '57'])).
% 0.20/0.51  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.20/0.51  thf('59', plain, (![X11 : $i]: (r2_hidden @ X11 @ (k1_ordinal1 @ X11))),
% 0.20/0.51      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.20/0.51  thf('60', plain,
% 0.20/0.51      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.20/0.51       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['58', '59'])).
% 0.20/0.51  thf('61', plain, ($false),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['1', '36', '37', '60'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

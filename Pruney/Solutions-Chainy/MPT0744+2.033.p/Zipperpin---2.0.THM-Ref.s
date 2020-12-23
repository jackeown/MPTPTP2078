%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.l340ZY0HeS

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 112 expanded)
%              Number of leaves         :   18 (  37 expanded)
%              Depth                    :   13
%              Number of atoms          :  457 ( 869 expanded)
%              Number of equality atoms :   13 (  15 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

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
    ! [X10: $i,X11: $i] :
      ( ~ ( v3_ordinal1 @ X10 )
      | ~ ( v3_ordinal1 @ X11 )
      | ( r1_ordinal1 @ X10 @ X11 )
      | ( r1_ordinal1 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v3_ordinal1 @ X13 )
      | ~ ( v3_ordinal1 @ X14 )
      | ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_ordinal1 @ X13 @ X14 ) ) ),
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

thf('11',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['11'])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('13',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X16 = X15 )
      | ( r2_hidden @ X16 @ X15 )
      | ~ ( r2_hidden @ X16 @ ( k1_ordinal1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('14',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ( sk_A = sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('15',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( r1_tarski @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('16',plain,
    ( ( ( sk_A = sk_B )
      | ~ ( r1_tarski @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf('18',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('19',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_A )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v3_ordinal1 @ X10 )
      | ~ ( v3_ordinal1 @ X11 )
      | ( r1_ordinal1 @ X10 @ X11 )
      | ( r1_ordinal1 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r1_ordinal1 @ sk_A @ sk_A ) ),
    inference(eq_fact,[status(thm)],['22'])).

thf('24',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    r1_ordinal1 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','25'])).

thf('27',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['11'])).

thf('28',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['11'])).

thf('29',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v3_ordinal1 @ X13 )
      | ~ ( v3_ordinal1 @ X14 )
      | ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_ordinal1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('30',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('34',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r2_xboole_0 @ X6 @ X8 )
      | ( X6 = X8 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('35',plain,
    ( ( ( sk_A = sk_B )
      | ( r2_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t21_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_xboole_0 @ A @ B )
           => ( r2_hidden @ A @ B ) ) ) ) )).

thf('36',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v3_ordinal1 @ X18 )
      | ( r2_hidden @ X19 @ X18 )
      | ~ ( r2_xboole_0 @ X19 @ X18 )
      | ~ ( v1_ordinal1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t21_ordinal1])).

thf('37',plain,
    ( ( ( sk_A = sk_B )
      | ~ ( v1_ordinal1 @ sk_A )
      | ( r2_hidden @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('39',plain,(
    ! [X9: $i] :
      ( ( v1_ordinal1 @ X9 )
      | ~ ( v3_ordinal1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('40',plain,(
    v1_ordinal1 @ sk_A ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( ( sk_A = sk_B )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['37','40','41'])).

thf('43',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r2_hidden @ X16 @ ( k1_ordinal1 @ X17 ) )
      | ~ ( r2_hidden @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('44',plain,
    ( ( ( sk_A = sk_B )
      | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('46',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('48',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r2_hidden @ X16 @ ( k1_ordinal1 @ X17 ) )
      | ( X16 != X17 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('50',plain,(
    ! [X17: $i] :
      ( r2_hidden @ X17 @ ( k1_ordinal1 @ X17 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['48','50'])).

thf('52',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','26','27','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.l340ZY0HeS
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:22:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 234 iterations in 0.098s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.55  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 0.20/0.55  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.20/0.55  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 0.20/0.55  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.55  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.20/0.55  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.20/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.55  thf(t34_ordinal1, conjecture,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( v3_ordinal1 @ A ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( v3_ordinal1 @ B ) =>
% 0.20/0.55           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.20/0.55             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i]:
% 0.20/0.55        ( ( v3_ordinal1 @ A ) =>
% 0.20/0.55          ( ![B:$i]:
% 0.20/0.55            ( ( v3_ordinal1 @ B ) =>
% 0.20/0.55              ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.20/0.55                ( r1_ordinal1 @ A @ B ) ) ) ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t34_ordinal1])).
% 0.20/0.55  thf('0', plain,
% 0.20/0.55      ((~ (r1_ordinal1 @ sk_A @ sk_B)
% 0.20/0.55        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('1', plain,
% 0.20/0.55      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.20/0.55       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.20/0.55      inference('split', [status(esa)], ['0'])).
% 0.20/0.55  thf(connectedness_r1_ordinal1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.20/0.55       ( ( r1_ordinal1 @ A @ B ) | ( r1_ordinal1 @ B @ A ) ) ))).
% 0.20/0.55  thf('2', plain,
% 0.20/0.55      (![X10 : $i, X11 : $i]:
% 0.20/0.55         (~ (v3_ordinal1 @ X10)
% 0.20/0.55          | ~ (v3_ordinal1 @ X11)
% 0.20/0.55          | (r1_ordinal1 @ X10 @ X11)
% 0.20/0.55          | (r1_ordinal1 @ X11 @ X10))),
% 0.20/0.55      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.20/0.55  thf(redefinition_r1_ordinal1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.20/0.55       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.20/0.55  thf('3', plain,
% 0.20/0.55      (![X13 : $i, X14 : $i]:
% 0.20/0.55         (~ (v3_ordinal1 @ X13)
% 0.20/0.55          | ~ (v3_ordinal1 @ X14)
% 0.20/0.55          | (r1_tarski @ X13 @ X14)
% 0.20/0.55          | ~ (r1_ordinal1 @ X13 @ X14))),
% 0.20/0.55      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.20/0.55  thf('4', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((r1_ordinal1 @ X0 @ X1)
% 0.20/0.55          | ~ (v3_ordinal1 @ X0)
% 0.20/0.55          | ~ (v3_ordinal1 @ X1)
% 0.20/0.55          | (r1_tarski @ X1 @ X0)
% 0.20/0.55          | ~ (v3_ordinal1 @ X0)
% 0.20/0.55          | ~ (v3_ordinal1 @ X1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.55  thf('5', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((r1_tarski @ X1 @ X0)
% 0.20/0.55          | ~ (v3_ordinal1 @ X1)
% 0.20/0.55          | ~ (v3_ordinal1 @ X0)
% 0.20/0.55          | (r1_ordinal1 @ X0 @ X1))),
% 0.20/0.55      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.55  thf('6', plain,
% 0.20/0.55      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.55      inference('split', [status(esa)], ['0'])).
% 0.20/0.55  thf('7', plain,
% 0.20/0.55      (((~ (v3_ordinal1 @ sk_A)
% 0.20/0.55         | ~ (v3_ordinal1 @ sk_B)
% 0.20/0.55         | (r1_tarski @ sk_B @ sk_A))) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.55  thf('8', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('9', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('10', plain,
% 0.20/0.55      (((r1_tarski @ sk_B @ sk_A)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.55      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.20/0.55  thf('11', plain,
% 0.20/0.55      (((r1_ordinal1 @ sk_A @ sk_B) | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('12', plain,
% 0.20/0.55      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.20/0.55         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.55      inference('split', [status(esa)], ['11'])).
% 0.20/0.55  thf(t13_ordinal1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.20/0.55       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.20/0.55  thf('13', plain,
% 0.20/0.55      (![X15 : $i, X16 : $i]:
% 0.20/0.55         (((X16) = (X15))
% 0.20/0.55          | (r2_hidden @ X16 @ X15)
% 0.20/0.55          | ~ (r2_hidden @ X16 @ (k1_ordinal1 @ X15)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.20/0.55  thf('14', plain,
% 0.20/0.55      ((((r2_hidden @ sk_A @ sk_B) | ((sk_A) = (sk_B))))
% 0.20/0.55         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.55  thf(t7_ordinal1, axiom,
% 0.20/0.55    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.55  thf('15', plain,
% 0.20/0.55      (![X20 : $i, X21 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X20 @ X21) | ~ (r1_tarski @ X21 @ X20))),
% 0.20/0.55      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.20/0.55  thf('16', plain,
% 0.20/0.55      (((((sk_A) = (sk_B)) | ~ (r1_tarski @ sk_B @ sk_A)))
% 0.20/0.55         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.55  thf('17', plain,
% 0.20/0.55      ((((sk_A) = (sk_B)))
% 0.20/0.55         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 0.20/0.55             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['10', '16'])).
% 0.20/0.55  thf('18', plain,
% 0.20/0.55      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.55      inference('split', [status(esa)], ['0'])).
% 0.20/0.55  thf('19', plain,
% 0.20/0.55      ((~ (r1_ordinal1 @ sk_A @ sk_A))
% 0.20/0.55         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 0.20/0.55             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.55  thf('20', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('21', plain,
% 0.20/0.55      (![X10 : $i, X11 : $i]:
% 0.20/0.55         (~ (v3_ordinal1 @ X10)
% 0.20/0.55          | ~ (v3_ordinal1 @ X11)
% 0.20/0.55          | (r1_ordinal1 @ X10 @ X11)
% 0.20/0.55          | (r1_ordinal1 @ X11 @ X10))),
% 0.20/0.55      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.20/0.55  thf('22', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((r1_ordinal1 @ X0 @ sk_A)
% 0.20/0.55          | (r1_ordinal1 @ sk_A @ X0)
% 0.20/0.55          | ~ (v3_ordinal1 @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.55  thf('23', plain, ((~ (v3_ordinal1 @ sk_A) | (r1_ordinal1 @ sk_A @ sk_A))),
% 0.20/0.55      inference('eq_fact', [status(thm)], ['22'])).
% 0.20/0.55  thf('24', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('25', plain, ((r1_ordinal1 @ sk_A @ sk_A)),
% 0.20/0.55      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.55  thf('26', plain,
% 0.20/0.55      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.20/0.55       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.20/0.55      inference('demod', [status(thm)], ['19', '25'])).
% 0.20/0.55  thf('27', plain,
% 0.20/0.55      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.20/0.55       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.20/0.55      inference('split', [status(esa)], ['11'])).
% 0.20/0.55  thf('28', plain,
% 0.20/0.55      (((r1_ordinal1 @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.55      inference('split', [status(esa)], ['11'])).
% 0.20/0.55  thf('29', plain,
% 0.20/0.55      (![X13 : $i, X14 : $i]:
% 0.20/0.55         (~ (v3_ordinal1 @ X13)
% 0.20/0.55          | ~ (v3_ordinal1 @ X14)
% 0.20/0.55          | (r1_tarski @ X13 @ X14)
% 0.20/0.55          | ~ (r1_ordinal1 @ X13 @ X14))),
% 0.20/0.55      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.20/0.55  thf('30', plain,
% 0.20/0.55      ((((r1_tarski @ sk_A @ sk_B)
% 0.20/0.55         | ~ (v3_ordinal1 @ sk_B)
% 0.20/0.55         | ~ (v3_ordinal1 @ sk_A))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.55  thf('31', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('32', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('33', plain,
% 0.20/0.55      (((r1_tarski @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.55      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.20/0.55  thf(d8_xboole_0, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.20/0.55       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.20/0.55  thf('34', plain,
% 0.20/0.55      (![X6 : $i, X8 : $i]:
% 0.20/0.55         ((r2_xboole_0 @ X6 @ X8) | ((X6) = (X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.20/0.55      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.20/0.55  thf('35', plain,
% 0.20/0.55      (((((sk_A) = (sk_B)) | (r2_xboole_0 @ sk_A @ sk_B)))
% 0.20/0.55         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.55  thf(t21_ordinal1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( v1_ordinal1 @ A ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( v3_ordinal1 @ B ) =>
% 0.20/0.55           ( ( r2_xboole_0 @ A @ B ) => ( r2_hidden @ A @ B ) ) ) ) ))).
% 0.20/0.55  thf('36', plain,
% 0.20/0.55      (![X18 : $i, X19 : $i]:
% 0.20/0.55         (~ (v3_ordinal1 @ X18)
% 0.20/0.55          | (r2_hidden @ X19 @ X18)
% 0.20/0.55          | ~ (r2_xboole_0 @ X19 @ X18)
% 0.20/0.55          | ~ (v1_ordinal1 @ X19))),
% 0.20/0.55      inference('cnf', [status(esa)], [t21_ordinal1])).
% 0.20/0.55  thf('37', plain,
% 0.20/0.55      (((((sk_A) = (sk_B))
% 0.20/0.55         | ~ (v1_ordinal1 @ sk_A)
% 0.20/0.55         | (r2_hidden @ sk_A @ sk_B)
% 0.20/0.55         | ~ (v3_ordinal1 @ sk_B))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.55  thf('38', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(cc1_ordinal1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 0.20/0.55  thf('39', plain, (![X9 : $i]: ((v1_ordinal1 @ X9) | ~ (v3_ordinal1 @ X9))),
% 0.20/0.55      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.20/0.55  thf('40', plain, ((v1_ordinal1 @ sk_A)),
% 0.20/0.55      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.55  thf('41', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('42', plain,
% 0.20/0.55      (((((sk_A) = (sk_B)) | (r2_hidden @ sk_A @ sk_B)))
% 0.20/0.55         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.55      inference('demod', [status(thm)], ['37', '40', '41'])).
% 0.20/0.55  thf('43', plain,
% 0.20/0.55      (![X16 : $i, X17 : $i]:
% 0.20/0.55         ((r2_hidden @ X16 @ (k1_ordinal1 @ X17)) | ~ (r2_hidden @ X16 @ X17))),
% 0.20/0.55      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.20/0.55  thf('44', plain,
% 0.20/0.55      (((((sk_A) = (sk_B)) | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))
% 0.20/0.55         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.55  thf('45', plain,
% 0.20/0.55      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.20/0.55         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.55      inference('split', [status(esa)], ['0'])).
% 0.20/0.55  thf('46', plain,
% 0.20/0.55      ((((sk_A) = (sk_B)))
% 0.20/0.55         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.20/0.55             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.55  thf('47', plain,
% 0.20/0.55      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.20/0.55         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.55      inference('split', [status(esa)], ['0'])).
% 0.20/0.55  thf('48', plain,
% 0.20/0.55      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 0.20/0.55         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.20/0.55             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.55  thf('49', plain,
% 0.20/0.55      (![X16 : $i, X17 : $i]:
% 0.20/0.55         ((r2_hidden @ X16 @ (k1_ordinal1 @ X17)) | ((X16) != (X17)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.20/0.55  thf('50', plain, (![X17 : $i]: (r2_hidden @ X17 @ (k1_ordinal1 @ X17))),
% 0.20/0.55      inference('simplify', [status(thm)], ['49'])).
% 0.20/0.55  thf('51', plain,
% 0.20/0.55      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.20/0.55       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.20/0.55      inference('demod', [status(thm)], ['48', '50'])).
% 0.20/0.55  thf('52', plain, ($false),
% 0.20/0.55      inference('sat_resolution*', [status(thm)], ['1', '26', '27', '51'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.40/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

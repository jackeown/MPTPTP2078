%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eSq2Feg5Pq

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 111 expanded)
%              Number of leaves         :   19 (  37 expanded)
%              Depth                    :   13
%              Number of atoms          :  454 ( 856 expanded)
%              Number of equality atoms :   12 (  13 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

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
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf(connectedness_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
        | ( r1_ordinal1 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v3_ordinal1 @ X4 )
      | ~ ( v3_ordinal1 @ X5 )
      | ( r1_ordinal1 @ X4 @ X5 )
      | ( r1_ordinal1 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v3_ordinal1 @ X7 )
      | ~ ( v3_ordinal1 @ X8 )
      | ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_ordinal1 @ X7 @ X8 ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ( X11 = X10 )
      | ( r2_hidden @ X11 @ X10 )
      | ~ ( r2_hidden @ X11 @ ( k1_ordinal1 @ X10 ) ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ~ ( v3_ordinal1 @ X4 )
      | ~ ( v3_ordinal1 @ X5 )
      | ( r1_ordinal1 @ X4 @ X5 )
      | ( r1_ordinal1 @ X5 @ X4 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ~ ( v3_ordinal1 @ X7 )
      | ~ ( v3_ordinal1 @ X8 )
      | ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_ordinal1 @ X7 @ X8 ) ) ),
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
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ~ ( v3_ordinal1 @ X13 )
      | ( r2_hidden @ X14 @ X13 )
      | ~ ( r2_xboole_0 @ X14 @ X13 )
      | ~ ( v1_ordinal1 @ X14 ) ) ),
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
    ! [X3: $i] :
      ( ( v1_ordinal1 @ X3 )
      | ~ ( v3_ordinal1 @ X3 ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ ( k1_ordinal1 @ X12 ) )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
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

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('49',plain,(
    ! [X9: $i] :
      ( r2_hidden @ X9 @ ( k1_ordinal1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('50',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','26','27','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eSq2Feg5Pq
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:52:24 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 119 iterations in 0.039s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 0.21/0.48  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 0.21/0.48  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.21/0.48  thf(t34_ordinal1, conjecture,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v3_ordinal1 @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( v3_ordinal1 @ B ) =>
% 0.21/0.48           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.21/0.48             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]:
% 0.21/0.48        ( ( v3_ordinal1 @ A ) =>
% 0.21/0.48          ( ![B:$i]:
% 0.21/0.48            ( ( v3_ordinal1 @ B ) =>
% 0.21/0.48              ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.21/0.48                ( r1_ordinal1 @ A @ B ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t34_ordinal1])).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      ((~ (r1_ordinal1 @ sk_A @ sk_B)
% 0.21/0.48        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.21/0.48       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf(connectedness_r1_ordinal1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.21/0.48       ( ( r1_ordinal1 @ A @ B ) | ( r1_ordinal1 @ B @ A ) ) ))).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X4 : $i, X5 : $i]:
% 0.21/0.48         (~ (v3_ordinal1 @ X4)
% 0.21/0.48          | ~ (v3_ordinal1 @ X5)
% 0.21/0.48          | (r1_ordinal1 @ X4 @ X5)
% 0.21/0.48          | (r1_ordinal1 @ X5 @ X4))),
% 0.21/0.48      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.21/0.48  thf(redefinition_r1_ordinal1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.21/0.48       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i]:
% 0.21/0.48         (~ (v3_ordinal1 @ X7)
% 0.21/0.48          | ~ (v3_ordinal1 @ X8)
% 0.21/0.48          | (r1_tarski @ X7 @ X8)
% 0.21/0.48          | ~ (r1_ordinal1 @ X7 @ X8))),
% 0.21/0.48      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r1_ordinal1 @ X0 @ X1)
% 0.21/0.48          | ~ (v3_ordinal1 @ X0)
% 0.21/0.48          | ~ (v3_ordinal1 @ X1)
% 0.21/0.48          | (r1_tarski @ X1 @ X0)
% 0.21/0.48          | ~ (v3_ordinal1 @ X0)
% 0.21/0.48          | ~ (v3_ordinal1 @ X1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r1_tarski @ X1 @ X0)
% 0.21/0.48          | ~ (v3_ordinal1 @ X1)
% 0.21/0.48          | ~ (v3_ordinal1 @ X0)
% 0.21/0.48          | (r1_ordinal1 @ X0 @ X1))),
% 0.21/0.48      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (((~ (v3_ordinal1 @ sk_A)
% 0.21/0.48         | ~ (v3_ordinal1 @ sk_B)
% 0.21/0.48         | (r1_tarski @ sk_B @ sk_A))) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.48  thf('8', plain, ((v3_ordinal1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('9', plain, ((v3_ordinal1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (((r1_tarski @ sk_B @ sk_A)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (((r1_ordinal1 @ sk_A @ sk_B) | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.21/0.48         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.21/0.48      inference('split', [status(esa)], ['11'])).
% 0.21/0.48  thf(t13_ordinal1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.21/0.48       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (![X10 : $i, X11 : $i]:
% 0.21/0.48         (((X11) = (X10))
% 0.21/0.48          | (r2_hidden @ X11 @ X10)
% 0.21/0.48          | ~ (r2_hidden @ X11 @ (k1_ordinal1 @ X10)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      ((((r2_hidden @ sk_A @ sk_B) | ((sk_A) = (sk_B))))
% 0.21/0.48         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.48  thf(t7_ordinal1, axiom,
% 0.21/0.48    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (![X15 : $i, X16 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X15 @ X16) | ~ (r1_tarski @ X16 @ X15))),
% 0.21/0.48      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      (((((sk_A) = (sk_B)) | ~ (r1_tarski @ sk_B @ sk_A)))
% 0.21/0.48         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      ((((sk_A) = (sk_B)))
% 0.21/0.48         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 0.21/0.48             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['10', '16'])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      ((~ (r1_ordinal1 @ sk_A @ sk_A))
% 0.21/0.48         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 0.21/0.48             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.48  thf('20', plain, ((v3_ordinal1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (![X4 : $i, X5 : $i]:
% 0.21/0.48         (~ (v3_ordinal1 @ X4)
% 0.21/0.48          | ~ (v3_ordinal1 @ X5)
% 0.21/0.48          | (r1_ordinal1 @ X4 @ X5)
% 0.21/0.48          | (r1_ordinal1 @ X5 @ X4))),
% 0.21/0.48      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r1_ordinal1 @ X0 @ sk_A)
% 0.21/0.48          | (r1_ordinal1 @ sk_A @ X0)
% 0.21/0.48          | ~ (v3_ordinal1 @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.48  thf('23', plain, ((~ (v3_ordinal1 @ sk_A) | (r1_ordinal1 @ sk_A @ sk_A))),
% 0.21/0.48      inference('eq_fact', [status(thm)], ['22'])).
% 0.21/0.48  thf('24', plain, ((v3_ordinal1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('25', plain, ((r1_ordinal1 @ sk_A @ sk_A)),
% 0.21/0.48      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.21/0.48       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.21/0.48      inference('demod', [status(thm)], ['19', '25'])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.21/0.48       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.21/0.48      inference('split', [status(esa)], ['11'])).
% 0.21/0.48  thf('28', plain,
% 0.21/0.48      (((r1_ordinal1 @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('split', [status(esa)], ['11'])).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i]:
% 0.21/0.48         (~ (v3_ordinal1 @ X7)
% 0.21/0.48          | ~ (v3_ordinal1 @ X8)
% 0.21/0.48          | (r1_tarski @ X7 @ X8)
% 0.21/0.48          | ~ (r1_ordinal1 @ X7 @ X8))),
% 0.21/0.48      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.21/0.48  thf('30', plain,
% 0.21/0.48      ((((r1_tarski @ sk_A @ sk_B)
% 0.21/0.48         | ~ (v3_ordinal1 @ sk_B)
% 0.21/0.48         | ~ (v3_ordinal1 @ sk_A))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.48  thf('31', plain, ((v3_ordinal1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('32', plain, ((v3_ordinal1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('33', plain,
% 0.21/0.48      (((r1_tarski @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.21/0.48  thf(d8_xboole_0, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.21/0.48       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.21/0.48  thf('34', plain,
% 0.21/0.48      (![X0 : $i, X2 : $i]:
% 0.21/0.48         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.48      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.21/0.48  thf('35', plain,
% 0.21/0.48      (((((sk_A) = (sk_B)) | (r2_xboole_0 @ sk_A @ sk_B)))
% 0.21/0.48         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.48  thf(t21_ordinal1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_ordinal1 @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( v3_ordinal1 @ B ) =>
% 0.21/0.48           ( ( r2_xboole_0 @ A @ B ) => ( r2_hidden @ A @ B ) ) ) ) ))).
% 0.21/0.48  thf('36', plain,
% 0.21/0.48      (![X13 : $i, X14 : $i]:
% 0.21/0.48         (~ (v3_ordinal1 @ X13)
% 0.21/0.48          | (r2_hidden @ X14 @ X13)
% 0.21/0.48          | ~ (r2_xboole_0 @ X14 @ X13)
% 0.21/0.48          | ~ (v1_ordinal1 @ X14))),
% 0.21/0.48      inference('cnf', [status(esa)], [t21_ordinal1])).
% 0.21/0.48  thf('37', plain,
% 0.21/0.48      (((((sk_A) = (sk_B))
% 0.21/0.48         | ~ (v1_ordinal1 @ sk_A)
% 0.21/0.48         | (r2_hidden @ sk_A @ sk_B)
% 0.21/0.48         | ~ (v3_ordinal1 @ sk_B))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.48  thf('38', plain, ((v3_ordinal1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(cc1_ordinal1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 0.21/0.48  thf('39', plain, (![X3 : $i]: ((v1_ordinal1 @ X3) | ~ (v3_ordinal1 @ X3))),
% 0.21/0.48      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.21/0.48  thf('40', plain, ((v1_ordinal1 @ sk_A)),
% 0.21/0.48      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.48  thf('41', plain, ((v3_ordinal1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('42', plain,
% 0.21/0.48      (((((sk_A) = (sk_B)) | (r2_hidden @ sk_A @ sk_B)))
% 0.21/0.48         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('demod', [status(thm)], ['37', '40', '41'])).
% 0.21/0.48  thf('43', plain,
% 0.21/0.48      (![X11 : $i, X12 : $i]:
% 0.21/0.48         ((r2_hidden @ X11 @ (k1_ordinal1 @ X12)) | ~ (r2_hidden @ X11 @ X12))),
% 0.21/0.48      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.21/0.48  thf('44', plain,
% 0.21/0.48      (((((sk_A) = (sk_B)) | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))
% 0.21/0.48         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.48  thf('45', plain,
% 0.21/0.48      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.21/0.48         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('46', plain,
% 0.21/0.48      ((((sk_A) = (sk_B)))
% 0.21/0.48         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.21/0.48             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.48  thf('47', plain,
% 0.21/0.48      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.21/0.48         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('48', plain,
% 0.21/0.48      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 0.21/0.48         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.21/0.48             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.48  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.21/0.48  thf('49', plain, (![X9 : $i]: (r2_hidden @ X9 @ (k1_ordinal1 @ X9))),
% 0.21/0.48      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.21/0.48  thf('50', plain,
% 0.21/0.48      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.21/0.48       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.21/0.48      inference('demod', [status(thm)], ['48', '49'])).
% 0.21/0.48  thf('51', plain, ($false),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['1', '26', '27', '50'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

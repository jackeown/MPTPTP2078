%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MWdroIxKX3

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:07 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 115 expanded)
%              Number of leaves         :   15 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :  471 ( 927 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X3: $i,X4: $i] :
      ( ~ ( v3_ordinal1 @ X3 )
      | ~ ( v3_ordinal1 @ X4 )
      | ( r1_ordinal1 @ X3 @ X4 )
      | ( r1_ordinal1 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[connectedness_r1_ordinal1])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v3_ordinal1 @ X6 )
      | ~ ( v3_ordinal1 @ X7 )
      | ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_ordinal1 @ X6 @ X7 ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ( X10 = X9 )
      | ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ ( k1_ordinal1 @ X9 ) ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ~ ( v3_ordinal1 @ X3 )
      | ~ ( v3_ordinal1 @ X4 )
      | ( r1_ordinal1 @ X3 @ X4 )
      | ( r1_ordinal1 @ X4 @ X3 ) ) ),
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

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('28',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v3_ordinal1 @ X12 )
      | ( r1_ordinal1 @ X13 @ X12 )
      | ( r2_hidden @ X12 @ X13 )
      | ~ ( v3_ordinal1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('29',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ ( k1_ordinal1 @ X11 ) )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_ordinal1 @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v3_ordinal1 @ X6 )
      | ~ ( v3_ordinal1 @ X7 )
      | ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_ordinal1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('37',plain,
    ( ( ( r1_tarski @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['11'])).

thf('42',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v3_ordinal1 @ X6 )
      | ~ ( v3_ordinal1 @ X7 )
      | ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_ordinal1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('43',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('47',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('48',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_A )
      | ( sk_B = sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_B = sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','48'])).

thf('50',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('51',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('52',plain,(
    ! [X8: $i] :
      ( r2_hidden @ X8 @ ( k1_ordinal1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('53',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','26','27','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MWdroIxKX3
% 0.14/0.33  % Computer   : n015.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 18:02:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 118 iterations in 0.060s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.20/0.51  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
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
% 0.20/0.51      (![X3 : $i, X4 : $i]:
% 0.20/0.51         (~ (v3_ordinal1 @ X3)
% 0.20/0.51          | ~ (v3_ordinal1 @ X4)
% 0.20/0.51          | (r1_ordinal1 @ X3 @ X4)
% 0.20/0.51          | (r1_ordinal1 @ X4 @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.20/0.51  thf(redefinition_r1_ordinal1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.20/0.51       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X6 : $i, X7 : $i]:
% 0.20/0.51         (~ (v3_ordinal1 @ X6)
% 0.20/0.51          | ~ (v3_ordinal1 @ X7)
% 0.20/0.51          | (r1_tarski @ X6 @ X7)
% 0.20/0.51          | ~ (r1_ordinal1 @ X6 @ X7))),
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
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (((r1_ordinal1 @ sk_A @ sk_B) | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.20/0.51         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.51      inference('split', [status(esa)], ['11'])).
% 0.20/0.51  thf(t13_ordinal1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.20/0.51       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X9 : $i, X10 : $i]:
% 0.20/0.51         (((X10) = (X9))
% 0.20/0.51          | (r2_hidden @ X10 @ X9)
% 0.20/0.51          | ~ (r2_hidden @ X10 @ (k1_ordinal1 @ X9)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      ((((r2_hidden @ sk_A @ sk_B) | ((sk_A) = (sk_B))))
% 0.20/0.51         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.51  thf(t7_ordinal1, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (![X14 : $i, X15 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X14 @ X15) | ~ (r1_tarski @ X15 @ X14))),
% 0.20/0.51      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (((((sk_A) = (sk_B)) | ~ (r1_tarski @ sk_B @ sk_A)))
% 0.20/0.51         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      ((((sk_A) = (sk_B)))
% 0.20/0.51         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 0.20/0.51             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['10', '16'])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      ((~ (r1_ordinal1 @ sk_A @ sk_A))
% 0.20/0.51         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 0.20/0.51             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.51  thf('20', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      (![X3 : $i, X4 : $i]:
% 0.20/0.51         (~ (v3_ordinal1 @ X3)
% 0.20/0.51          | ~ (v3_ordinal1 @ X4)
% 0.20/0.51          | (r1_ordinal1 @ X3 @ X4)
% 0.20/0.51          | (r1_ordinal1 @ X4 @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [connectedness_r1_ordinal1])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r1_ordinal1 @ X0 @ sk_A)
% 0.20/0.51          | (r1_ordinal1 @ sk_A @ X0)
% 0.20/0.51          | ~ (v3_ordinal1 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.51  thf('23', plain, ((~ (v3_ordinal1 @ sk_A) | (r1_ordinal1 @ sk_A @ sk_A))),
% 0.20/0.51      inference('eq_fact', [status(thm)], ['22'])).
% 0.20/0.51  thf('24', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('25', plain, ((r1_ordinal1 @ sk_A @ sk_A)),
% 0.20/0.51      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.20/0.51       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['19', '25'])).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.20/0.51       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.20/0.51      inference('split', [status(esa)], ['11'])).
% 0.20/0.51  thf(t26_ordinal1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v3_ordinal1 @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( v3_ordinal1 @ B ) =>
% 0.20/0.51           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i]:
% 0.20/0.51         (~ (v3_ordinal1 @ X12)
% 0.20/0.51          | (r1_ordinal1 @ X13 @ X12)
% 0.20/0.51          | (r2_hidden @ X12 @ X13)
% 0.20/0.51          | ~ (v3_ordinal1 @ X13))),
% 0.20/0.51      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      (![X10 : $i, X11 : $i]:
% 0.20/0.51         ((r2_hidden @ X10 @ (k1_ordinal1 @ X11)) | ~ (r2_hidden @ X10 @ X11))),
% 0.20/0.51      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (v3_ordinal1 @ X0)
% 0.20/0.51          | (r1_ordinal1 @ X0 @ X1)
% 0.20/0.51          | ~ (v3_ordinal1 @ X1)
% 0.20/0.51          | (r2_hidden @ X1 @ (k1_ordinal1 @ X0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.20/0.51         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      (((~ (v3_ordinal1 @ sk_A)
% 0.20/0.51         | (r1_ordinal1 @ sk_B @ sk_A)
% 0.20/0.51         | ~ (v3_ordinal1 @ sk_B)))
% 0.20/0.51         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.51  thf('33', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('34', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      (((r1_ordinal1 @ sk_B @ sk_A))
% 0.20/0.51         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.51      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      (![X6 : $i, X7 : $i]:
% 0.20/0.51         (~ (v3_ordinal1 @ X6)
% 0.20/0.51          | ~ (v3_ordinal1 @ X7)
% 0.20/0.51          | (r1_tarski @ X6 @ X7)
% 0.20/0.51          | ~ (r1_ordinal1 @ X6 @ X7))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.20/0.51  thf('37', plain,
% 0.20/0.51      ((((r1_tarski @ sk_B @ sk_A)
% 0.20/0.51         | ~ (v3_ordinal1 @ sk_A)
% 0.20/0.51         | ~ (v3_ordinal1 @ sk_B)))
% 0.20/0.51         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.51  thf('38', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('39', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      (((r1_tarski @ sk_B @ sk_A))
% 0.20/0.51         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.51      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.20/0.51  thf('41', plain,
% 0.20/0.51      (((r1_ordinal1 @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('split', [status(esa)], ['11'])).
% 0.20/0.51  thf('42', plain,
% 0.20/0.51      (![X6 : $i, X7 : $i]:
% 0.20/0.51         (~ (v3_ordinal1 @ X6)
% 0.20/0.51          | ~ (v3_ordinal1 @ X7)
% 0.20/0.51          | (r1_tarski @ X6 @ X7)
% 0.20/0.51          | ~ (r1_ordinal1 @ X6 @ X7))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.20/0.51  thf('43', plain,
% 0.20/0.51      ((((r1_tarski @ sk_A @ sk_B)
% 0.20/0.51         | ~ (v3_ordinal1 @ sk_B)
% 0.20/0.51         | ~ (v3_ordinal1 @ sk_A))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.51  thf('44', plain, ((v3_ordinal1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('45', plain, ((v3_ordinal1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('46', plain,
% 0.20/0.51      (((r1_tarski @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.20/0.51  thf(d10_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.51  thf('47', plain,
% 0.20/0.51      (![X0 : $i, X2 : $i]:
% 0.20/0.51         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.51  thf('48', plain,
% 0.20/0.51      (((~ (r1_tarski @ sk_B @ sk_A) | ((sk_B) = (sk_A))))
% 0.20/0.51         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.51  thf('49', plain,
% 0.20/0.51      ((((sk_B) = (sk_A)))
% 0.20/0.51         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.20/0.51             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['40', '48'])).
% 0.20/0.51  thf('50', plain,
% 0.20/0.51      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.20/0.51         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('51', plain,
% 0.20/0.51      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 0.20/0.51         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.20/0.51             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['49', '50'])).
% 0.20/0.51  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.20/0.51  thf('52', plain, (![X8 : $i]: (r2_hidden @ X8 @ (k1_ordinal1 @ X8))),
% 0.20/0.51      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.20/0.51  thf('53', plain,
% 0.20/0.51      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.20/0.51       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['51', '52'])).
% 0.20/0.51  thf('54', plain, ($false),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['1', '26', '27', '53'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.36/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

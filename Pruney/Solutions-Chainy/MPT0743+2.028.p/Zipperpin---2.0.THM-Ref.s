%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DdNxI3Icqb

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:56 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 178 expanded)
%              Number of leaves         :   18 (  54 expanded)
%              Depth                    :   23
%              Number of atoms          :  460 (1382 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('0',plain,(
    ! [X15: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X15 ) )
      | ~ ( v3_ordinal1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X13 = X12 )
      | ( r2_hidden @ X13 @ X12 )
      | ~ ( r2_hidden @ X13 @ ( k1_ordinal1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_ordinal1 @ X0 ) ) @ X0 )
      | ( ( sk_C @ X1 @ ( k1_ordinal1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

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

thf('4',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['4'])).

thf(d2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
    <=> ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( r1_tarski @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( r1_tarski @ X6 @ X7 )
      | ~ ( v1_ordinal1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('7',plain,
    ( ( ~ ( v1_ordinal1 @ sk_B_1 )
      | ( r1_tarski @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('9',plain,(
    ! [X4: $i] :
      ( ( v1_ordinal1 @ X4 )
      | ~ ( v3_ordinal1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('10',plain,(
    v1_ordinal1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( r1_tarski @ sk_A @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_B_1 )
        | ~ ( r2_hidden @ X0 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 )
    | ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 )
    | ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['14'])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('16',plain,(
    ! [X11: $i] :
      ( r2_hidden @ X11 @ ( k1_ordinal1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('17',plain,(
    ! [X15: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X15 ) )
      | ~ ( v3_ordinal1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('18',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['4'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v3_ordinal1 @ X9 )
      | ~ ( v3_ordinal1 @ X10 )
      | ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_ordinal1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('20',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_B_1 )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('27',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_B_1 )
        | ~ ( r2_hidden @ X0 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['16','27'])).

thf('29',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
   <= ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['14'])).

thf('30',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('32',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['15','30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['13','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ ( k1_ordinal1 @ sk_A ) )
        = sk_A )
      | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_ordinal1 @ sk_A ) ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['3','33'])).

thf('35',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('36',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 )
    | ( ( sk_C @ sk_B_1 @ ( k1_ordinal1 @ sk_A ) )
      = sk_A )
    | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( sk_C @ sk_B_1 @ ( k1_ordinal1 @ sk_A ) )
      = sk_A )
    | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('39',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
    | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 )
    | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('41',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['15','30','31'])).

thf('42',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(simpl_trail,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 )
    | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['39','42'])).

thf('44',plain,(
    r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v3_ordinal1 @ X9 )
      | ~ ( v3_ordinal1 @ X10 )
      | ( r1_ordinal1 @ X9 @ X10 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('46',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 )
    | ~ ( v3_ordinal1 @ sk_B_1 )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['14'])).

thf('50',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['15','30'])).

thf('51',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['48','51'])).

thf('53',plain,(
    ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','52'])).

thf('54',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['53','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DdNxI3Icqb
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:24:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.51/0.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.51/0.69  % Solved by: fo/fo7.sh
% 0.51/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.69  % done 354 iterations in 0.244s
% 0.51/0.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.51/0.69  % SZS output start Refutation
% 0.51/0.69  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.51/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.51/0.69  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.51/0.69  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.51/0.69  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 0.51/0.69  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.51/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.51/0.69  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 0.51/0.69  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.51/0.69  thf(t29_ordinal1, axiom,
% 0.51/0.69    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 0.51/0.69  thf('0', plain,
% 0.51/0.69      (![X15 : $i]:
% 0.51/0.69         ((v3_ordinal1 @ (k1_ordinal1 @ X15)) | ~ (v3_ordinal1 @ X15))),
% 0.51/0.69      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.51/0.69  thf(d3_tarski, axiom,
% 0.51/0.69    (![A:$i,B:$i]:
% 0.51/0.69     ( ( r1_tarski @ A @ B ) <=>
% 0.51/0.69       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.51/0.69  thf('1', plain,
% 0.51/0.69      (![X1 : $i, X3 : $i]:
% 0.51/0.69         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.51/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.51/0.69  thf(t13_ordinal1, axiom,
% 0.51/0.69    (![A:$i,B:$i]:
% 0.51/0.69     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.51/0.69       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.51/0.69  thf('2', plain,
% 0.51/0.69      (![X12 : $i, X13 : $i]:
% 0.51/0.69         (((X13) = (X12))
% 0.51/0.69          | (r2_hidden @ X13 @ X12)
% 0.51/0.69          | ~ (r2_hidden @ X13 @ (k1_ordinal1 @ X12)))),
% 0.51/0.69      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.51/0.69  thf('3', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         ((r1_tarski @ (k1_ordinal1 @ X0) @ X1)
% 0.51/0.69          | (r2_hidden @ (sk_C @ X1 @ (k1_ordinal1 @ X0)) @ X0)
% 0.51/0.69          | ((sk_C @ X1 @ (k1_ordinal1 @ X0)) = (X0)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['1', '2'])).
% 0.51/0.69  thf(t33_ordinal1, conjecture,
% 0.51/0.69    (![A:$i]:
% 0.51/0.69     ( ( v3_ordinal1 @ A ) =>
% 0.51/0.69       ( ![B:$i]:
% 0.51/0.69         ( ( v3_ordinal1 @ B ) =>
% 0.51/0.69           ( ( r2_hidden @ A @ B ) <=>
% 0.51/0.69             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 0.51/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.69    (~( ![A:$i]:
% 0.51/0.69        ( ( v3_ordinal1 @ A ) =>
% 0.51/0.69          ( ![B:$i]:
% 0.51/0.69            ( ( v3_ordinal1 @ B ) =>
% 0.51/0.69              ( ( r2_hidden @ A @ B ) <=>
% 0.51/0.69                ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ) )),
% 0.51/0.69    inference('cnf.neg', [status(esa)], [t33_ordinal1])).
% 0.51/0.69  thf('4', plain,
% 0.51/0.69      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B_1)
% 0.51/0.69        | (r2_hidden @ sk_A @ sk_B_1))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('5', plain,
% 0.51/0.69      (((r2_hidden @ sk_A @ sk_B_1)) <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.51/0.69      inference('split', [status(esa)], ['4'])).
% 0.51/0.69  thf(d2_ordinal1, axiom,
% 0.51/0.69    (![A:$i]:
% 0.51/0.69     ( ( v1_ordinal1 @ A ) <=>
% 0.51/0.69       ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( r1_tarski @ B @ A ) ) ) ))).
% 0.51/0.69  thf('6', plain,
% 0.51/0.69      (![X6 : $i, X7 : $i]:
% 0.51/0.69         (~ (r2_hidden @ X6 @ X7)
% 0.51/0.69          | (r1_tarski @ X6 @ X7)
% 0.51/0.69          | ~ (v1_ordinal1 @ X7))),
% 0.51/0.69      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.51/0.69  thf('7', plain,
% 0.51/0.69      (((~ (v1_ordinal1 @ sk_B_1) | (r1_tarski @ sk_A @ sk_B_1)))
% 0.51/0.69         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['5', '6'])).
% 0.51/0.69  thf('8', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf(cc1_ordinal1, axiom,
% 0.51/0.69    (![A:$i]:
% 0.51/0.69     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 0.51/0.69  thf('9', plain, (![X4 : $i]: ((v1_ordinal1 @ X4) | ~ (v3_ordinal1 @ X4))),
% 0.51/0.69      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.51/0.69  thf('10', plain, ((v1_ordinal1 @ sk_B_1)),
% 0.51/0.69      inference('sup-', [status(thm)], ['8', '9'])).
% 0.51/0.69  thf('11', plain,
% 0.51/0.69      (((r1_tarski @ sk_A @ sk_B_1)) <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.51/0.69      inference('demod', [status(thm)], ['7', '10'])).
% 0.51/0.69  thf('12', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.69         (~ (r2_hidden @ X0 @ X1)
% 0.51/0.69          | (r2_hidden @ X0 @ X2)
% 0.51/0.69          | ~ (r1_tarski @ X1 @ X2))),
% 0.51/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.51/0.69  thf('13', plain,
% 0.51/0.69      ((![X0 : $i]: ((r2_hidden @ X0 @ sk_B_1) | ~ (r2_hidden @ X0 @ sk_A)))
% 0.51/0.69         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['11', '12'])).
% 0.51/0.69  thf('14', plain,
% 0.51/0.69      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B_1)
% 0.51/0.69        | ~ (r2_hidden @ sk_A @ sk_B_1))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('15', plain,
% 0.51/0.69      (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B_1)) | 
% 0.51/0.69       ~ ((r2_hidden @ sk_A @ sk_B_1))),
% 0.51/0.69      inference('split', [status(esa)], ['14'])).
% 0.51/0.69  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.51/0.69  thf('16', plain, (![X11 : $i]: (r2_hidden @ X11 @ (k1_ordinal1 @ X11))),
% 0.51/0.69      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.51/0.69  thf('17', plain,
% 0.51/0.69      (![X15 : $i]:
% 0.51/0.69         ((v3_ordinal1 @ (k1_ordinal1 @ X15)) | ~ (v3_ordinal1 @ X15))),
% 0.51/0.69      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.51/0.69  thf('18', plain,
% 0.51/0.69      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B_1))
% 0.51/0.69         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B_1)))),
% 0.51/0.69      inference('split', [status(esa)], ['4'])).
% 0.51/0.69  thf(redefinition_r1_ordinal1, axiom,
% 0.51/0.69    (![A:$i,B:$i]:
% 0.51/0.69     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.51/0.69       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.51/0.69  thf('19', plain,
% 0.51/0.69      (![X9 : $i, X10 : $i]:
% 0.51/0.69         (~ (v3_ordinal1 @ X9)
% 0.51/0.69          | ~ (v3_ordinal1 @ X10)
% 0.51/0.69          | (r1_tarski @ X9 @ X10)
% 0.51/0.69          | ~ (r1_ordinal1 @ X9 @ X10))),
% 0.51/0.69      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.51/0.69  thf('20', plain,
% 0.51/0.69      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B_1)
% 0.51/0.69         | ~ (v3_ordinal1 @ sk_B_1)
% 0.51/0.69         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.51/0.69         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B_1)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['18', '19'])).
% 0.51/0.69  thf('21', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('22', plain,
% 0.51/0.69      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B_1)
% 0.51/0.69         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.51/0.69         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B_1)))),
% 0.51/0.69      inference('demod', [status(thm)], ['20', '21'])).
% 0.51/0.69  thf('23', plain,
% 0.51/0.69      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B_1)))
% 0.51/0.69         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B_1)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['17', '22'])).
% 0.51/0.69  thf('24', plain, ((v3_ordinal1 @ sk_A)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('25', plain,
% 0.51/0.69      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B_1))
% 0.51/0.69         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B_1)))),
% 0.51/0.69      inference('demod', [status(thm)], ['23', '24'])).
% 0.51/0.69  thf('26', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.69         (~ (r2_hidden @ X0 @ X1)
% 0.51/0.69          | (r2_hidden @ X0 @ X2)
% 0.51/0.69          | ~ (r1_tarski @ X1 @ X2))),
% 0.51/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.51/0.69  thf('27', plain,
% 0.51/0.69      ((![X0 : $i]:
% 0.51/0.69          ((r2_hidden @ X0 @ sk_B_1)
% 0.51/0.69           | ~ (r2_hidden @ X0 @ (k1_ordinal1 @ sk_A))))
% 0.51/0.69         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B_1)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['25', '26'])).
% 0.51/0.69  thf('28', plain,
% 0.51/0.69      (((r2_hidden @ sk_A @ sk_B_1))
% 0.51/0.69         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B_1)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['16', '27'])).
% 0.51/0.69  thf('29', plain,
% 0.51/0.69      ((~ (r2_hidden @ sk_A @ sk_B_1)) <= (~ ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.51/0.69      inference('split', [status(esa)], ['14'])).
% 0.51/0.69  thf('30', plain,
% 0.51/0.69      (((r2_hidden @ sk_A @ sk_B_1)) | 
% 0.51/0.69       ~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B_1))),
% 0.51/0.69      inference('sup-', [status(thm)], ['28', '29'])).
% 0.51/0.69  thf('31', plain,
% 0.51/0.69      (((r2_hidden @ sk_A @ sk_B_1)) | 
% 0.51/0.69       ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B_1))),
% 0.51/0.69      inference('split', [status(esa)], ['4'])).
% 0.51/0.69  thf('32', plain, (((r2_hidden @ sk_A @ sk_B_1))),
% 0.51/0.69      inference('sat_resolution*', [status(thm)], ['15', '30', '31'])).
% 0.51/0.69  thf('33', plain,
% 0.51/0.69      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B_1) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.51/0.69      inference('simpl_trail', [status(thm)], ['13', '32'])).
% 0.51/0.69  thf('34', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         (((sk_C @ X0 @ (k1_ordinal1 @ sk_A)) = (sk_A))
% 0.51/0.69          | (r1_tarski @ (k1_ordinal1 @ sk_A) @ X0)
% 0.51/0.69          | (r2_hidden @ (sk_C @ X0 @ (k1_ordinal1 @ sk_A)) @ sk_B_1))),
% 0.51/0.69      inference('sup-', [status(thm)], ['3', '33'])).
% 0.51/0.69  thf('35', plain,
% 0.51/0.69      (![X1 : $i, X3 : $i]:
% 0.51/0.69         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.51/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.51/0.69  thf('36', plain,
% 0.51/0.69      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B_1)
% 0.51/0.69        | ((sk_C @ sk_B_1 @ (k1_ordinal1 @ sk_A)) = (sk_A))
% 0.51/0.69        | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B_1))),
% 0.51/0.69      inference('sup-', [status(thm)], ['34', '35'])).
% 0.51/0.69  thf('37', plain,
% 0.51/0.69      ((((sk_C @ sk_B_1 @ (k1_ordinal1 @ sk_A)) = (sk_A))
% 0.51/0.69        | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B_1))),
% 0.51/0.69      inference('simplify', [status(thm)], ['36'])).
% 0.51/0.69  thf('38', plain,
% 0.51/0.69      (![X1 : $i, X3 : $i]:
% 0.51/0.69         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.51/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.51/0.69  thf('39', plain,
% 0.51/0.69      ((~ (r2_hidden @ sk_A @ sk_B_1)
% 0.51/0.69        | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B_1)
% 0.51/0.69        | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B_1))),
% 0.51/0.69      inference('sup-', [status(thm)], ['37', '38'])).
% 0.51/0.69  thf('40', plain,
% 0.51/0.69      (((r2_hidden @ sk_A @ sk_B_1)) <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.51/0.69      inference('split', [status(esa)], ['4'])).
% 0.51/0.69  thf('41', plain, (((r2_hidden @ sk_A @ sk_B_1))),
% 0.51/0.69      inference('sat_resolution*', [status(thm)], ['15', '30', '31'])).
% 0.51/0.69  thf('42', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.51/0.69      inference('simpl_trail', [status(thm)], ['40', '41'])).
% 0.51/0.69  thf('43', plain,
% 0.51/0.69      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B_1)
% 0.51/0.69        | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B_1))),
% 0.51/0.69      inference('demod', [status(thm)], ['39', '42'])).
% 0.51/0.69  thf('44', plain, ((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B_1)),
% 0.51/0.69      inference('simplify', [status(thm)], ['43'])).
% 0.51/0.69  thf('45', plain,
% 0.51/0.69      (![X9 : $i, X10 : $i]:
% 0.51/0.69         (~ (v3_ordinal1 @ X9)
% 0.51/0.69          | ~ (v3_ordinal1 @ X10)
% 0.51/0.69          | (r1_ordinal1 @ X9 @ X10)
% 0.51/0.69          | ~ (r1_tarski @ X9 @ X10))),
% 0.51/0.69      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.51/0.69  thf('46', plain,
% 0.51/0.69      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B_1)
% 0.51/0.69        | ~ (v3_ordinal1 @ sk_B_1)
% 0.51/0.69        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['44', '45'])).
% 0.51/0.69  thf('47', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('48', plain,
% 0.51/0.69      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B_1)
% 0.51/0.69        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A)))),
% 0.51/0.69      inference('demod', [status(thm)], ['46', '47'])).
% 0.51/0.69  thf('49', plain,
% 0.51/0.69      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B_1))
% 0.51/0.69         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B_1)))),
% 0.51/0.69      inference('split', [status(esa)], ['14'])).
% 0.51/0.69  thf('50', plain, (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B_1))),
% 0.51/0.69      inference('sat_resolution*', [status(thm)], ['15', '30'])).
% 0.51/0.69  thf('51', plain, (~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B_1)),
% 0.51/0.69      inference('simpl_trail', [status(thm)], ['49', '50'])).
% 0.51/0.69  thf('52', plain, (~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))),
% 0.51/0.69      inference('clc', [status(thm)], ['48', '51'])).
% 0.51/0.69  thf('53', plain, (~ (v3_ordinal1 @ sk_A)),
% 0.51/0.69      inference('sup-', [status(thm)], ['0', '52'])).
% 0.51/0.69  thf('54', plain, ((v3_ordinal1 @ sk_A)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('55', plain, ($false), inference('demod', [status(thm)], ['53', '54'])).
% 0.51/0.69  
% 0.51/0.69  % SZS output end Refutation
% 0.51/0.69  
% 0.51/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

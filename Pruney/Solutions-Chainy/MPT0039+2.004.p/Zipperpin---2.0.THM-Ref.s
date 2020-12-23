%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wHsa86dfdK

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:58 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 187 expanded)
%              Number of leaves         :   18 (  64 expanded)
%              Depth                    :   17
%              Number of atoms          :  450 (1338 expanded)
%              Number of equality atoms :   22 (  76 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t32_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = ( k4_xboole_0 @ B @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ A @ B )
          = ( k4_xboole_0 @ B @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t32_xboole_1])).

thf('1',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( r2_hidden @ X11 @ X8 )
      | ( X10
       != ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('3',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ( r2_hidden @ X11 @ X8 )
      | ~ ( r2_hidden @ X11 @ ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
      | ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ~ ( r2_hidden @ X11 @ X9 )
      | ( X10
       != ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('6',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['4','6'])).

thf('8',plain,(
    v1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('9',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('13',plain,(
    ! [X13: $i,X15: $i] :
      ( ( r2_xboole_0 @ X13 @ X15 )
      | ( X13 = X15 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ( r2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ~ ( r2_hidden @ C @ A ) ) ) )).

thf('15',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r2_xboole_0 @ X16 @ X17 )
      | ( r2_hidden @ ( sk_C_1 @ X17 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['9','18'])).

thf('20',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['8','19'])).

thf('21',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( r2_hidden @ X7 @ X9 )
      | ( r2_hidden @ X7 @ X10 )
      | ( X10
       != ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('23',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X7 @ ( k4_xboole_0 @ X8 @ X9 ) )
      | ( r2_hidden @ X7 @ X9 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 @ X1 ) @ X0 )
      | ( r1_tarski @ X1 @ X2 )
      | ~ ( v1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('31',plain,
    ( ( r1_tarski @ sk_A @ sk_B_1 )
    | ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X13: $i,X15: $i] :
      ( ( r2_xboole_0 @ X13 @ X15 )
      | ( X13 = X15 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('34',plain,
    ( ( sk_A = sk_B_1 )
    | ( r2_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    r2_xboole_0 @ sk_A @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r2_xboole_0 @ X16 @ X17 )
      | ( r2_hidden @ ( sk_C_1 @ X17 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('38',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['8','19'])).

thf('41',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 @ X1 ) @ X0 )
      | ( r1_tarski @ X1 @ X2 )
      | ~ ( v1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('47',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_A )
    | ( r1_tarski @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['38','50'])).

thf('52',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r2_xboole_0 @ X16 @ X17 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X17 @ X16 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('53',plain,(
    ~ ( r2_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    r2_xboole_0 @ sk_A @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['34','35'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['53','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wHsa86dfdK
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:22:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.65/1.87  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.65/1.87  % Solved by: fo/fo7.sh
% 1.65/1.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.65/1.87  % done 2176 iterations in 1.383s
% 1.65/1.87  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.65/1.87  % SZS output start Refutation
% 1.65/1.87  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.65/1.87  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.65/1.87  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.65/1.87  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.65/1.87  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.65/1.87  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.65/1.87  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.65/1.87  thf(sk_A_type, type, sk_A: $i).
% 1.65/1.87  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 1.65/1.87  thf(sk_B_type, type, sk_B: $i > $i).
% 1.65/1.87  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.65/1.87  thf(d1_xboole_0, axiom,
% 1.65/1.87    (![A:$i]:
% 1.65/1.87     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.65/1.87  thf('0', plain,
% 1.65/1.87      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.65/1.87      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.65/1.87  thf(t32_xboole_1, conjecture,
% 1.65/1.87    (![A:$i,B:$i]:
% 1.65/1.87     ( ( ( k4_xboole_0 @ A @ B ) = ( k4_xboole_0 @ B @ A ) ) =>
% 1.65/1.87       ( ( A ) = ( B ) ) ))).
% 1.65/1.87  thf(zf_stmt_0, negated_conjecture,
% 1.65/1.87    (~( ![A:$i,B:$i]:
% 1.65/1.87        ( ( ( k4_xboole_0 @ A @ B ) = ( k4_xboole_0 @ B @ A ) ) =>
% 1.65/1.87          ( ( A ) = ( B ) ) ) )),
% 1.65/1.87    inference('cnf.neg', [status(esa)], [t32_xboole_1])).
% 1.65/1.87  thf('1', plain,
% 1.65/1.87      (((k4_xboole_0 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_B_1 @ sk_A))),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf(d5_xboole_0, axiom,
% 1.65/1.87    (![A:$i,B:$i,C:$i]:
% 1.65/1.87     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.65/1.87       ( ![D:$i]:
% 1.65/1.87         ( ( r2_hidden @ D @ C ) <=>
% 1.65/1.87           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.65/1.87  thf('2', plain,
% 1.65/1.87      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 1.65/1.87         (~ (r2_hidden @ X11 @ X10)
% 1.65/1.87          | (r2_hidden @ X11 @ X8)
% 1.65/1.87          | ((X10) != (k4_xboole_0 @ X8 @ X9)))),
% 1.65/1.87      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.65/1.87  thf('3', plain,
% 1.65/1.87      (![X8 : $i, X9 : $i, X11 : $i]:
% 1.65/1.87         ((r2_hidden @ X11 @ X8)
% 1.65/1.87          | ~ (r2_hidden @ X11 @ (k4_xboole_0 @ X8 @ X9)))),
% 1.65/1.87      inference('simplify', [status(thm)], ['2'])).
% 1.65/1.87  thf('4', plain,
% 1.65/1.87      (![X0 : $i]:
% 1.65/1.87         (~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_A @ sk_B_1))
% 1.65/1.87          | (r2_hidden @ X0 @ sk_B_1))),
% 1.65/1.87      inference('sup-', [status(thm)], ['1', '3'])).
% 1.65/1.87  thf('5', plain,
% 1.65/1.87      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 1.65/1.87         (~ (r2_hidden @ X11 @ X10)
% 1.65/1.87          | ~ (r2_hidden @ X11 @ X9)
% 1.65/1.87          | ((X10) != (k4_xboole_0 @ X8 @ X9)))),
% 1.65/1.87      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.65/1.87  thf('6', plain,
% 1.65/1.87      (![X8 : $i, X9 : $i, X11 : $i]:
% 1.65/1.87         (~ (r2_hidden @ X11 @ X9)
% 1.65/1.87          | ~ (r2_hidden @ X11 @ (k4_xboole_0 @ X8 @ X9)))),
% 1.65/1.87      inference('simplify', [status(thm)], ['5'])).
% 1.65/1.87  thf('7', plain,
% 1.65/1.87      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_A @ sk_B_1))),
% 1.65/1.87      inference('clc', [status(thm)], ['4', '6'])).
% 1.65/1.87  thf('8', plain, ((v1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B_1))),
% 1.65/1.87      inference('sup-', [status(thm)], ['0', '7'])).
% 1.65/1.87  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.65/1.87  thf('9', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.65/1.87      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.65/1.87  thf(d3_tarski, axiom,
% 1.65/1.87    (![A:$i,B:$i]:
% 1.65/1.87     ( ( r1_tarski @ A @ B ) <=>
% 1.65/1.87       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.65/1.87  thf('10', plain,
% 1.65/1.87      (![X4 : $i, X6 : $i]:
% 1.65/1.87         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 1.65/1.87      inference('cnf', [status(esa)], [d3_tarski])).
% 1.65/1.87  thf('11', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.65/1.87      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.65/1.87  thf('12', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.65/1.87      inference('sup-', [status(thm)], ['10', '11'])).
% 1.65/1.87  thf(d8_xboole_0, axiom,
% 1.65/1.87    (![A:$i,B:$i]:
% 1.65/1.87     ( ( r2_xboole_0 @ A @ B ) <=>
% 1.65/1.87       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 1.65/1.87  thf('13', plain,
% 1.65/1.87      (![X13 : $i, X15 : $i]:
% 1.65/1.87         ((r2_xboole_0 @ X13 @ X15)
% 1.65/1.87          | ((X13) = (X15))
% 1.65/1.87          | ~ (r1_tarski @ X13 @ X15))),
% 1.65/1.87      inference('cnf', [status(esa)], [d8_xboole_0])).
% 1.65/1.87  thf('14', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | (r2_xboole_0 @ X1 @ X0))),
% 1.65/1.87      inference('sup-', [status(thm)], ['12', '13'])).
% 1.65/1.87  thf(t6_xboole_0, axiom,
% 1.65/1.87    (![A:$i,B:$i]:
% 1.65/1.87     ( ~( ( r2_xboole_0 @ A @ B ) & 
% 1.65/1.87          ( ![C:$i]:
% 1.65/1.87            ( ~( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ) ) ) ))).
% 1.65/1.87  thf('15', plain,
% 1.65/1.87      (![X16 : $i, X17 : $i]:
% 1.65/1.87         (~ (r2_xboole_0 @ X16 @ X17)
% 1.65/1.87          | (r2_hidden @ (sk_C_1 @ X17 @ X16) @ X17))),
% 1.65/1.87      inference('cnf', [status(esa)], [t6_xboole_0])).
% 1.65/1.87  thf('16', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         (((X1) = (X0))
% 1.65/1.87          | ~ (v1_xboole_0 @ X1)
% 1.65/1.87          | (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X0))),
% 1.65/1.87      inference('sup-', [status(thm)], ['14', '15'])).
% 1.65/1.87  thf('17', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.65/1.87      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.65/1.87  thf('18', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.65/1.87      inference('sup-', [status(thm)], ['16', '17'])).
% 1.65/1.87  thf('19', plain,
% 1.65/1.87      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 1.65/1.87      inference('sup-', [status(thm)], ['9', '18'])).
% 1.65/1.87  thf('20', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 1.65/1.87      inference('sup-', [status(thm)], ['8', '19'])).
% 1.65/1.87  thf('21', plain,
% 1.65/1.87      (![X4 : $i, X6 : $i]:
% 1.65/1.87         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 1.65/1.87      inference('cnf', [status(esa)], [d3_tarski])).
% 1.65/1.87  thf('22', plain,
% 1.65/1.87      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.65/1.87         (~ (r2_hidden @ X7 @ X8)
% 1.65/1.87          | (r2_hidden @ X7 @ X9)
% 1.65/1.87          | (r2_hidden @ X7 @ X10)
% 1.65/1.87          | ((X10) != (k4_xboole_0 @ X8 @ X9)))),
% 1.65/1.87      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.65/1.87  thf('23', plain,
% 1.65/1.87      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.65/1.87         ((r2_hidden @ X7 @ (k4_xboole_0 @ X8 @ X9))
% 1.65/1.87          | (r2_hidden @ X7 @ X9)
% 1.65/1.87          | ~ (r2_hidden @ X7 @ X8))),
% 1.65/1.87      inference('simplify', [status(thm)], ['22'])).
% 1.65/1.87  thf('24', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.87         ((r1_tarski @ X0 @ X1)
% 1.65/1.87          | (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 1.65/1.87          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X2)))),
% 1.65/1.87      inference('sup-', [status(thm)], ['21', '23'])).
% 1.65/1.87  thf('25', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.65/1.87      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.65/1.87  thf('26', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.87         ((r2_hidden @ (sk_C @ X2 @ X1) @ X0)
% 1.65/1.87          | (r1_tarski @ X1 @ X2)
% 1.65/1.87          | ~ (v1_xboole_0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.65/1.87      inference('sup-', [status(thm)], ['24', '25'])).
% 1.65/1.87  thf('27', plain,
% 1.65/1.87      (![X0 : $i]:
% 1.65/1.87         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.65/1.87          | (r1_tarski @ sk_A @ X0)
% 1.65/1.87          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B_1))),
% 1.65/1.87      inference('sup-', [status(thm)], ['20', '26'])).
% 1.65/1.87  thf('28', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.65/1.87      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.65/1.87  thf('29', plain,
% 1.65/1.87      (![X0 : $i]:
% 1.65/1.87         ((r1_tarski @ sk_A @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B_1))),
% 1.65/1.87      inference('demod', [status(thm)], ['27', '28'])).
% 1.65/1.87  thf('30', plain,
% 1.65/1.87      (![X4 : $i, X6 : $i]:
% 1.65/1.87         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 1.65/1.87      inference('cnf', [status(esa)], [d3_tarski])).
% 1.65/1.87  thf('31', plain,
% 1.65/1.87      (((r1_tarski @ sk_A @ sk_B_1) | (r1_tarski @ sk_A @ sk_B_1))),
% 1.65/1.87      inference('sup-', [status(thm)], ['29', '30'])).
% 1.65/1.87  thf('32', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 1.65/1.87      inference('simplify', [status(thm)], ['31'])).
% 1.65/1.87  thf('33', plain,
% 1.65/1.87      (![X13 : $i, X15 : $i]:
% 1.65/1.87         ((r2_xboole_0 @ X13 @ X15)
% 1.65/1.87          | ((X13) = (X15))
% 1.65/1.87          | ~ (r1_tarski @ X13 @ X15))),
% 1.65/1.87      inference('cnf', [status(esa)], [d8_xboole_0])).
% 1.65/1.87  thf('34', plain, ((((sk_A) = (sk_B_1)) | (r2_xboole_0 @ sk_A @ sk_B_1))),
% 1.65/1.87      inference('sup-', [status(thm)], ['32', '33'])).
% 1.65/1.87  thf('35', plain, (((sk_A) != (sk_B_1))),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf('36', plain, ((r2_xboole_0 @ sk_A @ sk_B_1)),
% 1.65/1.87      inference('simplify_reflect-', [status(thm)], ['34', '35'])).
% 1.65/1.87  thf('37', plain,
% 1.65/1.87      (![X16 : $i, X17 : $i]:
% 1.65/1.87         (~ (r2_xboole_0 @ X16 @ X17)
% 1.65/1.87          | (r2_hidden @ (sk_C_1 @ X17 @ X16) @ X17))),
% 1.65/1.87      inference('cnf', [status(esa)], [t6_xboole_0])).
% 1.65/1.87  thf('38', plain, ((r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1)),
% 1.65/1.87      inference('sup-', [status(thm)], ['36', '37'])).
% 1.65/1.87  thf('39', plain,
% 1.65/1.87      (((k4_xboole_0 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_B_1 @ sk_A))),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf('40', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 1.65/1.87      inference('sup-', [status(thm)], ['8', '19'])).
% 1.65/1.87  thf('41', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_B_1 @ sk_A))),
% 1.65/1.87      inference('demod', [status(thm)], ['39', '40'])).
% 1.65/1.87  thf('42', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.87         ((r2_hidden @ (sk_C @ X2 @ X1) @ X0)
% 1.65/1.87          | (r1_tarski @ X1 @ X2)
% 1.65/1.87          | ~ (v1_xboole_0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.65/1.87      inference('sup-', [status(thm)], ['24', '25'])).
% 1.65/1.87  thf('43', plain,
% 1.65/1.87      (![X0 : $i]:
% 1.65/1.87         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.65/1.87          | (r1_tarski @ sk_B_1 @ X0)
% 1.65/1.87          | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_A))),
% 1.65/1.87      inference('sup-', [status(thm)], ['41', '42'])).
% 1.65/1.87  thf('44', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.65/1.87      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.65/1.87  thf('45', plain,
% 1.65/1.87      (![X0 : $i]:
% 1.65/1.87         ((r1_tarski @ sk_B_1 @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_A))),
% 1.65/1.87      inference('demod', [status(thm)], ['43', '44'])).
% 1.65/1.87  thf('46', plain,
% 1.65/1.87      (![X4 : $i, X6 : $i]:
% 1.65/1.87         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 1.65/1.87      inference('cnf', [status(esa)], [d3_tarski])).
% 1.65/1.87  thf('47', plain,
% 1.65/1.87      (((r1_tarski @ sk_B_1 @ sk_A) | (r1_tarski @ sk_B_1 @ sk_A))),
% 1.65/1.87      inference('sup-', [status(thm)], ['45', '46'])).
% 1.65/1.87  thf('48', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 1.65/1.87      inference('simplify', [status(thm)], ['47'])).
% 1.65/1.87  thf('49', plain,
% 1.65/1.87      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.65/1.87         (~ (r2_hidden @ X3 @ X4)
% 1.65/1.87          | (r2_hidden @ X3 @ X5)
% 1.65/1.87          | ~ (r1_tarski @ X4 @ X5))),
% 1.65/1.87      inference('cnf', [status(esa)], [d3_tarski])).
% 1.65/1.87  thf('50', plain,
% 1.65/1.87      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 1.65/1.87      inference('sup-', [status(thm)], ['48', '49'])).
% 1.65/1.87  thf('51', plain, ((r2_hidden @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)),
% 1.65/1.87      inference('sup-', [status(thm)], ['38', '50'])).
% 1.65/1.87  thf('52', plain,
% 1.65/1.87      (![X16 : $i, X17 : $i]:
% 1.65/1.87         (~ (r2_xboole_0 @ X16 @ X17)
% 1.65/1.87          | ~ (r2_hidden @ (sk_C_1 @ X17 @ X16) @ X16))),
% 1.65/1.87      inference('cnf', [status(esa)], [t6_xboole_0])).
% 1.65/1.87  thf('53', plain, (~ (r2_xboole_0 @ sk_A @ sk_B_1)),
% 1.65/1.87      inference('sup-', [status(thm)], ['51', '52'])).
% 1.65/1.87  thf('54', plain, ((r2_xboole_0 @ sk_A @ sk_B_1)),
% 1.65/1.87      inference('simplify_reflect-', [status(thm)], ['34', '35'])).
% 1.65/1.87  thf('55', plain, ($false), inference('demod', [status(thm)], ['53', '54'])).
% 1.65/1.87  
% 1.65/1.87  % SZS output end Refutation
% 1.65/1.87  
% 1.65/1.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

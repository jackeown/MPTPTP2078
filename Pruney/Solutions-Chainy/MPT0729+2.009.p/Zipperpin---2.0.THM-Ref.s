%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pOlGpbVnVz

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:42 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 243 expanded)
%              Number of leaves         :   21 (  81 expanded)
%              Depth                    :   18
%              Number of atoms          :  471 (1741 expanded)
%              Number of equality atoms :   22 ( 135 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t12_ordinal1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k1_ordinal1 @ A )
        = ( k1_ordinal1 @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k1_ordinal1 @ A )
          = ( k1_ordinal1 @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_ordinal1])).

thf('0',plain,
    ( ( k1_ordinal1 @ sk_A )
    = ( k1_ordinal1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('1',plain,(
    ! [X46: $i] :
      ( r2_hidden @ X46 @ ( k1_ordinal1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('2',plain,(
    r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('3',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( r2_hidden @ X47 @ X48 )
      | ~ ( r1_tarski @ X48 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('5',plain,(
    ! [X45: $i] :
      ( ( k1_ordinal1 @ X45 )
      = ( k2_xboole_0 @ X45 @ ( k1_tarski @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k1_ordinal1 @ sk_A )
    = ( k1_ordinal1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('9',plain,(
    ! [X43: $i,X44: $i] :
      ( ( ( k4_xboole_0 @ X43 @ ( k1_tarski @ X44 ) )
        = X43 )
      | ( r2_hidden @ X44 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_xboole_0 @ X10 @ X12 )
      | ( ( k4_xboole_0 @ X10 @ X12 )
       != X10 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X45: $i] :
      ( ( k1_ordinal1 @ X45 )
      = ( k2_xboole_0 @ X45 @ ( k1_tarski @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(t73_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) )
      | ~ ( r1_xboole_0 @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t73_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( r1_tarski @ X1 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_ordinal1 @ sk_A ) )
      | ( r1_tarski @ X0 @ sk_B )
      | ( r2_hidden @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','16'])).

thf('18',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['7','17'])).

thf('19',plain,
    ( ( k1_ordinal1 @ sk_A )
    = ( k1_ordinal1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('21',plain,(
    r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( r1_tarski @ X1 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('23',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r1_tarski @ sk_A @ sk_B )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['18','27'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('29',plain,(
    ! [X37: $i,X39: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X37 ) @ X39 )
      | ~ ( r2_hidden @ X37 @ X39 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('30',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('32',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_tarski @ X15 @ X14 )
      | ( r1_tarski @ ( k2_xboole_0 @ X13 @ X15 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ sk_B )
      | ( r1_tarski @ ( k2_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r1_tarski @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_B ) ) @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X45: $i] :
      ( ( k1_ordinal1 @ X45 )
      = ( k2_xboole_0 @ X45 @ ( k1_tarski @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('36',plain,
    ( ( k1_ordinal1 @ sk_A )
    = ( k1_ordinal1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X46: $i] :
      ( r2_hidden @ X46 @ ( k1_ordinal1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('40',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( r2_hidden @ X47 @ X48 )
      | ~ ( r1_tarski @ X48 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('41',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X37: $i,X39: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X37 ) @ X39 )
      | ~ ( r2_hidden @ X37 @ X39 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('44',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['7','17'])).

thf('46',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_tarski @ X15 @ X14 )
      | ( r1_tarski @ ( k2_xboole_0 @ X13 @ X15 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ sk_A )
      | ( r1_tarski @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['38','41'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('50',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( r1_tarski @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['47','50'])).

thf('52',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_A @ ( k1_tarski @ sk_A ) ) @ sk_B ),
    inference('sup-',[status(thm)],['44','51'])).

thf('53',plain,(
    ! [X45: $i] :
      ( ( k1_ordinal1 @ X45 )
      = ( k2_xboole_0 @ X45 @ ( k1_tarski @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('54',plain,(
    r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['4','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pOlGpbVnVz
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:25:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.77/0.95  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.77/0.95  % Solved by: fo/fo7.sh
% 0.77/0.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/0.95  % done 1045 iterations in 0.473s
% 0.77/0.95  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.77/0.95  % SZS output start Refutation
% 0.77/0.95  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.77/0.95  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.77/0.95  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.77/0.95  thf(sk_B_type, type, sk_B: $i).
% 0.77/0.95  thf(sk_A_type, type, sk_A: $i).
% 0.77/0.95  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.77/0.95  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.77/0.95  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.77/0.95  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.77/0.95  thf(t12_ordinal1, conjecture,
% 0.77/0.95    (![A:$i,B:$i]:
% 0.77/0.95     ( ( ( k1_ordinal1 @ A ) = ( k1_ordinal1 @ B ) ) => ( ( A ) = ( B ) ) ))).
% 0.77/0.95  thf(zf_stmt_0, negated_conjecture,
% 0.77/0.95    (~( ![A:$i,B:$i]:
% 0.77/0.95        ( ( ( k1_ordinal1 @ A ) = ( k1_ordinal1 @ B ) ) => ( ( A ) = ( B ) ) ) )),
% 0.77/0.95    inference('cnf.neg', [status(esa)], [t12_ordinal1])).
% 0.77/0.95  thf('0', plain, (((k1_ordinal1 @ sk_A) = (k1_ordinal1 @ sk_B))),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.77/0.95  thf('1', plain, (![X46 : $i]: (r2_hidden @ X46 @ (k1_ordinal1 @ X46))),
% 0.77/0.95      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.77/0.95  thf('2', plain, ((r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))),
% 0.77/0.95      inference('sup+', [status(thm)], ['0', '1'])).
% 0.77/0.95  thf(t7_ordinal1, axiom,
% 0.77/0.95    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.77/0.95  thf('3', plain,
% 0.77/0.95      (![X47 : $i, X48 : $i]:
% 0.77/0.95         (~ (r2_hidden @ X47 @ X48) | ~ (r1_tarski @ X48 @ X47))),
% 0.77/0.95      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.77/0.95  thf('4', plain, (~ (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 0.77/0.95      inference('sup-', [status(thm)], ['2', '3'])).
% 0.77/0.95  thf(d1_ordinal1, axiom,
% 0.77/0.95    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.77/0.95  thf('5', plain,
% 0.77/0.95      (![X45 : $i]:
% 0.77/0.95         ((k1_ordinal1 @ X45) = (k2_xboole_0 @ X45 @ (k1_tarski @ X45)))),
% 0.77/0.95      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.77/0.95  thf(t7_xboole_1, axiom,
% 0.77/0.95    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.77/0.95  thf('6', plain,
% 0.77/0.95      (![X8 : $i, X9 : $i]: (r1_tarski @ X8 @ (k2_xboole_0 @ X8 @ X9))),
% 0.77/0.95      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.77/0.95  thf('7', plain, (![X0 : $i]: (r1_tarski @ X0 @ (k1_ordinal1 @ X0))),
% 0.77/0.95      inference('sup+', [status(thm)], ['5', '6'])).
% 0.77/0.95  thf('8', plain, (((k1_ordinal1 @ sk_A) = (k1_ordinal1 @ sk_B))),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf(t65_zfmisc_1, axiom,
% 0.77/0.95    (![A:$i,B:$i]:
% 0.77/0.95     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.77/0.95       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.77/0.95  thf('9', plain,
% 0.77/0.95      (![X43 : $i, X44 : $i]:
% 0.77/0.95         (((k4_xboole_0 @ X43 @ (k1_tarski @ X44)) = (X43))
% 0.77/0.95          | (r2_hidden @ X44 @ X43))),
% 0.77/0.95      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.77/0.95  thf(t83_xboole_1, axiom,
% 0.77/0.95    (![A:$i,B:$i]:
% 0.77/0.95     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.77/0.95  thf('10', plain,
% 0.77/0.95      (![X10 : $i, X12 : $i]:
% 0.77/0.95         ((r1_xboole_0 @ X10 @ X12) | ((k4_xboole_0 @ X10 @ X12) != (X10)))),
% 0.77/0.95      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.77/0.95  thf('11', plain,
% 0.77/0.95      (![X0 : $i, X1 : $i]:
% 0.77/0.95         (((X0) != (X0))
% 0.77/0.95          | (r2_hidden @ X1 @ X0)
% 0.77/0.95          | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.77/0.95      inference('sup-', [status(thm)], ['9', '10'])).
% 0.77/0.95  thf('12', plain,
% 0.77/0.95      (![X0 : $i, X1 : $i]:
% 0.77/0.95         ((r1_xboole_0 @ X0 @ (k1_tarski @ X1)) | (r2_hidden @ X1 @ X0))),
% 0.77/0.95      inference('simplify', [status(thm)], ['11'])).
% 0.77/0.95  thf('13', plain,
% 0.77/0.95      (![X45 : $i]:
% 0.77/0.95         ((k1_ordinal1 @ X45) = (k2_xboole_0 @ X45 @ (k1_tarski @ X45)))),
% 0.77/0.95      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.77/0.95  thf(t73_xboole_1, axiom,
% 0.77/0.95    (![A:$i,B:$i,C:$i]:
% 0.77/0.95     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.77/0.95       ( r1_tarski @ A @ B ) ))).
% 0.77/0.95  thf('14', plain,
% 0.77/0.95      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.77/0.95         ((r1_tarski @ X5 @ X6)
% 0.77/0.95          | ~ (r1_tarski @ X5 @ (k2_xboole_0 @ X6 @ X7))
% 0.77/0.95          | ~ (r1_xboole_0 @ X5 @ X7))),
% 0.77/0.95      inference('cnf', [status(esa)], [t73_xboole_1])).
% 0.77/0.95  thf('15', plain,
% 0.77/0.95      (![X0 : $i, X1 : $i]:
% 0.77/0.95         (~ (r1_tarski @ X1 @ (k1_ordinal1 @ X0))
% 0.77/0.95          | ~ (r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.77/0.95          | (r1_tarski @ X1 @ X0))),
% 0.77/0.95      inference('sup-', [status(thm)], ['13', '14'])).
% 0.77/0.95  thf('16', plain,
% 0.77/0.95      (![X0 : $i, X1 : $i]:
% 0.77/0.95         ((r2_hidden @ X0 @ X1)
% 0.77/0.95          | (r1_tarski @ X1 @ X0)
% 0.77/0.95          | ~ (r1_tarski @ X1 @ (k1_ordinal1 @ X0)))),
% 0.77/0.95      inference('sup-', [status(thm)], ['12', '15'])).
% 0.77/0.95  thf('17', plain,
% 0.77/0.95      (![X0 : $i]:
% 0.77/0.95         (~ (r1_tarski @ X0 @ (k1_ordinal1 @ sk_A))
% 0.77/0.95          | (r1_tarski @ X0 @ sk_B)
% 0.77/0.95          | (r2_hidden @ sk_B @ X0))),
% 0.77/0.95      inference('sup-', [status(thm)], ['8', '16'])).
% 0.77/0.95  thf('18', plain, (((r2_hidden @ sk_B @ sk_A) | (r1_tarski @ sk_A @ sk_B))),
% 0.77/0.95      inference('sup-', [status(thm)], ['7', '17'])).
% 0.77/0.95  thf('19', plain, (((k1_ordinal1 @ sk_A) = (k1_ordinal1 @ sk_B))),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('20', plain, (![X0 : $i]: (r1_tarski @ X0 @ (k1_ordinal1 @ X0))),
% 0.77/0.95      inference('sup+', [status(thm)], ['5', '6'])).
% 0.77/0.95  thf('21', plain, ((r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A))),
% 0.77/0.95      inference('sup+', [status(thm)], ['19', '20'])).
% 0.77/0.95  thf('22', plain,
% 0.77/0.95      (![X0 : $i, X1 : $i]:
% 0.77/0.95         ((r2_hidden @ X0 @ X1)
% 0.77/0.95          | (r1_tarski @ X1 @ X0)
% 0.77/0.95          | ~ (r1_tarski @ X1 @ (k1_ordinal1 @ X0)))),
% 0.77/0.95      inference('sup-', [status(thm)], ['12', '15'])).
% 0.77/0.95  thf('23', plain, (((r1_tarski @ sk_B @ sk_A) | (r2_hidden @ sk_A @ sk_B))),
% 0.77/0.95      inference('sup-', [status(thm)], ['21', '22'])).
% 0.77/0.95  thf(d10_xboole_0, axiom,
% 0.77/0.95    (![A:$i,B:$i]:
% 0.77/0.95     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.77/0.95  thf('24', plain,
% 0.77/0.95      (![X2 : $i, X4 : $i]:
% 0.77/0.95         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.77/0.95      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.77/0.95  thf('25', plain,
% 0.77/0.95      (((r2_hidden @ sk_A @ sk_B)
% 0.77/0.95        | ~ (r1_tarski @ sk_A @ sk_B)
% 0.77/0.95        | ((sk_A) = (sk_B)))),
% 0.77/0.95      inference('sup-', [status(thm)], ['23', '24'])).
% 0.77/0.95  thf('26', plain, (((sk_A) != (sk_B))),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('27', plain, (((r2_hidden @ sk_A @ sk_B) | ~ (r1_tarski @ sk_A @ sk_B))),
% 0.77/0.95      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 0.77/0.95  thf('28', plain, (((r2_hidden @ sk_B @ sk_A) | (r2_hidden @ sk_A @ sk_B))),
% 0.77/0.95      inference('sup-', [status(thm)], ['18', '27'])).
% 0.77/0.95  thf(l1_zfmisc_1, axiom,
% 0.77/0.95    (![A:$i,B:$i]:
% 0.77/0.95     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.77/0.95  thf('29', plain,
% 0.77/0.95      (![X37 : $i, X39 : $i]:
% 0.77/0.95         ((r1_tarski @ (k1_tarski @ X37) @ X39) | ~ (r2_hidden @ X37 @ X39))),
% 0.77/0.95      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.77/0.95  thf('30', plain,
% 0.77/0.95      (((r2_hidden @ sk_A @ sk_B) | (r1_tarski @ (k1_tarski @ sk_B) @ sk_A))),
% 0.77/0.95      inference('sup-', [status(thm)], ['28', '29'])).
% 0.77/0.95  thf('31', plain, (((r1_tarski @ sk_B @ sk_A) | (r2_hidden @ sk_A @ sk_B))),
% 0.77/0.95      inference('sup-', [status(thm)], ['21', '22'])).
% 0.77/0.95  thf(t8_xboole_1, axiom,
% 0.77/0.95    (![A:$i,B:$i,C:$i]:
% 0.77/0.95     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.77/0.95       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.77/0.95  thf('32', plain,
% 0.77/0.95      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.77/0.95         (~ (r1_tarski @ X13 @ X14)
% 0.77/0.95          | ~ (r1_tarski @ X15 @ X14)
% 0.77/0.95          | (r1_tarski @ (k2_xboole_0 @ X13 @ X15) @ X14))),
% 0.77/0.95      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.77/0.95  thf('33', plain,
% 0.77/0.95      (![X0 : $i]:
% 0.77/0.95         ((r2_hidden @ sk_A @ sk_B)
% 0.77/0.95          | (r1_tarski @ (k2_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.77/0.95          | ~ (r1_tarski @ X0 @ sk_A))),
% 0.77/0.95      inference('sup-', [status(thm)], ['31', '32'])).
% 0.77/0.95  thf('34', plain,
% 0.77/0.95      (((r2_hidden @ sk_A @ sk_B)
% 0.77/0.95        | (r1_tarski @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_B)) @ sk_A)
% 0.77/0.95        | (r2_hidden @ sk_A @ sk_B))),
% 0.77/0.95      inference('sup-', [status(thm)], ['30', '33'])).
% 0.77/0.95  thf('35', plain,
% 0.77/0.95      (![X45 : $i]:
% 0.77/0.95         ((k1_ordinal1 @ X45) = (k2_xboole_0 @ X45 @ (k1_tarski @ X45)))),
% 0.77/0.95      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.77/0.95  thf('36', plain, (((k1_ordinal1 @ sk_A) = (k1_ordinal1 @ sk_B))),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('37', plain,
% 0.77/0.95      (((r2_hidden @ sk_A @ sk_B)
% 0.77/0.95        | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_A)
% 0.77/0.95        | (r2_hidden @ sk_A @ sk_B))),
% 0.77/0.95      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.77/0.95  thf('38', plain,
% 0.77/0.95      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_A) | (r2_hidden @ sk_A @ sk_B))),
% 0.77/0.95      inference('simplify', [status(thm)], ['37'])).
% 0.77/0.95  thf('39', plain, (![X46 : $i]: (r2_hidden @ X46 @ (k1_ordinal1 @ X46))),
% 0.77/0.95      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.77/0.95  thf('40', plain,
% 0.77/0.95      (![X47 : $i, X48 : $i]:
% 0.77/0.95         (~ (r2_hidden @ X47 @ X48) | ~ (r1_tarski @ X48 @ X47))),
% 0.77/0.95      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.77/0.95  thf('41', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X0)),
% 0.77/0.95      inference('sup-', [status(thm)], ['39', '40'])).
% 0.77/0.95  thf('42', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.77/0.95      inference('clc', [status(thm)], ['38', '41'])).
% 0.77/0.95  thf('43', plain,
% 0.77/0.95      (![X37 : $i, X39 : $i]:
% 0.77/0.95         ((r1_tarski @ (k1_tarski @ X37) @ X39) | ~ (r2_hidden @ X37 @ X39))),
% 0.77/0.95      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.77/0.95  thf('44', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.77/0.95      inference('sup-', [status(thm)], ['42', '43'])).
% 0.77/0.95  thf('45', plain, (((r2_hidden @ sk_B @ sk_A) | (r1_tarski @ sk_A @ sk_B))),
% 0.77/0.95      inference('sup-', [status(thm)], ['7', '17'])).
% 0.77/0.95  thf('46', plain,
% 0.77/0.95      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.77/0.95         (~ (r1_tarski @ X13 @ X14)
% 0.77/0.95          | ~ (r1_tarski @ X15 @ X14)
% 0.77/0.95          | (r1_tarski @ (k2_xboole_0 @ X13 @ X15) @ X14))),
% 0.77/0.95      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.77/0.95  thf('47', plain,
% 0.77/0.95      (![X0 : $i]:
% 0.77/0.95         ((r2_hidden @ sk_B @ sk_A)
% 0.77/0.95          | (r1_tarski @ (k2_xboole_0 @ sk_A @ X0) @ sk_B)
% 0.77/0.95          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.77/0.95      inference('sup-', [status(thm)], ['45', '46'])).
% 0.77/0.95  thf('48', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.77/0.95      inference('clc', [status(thm)], ['38', '41'])).
% 0.77/0.95  thf(antisymmetry_r2_hidden, axiom,
% 0.77/0.95    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.77/0.95  thf('49', plain,
% 0.77/0.95      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.77/0.95      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.77/0.95  thf('50', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 0.77/0.95      inference('sup-', [status(thm)], ['48', '49'])).
% 0.77/0.95  thf('51', plain,
% 0.77/0.95      (![X0 : $i]:
% 0.77/0.95         (~ (r1_tarski @ X0 @ sk_B)
% 0.77/0.95          | (r1_tarski @ (k2_xboole_0 @ sk_A @ X0) @ sk_B))),
% 0.77/0.95      inference('clc', [status(thm)], ['47', '50'])).
% 0.77/0.95  thf('52', plain,
% 0.77/0.95      ((r1_tarski @ (k2_xboole_0 @ sk_A @ (k1_tarski @ sk_A)) @ sk_B)),
% 0.77/0.95      inference('sup-', [status(thm)], ['44', '51'])).
% 0.77/0.95  thf('53', plain,
% 0.77/0.95      (![X45 : $i]:
% 0.77/0.95         ((k1_ordinal1 @ X45) = (k2_xboole_0 @ X45 @ (k1_tarski @ X45)))),
% 0.77/0.95      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.77/0.95  thf('54', plain, ((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 0.77/0.95      inference('demod', [status(thm)], ['52', '53'])).
% 0.77/0.95  thf('55', plain, ($false), inference('demod', [status(thm)], ['4', '54'])).
% 0.77/0.95  
% 0.77/0.95  % SZS output end Refutation
% 0.77/0.95  
% 0.77/0.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.57FQ19ZWPV

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:43 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 200 expanded)
%              Number of leaves         :   20 (  65 expanded)
%              Depth                    :   14
%              Number of atoms          :  489 (1610 expanded)
%              Number of equality atoms :   64 ( 252 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t44_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ( B != C )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ( B != C )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t44_zfmisc_1])).

thf('1',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('3',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('9',plain,(
    ! [X21: $i] :
      ( ( k2_tarski @ X21 @ X21 )
      = ( k1_tarski @ X21 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('10',plain,(
    ! [X15: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X17 )
      | ( X19 = X18 )
      | ( X19 = X15 )
      | ( X17
       != ( k2_tarski @ X18 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('11',plain,(
    ! [X15: $i,X18: $i,X19: $i] :
      ( ( X19 = X15 )
      | ( X19 = X18 )
      | ~ ( r2_hidden @ X19 @ ( k2_tarski @ X18 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( sk_B @ sk_B_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('16',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    | ( sk_B_1
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','24'])).

thf('26',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('27',plain,
    ( ( sk_B @ sk_B_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['8','13'])).

thf('28',plain,
    ( ( sk_B_1
      = ( k1_tarski @ sk_A ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( X5 != X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('33',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['32'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('34',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X8 @ ( k2_xboole_0 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r1_tarski @ sk_C_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['31','35'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('37',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('38',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('40',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C_1 ) @ ( k1_tarski @ sk_A ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','43'])).

thf('45',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    r2_hidden @ ( sk_B @ sk_C_1 ) @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('48',plain,
    ( ( sk_B @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('50',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k1_tarski @ sk_A ) )
    | ( sk_C_1
      = ( k1_tarski @ ( sk_B @ sk_C_1 ) ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    r1_tarski @ sk_C_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['31','35'])).

thf('52',plain,
    ( ( sk_B @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['46','47'])).

thf('53',plain,
    ( ( sk_C_1
      = ( k1_tarski @ sk_A ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( sk_C_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['53','54'])).

thf('56',plain,(
    sk_C_1 = sk_B_1 ),
    inference('sup+',[status(thm)],['30','55'])).

thf('57',plain,(
    sk_B_1 != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['56','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.57FQ19ZWPV
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:12:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.51  % Solved by: fo/fo7.sh
% 0.19/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.51  % done 176 iterations in 0.060s
% 0.19/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.51  % SZS output start Refutation
% 0.19/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.51  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.51  thf(t7_xboole_0, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.19/0.51          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.19/0.51  thf('0', plain,
% 0.19/0.51      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.19/0.51      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.19/0.51  thf(t44_zfmisc_1, conjecture,
% 0.19/0.51    (![A:$i,B:$i,C:$i]:
% 0.19/0.51     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.19/0.51          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.51          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.19/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.51        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.19/0.51             ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.51             ( ( C ) != ( k1_xboole_0 ) ) ) ) )),
% 0.19/0.51    inference('cnf.neg', [status(esa)], [t44_zfmisc_1])).
% 0.19/0.51  thf('1', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(t7_xboole_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.19/0.51  thf('2', plain,
% 0.19/0.51      (![X13 : $i, X14 : $i]: (r1_tarski @ X13 @ (k2_xboole_0 @ X13 @ X14))),
% 0.19/0.51      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.19/0.51  thf('3', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.19/0.51      inference('sup+', [status(thm)], ['1', '2'])).
% 0.19/0.51  thf(d3_tarski, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( r1_tarski @ A @ B ) <=>
% 0.19/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.19/0.51  thf('4', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.51         (~ (r2_hidden @ X0 @ X1)
% 0.19/0.51          | (r2_hidden @ X0 @ X2)
% 0.19/0.51          | ~ (r1_tarski @ X1 @ X2))),
% 0.19/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.51  thf('5', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((r2_hidden @ X0 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.19/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.51  thf('6', plain,
% 0.19/0.51      ((((sk_B_1) = (k1_xboole_0))
% 0.19/0.51        | (r2_hidden @ (sk_B @ sk_B_1) @ (k1_tarski @ sk_A)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['0', '5'])).
% 0.19/0.51  thf('7', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('8', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (k1_tarski @ sk_A))),
% 0.19/0.51      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.19/0.51  thf(t69_enumset1, axiom,
% 0.19/0.51    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.19/0.51  thf('9', plain, (![X21 : $i]: ((k2_tarski @ X21 @ X21) = (k1_tarski @ X21))),
% 0.19/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.51  thf(d2_tarski, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i]:
% 0.19/0.51     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.19/0.51       ( ![D:$i]:
% 0.19/0.51         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.19/0.51  thf('10', plain,
% 0.19/0.51      (![X15 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.19/0.51         (~ (r2_hidden @ X19 @ X17)
% 0.19/0.51          | ((X19) = (X18))
% 0.19/0.51          | ((X19) = (X15))
% 0.19/0.51          | ((X17) != (k2_tarski @ X18 @ X15)))),
% 0.19/0.51      inference('cnf', [status(esa)], [d2_tarski])).
% 0.19/0.51  thf('11', plain,
% 0.19/0.51      (![X15 : $i, X18 : $i, X19 : $i]:
% 0.19/0.51         (((X19) = (X15))
% 0.19/0.51          | ((X19) = (X18))
% 0.19/0.51          | ~ (r2_hidden @ X19 @ (k2_tarski @ X18 @ X15)))),
% 0.19/0.51      inference('simplify', [status(thm)], ['10'])).
% 0.19/0.51  thf('12', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['9', '11'])).
% 0.19/0.51  thf('13', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.19/0.51      inference('simplify', [status(thm)], ['12'])).
% 0.19/0.51  thf('14', plain, (((sk_B @ sk_B_1) = (sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['8', '13'])).
% 0.19/0.51  thf('15', plain,
% 0.19/0.51      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.19/0.51      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.19/0.51  thf('16', plain,
% 0.19/0.51      (![X1 : $i, X3 : $i]:
% 0.19/0.51         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.19/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.51  thf('17', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.19/0.51      inference('simplify', [status(thm)], ['12'])).
% 0.19/0.51  thf('18', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.19/0.51          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.51  thf('19', plain,
% 0.19/0.51      (![X1 : $i, X3 : $i]:
% 0.19/0.51         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.19/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.51  thf('20', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (~ (r2_hidden @ X0 @ X1)
% 0.19/0.51          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.19/0.51          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.19/0.51      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.51  thf('21', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.19/0.51      inference('simplify', [status(thm)], ['20'])).
% 0.19/0.51  thf('22', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (((X0) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['15', '21'])).
% 0.19/0.51  thf(d10_xboole_0, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.51  thf('23', plain,
% 0.19/0.51      (![X5 : $i, X7 : $i]:
% 0.19/0.51         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 0.19/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.51  thf('24', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (((X0) = (k1_xboole_0))
% 0.19/0.51          | ~ (r1_tarski @ X0 @ (k1_tarski @ (sk_B @ X0)))
% 0.19/0.51          | ((X0) = (k1_tarski @ (sk_B @ X0))))),
% 0.19/0.51      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.51  thf('25', plain,
% 0.19/0.51      ((~ (r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.19/0.51        | ((sk_B_1) = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.19/0.51        | ((sk_B_1) = (k1_xboole_0)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['14', '24'])).
% 0.19/0.51  thf('26', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.19/0.51      inference('sup+', [status(thm)], ['1', '2'])).
% 0.19/0.51  thf('27', plain, (((sk_B @ sk_B_1) = (sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['8', '13'])).
% 0.19/0.51  thf('28', plain,
% 0.19/0.51      ((((sk_B_1) = (k1_tarski @ sk_A)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.19/0.51      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.19/0.51  thf('29', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('30', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 0.19/0.51      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 0.19/0.51  thf('31', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('32', plain,
% 0.19/0.51      (![X5 : $i, X6 : $i]: ((r1_tarski @ X5 @ X6) | ((X5) != (X6)))),
% 0.19/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.51  thf('33', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 0.19/0.51      inference('simplify', [status(thm)], ['32'])).
% 0.19/0.51  thf(t10_xboole_1, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i]:
% 0.19/0.51     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.19/0.51  thf('34', plain,
% 0.19/0.51      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.19/0.51         (~ (r1_tarski @ X8 @ X9) | (r1_tarski @ X8 @ (k2_xboole_0 @ X10 @ X9)))),
% 0.19/0.51      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.19/0.51  thf('35', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['33', '34'])).
% 0.19/0.51  thf('36', plain, ((r1_tarski @ sk_C_1 @ (k1_tarski @ sk_A))),
% 0.19/0.51      inference('sup+', [status(thm)], ['31', '35'])).
% 0.19/0.51  thf(t12_xboole_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.19/0.51  thf('37', plain,
% 0.19/0.51      (![X11 : $i, X12 : $i]:
% 0.19/0.51         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 0.19/0.51      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.19/0.51  thf('38', plain,
% 0.19/0.51      (((k2_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['36', '37'])).
% 0.19/0.51  thf('39', plain,
% 0.19/0.51      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.19/0.51      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.19/0.51  thf('40', plain,
% 0.19/0.51      (![X13 : $i, X14 : $i]: (r1_tarski @ X13 @ (k2_xboole_0 @ X13 @ X14))),
% 0.19/0.51      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.19/0.51  thf('41', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.51         (~ (r2_hidden @ X0 @ X1)
% 0.19/0.51          | (r2_hidden @ X0 @ X2)
% 0.19/0.51          | ~ (r1_tarski @ X1 @ X2))),
% 0.19/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.51  thf('42', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.51         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X1))),
% 0.19/0.51      inference('sup-', [status(thm)], ['40', '41'])).
% 0.19/0.51  thf('43', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (((X0) = (k1_xboole_0))
% 0.19/0.51          | (r2_hidden @ (sk_B @ X0) @ (k2_xboole_0 @ X0 @ X1)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['39', '42'])).
% 0.19/0.51  thf('44', plain,
% 0.19/0.51      (((r2_hidden @ (sk_B @ sk_C_1) @ (k1_tarski @ sk_A))
% 0.19/0.51        | ((sk_C_1) = (k1_xboole_0)))),
% 0.19/0.51      inference('sup+', [status(thm)], ['38', '43'])).
% 0.19/0.51  thf('45', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('46', plain, ((r2_hidden @ (sk_B @ sk_C_1) @ (k1_tarski @ sk_A))),
% 0.19/0.51      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 0.19/0.51  thf('47', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.19/0.51      inference('simplify', [status(thm)], ['12'])).
% 0.19/0.51  thf('48', plain, (((sk_B @ sk_C_1) = (sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['46', '47'])).
% 0.19/0.51  thf('49', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (((X0) = (k1_xboole_0))
% 0.19/0.51          | ~ (r1_tarski @ X0 @ (k1_tarski @ (sk_B @ X0)))
% 0.19/0.51          | ((X0) = (k1_tarski @ (sk_B @ X0))))),
% 0.19/0.51      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.51  thf('50', plain,
% 0.19/0.51      ((~ (r1_tarski @ sk_C_1 @ (k1_tarski @ sk_A))
% 0.19/0.51        | ((sk_C_1) = (k1_tarski @ (sk_B @ sk_C_1)))
% 0.19/0.51        | ((sk_C_1) = (k1_xboole_0)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['48', '49'])).
% 0.19/0.51  thf('51', plain, ((r1_tarski @ sk_C_1 @ (k1_tarski @ sk_A))),
% 0.19/0.51      inference('sup+', [status(thm)], ['31', '35'])).
% 0.19/0.51  thf('52', plain, (((sk_B @ sk_C_1) = (sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['46', '47'])).
% 0.19/0.51  thf('53', plain,
% 0.19/0.51      ((((sk_C_1) = (k1_tarski @ sk_A)) | ((sk_C_1) = (k1_xboole_0)))),
% 0.19/0.51      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.19/0.51  thf('54', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('55', plain, (((sk_C_1) = (k1_tarski @ sk_A))),
% 0.19/0.51      inference('simplify_reflect-', [status(thm)], ['53', '54'])).
% 0.19/0.51  thf('56', plain, (((sk_C_1) = (sk_B_1))),
% 0.19/0.51      inference('sup+', [status(thm)], ['30', '55'])).
% 0.19/0.51  thf('57', plain, (((sk_B_1) != (sk_C_1))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('58', plain, ($false),
% 0.19/0.51      inference('simplify_reflect-', [status(thm)], ['56', '57'])).
% 0.19/0.51  
% 0.19/0.51  % SZS output end Refutation
% 0.19/0.51  
% 0.19/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

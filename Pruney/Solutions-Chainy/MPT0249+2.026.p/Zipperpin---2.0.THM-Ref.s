%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xb1RKXV4yd

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:42 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 416 expanded)
%              Number of leaves         :   17 ( 127 expanded)
%              Depth                    :   19
%              Number of atoms          :  485 (3468 expanded)
%              Number of equality atoms :   58 ( 538 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('2',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('4',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('10',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X18 )
      | ( X19 = X16 )
      | ( X18
       != ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('11',plain,(
    ! [X16: $i,X19: $i] :
      ( ( X19 = X16 )
      | ~ ( r2_hidden @ X19 @ ( k1_tarski @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ( sk_B @ sk_B_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('14',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    ! [X16: $i,X19: $i] :
      ( ( X19 = X16 )
      | ~ ( r2_hidden @ X19 @ ( k1_tarski @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X11: $i,X13: $i] :
      ( ( X11 = X13 )
      | ~ ( r1_tarski @ X13 @ X11 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    | ( sk_B_1
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','22'])).

thf('24',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('25',plain,
    ( ( sk_B @ sk_B_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['9','11'])).

thf('26',plain,
    ( ( sk_B_1
      = ( k1_tarski @ sk_A ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['26','27'])).

thf('29',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['0','28'])).

thf('30',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('31',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ( X6
       != ( k2_xboole_0 @ X7 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('32',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ ( k2_xboole_0 @ X7 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X11: $i,X13: $i] :
      ( ( X11 = X13 )
      | ~ ( r1_tarski @ X13 @ X11 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_C_2 )
    | ( ( k2_xboole_0 @ sk_B_1 @ sk_C_2 )
      = sk_C_2 ) ),
    inference('sup-',[status(thm)],['29','38'])).

thf('40',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['0','28'])).

thf('41',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('42',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ ( k2_xboole_0 @ X7 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C_2 ) @ sk_B_1 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf('45',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    r2_hidden @ ( sk_B @ sk_C_2 ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).

thf('47',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['26','27'])).

thf('48',plain,(
    ! [X16: $i,X19: $i] :
      ( ( X19 = X16 )
      | ~ ( r2_hidden @ X19 @ ( k1_tarski @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_B @ sk_C_2 )
    = sk_A ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('52',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C_2 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['26','27'])).

thf('54',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_C_2 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    r1_tarski @ sk_B_1 @ sk_C_2 ),
    inference('simplify_reflect-',[status(thm)],['54','55'])).

thf('57',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['0','28'])).

thf('58',plain,(
    sk_B_1 = sk_C_2 ),
    inference(demod,[status(thm)],['39','56','57'])).

thf('59',plain,(
    sk_B_1 != sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['58','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xb1RKXV4yd
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:47:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.47/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.66  % Solved by: fo/fo7.sh
% 0.47/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.66  % done 507 iterations in 0.203s
% 0.47/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.66  % SZS output start Refutation
% 0.47/0.66  thf(sk_B_type, type, sk_B: $i > $i).
% 0.47/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.66  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.47/0.66  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.47/0.66  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.47/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.66  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.47/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.66  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.47/0.66  thf(t44_zfmisc_1, conjecture,
% 0.47/0.66    (![A:$i,B:$i,C:$i]:
% 0.47/0.66     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.47/0.66          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.47/0.66          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.47/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.66    (~( ![A:$i,B:$i,C:$i]:
% 0.47/0.66        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.47/0.66             ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.47/0.66             ( ( C ) != ( k1_xboole_0 ) ) ) ) )),
% 0.47/0.66    inference('cnf.neg', [status(esa)], [t44_zfmisc_1])).
% 0.47/0.66  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(t7_xboole_0, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.47/0.66          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.47/0.66  thf('1', plain,
% 0.47/0.66      (![X10 : $i]:
% 0.47/0.66         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.47/0.66      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.47/0.66  thf('2', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(t7_xboole_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.47/0.66  thf('3', plain,
% 0.47/0.66      (![X14 : $i, X15 : $i]: (r1_tarski @ X14 @ (k2_xboole_0 @ X14 @ X15))),
% 0.47/0.66      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.47/0.66  thf('4', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.47/0.66      inference('sup+', [status(thm)], ['2', '3'])).
% 0.47/0.66  thf(d3_tarski, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( r1_tarski @ A @ B ) <=>
% 0.47/0.66       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.47/0.66  thf('5', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.66         (~ (r2_hidden @ X0 @ X1)
% 0.47/0.66          | (r2_hidden @ X0 @ X2)
% 0.47/0.66          | ~ (r1_tarski @ X1 @ X2))),
% 0.47/0.66      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.66  thf('6', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((r2_hidden @ X0 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.47/0.66      inference('sup-', [status(thm)], ['4', '5'])).
% 0.47/0.66  thf('7', plain,
% 0.47/0.66      ((((sk_B_1) = (k1_xboole_0))
% 0.47/0.66        | (r2_hidden @ (sk_B @ sk_B_1) @ (k1_tarski @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['1', '6'])).
% 0.47/0.66  thf('8', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('9', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (k1_tarski @ sk_A))),
% 0.47/0.66      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.47/0.66  thf(d1_tarski, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.47/0.66       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.47/0.66  thf('10', plain,
% 0.47/0.66      (![X16 : $i, X18 : $i, X19 : $i]:
% 0.47/0.66         (~ (r2_hidden @ X19 @ X18)
% 0.47/0.66          | ((X19) = (X16))
% 0.47/0.66          | ((X18) != (k1_tarski @ X16)))),
% 0.47/0.66      inference('cnf', [status(esa)], [d1_tarski])).
% 0.47/0.66  thf('11', plain,
% 0.47/0.66      (![X16 : $i, X19 : $i]:
% 0.47/0.66         (((X19) = (X16)) | ~ (r2_hidden @ X19 @ (k1_tarski @ X16)))),
% 0.47/0.66      inference('simplify', [status(thm)], ['10'])).
% 0.47/0.66  thf('12', plain, (((sk_B @ sk_B_1) = (sk_A))),
% 0.47/0.66      inference('sup-', [status(thm)], ['9', '11'])).
% 0.47/0.66  thf('13', plain,
% 0.47/0.66      (![X10 : $i]:
% 0.47/0.66         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.47/0.66      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.47/0.66  thf('14', plain,
% 0.47/0.66      (![X1 : $i, X3 : $i]:
% 0.47/0.66         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.47/0.66      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.66  thf('15', plain,
% 0.47/0.66      (![X16 : $i, X19 : $i]:
% 0.47/0.66         (((X19) = (X16)) | ~ (r2_hidden @ X19 @ (k1_tarski @ X16)))),
% 0.47/0.66      inference('simplify', [status(thm)], ['10'])).
% 0.47/0.66  thf('16', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.47/0.66          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['14', '15'])).
% 0.47/0.66  thf('17', plain,
% 0.47/0.66      (![X1 : $i, X3 : $i]:
% 0.47/0.66         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.47/0.66      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.66  thf('18', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (~ (r2_hidden @ X0 @ X1)
% 0.47/0.66          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.47/0.66          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.47/0.66      inference('sup-', [status(thm)], ['16', '17'])).
% 0.47/0.66  thf('19', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.47/0.66      inference('simplify', [status(thm)], ['18'])).
% 0.47/0.66  thf('20', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (((X0) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['13', '19'])).
% 0.47/0.66  thf(d10_xboole_0, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.47/0.66  thf('21', plain,
% 0.47/0.66      (![X11 : $i, X13 : $i]:
% 0.47/0.66         (((X11) = (X13))
% 0.47/0.66          | ~ (r1_tarski @ X13 @ X11)
% 0.47/0.66          | ~ (r1_tarski @ X11 @ X13))),
% 0.47/0.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.66  thf('22', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (((X0) = (k1_xboole_0))
% 0.47/0.66          | ~ (r1_tarski @ X0 @ (k1_tarski @ (sk_B @ X0)))
% 0.47/0.66          | ((X0) = (k1_tarski @ (sk_B @ X0))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['20', '21'])).
% 0.47/0.66  thf('23', plain,
% 0.47/0.66      ((~ (r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.47/0.66        | ((sk_B_1) = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.47/0.66        | ((sk_B_1) = (k1_xboole_0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['12', '22'])).
% 0.47/0.66  thf('24', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.47/0.66      inference('sup+', [status(thm)], ['2', '3'])).
% 0.47/0.66  thf('25', plain, (((sk_B @ sk_B_1) = (sk_A))),
% 0.47/0.66      inference('sup-', [status(thm)], ['9', '11'])).
% 0.47/0.66  thf('26', plain,
% 0.47/0.66      ((((sk_B_1) = (k1_tarski @ sk_A)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.47/0.66      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.47/0.66  thf('27', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('28', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 0.47/0.66      inference('simplify_reflect-', [status(thm)], ['26', '27'])).
% 0.47/0.66  thf('29', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.47/0.66      inference('demod', [status(thm)], ['0', '28'])).
% 0.47/0.66  thf('30', plain,
% 0.47/0.66      (![X1 : $i, X3 : $i]:
% 0.47/0.66         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.47/0.66      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.66  thf(d3_xboole_0, axiom,
% 0.47/0.66    (![A:$i,B:$i,C:$i]:
% 0.47/0.66     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.47/0.66       ( ![D:$i]:
% 0.47/0.66         ( ( r2_hidden @ D @ C ) <=>
% 0.47/0.66           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.47/0.66  thf('31', plain,
% 0.47/0.66      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.47/0.66         (~ (r2_hidden @ X4 @ X5)
% 0.47/0.66          | (r2_hidden @ X4 @ X6)
% 0.47/0.66          | ((X6) != (k2_xboole_0 @ X7 @ X5)))),
% 0.47/0.66      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.47/0.66  thf('32', plain,
% 0.47/0.66      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.47/0.66         ((r2_hidden @ X4 @ (k2_xboole_0 @ X7 @ X5)) | ~ (r2_hidden @ X4 @ X5))),
% 0.47/0.66      inference('simplify', [status(thm)], ['31'])).
% 0.47/0.66  thf('33', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.66         ((r1_tarski @ X0 @ X1)
% 0.47/0.66          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_xboole_0 @ X2 @ X0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['30', '32'])).
% 0.47/0.66  thf('34', plain,
% 0.47/0.66      (![X1 : $i, X3 : $i]:
% 0.47/0.66         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.47/0.66      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.66  thf('35', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         ((r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.47/0.66          | (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['33', '34'])).
% 0.47/0.66  thf('36', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.47/0.66      inference('simplify', [status(thm)], ['35'])).
% 0.47/0.66  thf('37', plain,
% 0.47/0.66      (![X11 : $i, X13 : $i]:
% 0.47/0.66         (((X11) = (X13))
% 0.47/0.66          | ~ (r1_tarski @ X13 @ X11)
% 0.47/0.66          | ~ (r1_tarski @ X11 @ X13))),
% 0.47/0.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.66  thf('38', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 0.47/0.66          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['36', '37'])).
% 0.47/0.66  thf('39', plain,
% 0.47/0.66      ((~ (r1_tarski @ sk_B_1 @ sk_C_2)
% 0.47/0.66        | ((k2_xboole_0 @ sk_B_1 @ sk_C_2) = (sk_C_2)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['29', '38'])).
% 0.47/0.66  thf('40', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.47/0.66      inference('demod', [status(thm)], ['0', '28'])).
% 0.47/0.66  thf('41', plain,
% 0.47/0.66      (![X10 : $i]:
% 0.47/0.66         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.47/0.66      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.47/0.66  thf('42', plain,
% 0.47/0.66      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.47/0.66         ((r2_hidden @ X4 @ (k2_xboole_0 @ X7 @ X5)) | ~ (r2_hidden @ X4 @ X5))),
% 0.47/0.66      inference('simplify', [status(thm)], ['31'])).
% 0.47/0.66  thf('43', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (((X0) = (k1_xboole_0))
% 0.47/0.66          | (r2_hidden @ (sk_B @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['41', '42'])).
% 0.47/0.66  thf('44', plain,
% 0.47/0.66      (((r2_hidden @ (sk_B @ sk_C_2) @ sk_B_1) | ((sk_C_2) = (k1_xboole_0)))),
% 0.47/0.66      inference('sup+', [status(thm)], ['40', '43'])).
% 0.47/0.66  thf('45', plain, (((sk_C_2) != (k1_xboole_0))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('46', plain, ((r2_hidden @ (sk_B @ sk_C_2) @ sk_B_1)),
% 0.47/0.66      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 0.47/0.66  thf('47', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 0.47/0.66      inference('simplify_reflect-', [status(thm)], ['26', '27'])).
% 0.47/0.66  thf('48', plain,
% 0.47/0.66      (![X16 : $i, X19 : $i]:
% 0.47/0.66         (((X19) = (X16)) | ~ (r2_hidden @ X19 @ (k1_tarski @ X16)))),
% 0.47/0.66      inference('simplify', [status(thm)], ['10'])).
% 0.47/0.66  thf('49', plain,
% 0.47/0.66      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_B_1) | ((X0) = (sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['47', '48'])).
% 0.47/0.66  thf('50', plain, (((sk_B @ sk_C_2) = (sk_A))),
% 0.47/0.66      inference('sup-', [status(thm)], ['46', '49'])).
% 0.47/0.66  thf('51', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (((X0) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['13', '19'])).
% 0.47/0.66  thf('52', plain,
% 0.47/0.66      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_C_2) | ((sk_C_2) = (k1_xboole_0)))),
% 0.47/0.66      inference('sup+', [status(thm)], ['50', '51'])).
% 0.47/0.66  thf('53', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 0.47/0.66      inference('simplify_reflect-', [status(thm)], ['26', '27'])).
% 0.47/0.66  thf('54', plain,
% 0.47/0.66      (((r1_tarski @ sk_B_1 @ sk_C_2) | ((sk_C_2) = (k1_xboole_0)))),
% 0.47/0.66      inference('demod', [status(thm)], ['52', '53'])).
% 0.47/0.66  thf('55', plain, (((sk_C_2) != (k1_xboole_0))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('56', plain, ((r1_tarski @ sk_B_1 @ sk_C_2)),
% 0.47/0.66      inference('simplify_reflect-', [status(thm)], ['54', '55'])).
% 0.47/0.66  thf('57', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.47/0.66      inference('demod', [status(thm)], ['0', '28'])).
% 0.47/0.66  thf('58', plain, (((sk_B_1) = (sk_C_2))),
% 0.47/0.66      inference('demod', [status(thm)], ['39', '56', '57'])).
% 0.47/0.66  thf('59', plain, (((sk_B_1) != (sk_C_2))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('60', plain, ($false),
% 0.47/0.66      inference('simplify_reflect-', [status(thm)], ['58', '59'])).
% 0.47/0.66  
% 0.47/0.66  % SZS output end Refutation
% 0.47/0.66  
% 0.47/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

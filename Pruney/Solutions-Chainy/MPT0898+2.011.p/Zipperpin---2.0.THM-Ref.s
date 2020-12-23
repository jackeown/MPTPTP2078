%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oQr29nBS7p

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 408 expanded)
%              Number of leaves         :   11 ( 118 expanded)
%              Depth                    :   21
%              Number of atoms          :  716 (5049 expanded)
%              Number of equality atoms :  144 ( 876 expanded)
%              Maximal formula depth    :   16 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t58_mcart_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_zfmisc_1 @ A @ A @ A @ A )
        = ( k4_zfmisc_1 @ B @ B @ B @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_zfmisc_1 @ A @ A @ A @ A )
          = ( k4_zfmisc_1 @ B @ B @ B @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t58_mcart_1])).

thf('0',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t55_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 ) )
    <=> ( ( k4_zfmisc_1 @ A @ B @ C @ D )
       != k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( ( k4_zfmisc_1 @ X13 @ X14 @ X15 @ X16 )
       != k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X14 = k1_xboole_0 )
      | ( X13 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('2',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
     != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t36_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( k3_zfmisc_1 @ A @ B @ C )
        = ( k3_zfmisc_1 @ D @ E @ F ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( C = k1_xboole_0 )
        | ( ( A = D )
          & ( B = E )
          & ( C = F ) ) ) ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X9 @ X8 @ X7 )
       != ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) )
      | ( X7 = X12 ) ) ),
    inference(cnf,[status(esa)],[t36_mcart_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k3_zfmisc_1 @ X6 @ X5 @ X4 )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X4 = X0 )
      | ( X6 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A ) )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X0 = sk_B ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A ) )
      | ( X0 = sk_B )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = sk_B ) ),
    inference(eq_res,[status(thm)],['14'])).

thf('16',plain,
    ( ( sk_A = sk_B )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_A @ sk_A @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X13: $i,X14: $i,X15: $i,X17: $i] :
      ( ( X17 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X13 @ X14 @ X15 @ X17 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('22',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_zfmisc_1 @ X13 @ X14 @ X15 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k3_zfmisc_1 @ X6 @ X5 @ X4 )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X4 = X0 )
      | ( X6 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('24',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( ( k3_zfmisc_1 @ X5 @ X4 @ X3 )
       != k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X5 @ X4 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X13: $i,X14: $i,X15: $i,X17: $i] :
      ( ( X14 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X13 @ X14 @ X15 @ X17 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('29',plain,(
    ! [X13: $i,X15: $i,X17: $i] :
      ( ( k4_zfmisc_1 @ X13 @ k1_xboole_0 @ X15 @ X17 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('31',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X5 @ X4 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X13: $i,X14: $i,X15: $i,X17: $i] :
      ( ( X15 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X13 @ X14 @ X15 @ X17 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('42',plain,(
    ! [X13: $i,X14: $i,X17: $i] :
      ( ( k4_zfmisc_1 @ X13 @ X14 @ k1_xboole_0 @ X17 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( k1_xboole_0 != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['27','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    sk_A = k1_xboole_0 ),
    inference(condensation,[status(thm)],['45'])).

thf('47',plain,(
    sk_A = k1_xboole_0 ),
    inference(condensation,[status(thm)],['45'])).

thf('48',plain,
    ( ( sk_B = sk_A )
    | ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
     != sk_A ) ),
    inference(demod,[status(thm)],['3','46','47'])).

thf('49',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
 != sk_A ),
    inference('simplify_reflect-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X13: $i,X14: $i,X15: $i,X17: $i] :
      ( ( X13 != k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X13 @ X14 @ X15 @ X17 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t55_mcart_1])).

thf('52',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ( k4_zfmisc_1 @ k1_xboole_0 @ X14 @ X15 @ X17 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    sk_A = k1_xboole_0 ),
    inference(condensation,[status(thm)],['45'])).

thf('54',plain,(
    sk_A = k1_xboole_0 ),
    inference(condensation,[status(thm)],['45'])).

thf('55',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ( k4_zfmisc_1 @ sk_A @ X14 @ X15 @ X17 )
      = sk_A ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['50','55'])).

thf('57',plain,(
    $false ),
    inference(simplify,[status(thm)],['56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oQr29nBS7p
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:10:10 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 50 iterations in 0.039s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.21/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.50  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.50  thf(t58_mcart_1, conjecture,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( k4_zfmisc_1 @ A @ A @ A @ A ) = ( k4_zfmisc_1 @ B @ B @ B @ B ) ) =>
% 0.21/0.50       ( ( A ) = ( B ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i]:
% 0.21/0.50        ( ( ( k4_zfmisc_1 @ A @ A @ A @ A ) = ( k4_zfmisc_1 @ B @ B @ B @ B ) ) =>
% 0.21/0.50          ( ( A ) = ( B ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t58_mcart_1])).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.21/0.50         = (k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t55_mcart_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.50     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.50         ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) ) <=>
% 0.21/0.50       ( ( k4_zfmisc_1 @ A @ B @ C @ D ) != ( k1_xboole_0 ) ) ))).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.50         (((k4_zfmisc_1 @ X13 @ X14 @ X15 @ X16) != (k1_xboole_0))
% 0.21/0.50          | ((X16) = (k1_xboole_0))
% 0.21/0.50          | ((X15) = (k1_xboole_0))
% 0.21/0.50          | ((X14) = (k1_xboole_0))
% 0.21/0.50          | ((X13) = (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      ((((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) != (k1_xboole_0))
% 0.21/0.50        | ((sk_B) = (k1_xboole_0))
% 0.21/0.50        | ((sk_B) = (k1_xboole_0))
% 0.21/0.50        | ((sk_B) = (k1_xboole_0))
% 0.21/0.50        | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      ((((sk_B) = (k1_xboole_0))
% 0.21/0.50        | ((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) != (k1_xboole_0)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.50  thf(d3_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.21/0.50       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         ((k3_zfmisc_1 @ X0 @ X1 @ X2)
% 0.21/0.50           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1) @ X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         ((k3_zfmisc_1 @ X0 @ X1 @ X2)
% 0.21/0.50           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1) @ X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.50         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.21/0.50           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 0.21/0.50      inference('sup+', [status(thm)], ['4', '5'])).
% 0.21/0.50  thf(d4_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.50     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.21/0.50       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.50         ((k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6)
% 0.21/0.50           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X4 @ X5) @ X6))),
% 0.21/0.50      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.50         ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.21/0.50           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.21/0.50         = (k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.50         ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.21/0.50           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.50  thf(t36_mcart_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.21/0.50     ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.21/0.50       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.50         ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.21/0.50         ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ) ))).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.50         (((X7) = (k1_xboole_0))
% 0.21/0.50          | ((X8) = (k1_xboole_0))
% 0.21/0.50          | ((X9) = (k1_xboole_0))
% 0.21/0.50          | ((k3_zfmisc_1 @ X9 @ X8 @ X7) != (k3_zfmisc_1 @ X10 @ X11 @ X12))
% 0.21/0.50          | ((X7) = (X12)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t36_mcart_1])).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.50         (((k3_zfmisc_1 @ X6 @ X5 @ X4) != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.50          | ((X4) = (X0))
% 0.21/0.50          | ((X6) = (k1_xboole_0))
% 0.21/0.50          | ((X5) = (k1_xboole_0))
% 0.21/0.50          | ((X4) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (((k3_zfmisc_1 @ X2 @ X1 @ X0)
% 0.21/0.50            != (k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A))
% 0.21/0.50          | ((X0) = (k1_xboole_0))
% 0.21/0.50          | ((X1) = (k1_xboole_0))
% 0.21/0.50          | ((X2) = (k1_xboole_0))
% 0.21/0.50          | ((X0) = (sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['9', '12'])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.50         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.21/0.50            != (k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A))
% 0.21/0.50          | ((X0) = (sk_B))
% 0.21/0.50          | ((k2_zfmisc_1 @ X3 @ X2) = (k1_xboole_0))
% 0.21/0.50          | ((X1) = (k1_xboole_0))
% 0.21/0.50          | ((X0) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['8', '13'])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      ((((sk_A) = (k1_xboole_0))
% 0.21/0.50        | ((sk_A) = (k1_xboole_0))
% 0.21/0.50        | ((k2_zfmisc_1 @ sk_A @ sk_A) = (k1_xboole_0))
% 0.21/0.50        | ((sk_A) = (sk_B)))),
% 0.21/0.50      inference('eq_res', [status(thm)], ['14'])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      ((((sk_A) = (sk_B))
% 0.21/0.50        | ((k2_zfmisc_1 @ sk_A @ sk_A) = (k1_xboole_0))
% 0.21/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.50  thf('17', plain, (((sk_A) != (sk_B))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      ((((k2_zfmisc_1 @ sk_A @ sk_A) = (k1_xboole_0))
% 0.21/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         ((k3_zfmisc_1 @ X0 @ X1 @ X2)
% 0.21/0.50           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1) @ X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((k3_zfmisc_1 @ sk_A @ sk_A @ X0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.21/0.50          | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup+', [status(thm)], ['18', '19'])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      (![X13 : $i, X14 : $i, X15 : $i, X17 : $i]:
% 0.21/0.50         (((X17) != (k1_xboole_0))
% 0.21/0.50          | ((k4_zfmisc_1 @ X13 @ X14 @ X15 @ X17) = (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.50         ((k4_zfmisc_1 @ X13 @ X14 @ X15 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['21'])).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.50         (((k3_zfmisc_1 @ X6 @ X5 @ X4) != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.50          | ((X4) = (X0))
% 0.21/0.50          | ((X6) = (k1_xboole_0))
% 0.21/0.50          | ((X5) = (k1_xboole_0))
% 0.21/0.50          | ((X4) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.50         (((k3_zfmisc_1 @ X5 @ X4 @ X3) != (k1_xboole_0))
% 0.21/0.50          | ((X3) = (k1_xboole_0))
% 0.21/0.50          | ((X4) = (k1_xboole_0))
% 0.21/0.50          | ((X5) = (k1_xboole_0))
% 0.21/0.50          | ((X3) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.50         (((X5) = (k1_xboole_0))
% 0.21/0.50          | ((X4) = (k1_xboole_0))
% 0.21/0.50          | ((X3) = (k1_xboole_0))
% 0.21/0.50          | ((k3_zfmisc_1 @ X5 @ X4 @ X3) != (k1_xboole_0)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((k2_zfmisc_1 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 0.21/0.50          | ((sk_A) = (k1_xboole_0))
% 0.21/0.50          | ((X0) = (k1_xboole_0))
% 0.21/0.50          | ((sk_A) = (k1_xboole_0))
% 0.21/0.50          | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['20', '25'])).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((X0) = (k1_xboole_0))
% 0.21/0.50          | ((sk_A) = (k1_xboole_0))
% 0.21/0.50          | ((k2_zfmisc_1 @ k1_xboole_0 @ X0) != (k1_xboole_0)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      (![X13 : $i, X14 : $i, X15 : $i, X17 : $i]:
% 0.21/0.50         (((X14) != (k1_xboole_0))
% 0.21/0.50          | ((k4_zfmisc_1 @ X13 @ X14 @ X15 @ X17) = (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      (![X13 : $i, X15 : $i, X17 : $i]:
% 0.21/0.50         ((k4_zfmisc_1 @ X13 @ k1_xboole_0 @ X15 @ X17) = (k1_xboole_0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['28'])).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.50         ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.21/0.50           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.50         (((X5) = (k1_xboole_0))
% 0.21/0.50          | ((X4) = (k1_xboole_0))
% 0.21/0.50          | ((X3) = (k1_xboole_0))
% 0.21/0.50          | ((k3_zfmisc_1 @ X5 @ X4 @ X3) != (k1_xboole_0)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.50         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 0.21/0.50          | ((X0) = (k1_xboole_0))
% 0.21/0.50          | ((X1) = (k1_xboole_0))
% 0.21/0.50          | ((k2_zfmisc_1 @ X3 @ X2) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.50          | ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))
% 0.21/0.50          | ((X1) = (k1_xboole_0))
% 0.21/0.50          | ((X0) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['29', '32'])).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (((X0) = (k1_xboole_0))
% 0.21/0.50          | ((X1) = (k1_xboole_0))
% 0.21/0.50          | ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['33'])).
% 0.21/0.50  thf('35', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((k2_zfmisc_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.21/0.50          | ((X1) = (k1_xboole_0)))),
% 0.21/0.50      inference('condensation', [status(thm)], ['34'])).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      (![X0 : $i]: ((k2_zfmisc_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('condensation', [status(thm)], ['35'])).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         ((k3_zfmisc_1 @ X0 @ X1 @ X2)
% 0.21/0.50           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1) @ X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.50  thf('38', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((k3_zfmisc_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['36', '37'])).
% 0.21/0.50  thf('39', plain,
% 0.21/0.50      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.50         ((k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6)
% 0.21/0.50           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X4 @ X5) @ X6))),
% 0.21/0.50      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.21/0.50  thf('40', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         ((k4_zfmisc_1 @ X2 @ X1 @ k1_xboole_0 @ X0)
% 0.21/0.50           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['38', '39'])).
% 0.21/0.50  thf('41', plain,
% 0.21/0.50      (![X13 : $i, X14 : $i, X15 : $i, X17 : $i]:
% 0.21/0.50         (((X15) != (k1_xboole_0))
% 0.21/0.50          | ((k4_zfmisc_1 @ X13 @ X14 @ X15 @ X17) = (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.21/0.50  thf('42', plain,
% 0.21/0.50      (![X13 : $i, X14 : $i, X17 : $i]:
% 0.21/0.50         ((k4_zfmisc_1 @ X13 @ X14 @ k1_xboole_0 @ X17) = (k1_xboole_0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['41'])).
% 0.21/0.50  thf('43', plain,
% 0.21/0.50      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['40', '42'])).
% 0.21/0.50  thf('44', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((X0) = (k1_xboole_0))
% 0.21/0.50          | ((sk_A) = (k1_xboole_0))
% 0.21/0.50          | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['27', '43'])).
% 0.21/0.50  thf('45', plain,
% 0.21/0.50      (![X0 : $i]: (((sk_A) = (k1_xboole_0)) | ((X0) = (k1_xboole_0)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['44'])).
% 0.21/0.50  thf('46', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.50      inference('condensation', [status(thm)], ['45'])).
% 0.21/0.50  thf('47', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.50      inference('condensation', [status(thm)], ['45'])).
% 0.21/0.50  thf('48', plain,
% 0.21/0.50      ((((sk_B) = (sk_A))
% 0.21/0.50        | ((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) != (sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['3', '46', '47'])).
% 0.21/0.50  thf('49', plain, (((sk_A) != (sk_B))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('50', plain, (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) != (sk_A))),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['48', '49'])).
% 0.21/0.50  thf('51', plain,
% 0.21/0.50      (![X13 : $i, X14 : $i, X15 : $i, X17 : $i]:
% 0.21/0.50         (((X13) != (k1_xboole_0))
% 0.21/0.50          | ((k4_zfmisc_1 @ X13 @ X14 @ X15 @ X17) = (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t55_mcart_1])).
% 0.21/0.50  thf('52', plain,
% 0.21/0.50      (![X14 : $i, X15 : $i, X17 : $i]:
% 0.21/0.50         ((k4_zfmisc_1 @ k1_xboole_0 @ X14 @ X15 @ X17) = (k1_xboole_0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['51'])).
% 0.21/0.50  thf('53', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.50      inference('condensation', [status(thm)], ['45'])).
% 0.21/0.50  thf('54', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.50      inference('condensation', [status(thm)], ['45'])).
% 0.21/0.50  thf('55', plain,
% 0.21/0.50      (![X14 : $i, X15 : $i, X17 : $i]:
% 0.21/0.50         ((k4_zfmisc_1 @ sk_A @ X14 @ X15 @ X17) = (sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.21/0.50  thf('56', plain, (((sk_A) != (sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['50', '55'])).
% 0.21/0.50  thf('57', plain, ($false), inference('simplify', [status(thm)], ['56'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

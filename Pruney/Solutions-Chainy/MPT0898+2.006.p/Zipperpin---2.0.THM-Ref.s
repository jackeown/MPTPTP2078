%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UJHvQLnkkL

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:43 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 373 expanded)
%              Number of leaves         :   11 ( 113 expanded)
%              Depth                    :   18
%              Number of atoms          :  674 (4620 expanded)
%              Number of equality atoms :  132 ( 774 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('2',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X6 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
     != k1_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_B @ sk_B @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('14',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X6 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

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

thf('18',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X16 @ X15 @ X14 )
       != ( k3_zfmisc_1 @ X17 @ X18 @ X19 ) )
      | ( X14 = X19 ) ) ),
    inference(cnf,[status(esa)],[t36_mcart_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k3_zfmisc_1 @ X6 @ X5 @ X4 )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X4 = X0 )
      | ( X6 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A ) )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X0 = sk_B ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A ) )
      | ( X0 = sk_B )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = sk_B ) ),
    inference(eq_res,[status(thm)],['21'])).

thf('23',plain,
    ( ( sk_A = sk_B )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('27',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['27'])).

thf('30',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['27'])).

thf('31',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
     != sk_A )
    | ( ( k3_zfmisc_1 @ sk_B @ sk_B @ sk_B )
      = sk_A )
    | ( sk_B = sk_A ) ),
    inference(demod,[status(thm)],['12','28','29','30'])).

thf('32',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
     != sk_A )
    | ( ( k3_zfmisc_1 @ sk_B @ sk_B @ sk_B )
      = sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X6 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('35',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('36',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['34','36'])).

thf('38',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['27'])).

thf('39',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['27'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_A )
      = sk_A ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( sk_A != sk_A )
    | ( ( k3_zfmisc_1 @ sk_B @ sk_B @ sk_B )
      = sk_A ) ),
    inference(demod,[status(thm)],['33','40'])).

thf('42',plain,
    ( ( k3_zfmisc_1 @ sk_B @ sk_B @ sk_B )
    = sk_A ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['34','36'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( k3_zfmisc_1 @ X6 @ X5 @ X4 )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X4 = X0 )
      | ( X6 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('45',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( ( k3_zfmisc_1 @ X5 @ X4 @ X3 )
       != k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X5 @ X4 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['27'])).

thf('48',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['27'])).

thf('49',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['27'])).

thf('50',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['27'])).

thf('51',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( X5 = sk_A )
      | ( X4 = sk_A )
      | ( X3 = sk_A )
      | ( ( k3_zfmisc_1 @ X5 @ X4 @ X3 )
       != sk_A ) ) ),
    inference(demod,[status(thm)],['46','47','48','49','50'])).

thf('52',plain,
    ( ( sk_A != sk_A )
    | ( sk_B = sk_A )
    | ( sk_B = sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['42','51'])).

thf('53',plain,(
    sk_B = sk_A ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['53','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UJHvQLnkkL
% 0.14/0.37  % Computer   : n001.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 18:33:45 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.23/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.55  % Solved by: fo/fo7.sh
% 0.23/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.55  % done 83 iterations in 0.058s
% 0.23/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.55  % SZS output start Refutation
% 0.23/0.55  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.23/0.55  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.23/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.23/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.55  thf(t58_mcart_1, conjecture,
% 0.23/0.55    (![A:$i,B:$i]:
% 0.23/0.55     ( ( ( k4_zfmisc_1 @ A @ A @ A @ A ) = ( k4_zfmisc_1 @ B @ B @ B @ B ) ) =>
% 0.23/0.55       ( ( A ) = ( B ) ) ))).
% 0.23/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.55    (~( ![A:$i,B:$i]:
% 0.23/0.55        ( ( ( k4_zfmisc_1 @ A @ A @ A @ A ) = ( k4_zfmisc_1 @ B @ B @ B @ B ) ) =>
% 0.23/0.55          ( ( A ) = ( B ) ) ) )),
% 0.23/0.55    inference('cnf.neg', [status(esa)], [t58_mcart_1])).
% 0.23/0.55  thf('0', plain,
% 0.23/0.55      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.23/0.55         = (k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf(d3_zfmisc_1, axiom,
% 0.23/0.55    (![A:$i,B:$i,C:$i]:
% 0.23/0.55     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.23/0.55       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.23/0.55  thf('1', plain,
% 0.23/0.55      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.23/0.55         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.23/0.55           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.23/0.55      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.23/0.55  thf('2', plain,
% 0.23/0.55      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.23/0.55         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.23/0.55           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.23/0.55      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.23/0.55  thf('3', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.55         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.23/0.55           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 0.23/0.55      inference('sup+', [status(thm)], ['1', '2'])).
% 0.23/0.55  thf('4', plain,
% 0.23/0.55      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.23/0.55         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.23/0.55           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.23/0.55      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.23/0.55  thf(t113_zfmisc_1, axiom,
% 0.23/0.55    (![A:$i,B:$i]:
% 0.23/0.55     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.23/0.55       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.23/0.55  thf('5', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i]:
% 0.23/0.55         (((X0) = (k1_xboole_0))
% 0.23/0.55          | ((X1) = (k1_xboole_0))
% 0.23/0.55          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.23/0.55      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.23/0.55  thf('6', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.55         (((k3_zfmisc_1 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 0.23/0.55          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0))
% 0.23/0.55          | ((X0) = (k1_xboole_0)))),
% 0.23/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.23/0.55  thf('7', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.55         (((k2_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X2 @ X1) @ X0) != (k1_xboole_0))
% 0.23/0.55          | ((X0) = (k1_xboole_0))
% 0.23/0.55          | ((k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1) = (k1_xboole_0)))),
% 0.23/0.55      inference('sup-', [status(thm)], ['3', '6'])).
% 0.23/0.55  thf('8', plain,
% 0.23/0.55      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.23/0.55         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.23/0.55           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.23/0.55      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.23/0.55  thf('9', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.55         (((k2_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X2 @ X1) @ X0) != (k1_xboole_0))
% 0.23/0.55          | ((X0) = (k1_xboole_0))
% 0.23/0.55          | ((k3_zfmisc_1 @ X3 @ X2 @ X1) = (k1_xboole_0)))),
% 0.23/0.55      inference('demod', [status(thm)], ['7', '8'])).
% 0.23/0.55  thf(d4_zfmisc_1, axiom,
% 0.23/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.55     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.23/0.55       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.23/0.55  thf('10', plain,
% 0.23/0.55      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.23/0.55         ((k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9)
% 0.23/0.55           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X6 @ X7 @ X8) @ X9))),
% 0.23/0.55      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.23/0.55  thf('11', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.55         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 0.23/0.55          | ((X0) = (k1_xboole_0))
% 0.23/0.55          | ((k3_zfmisc_1 @ X3 @ X2 @ X1) = (k1_xboole_0)))),
% 0.23/0.55      inference('demod', [status(thm)], ['9', '10'])).
% 0.23/0.55  thf('12', plain,
% 0.23/0.55      ((((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) != (k1_xboole_0))
% 0.23/0.55        | ((k3_zfmisc_1 @ sk_B @ sk_B @ sk_B) = (k1_xboole_0))
% 0.23/0.55        | ((sk_B) = (k1_xboole_0)))),
% 0.23/0.55      inference('sup-', [status(thm)], ['0', '11'])).
% 0.23/0.55  thf('13', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.55         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.23/0.55           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 0.23/0.55      inference('sup+', [status(thm)], ['1', '2'])).
% 0.23/0.55  thf('14', plain,
% 0.23/0.55      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.23/0.55         ((k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9)
% 0.23/0.55           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X6 @ X7 @ X8) @ X9))),
% 0.23/0.55      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.23/0.55  thf('15', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.55         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.23/0.55           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.23/0.55      inference('demod', [status(thm)], ['13', '14'])).
% 0.23/0.55  thf('16', plain,
% 0.23/0.55      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.23/0.55         = (k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('17', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.55         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.23/0.55           = (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3))),
% 0.23/0.55      inference('demod', [status(thm)], ['13', '14'])).
% 0.23/0.55  thf(t36_mcart_1, axiom,
% 0.23/0.55    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.23/0.55     ( ( ( k3_zfmisc_1 @ A @ B @ C ) = ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.23/0.55       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.23/0.55         ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.23/0.55         ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ) ))).
% 0.23/0.55  thf('18', plain,
% 0.23/0.55      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.23/0.55         (((X14) = (k1_xboole_0))
% 0.23/0.55          | ((X15) = (k1_xboole_0))
% 0.23/0.55          | ((X16) = (k1_xboole_0))
% 0.23/0.55          | ((k3_zfmisc_1 @ X16 @ X15 @ X14) != (k3_zfmisc_1 @ X17 @ X18 @ X19))
% 0.23/0.55          | ((X14) = (X19)))),
% 0.23/0.55      inference('cnf', [status(esa)], [t36_mcart_1])).
% 0.23/0.55  thf('19', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.23/0.55         (((k3_zfmisc_1 @ X6 @ X5 @ X4) != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.23/0.55          | ((X4) = (X0))
% 0.23/0.55          | ((X6) = (k1_xboole_0))
% 0.23/0.55          | ((X5) = (k1_xboole_0))
% 0.23/0.55          | ((X4) = (k1_xboole_0)))),
% 0.23/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.23/0.55  thf('20', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.55         (((k3_zfmisc_1 @ X2 @ X1 @ X0)
% 0.23/0.55            != (k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A))
% 0.23/0.55          | ((X0) = (k1_xboole_0))
% 0.23/0.55          | ((X1) = (k1_xboole_0))
% 0.23/0.55          | ((X2) = (k1_xboole_0))
% 0.23/0.55          | ((X0) = (sk_B)))),
% 0.23/0.55      inference('sup-', [status(thm)], ['16', '19'])).
% 0.23/0.55  thf('21', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.55         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.23/0.55            != (k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A))
% 0.23/0.55          | ((X0) = (sk_B))
% 0.23/0.55          | ((k2_zfmisc_1 @ X3 @ X2) = (k1_xboole_0))
% 0.23/0.55          | ((X1) = (k1_xboole_0))
% 0.23/0.55          | ((X0) = (k1_xboole_0)))),
% 0.23/0.55      inference('sup-', [status(thm)], ['15', '20'])).
% 0.23/0.55  thf('22', plain,
% 0.23/0.55      ((((sk_A) = (k1_xboole_0))
% 0.23/0.55        | ((sk_A) = (k1_xboole_0))
% 0.23/0.55        | ((k2_zfmisc_1 @ sk_A @ sk_A) = (k1_xboole_0))
% 0.23/0.55        | ((sk_A) = (sk_B)))),
% 0.23/0.55      inference('eq_res', [status(thm)], ['21'])).
% 0.23/0.55  thf('23', plain,
% 0.23/0.55      ((((sk_A) = (sk_B))
% 0.23/0.55        | ((k2_zfmisc_1 @ sk_A @ sk_A) = (k1_xboole_0))
% 0.23/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.23/0.55      inference('simplify', [status(thm)], ['22'])).
% 0.23/0.55  thf('24', plain, (((sk_A) != (sk_B))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('25', plain,
% 0.23/0.55      ((((k2_zfmisc_1 @ sk_A @ sk_A) = (k1_xboole_0))
% 0.23/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.23/0.55      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.23/0.55  thf('26', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i]:
% 0.23/0.55         (((X0) = (k1_xboole_0))
% 0.23/0.55          | ((X1) = (k1_xboole_0))
% 0.23/0.55          | ((k2_zfmisc_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.23/0.55      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.23/0.55  thf('27', plain,
% 0.23/0.55      ((((k1_xboole_0) != (k1_xboole_0))
% 0.23/0.55        | ((sk_A) = (k1_xboole_0))
% 0.23/0.55        | ((sk_A) = (k1_xboole_0))
% 0.23/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.23/0.55      inference('sup-', [status(thm)], ['25', '26'])).
% 0.23/0.55  thf('28', plain, (((sk_A) = (k1_xboole_0))),
% 0.23/0.55      inference('simplify', [status(thm)], ['27'])).
% 0.23/0.55  thf('29', plain, (((sk_A) = (k1_xboole_0))),
% 0.23/0.55      inference('simplify', [status(thm)], ['27'])).
% 0.23/0.55  thf('30', plain, (((sk_A) = (k1_xboole_0))),
% 0.23/0.55      inference('simplify', [status(thm)], ['27'])).
% 0.23/0.55  thf('31', plain,
% 0.23/0.55      ((((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) != (sk_A))
% 0.23/0.55        | ((k3_zfmisc_1 @ sk_B @ sk_B @ sk_B) = (sk_A))
% 0.23/0.55        | ((sk_B) = (sk_A)))),
% 0.23/0.55      inference('demod', [status(thm)], ['12', '28', '29', '30'])).
% 0.23/0.55  thf('32', plain, (((sk_A) != (sk_B))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('33', plain,
% 0.23/0.55      ((((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) != (sk_A))
% 0.23/0.55        | ((k3_zfmisc_1 @ sk_B @ sk_B @ sk_B) = (sk_A)))),
% 0.23/0.55      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 0.23/0.55  thf('34', plain,
% 0.23/0.55      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.23/0.55         ((k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9)
% 0.23/0.55           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X6 @ X7 @ X8) @ X9))),
% 0.23/0.55      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.23/0.55  thf('35', plain,
% 0.23/0.55      (![X1 : $i, X2 : $i]:
% 0.23/0.55         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.23/0.55      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.23/0.55  thf('36', plain,
% 0.23/0.55      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.23/0.55      inference('simplify', [status(thm)], ['35'])).
% 0.23/0.55  thf('37', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.55         ((k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.23/0.55      inference('sup+', [status(thm)], ['34', '36'])).
% 0.23/0.55  thf('38', plain, (((sk_A) = (k1_xboole_0))),
% 0.23/0.55      inference('simplify', [status(thm)], ['27'])).
% 0.23/0.55  thf('39', plain, (((sk_A) = (k1_xboole_0))),
% 0.23/0.55      inference('simplify', [status(thm)], ['27'])).
% 0.23/0.55  thf('40', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.55         ((k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_A) = (sk_A))),
% 0.23/0.55      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.23/0.55  thf('41', plain,
% 0.23/0.55      ((((sk_A) != (sk_A)) | ((k3_zfmisc_1 @ sk_B @ sk_B @ sk_B) = (sk_A)))),
% 0.23/0.55      inference('demod', [status(thm)], ['33', '40'])).
% 0.23/0.55  thf('42', plain, (((k3_zfmisc_1 @ sk_B @ sk_B @ sk_B) = (sk_A))),
% 0.23/0.55      inference('simplify', [status(thm)], ['41'])).
% 0.23/0.55  thf('43', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.55         ((k4_zfmisc_1 @ X2 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.23/0.55      inference('sup+', [status(thm)], ['34', '36'])).
% 0.23/0.55  thf('44', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.23/0.55         (((k3_zfmisc_1 @ X6 @ X5 @ X4) != (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.23/0.55          | ((X4) = (X0))
% 0.23/0.55          | ((X6) = (k1_xboole_0))
% 0.23/0.55          | ((X5) = (k1_xboole_0))
% 0.23/0.55          | ((X4) = (k1_xboole_0)))),
% 0.23/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.23/0.55  thf('45', plain,
% 0.23/0.55      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.23/0.55         (((k3_zfmisc_1 @ X5 @ X4 @ X3) != (k1_xboole_0))
% 0.23/0.55          | ((X3) = (k1_xboole_0))
% 0.23/0.55          | ((X4) = (k1_xboole_0))
% 0.23/0.55          | ((X5) = (k1_xboole_0))
% 0.23/0.55          | ((X3) = (k1_xboole_0)))),
% 0.23/0.55      inference('sup-', [status(thm)], ['43', '44'])).
% 0.23/0.55  thf('46', plain,
% 0.23/0.55      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.23/0.55         (((X5) = (k1_xboole_0))
% 0.23/0.55          | ((X4) = (k1_xboole_0))
% 0.23/0.55          | ((X3) = (k1_xboole_0))
% 0.23/0.55          | ((k3_zfmisc_1 @ X5 @ X4 @ X3) != (k1_xboole_0)))),
% 0.23/0.55      inference('simplify', [status(thm)], ['45'])).
% 0.23/0.55  thf('47', plain, (((sk_A) = (k1_xboole_0))),
% 0.23/0.55      inference('simplify', [status(thm)], ['27'])).
% 0.23/0.55  thf('48', plain, (((sk_A) = (k1_xboole_0))),
% 0.23/0.55      inference('simplify', [status(thm)], ['27'])).
% 0.23/0.55  thf('49', plain, (((sk_A) = (k1_xboole_0))),
% 0.23/0.55      inference('simplify', [status(thm)], ['27'])).
% 0.23/0.55  thf('50', plain, (((sk_A) = (k1_xboole_0))),
% 0.23/0.55      inference('simplify', [status(thm)], ['27'])).
% 0.23/0.55  thf('51', plain,
% 0.23/0.55      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.23/0.55         (((X5) = (sk_A))
% 0.23/0.55          | ((X4) = (sk_A))
% 0.23/0.55          | ((X3) = (sk_A))
% 0.23/0.55          | ((k3_zfmisc_1 @ X5 @ X4 @ X3) != (sk_A)))),
% 0.23/0.55      inference('demod', [status(thm)], ['46', '47', '48', '49', '50'])).
% 0.23/0.55  thf('52', plain,
% 0.23/0.55      ((((sk_A) != (sk_A))
% 0.23/0.55        | ((sk_B) = (sk_A))
% 0.23/0.55        | ((sk_B) = (sk_A))
% 0.23/0.55        | ((sk_B) = (sk_A)))),
% 0.23/0.55      inference('sup-', [status(thm)], ['42', '51'])).
% 0.23/0.55  thf('53', plain, (((sk_B) = (sk_A))),
% 0.23/0.55      inference('simplify', [status(thm)], ['52'])).
% 0.23/0.55  thf('54', plain, (((sk_A) != (sk_B))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('55', plain, ($false),
% 0.23/0.55      inference('simplify_reflect-', [status(thm)], ['53', '54'])).
% 0.23/0.55  
% 0.23/0.55  % SZS output end Refutation
% 0.23/0.55  
% 0.23/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

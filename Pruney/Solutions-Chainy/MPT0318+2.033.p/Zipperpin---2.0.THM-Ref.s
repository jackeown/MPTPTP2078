%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xg6Umezq5q

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:25 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 231 expanded)
%              Number of leaves         :   14 (  65 expanded)
%              Depth                    :   17
%              Number of atoms          :  613 (2399 expanded)
%              Number of equality atoms :  104 ( 447 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t130_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( A != k1_xboole_0 )
     => ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A )
         != k1_xboole_0 )
        & ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( A != k1_xboole_0 )
       => ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A )
           != k1_xboole_0 )
          & ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t130_zfmisc_1])).

thf('0',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X13 @ X12 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('3',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('8',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X13 @ X12 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('11',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('15',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ( ( k4_xboole_0 @ X16 @ ( k1_tarski @ X15 ) )
       != X16 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('16',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
         != X0 )
        | ~ ( r2_hidden @ sk_B @ X0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ sk_B ) @ k1_xboole_0 )
       != ( k2_tarski @ X0 @ sk_B ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','16'])).

thf('18',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k4_xboole_0 @ X16 @ ( k1_tarski @ X17 ) )
        = X16 )
      | ( r2_hidden @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('19',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('20',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t73_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = k1_xboole_0 )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X18 @ X19 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X18 @ X20 ) @ X19 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t73_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
       != k1_xboole_0 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
         != k1_xboole_0 )
        | ( r2_hidden @ sk_B @ X0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ( r2_hidden @ X0 @ k1_xboole_0 )
        | ( r2_hidden @ sk_B @ ( k1_tarski @ X0 ) ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_B @ ( k1_tarski @ X0 ) )
        | ( r2_hidden @ X0 @ k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('27',plain,(
    ! [X0: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( X4 = X3 )
      | ( X4 = X0 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('28',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ k1_xboole_0 )
        | ( sk_B = X0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
        | ( X0 = sk_B ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ! [X0: $i] : ( sk_B = X0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['31','34'])).

thf('36',plain,
    ( ! [X0: $i] : ( sk_B = X0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['31','34'])).

thf('37',plain,
    ( ! [X0: $i] : ( sk_B = X0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['31','34'])).

thf('38',plain,
    ( ( sk_B != sk_B )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','35','36','37'])).

thf('39',plain,(
    ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
 != k1_xboole_0 ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('41',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['6','41'])).

thf('43',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('44',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('45',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('47',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X18 @ X20 ) @ X21 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( r2_hidden @ X18 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t73_zfmisc_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ( ( k4_xboole_0 @ X16 @ ( k1_tarski @ X15 ) )
       != X16 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('55',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['42','55'])).

thf('57',plain,(
    $false ),
    inference(simplify,[status(thm)],['56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xg6Umezq5q
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:51:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.65  % Solved by: fo/fo7.sh
% 0.46/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.65  % done 174 iterations in 0.159s
% 0.46/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.65  % SZS output start Refutation
% 0.46/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.65  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.65  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.65  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.65  thf(t130_zfmisc_1, conjecture,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.46/0.65       ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.46/0.65         ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.46/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.65    (~( ![A:$i,B:$i]:
% 0.46/0.65        ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.46/0.65          ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.46/0.65            ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ) )),
% 0.46/0.65    inference('cnf.neg', [status(esa)], [t130_zfmisc_1])).
% 0.46/0.65  thf('0', plain,
% 0.46/0.65      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))
% 0.46/0.65        | ((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('1', plain,
% 0.46/0.65      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))
% 0.46/0.65         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.46/0.65      inference('split', [status(esa)], ['0'])).
% 0.46/0.65  thf(t113_zfmisc_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.46/0.65       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.46/0.65  thf('2', plain,
% 0.46/0.65      (![X12 : $i, X13 : $i]:
% 0.46/0.65         (((X12) = (k1_xboole_0))
% 0.46/0.65          | ((X13) = (k1_xboole_0))
% 0.46/0.65          | ((k2_zfmisc_1 @ X13 @ X12) != (k1_xboole_0)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.46/0.65  thf('3', plain,
% 0.46/0.65      (((((k1_xboole_0) != (k1_xboole_0))
% 0.46/0.65         | ((sk_A) = (k1_xboole_0))
% 0.46/0.65         | ((k1_tarski @ sk_B) = (k1_xboole_0))))
% 0.46/0.65         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.65  thf('4', plain,
% 0.46/0.65      (((((k1_tarski @ sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.46/0.65         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.46/0.65      inference('simplify', [status(thm)], ['3'])).
% 0.46/0.65  thf('5', plain, (((sk_A) != (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('6', plain,
% 0.46/0.65      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.46/0.65         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.46/0.65      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.46/0.65  thf(d2_tarski, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.46/0.65       ( ![D:$i]:
% 0.46/0.65         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.46/0.65  thf('7', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.65         (((X1) != (X0))
% 0.46/0.65          | (r2_hidden @ X1 @ X2)
% 0.46/0.65          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d2_tarski])).
% 0.46/0.65  thf('8', plain,
% 0.46/0.65      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['7'])).
% 0.46/0.65  thf('9', plain,
% 0.46/0.65      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))
% 0.46/0.65         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('split', [status(esa)], ['0'])).
% 0.46/0.65  thf('10', plain,
% 0.46/0.65      (![X12 : $i, X13 : $i]:
% 0.46/0.65         (((X12) = (k1_xboole_0))
% 0.46/0.65          | ((X13) = (k1_xboole_0))
% 0.46/0.65          | ((k2_zfmisc_1 @ X13 @ X12) != (k1_xboole_0)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.46/0.65  thf('11', plain,
% 0.46/0.65      (((((k1_xboole_0) != (k1_xboole_0))
% 0.46/0.65         | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.46/0.65         | ((sk_A) = (k1_xboole_0))))
% 0.46/0.65         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['9', '10'])).
% 0.46/0.65  thf('12', plain,
% 0.46/0.65      (((((sk_A) = (k1_xboole_0)) | ((k1_tarski @ sk_B) = (k1_xboole_0))))
% 0.46/0.65         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('simplify', [status(thm)], ['11'])).
% 0.46/0.65  thf('13', plain, (((sk_A) != (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('14', plain,
% 0.46/0.65      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.46/0.65         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.46/0.65  thf(t65_zfmisc_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.46/0.65       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.46/0.65  thf('15', plain,
% 0.46/0.65      (![X15 : $i, X16 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X15 @ X16)
% 0.46/0.65          | ((k4_xboole_0 @ X16 @ (k1_tarski @ X15)) != (X16)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.46/0.65  thf('16', plain,
% 0.46/0.65      ((![X0 : $i]:
% 0.46/0.65          (((k4_xboole_0 @ X0 @ k1_xboole_0) != (X0))
% 0.46/0.65           | ~ (r2_hidden @ sk_B @ X0)))
% 0.46/0.65         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['14', '15'])).
% 0.46/0.65  thf('17', plain,
% 0.46/0.65      ((![X0 : $i]:
% 0.46/0.65          ((k4_xboole_0 @ (k2_tarski @ X0 @ sk_B) @ k1_xboole_0)
% 0.46/0.65            != (k2_tarski @ X0 @ sk_B)))
% 0.46/0.65         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['8', '16'])).
% 0.46/0.65  thf('18', plain,
% 0.46/0.65      (![X16 : $i, X17 : $i]:
% 0.46/0.65         (((k4_xboole_0 @ X16 @ (k1_tarski @ X17)) = (X16))
% 0.46/0.65          | (r2_hidden @ X17 @ X16))),
% 0.46/0.65      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.46/0.65  thf('19', plain,
% 0.46/0.65      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.46/0.65         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.46/0.65  thf(t69_enumset1, axiom,
% 0.46/0.65    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.46/0.65  thf('20', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.46/0.65      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.65  thf(t73_zfmisc_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_xboole_0 ) ) <=>
% 0.46/0.65       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.46/0.65  thf('21', plain,
% 0.46/0.65      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.46/0.65         ((r2_hidden @ X18 @ X19)
% 0.46/0.65          | ((k4_xboole_0 @ (k2_tarski @ X18 @ X20) @ X19) != (k1_xboole_0)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t73_zfmisc_1])).
% 0.46/0.65  thf('22', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) != (k1_xboole_0))
% 0.46/0.65          | (r2_hidden @ X0 @ X1))),
% 0.46/0.65      inference('sup-', [status(thm)], ['20', '21'])).
% 0.46/0.65  thf('23', plain,
% 0.46/0.65      ((![X0 : $i]:
% 0.46/0.65          (((k4_xboole_0 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 0.46/0.65           | (r2_hidden @ sk_B @ X0)))
% 0.46/0.65         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['19', '22'])).
% 0.46/0.65  thf('24', plain,
% 0.46/0.65      ((![X0 : $i]:
% 0.46/0.65          (((k1_xboole_0) != (k1_xboole_0))
% 0.46/0.65           | (r2_hidden @ X0 @ k1_xboole_0)
% 0.46/0.65           | (r2_hidden @ sk_B @ (k1_tarski @ X0))))
% 0.46/0.65         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['18', '23'])).
% 0.46/0.65  thf('25', plain,
% 0.46/0.65      ((![X0 : $i]:
% 0.46/0.65          ((r2_hidden @ sk_B @ (k1_tarski @ X0))
% 0.46/0.65           | (r2_hidden @ X0 @ k1_xboole_0)))
% 0.46/0.65         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.46/0.65      inference('simplify', [status(thm)], ['24'])).
% 0.46/0.65  thf('26', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.46/0.65      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.65  thf('27', plain,
% 0.46/0.65      (![X0 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X4 @ X2)
% 0.46/0.65          | ((X4) = (X3))
% 0.46/0.65          | ((X4) = (X0))
% 0.46/0.65          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d2_tarski])).
% 0.46/0.65  thf('28', plain,
% 0.46/0.65      (![X0 : $i, X3 : $i, X4 : $i]:
% 0.46/0.65         (((X4) = (X0))
% 0.46/0.65          | ((X4) = (X3))
% 0.46/0.65          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['27'])).
% 0.46/0.65  thf('29', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['26', '28'])).
% 0.46/0.65  thf('30', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['29'])).
% 0.46/0.66  thf('31', plain,
% 0.46/0.66      ((![X0 : $i]: ((r2_hidden @ X0 @ k1_xboole_0) | ((sk_B) = (X0))))
% 0.46/0.66         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['25', '30'])).
% 0.46/0.66  thf('32', plain,
% 0.46/0.66      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.46/0.66         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.46/0.66      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.46/0.66  thf('33', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['29'])).
% 0.46/0.66  thf('34', plain,
% 0.46/0.66      ((![X0 : $i]: (~ (r2_hidden @ X0 @ k1_xboole_0) | ((X0) = (sk_B))))
% 0.46/0.66         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['32', '33'])).
% 0.46/0.66  thf('35', plain,
% 0.46/0.66      ((![X0 : $i]: ((sk_B) = (X0)))
% 0.46/0.66         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.46/0.66      inference('clc', [status(thm)], ['31', '34'])).
% 0.46/0.66  thf('36', plain,
% 0.46/0.66      ((![X0 : $i]: ((sk_B) = (X0)))
% 0.46/0.66         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.46/0.66      inference('clc', [status(thm)], ['31', '34'])).
% 0.46/0.66  thf('37', plain,
% 0.46/0.66      ((![X0 : $i]: ((sk_B) = (X0)))
% 0.46/0.66         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.46/0.66      inference('clc', [status(thm)], ['31', '34'])).
% 0.46/0.66  thf('38', plain,
% 0.46/0.66      ((((sk_B) != (sk_B)))
% 0.46/0.66         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.46/0.66      inference('demod', [status(thm)], ['17', '35', '36', '37'])).
% 0.46/0.66  thf('39', plain,
% 0.46/0.66      (~ (((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['38'])).
% 0.46/0.66  thf('40', plain,
% 0.46/0.66      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))) | 
% 0.46/0.66       (((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))),
% 0.46/0.66      inference('split', [status(esa)], ['0'])).
% 0.46/0.66  thf('41', plain,
% 0.46/0.66      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))),
% 0.46/0.66      inference('sat_resolution*', [status(thm)], ['39', '40'])).
% 0.46/0.66  thf('42', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.46/0.66      inference('simpl_trail', [status(thm)], ['6', '41'])).
% 0.46/0.66  thf('43', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.46/0.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.66  thf('44', plain,
% 0.46/0.66      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['7'])).
% 0.46/0.66  thf('45', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['43', '44'])).
% 0.46/0.66  thf('46', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['43', '44'])).
% 0.46/0.66  thf('47', plain,
% 0.46/0.66      (![X18 : $i, X20 : $i, X21 : $i]:
% 0.46/0.66         (((k4_xboole_0 @ (k2_tarski @ X18 @ X20) @ X21) = (k1_xboole_0))
% 0.46/0.66          | ~ (r2_hidden @ X20 @ X21)
% 0.46/0.66          | ~ (r2_hidden @ X18 @ X21))),
% 0.46/0.66      inference('cnf', [status(esa)], [t73_zfmisc_1])).
% 0.46/0.66  thf('48', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.46/0.66          | ((k4_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0))
% 0.46/0.66              = (k1_xboole_0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['46', '47'])).
% 0.46/0.66  thf('49', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0))
% 0.46/0.66           = (k1_xboole_0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['45', '48'])).
% 0.46/0.66  thf('50', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.46/0.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.66  thf('51', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.46/0.66      inference('demod', [status(thm)], ['49', '50'])).
% 0.46/0.66  thf('52', plain,
% 0.46/0.66      (![X15 : $i, X16 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X15 @ X16)
% 0.46/0.66          | ((k4_xboole_0 @ X16 @ (k1_tarski @ X15)) != (X16)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.46/0.66  thf('53', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.46/0.66          | ~ (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['51', '52'])).
% 0.46/0.66  thf('54', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['43', '44'])).
% 0.46/0.66  thf('55', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.46/0.66      inference('demod', [status(thm)], ['53', '54'])).
% 0.46/0.66  thf('56', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['42', '55'])).
% 0.46/0.66  thf('57', plain, ($false), inference('simplify', [status(thm)], ['56'])).
% 0.46/0.66  
% 0.46/0.66  % SZS output end Refutation
% 0.46/0.66  
% 0.51/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

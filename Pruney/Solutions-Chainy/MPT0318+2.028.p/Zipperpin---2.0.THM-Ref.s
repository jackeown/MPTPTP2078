%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.N8XSZnoDCI

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 598 expanded)
%              Number of leaves         :   14 ( 151 expanded)
%              Depth                    :   21
%              Number of atoms          :  679 (6848 expanded)
%              Number of equality atoms :  132 (1393 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X16: $i,X17: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X17 @ X16 )
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

thf('7',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('8',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X17 @ X16 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('9',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('13',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X20 ) @ ( k1_tarski @ X21 ) )
        = ( k1_tarski @ X20 ) )
      | ( X20 = X21 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('14',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
          = ( k1_tarski @ sk_B ) )
        | ( sk_B = X0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('16',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
          = k1_xboole_0 )
        | ( sk_B = X0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('18',plain,(
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

thf('19',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ X22 @ X23 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X22 @ X24 ) @ X23 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t73_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
       != k1_xboole_0 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
         != k1_xboole_0 )
        | ( r2_hidden @ sk_B @ X0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ( sk_B = X0 )
        | ( r2_hidden @ sk_B @ ( k1_tarski @ X0 ) ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_B @ ( k1_tarski @ X0 ) )
        | ( sk_B = X0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('25',plain,(
    ! [X0: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( X4 = X3 )
      | ( X4 = X0 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('26',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ! [X0: $i] : ( sk_B = X0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['23','28'])).

thf('30',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('31',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X20 != X19 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X20 ) @ ( k1_tarski @ X19 ) )
       != ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('32',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X19 ) @ ( k1_tarski @ X19 ) )
     != ( k1_tarski @ X19 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
     != ( k1_tarski @ sk_B ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('35',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('36',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ! [X0: $i] : ( sk_B = X0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['23','28'])).

thf('38',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ! [X0: $i] : ( X0 != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','38'])).

thf('40',plain,(
    ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
 != k1_xboole_0 ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('42',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['6','42'])).

thf('44',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X20 ) @ ( k1_tarski @ X21 ) )
        = ( k1_tarski @ X20 ) )
      | ( X20 = X21 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
       != k1_xboole_0 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != k1_xboole_0 )
      | ( X0 = X1 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( ( k1_tarski @ X0 )
       != k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_B = X0 ) ) ),
    inference('sup-',[status(thm)],['43','48'])).

thf('50',plain,(
    ! [X0: $i] : ( sk_B = X0 ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf('52',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X19 ) @ ( k1_tarski @ X19 ) )
     != ( k1_tarski @ X19 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('53',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
     != ( k1_tarski @ sk_B ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf('55',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf('56',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['40','41'])).

thf('58',plain,(
    ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] : ( sk_B = X0 ) ),
    inference(simplify,[status(thm)],['49'])).

thf('60',plain,(
    sk_B != k1_xboole_0 ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] : ( X0 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','60'])).

thf('62',plain,(
    $false ),
    inference(simplify,[status(thm)],['61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.N8XSZnoDCI
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:06:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 96 iterations in 0.024s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(t130_zfmisc_1, conjecture,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.20/0.47       ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.47         ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i]:
% 0.20/0.47        ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.20/0.47          ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.47            ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t130_zfmisc_1])).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))
% 0.20/0.47        | ((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))
% 0.20/0.47         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.47  thf(t113_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.47       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X16 : $i, X17 : $i]:
% 0.20/0.47         (((X16) = (k1_xboole_0))
% 0.20/0.47          | ((X17) = (k1_xboole_0))
% 0.20/0.47          | ((k2_zfmisc_1 @ X17 @ X16) != (k1_xboole_0)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.47         | ((sk_A) = (k1_xboole_0))
% 0.20/0.47         | ((k1_tarski @ sk_B) = (k1_xboole_0))))
% 0.20/0.47         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (((((k1_tarski @ sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.20/0.47         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.47      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.47  thf('5', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.20/0.47         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))
% 0.20/0.47         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X16 : $i, X17 : $i]:
% 0.20/0.47         (((X16) = (k1_xboole_0))
% 0.20/0.47          | ((X17) = (k1_xboole_0))
% 0.20/0.47          | ((k2_zfmisc_1 @ X17 @ X16) != (k1_xboole_0)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.47         | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.20/0.47         | ((sk_A) = (k1_xboole_0))))
% 0.20/0.47         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (((((sk_A) = (k1_xboole_0)) | ((k1_tarski @ sk_B) = (k1_xboole_0))))
% 0.20/0.47         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.47      inference('simplify', [status(thm)], ['9'])).
% 0.20/0.47  thf('11', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.20/0.47         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.20/0.47  thf(t20_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.47         ( k1_tarski @ A ) ) <=>
% 0.20/0.47       ( ( A ) != ( B ) ) ))).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (![X20 : $i, X21 : $i]:
% 0.20/0.47         (((k4_xboole_0 @ (k1_tarski @ X20) @ (k1_tarski @ X21))
% 0.20/0.47            = (k1_tarski @ X20))
% 0.20/0.47          | ((X20) = (X21)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      ((![X0 : $i]:
% 0.20/0.47          (((k4_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_tarski @ sk_B))
% 0.20/0.47           | ((sk_B) = (X0))))
% 0.20/0.47         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.47      inference('sup+', [status(thm)], ['12', '13'])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.20/0.47         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      ((![X0 : $i]:
% 0.20/0.47          (((k4_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_xboole_0))
% 0.20/0.47           | ((sk_B) = (X0))))
% 0.20/0.47         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.47      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.20/0.47         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.20/0.47  thf(t69_enumset1, axiom,
% 0.20/0.47    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.47  thf('18', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.20/0.47      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.47  thf(t73_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.47       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.47         ((r2_hidden @ X22 @ X23)
% 0.20/0.47          | ((k4_xboole_0 @ (k2_tarski @ X22 @ X24) @ X23) != (k1_xboole_0)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t73_zfmisc_1])).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) != (k1_xboole_0))
% 0.20/0.47          | (r2_hidden @ X0 @ X1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      ((![X0 : $i]:
% 0.20/0.47          (((k4_xboole_0 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 0.20/0.47           | (r2_hidden @ sk_B @ X0)))
% 0.20/0.47         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['17', '20'])).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      ((![X0 : $i]:
% 0.20/0.47          (((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.47           | ((sk_B) = (X0))
% 0.20/0.47           | (r2_hidden @ sk_B @ (k1_tarski @ X0))))
% 0.20/0.47         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['16', '21'])).
% 0.20/0.47  thf('23', plain,
% 0.20/0.47      ((![X0 : $i]: ((r2_hidden @ sk_B @ (k1_tarski @ X0)) | ((sk_B) = (X0))))
% 0.20/0.47         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.47      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.47  thf('24', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.20/0.47      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.47  thf(d2_tarski, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.20/0.47       ( ![D:$i]:
% 0.20/0.47         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.20/0.47  thf('25', plain,
% 0.20/0.47      (![X0 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X4 @ X2)
% 0.20/0.47          | ((X4) = (X3))
% 0.20/0.47          | ((X4) = (X0))
% 0.20/0.47          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.20/0.47      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.47  thf('26', plain,
% 0.20/0.47      (![X0 : $i, X3 : $i, X4 : $i]:
% 0.20/0.47         (((X4) = (X0))
% 0.20/0.47          | ((X4) = (X3))
% 0.20/0.47          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['24', '26'])).
% 0.20/0.47  thf('28', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['27'])).
% 0.20/0.47  thf('29', plain,
% 0.20/0.47      ((![X0 : $i]: ((sk_B) = (X0)))
% 0.20/0.47         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.47      inference('clc', [status(thm)], ['23', '28'])).
% 0.20/0.47  thf('30', plain,
% 0.20/0.47      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.20/0.47         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.20/0.47  thf('31', plain,
% 0.20/0.47      (![X19 : $i, X20 : $i]:
% 0.20/0.47         (((X20) != (X19))
% 0.20/0.47          | ((k4_xboole_0 @ (k1_tarski @ X20) @ (k1_tarski @ X19))
% 0.20/0.47              != (k1_tarski @ X20)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.47  thf('32', plain,
% 0.20/0.47      (![X19 : $i]:
% 0.20/0.47         ((k4_xboole_0 @ (k1_tarski @ X19) @ (k1_tarski @ X19))
% 0.20/0.47           != (k1_tarski @ X19))),
% 0.20/0.47      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.47  thf('33', plain,
% 0.20/0.47      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0) != (k1_tarski @ sk_B)))
% 0.20/0.47         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['30', '32'])).
% 0.20/0.47  thf('34', plain,
% 0.20/0.47      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.20/0.47         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.20/0.47  thf('35', plain,
% 0.20/0.47      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.20/0.47         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.20/0.47  thf('36', plain,
% 0.20/0.47      ((((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.47         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.47      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.20/0.47  thf('37', plain,
% 0.20/0.47      ((![X0 : $i]: ((sk_B) = (X0)))
% 0.20/0.47         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.47      inference('clc', [status(thm)], ['23', '28'])).
% 0.20/0.47  thf('38', plain,
% 0.20/0.47      ((((sk_B) != (k1_xboole_0)))
% 0.20/0.47         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.47      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.47  thf('39', plain,
% 0.20/0.47      ((![X0 : $i]: ((X0) != (k1_xboole_0)))
% 0.20/0.47         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['29', '38'])).
% 0.20/0.47  thf('40', plain,
% 0.20/0.47      (~ (((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['39'])).
% 0.20/0.47  thf('41', plain,
% 0.20/0.47      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))) | 
% 0.20/0.47       (((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.47  thf('42', plain,
% 0.20/0.47      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))),
% 0.20/0.47      inference('sat_resolution*', [status(thm)], ['40', '41'])).
% 0.20/0.47  thf('43', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.20/0.47      inference('simpl_trail', [status(thm)], ['6', '42'])).
% 0.20/0.47  thf('44', plain,
% 0.20/0.47      (![X20 : $i, X21 : $i]:
% 0.20/0.47         (((k4_xboole_0 @ (k1_tarski @ X20) @ (k1_tarski @ X21))
% 0.20/0.47            = (k1_tarski @ X20))
% 0.20/0.47          | ((X20) = (X21)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.47  thf('45', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) != (k1_xboole_0))
% 0.20/0.47          | (r2_hidden @ X0 @ X1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.47  thf('46', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (((k1_tarski @ X0) != (k1_xboole_0))
% 0.20/0.47          | ((X0) = (X1))
% 0.20/0.47          | (r2_hidden @ X0 @ (k1_tarski @ X1)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.47  thf('47', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['27'])).
% 0.20/0.47  thf('48', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (((X0) = (X1)) | ((k1_tarski @ X0) != (k1_xboole_0)))),
% 0.20/0.47      inference('clc', [status(thm)], ['46', '47'])).
% 0.20/0.47  thf('49', plain,
% 0.20/0.47      (![X0 : $i]: (((k1_xboole_0) != (k1_xboole_0)) | ((sk_B) = (X0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['43', '48'])).
% 0.20/0.47  thf('50', plain, (![X0 : $i]: ((sk_B) = (X0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['49'])).
% 0.20/0.47  thf('51', plain,
% 0.20/0.47      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.20/0.47         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.20/0.47  thf('52', plain,
% 0.20/0.47      (![X19 : $i]:
% 0.20/0.47         ((k4_xboole_0 @ (k1_tarski @ X19) @ (k1_tarski @ X19))
% 0.20/0.47           != (k1_tarski @ X19))),
% 0.20/0.47      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.47  thf('53', plain,
% 0.20/0.47      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0) != (k1_tarski @ sk_B)))
% 0.20/0.47         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.47  thf('54', plain,
% 0.20/0.47      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.20/0.47         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.20/0.47  thf('55', plain,
% 0.20/0.47      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.20/0.47         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.20/0.47  thf('56', plain,
% 0.20/0.47      ((((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.47         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.47      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.20/0.47  thf('57', plain,
% 0.20/0.47      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))),
% 0.20/0.47      inference('sat_resolution*', [status(thm)], ['40', '41'])).
% 0.20/0.47  thf('58', plain,
% 0.20/0.47      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.47      inference('simpl_trail', [status(thm)], ['56', '57'])).
% 0.20/0.47  thf('59', plain, (![X0 : $i]: ((sk_B) = (X0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['49'])).
% 0.20/0.47  thf('60', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.47      inference('demod', [status(thm)], ['58', '59'])).
% 0.20/0.47  thf('61', plain, (![X0 : $i]: ((X0) != (k1_xboole_0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['50', '60'])).
% 0.20/0.47  thf('62', plain, ($false), inference('simplify', [status(thm)], ['61'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

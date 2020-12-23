%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SPFoQ3iJP9

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:16 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 181 expanded)
%              Number of leaves         :   19 (  64 expanded)
%              Depth                    :   15
%              Number of atoms          :  573 (1462 expanded)
%              Number of equality atoms :   44 ( 130 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t127_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_xboole_0 @ A @ B )
        | ( r1_xboole_0 @ C @ D ) )
     => ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_xboole_0 @ A @ B )
          | ( r1_xboole_0 @ C @ D ) )
       => ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t127_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( r1_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r1_xboole_0 @ sk_C_1 @ sk_D )
   <= ( r1_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(split,[status(esa)],['1'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('4',plain,
    ( ( ( k4_xboole_0 @ sk_C_1 @ sk_D )
      = sk_C_1 )
   <= ( r1_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,
    ( ( ( k4_xboole_0 @ sk_C_1 @ sk_C_1 )
      = ( k3_xboole_0 @ sk_C_1 @ sk_D ) )
   <= ( r1_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('7',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('10',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ sk_C_1 @ sk_D ) )
   <= ( r1_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['6','11'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('13',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X14 @ X16 ) @ ( k3_xboole_0 @ X15 @ X17 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X14 @ X15 ) @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('16',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('19',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','22'])).

thf('24',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X14 @ X16 ) @ ( k3_xboole_0 @ X15 @ X17 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X14 @ X15 ) @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ sk_C_1 @ sk_D ) ) )
        | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ sk_C_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_D ) ) )
   <= ( r1_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['12','25'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('27',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_zfmisc_1 @ X12 @ X13 )
        = k1_xboole_0 )
      | ( X13 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('28',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ sk_C_1 @ sk_D ) )
   <= ( r1_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['6','11'])).

thf('30',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('31',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('32',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ X10 )
      | ( ( k4_xboole_0 @ X8 @ X10 )
       != X8 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( X0 != X0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ! [X0: $i,X1: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ sk_C_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_D ) )
   <= ( r1_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['26','28','29','30','34'])).

thf('36',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['1'])).

thf('37',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('38',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('40',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_A )
      = ( k3_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('42',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X3 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('44',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        | ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ X1 ) @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_zfmisc_1 @ X12 @ X13 )
        = k1_xboole_0 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('46',plain,(
    ! [X13: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X13 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('48',plain,(
    ! [X13: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X13 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('49',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('50',plain,
    ( ! [X0: $i,X1: $i] :
        ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ X1 ) @ ( k2_zfmisc_1 @ sk_B @ X0 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['44','46','47','48','49'])).

thf('51',plain,(
    ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( r1_xboole_0 @ sk_C_1 @ sk_D )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['1'])).

thf('54',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_D ),
    inference('sat_resolution*',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ sk_C_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_D ) ) ),
    inference(simpl_trail,[status(thm)],['35','54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['0','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SPFoQ3iJP9
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:20:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.50/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.50/0.71  % Solved by: fo/fo7.sh
% 0.50/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.71  % done 259 iterations in 0.252s
% 0.50/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.50/0.71  % SZS output start Refutation
% 0.50/0.71  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.50/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.50/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.50/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.50/0.71  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.50/0.71  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.50/0.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.50/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.50/0.71  thf(sk_D_type, type, sk_D: $i).
% 0.50/0.71  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.50/0.71  thf(t127_zfmisc_1, conjecture,
% 0.50/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.71     ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 0.50/0.71       ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.50/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.71    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.71        ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 0.50/0.71          ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )),
% 0.50/0.71    inference('cnf.neg', [status(esa)], [t127_zfmisc_1])).
% 0.50/0.71  thf('0', plain,
% 0.50/0.71      (~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_C_1) @ 
% 0.50/0.71          (k2_zfmisc_1 @ sk_B @ sk_D))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('1', plain,
% 0.50/0.71      (((r1_xboole_0 @ sk_A @ sk_B) | (r1_xboole_0 @ sk_C_1 @ sk_D))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('2', plain,
% 0.50/0.71      (((r1_xboole_0 @ sk_C_1 @ sk_D)) <= (((r1_xboole_0 @ sk_C_1 @ sk_D)))),
% 0.50/0.71      inference('split', [status(esa)], ['1'])).
% 0.50/0.71  thf(t83_xboole_1, axiom,
% 0.50/0.71    (![A:$i,B:$i]:
% 0.50/0.71     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.50/0.71  thf('3', plain,
% 0.50/0.71      (![X8 : $i, X9 : $i]:
% 0.50/0.71         (((k4_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 0.50/0.71      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.50/0.71  thf('4', plain,
% 0.50/0.71      ((((k4_xboole_0 @ sk_C_1 @ sk_D) = (sk_C_1)))
% 0.50/0.71         <= (((r1_xboole_0 @ sk_C_1 @ sk_D)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['2', '3'])).
% 0.50/0.71  thf(t48_xboole_1, axiom,
% 0.50/0.71    (![A:$i,B:$i]:
% 0.50/0.71     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.50/0.71  thf('5', plain,
% 0.50/0.71      (![X6 : $i, X7 : $i]:
% 0.50/0.71         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.50/0.71           = (k3_xboole_0 @ X6 @ X7))),
% 0.50/0.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.50/0.71  thf('6', plain,
% 0.50/0.71      ((((k4_xboole_0 @ sk_C_1 @ sk_C_1) = (k3_xboole_0 @ sk_C_1 @ sk_D)))
% 0.50/0.71         <= (((r1_xboole_0 @ sk_C_1 @ sk_D)))),
% 0.50/0.71      inference('sup+', [status(thm)], ['4', '5'])).
% 0.50/0.71  thf(t3_boole, axiom,
% 0.50/0.71    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.50/0.71  thf('7', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.50/0.71      inference('cnf', [status(esa)], [t3_boole])).
% 0.50/0.71  thf('8', plain,
% 0.50/0.71      (![X6 : $i, X7 : $i]:
% 0.50/0.71         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.50/0.71           = (k3_xboole_0 @ X6 @ X7))),
% 0.50/0.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.50/0.71  thf('9', plain,
% 0.50/0.71      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.50/0.71      inference('sup+', [status(thm)], ['7', '8'])).
% 0.50/0.71  thf(t2_boole, axiom,
% 0.50/0.71    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.50/0.71  thf('10', plain,
% 0.50/0.71      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.50/0.71      inference('cnf', [status(esa)], [t2_boole])).
% 0.50/0.71  thf('11', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.50/0.71      inference('demod', [status(thm)], ['9', '10'])).
% 0.50/0.71  thf('12', plain,
% 0.50/0.71      ((((k1_xboole_0) = (k3_xboole_0 @ sk_C_1 @ sk_D)))
% 0.50/0.71         <= (((r1_xboole_0 @ sk_C_1 @ sk_D)))),
% 0.50/0.71      inference('demod', [status(thm)], ['6', '11'])).
% 0.50/0.71  thf(t123_zfmisc_1, axiom,
% 0.50/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.71     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 0.50/0.71       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.50/0.71  thf('13', plain,
% 0.50/0.71      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.50/0.71         ((k2_zfmisc_1 @ (k3_xboole_0 @ X14 @ X16) @ (k3_xboole_0 @ X15 @ X17))
% 0.50/0.71           = (k3_xboole_0 @ (k2_zfmisc_1 @ X14 @ X15) @ 
% 0.50/0.71              (k2_zfmisc_1 @ X16 @ X17)))),
% 0.50/0.71      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.50/0.71  thf(t4_xboole_0, axiom,
% 0.50/0.71    (![A:$i,B:$i]:
% 0.50/0.71     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.50/0.71            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.50/0.71       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.50/0.71            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.50/0.71  thf('14', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((r1_xboole_0 @ X0 @ X1)
% 0.50/0.71          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.50/0.71      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.50/0.71  thf('15', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.50/0.71      inference('demod', [status(thm)], ['9', '10'])).
% 0.50/0.71  thf('16', plain,
% 0.50/0.71      (![X6 : $i, X7 : $i]:
% 0.50/0.71         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.50/0.71           = (k3_xboole_0 @ X6 @ X7))),
% 0.50/0.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.50/0.71  thf('17', plain,
% 0.50/0.71      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.50/0.71      inference('sup+', [status(thm)], ['15', '16'])).
% 0.50/0.71  thf('18', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.50/0.71      inference('cnf', [status(esa)], [t3_boole])).
% 0.50/0.71  thf('19', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.50/0.71      inference('demod', [status(thm)], ['17', '18'])).
% 0.50/0.71  thf('20', plain,
% 0.50/0.71      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.50/0.71         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.50/0.71          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.50/0.71      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.50/0.71  thf('21', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.50/0.71      inference('sup-', [status(thm)], ['19', '20'])).
% 0.50/0.71  thf('22', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((r1_xboole_0 @ X1 @ X0)
% 0.50/0.71          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['14', '21'])).
% 0.50/0.71  thf('23', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.50/0.71         (~ (r1_xboole_0 @ 
% 0.50/0.71             (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.50/0.71             (k3_xboole_0 @ (k2_zfmisc_1 @ X3 @ X1) @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.50/0.71          | (r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ X1) @ (k2_zfmisc_1 @ X2 @ X0)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['13', '22'])).
% 0.50/0.71  thf('24', plain,
% 0.50/0.71      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.50/0.71         ((k2_zfmisc_1 @ (k3_xboole_0 @ X14 @ X16) @ (k3_xboole_0 @ X15 @ X17))
% 0.50/0.71           = (k3_xboole_0 @ (k2_zfmisc_1 @ X14 @ X15) @ 
% 0.50/0.71              (k2_zfmisc_1 @ X16 @ X17)))),
% 0.50/0.71      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.50/0.71  thf('25', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.50/0.71         (~ (r1_xboole_0 @ 
% 0.50/0.71             (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.50/0.71             (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0)))
% 0.50/0.71          | (r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ X1) @ (k2_zfmisc_1 @ X2 @ X0)))),
% 0.50/0.71      inference('demod', [status(thm)], ['23', '24'])).
% 0.50/0.71  thf('26', plain,
% 0.50/0.71      ((![X0 : $i, X1 : $i]:
% 0.50/0.71          (~ (r1_xboole_0 @ 
% 0.50/0.71              (k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ X0) @ k1_xboole_0) @ 
% 0.50/0.71              (k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.50/0.71               (k3_xboole_0 @ sk_C_1 @ sk_D)))
% 0.50/0.71           | (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ sk_C_1) @ 
% 0.50/0.71              (k2_zfmisc_1 @ X0 @ sk_D))))
% 0.50/0.71         <= (((r1_xboole_0 @ sk_C_1 @ sk_D)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['12', '25'])).
% 0.50/0.71  thf(t113_zfmisc_1, axiom,
% 0.50/0.71    (![A:$i,B:$i]:
% 0.50/0.71     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.50/0.71       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.50/0.71  thf('27', plain,
% 0.50/0.71      (![X12 : $i, X13 : $i]:
% 0.50/0.71         (((k2_zfmisc_1 @ X12 @ X13) = (k1_xboole_0))
% 0.50/0.71          | ((X13) != (k1_xboole_0)))),
% 0.50/0.71      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.50/0.71  thf('28', plain,
% 0.50/0.71      (![X12 : $i]: ((k2_zfmisc_1 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 0.50/0.71      inference('simplify', [status(thm)], ['27'])).
% 0.50/0.71  thf('29', plain,
% 0.50/0.71      ((((k1_xboole_0) = (k3_xboole_0 @ sk_C_1 @ sk_D)))
% 0.50/0.71         <= (((r1_xboole_0 @ sk_C_1 @ sk_D)))),
% 0.50/0.71      inference('demod', [status(thm)], ['6', '11'])).
% 0.50/0.71  thf('30', plain,
% 0.50/0.71      (![X12 : $i]: ((k2_zfmisc_1 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 0.50/0.71      inference('simplify', [status(thm)], ['27'])).
% 0.50/0.71  thf('31', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.50/0.71      inference('cnf', [status(esa)], [t3_boole])).
% 0.50/0.71  thf('32', plain,
% 0.50/0.71      (![X8 : $i, X10 : $i]:
% 0.50/0.71         ((r1_xboole_0 @ X8 @ X10) | ((k4_xboole_0 @ X8 @ X10) != (X8)))),
% 0.50/0.71      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.50/0.71  thf('33', plain,
% 0.50/0.71      (![X0 : $i]: (((X0) != (X0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.50/0.71      inference('sup-', [status(thm)], ['31', '32'])).
% 0.50/0.71  thf('34', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.50/0.71      inference('simplify', [status(thm)], ['33'])).
% 0.50/0.71  thf('35', plain,
% 0.50/0.71      ((![X0 : $i, X1 : $i]:
% 0.50/0.71          (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ sk_C_1) @ 
% 0.50/0.71           (k2_zfmisc_1 @ X0 @ sk_D)))
% 0.50/0.71         <= (((r1_xboole_0 @ sk_C_1 @ sk_D)))),
% 0.50/0.71      inference('demod', [status(thm)], ['26', '28', '29', '30', '34'])).
% 0.50/0.71  thf('36', plain,
% 0.50/0.71      (((r1_xboole_0 @ sk_A @ sk_B)) <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.50/0.71      inference('split', [status(esa)], ['1'])).
% 0.50/0.71  thf('37', plain,
% 0.50/0.71      (![X8 : $i, X9 : $i]:
% 0.50/0.71         (((k4_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 0.50/0.71      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.50/0.71  thf('38', plain,
% 0.50/0.71      ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))
% 0.50/0.71         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['36', '37'])).
% 0.50/0.71  thf('39', plain,
% 0.50/0.71      (![X6 : $i, X7 : $i]:
% 0.50/0.71         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.50/0.71           = (k3_xboole_0 @ X6 @ X7))),
% 0.50/0.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.50/0.71  thf('40', plain,
% 0.50/0.71      ((((k4_xboole_0 @ sk_A @ sk_A) = (k3_xboole_0 @ sk_A @ sk_B)))
% 0.50/0.71         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.50/0.71      inference('sup+', [status(thm)], ['38', '39'])).
% 0.50/0.71  thf('41', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.50/0.71      inference('demod', [status(thm)], ['9', '10'])).
% 0.50/0.71  thf('42', plain,
% 0.50/0.71      ((((k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_B)))
% 0.50/0.71         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.50/0.71      inference('demod', [status(thm)], ['40', '41'])).
% 0.50/0.71  thf('43', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.50/0.71         (~ (r1_xboole_0 @ 
% 0.50/0.71             (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.50/0.71             (k2_zfmisc_1 @ (k3_xboole_0 @ X3 @ X2) @ (k3_xboole_0 @ X1 @ X0)))
% 0.50/0.71          | (r1_xboole_0 @ (k2_zfmisc_1 @ X3 @ X1) @ (k2_zfmisc_1 @ X2 @ X0)))),
% 0.50/0.71      inference('demod', [status(thm)], ['23', '24'])).
% 0.50/0.71  thf('44', plain,
% 0.50/0.71      ((![X0 : $i, X1 : $i]:
% 0.50/0.71          (~ (r1_xboole_0 @ 
% 0.50/0.71              (k2_zfmisc_1 @ k1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.50/0.71              (k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 0.50/0.71               (k3_xboole_0 @ X1 @ X0)))
% 0.50/0.71           | (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ X1) @ 
% 0.50/0.71              (k2_zfmisc_1 @ sk_B @ X0))))
% 0.50/0.71         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['42', '43'])).
% 0.50/0.71  thf('45', plain,
% 0.50/0.71      (![X12 : $i, X13 : $i]:
% 0.50/0.71         (((k2_zfmisc_1 @ X12 @ X13) = (k1_xboole_0))
% 0.50/0.71          | ((X12) != (k1_xboole_0)))),
% 0.50/0.71      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.50/0.71  thf('46', plain,
% 0.50/0.71      (![X13 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X13) = (k1_xboole_0))),
% 0.50/0.71      inference('simplify', [status(thm)], ['45'])).
% 0.50/0.71  thf('47', plain,
% 0.50/0.71      ((((k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_B)))
% 0.50/0.71         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.50/0.71      inference('demod', [status(thm)], ['40', '41'])).
% 0.50/0.71  thf('48', plain,
% 0.50/0.71      (![X13 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X13) = (k1_xboole_0))),
% 0.50/0.71      inference('simplify', [status(thm)], ['45'])).
% 0.50/0.71  thf('49', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.50/0.71      inference('simplify', [status(thm)], ['33'])).
% 0.50/0.71  thf('50', plain,
% 0.50/0.71      ((![X0 : $i, X1 : $i]:
% 0.50/0.71          (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ X1) @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.50/0.71         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.50/0.71      inference('demod', [status(thm)], ['44', '46', '47', '48', '49'])).
% 0.50/0.71  thf('51', plain,
% 0.50/0.71      (~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_C_1) @ 
% 0.50/0.71          (k2_zfmisc_1 @ sk_B @ sk_D))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('52', plain, (~ ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.50/0.71      inference('sup-', [status(thm)], ['50', '51'])).
% 0.50/0.71  thf('53', plain,
% 0.50/0.71      (((r1_xboole_0 @ sk_C_1 @ sk_D)) | ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.50/0.71      inference('split', [status(esa)], ['1'])).
% 0.50/0.71  thf('54', plain, (((r1_xboole_0 @ sk_C_1 @ sk_D))),
% 0.50/0.71      inference('sat_resolution*', [status(thm)], ['52', '53'])).
% 0.50/0.71  thf('55', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ sk_C_1) @ (k2_zfmisc_1 @ X0 @ sk_D))),
% 0.50/0.71      inference('simpl_trail', [status(thm)], ['35', '54'])).
% 0.50/0.71  thf('56', plain, ($false), inference('demod', [status(thm)], ['0', '55'])).
% 0.50/0.71  
% 0.50/0.71  % SZS output end Refutation
% 0.50/0.71  
% 0.50/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

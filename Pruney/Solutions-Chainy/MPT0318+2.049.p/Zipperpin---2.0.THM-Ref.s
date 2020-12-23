%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ddLFl6F0dC

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:27 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 395 expanded)
%              Number of leaves         :   16 ( 104 expanded)
%              Depth                    :   20
%              Number of atoms          :  633 (4487 expanded)
%              Number of equality atoms :  116 ( 919 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

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

thf('1',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['1'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('3',plain,(
    ! [X31: $i,X32: $i] :
      ( ( X31 = k1_xboole_0 )
      | ( X32 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X32 @ X31 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('4',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf(t19_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k1_tarski @ A ) ) )).

thf('8',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X34 ) @ ( k2_tarski @ X34 @ X35 ) )
      = ( k1_tarski @ X34 ) ) ),
    inference(cnf,[status(esa)],[t19_zfmisc_1])).

thf('9',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_B @ X0 ) )
        = ( k1_tarski @ sk_B ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('11',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_B @ X0 ) )
        = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('13',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['1'])).

thf('14',plain,(
    ! [X31: $i,X32: $i] :
      ( ( X31 = k1_xboole_0 )
      | ( X32 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X32 @ X31 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('15',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X34 ) @ ( k2_tarski @ X34 @ X35 ) )
      = ( k1_tarski @ X34 ) ) ),
    inference(cnf,[status(esa)],[t19_zfmisc_1])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_B @ X0 ) )
        = ( k1_tarski @ sk_B ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

thf('22',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_B @ X0 ) )
        = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k3_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','22'])).

thf('24',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

thf('25',plain,
    ( ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('27',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('28',plain,(
    ! [X2: $i] :
      ( ( k5_xboole_0 @ X2 @ X2 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('29',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('31',plain,(
    ! [X36: $i,X37: $i] :
      ( ( X37 != X36 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X37 ) @ ( k1_tarski @ X36 ) )
       != ( k1_tarski @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('32',plain,(
    ! [X36: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X36 ) @ ( k1_tarski @ X36 ) )
     != ( k1_tarski @ X36 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_B ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

thf('35',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

thf('36',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['29','36'])).

thf('38',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['1'])).

thf('39',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_B @ X0 ) )
      = k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['11','39'])).

thf('41',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['0','40'])).

thf('42',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('43',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['37','38'])).

thf('44',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('47',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X2: $i] :
      ( ( k5_xboole_0 @ X2 @ X2 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('49',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('51',plain,(
    ! [X36: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X36 ) @ ( k1_tarski @ X36 ) )
     != ( k1_tarski @ X36 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('52',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_B ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('54',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('55',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['37','38'])).

thf('57',plain,(
    ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['55','56'])).

thf('58',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['49','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ddLFl6F0dC
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:48:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 103 iterations in 0.031s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.48  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.48  thf(t69_enumset1, axiom,
% 0.20/0.48    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.48  thf('0', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.48  thf(t130_zfmisc_1, conjecture,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.20/0.48       ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.48         ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i]:
% 0.20/0.48        ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.20/0.48          ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.48            ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t130_zfmisc_1])).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))
% 0.20/0.48        | ((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))
% 0.20/0.48         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.48      inference('split', [status(esa)], ['1'])).
% 0.20/0.48  thf(t113_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.48       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X31 : $i, X32 : $i]:
% 0.20/0.48         (((X31) = (k1_xboole_0))
% 0.20/0.48          | ((X32) = (k1_xboole_0))
% 0.20/0.48          | ((k2_zfmisc_1 @ X32 @ X31) != (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.48         | ((sk_A) = (k1_xboole_0))
% 0.20/0.48         | ((k1_tarski @ sk_B) = (k1_xboole_0))))
% 0.20/0.48         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (((((k1_tarski @ sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.20/0.48         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.48      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.48  thf('6', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.20/0.48         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf(t19_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.20/0.48       ( k1_tarski @ A ) ))).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X34 : $i, X35 : $i]:
% 0.20/0.48         ((k3_xboole_0 @ (k1_tarski @ X34) @ (k2_tarski @ X34 @ X35))
% 0.20/0.48           = (k1_tarski @ X34))),
% 0.20/0.48      inference('cnf', [status(esa)], [t19_zfmisc_1])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      ((![X0 : $i]:
% 0.20/0.48          ((k3_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_B @ X0))
% 0.20/0.48            = (k1_tarski @ sk_B)))
% 0.20/0.48         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.48      inference('sup+', [status(thm)], ['7', '8'])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.20/0.48         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      ((![X0 : $i]:
% 0.20/0.48          ((k3_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_B @ X0))
% 0.20/0.48            = (k1_xboole_0)))
% 0.20/0.48         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.48      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.48  thf('12', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))
% 0.20/0.48         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.48      inference('split', [status(esa)], ['1'])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X31 : $i, X32 : $i]:
% 0.20/0.48         (((X31) = (k1_xboole_0))
% 0.20/0.48          | ((X32) = (k1_xboole_0))
% 0.20/0.48          | ((k2_zfmisc_1 @ X32 @ X31) != (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.48         | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.20/0.48         | ((sk_A) = (k1_xboole_0))))
% 0.20/0.48         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (((((sk_A) = (k1_xboole_0)) | ((k1_tarski @ sk_B) = (k1_xboole_0))))
% 0.20/0.48         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.48      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.48  thf('17', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.20/0.48         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (![X34 : $i, X35 : $i]:
% 0.20/0.48         ((k3_xboole_0 @ (k1_tarski @ X34) @ (k2_tarski @ X34 @ X35))
% 0.20/0.48           = (k1_tarski @ X34))),
% 0.20/0.48      inference('cnf', [status(esa)], [t19_zfmisc_1])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      ((![X0 : $i]:
% 0.20/0.48          ((k3_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_B @ X0))
% 0.20/0.48            = (k1_tarski @ sk_B)))
% 0.20/0.48         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.48      inference('sup+', [status(thm)], ['18', '19'])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.20/0.48         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      ((![X0 : $i]:
% 0.20/0.48          ((k3_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_B @ X0))
% 0.20/0.48            = (k1_xboole_0)))
% 0.20/0.48         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.48      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      ((((k3_xboole_0 @ k1_xboole_0 @ (k1_tarski @ sk_B)) = (k1_xboole_0)))
% 0.20/0.48         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.48      inference('sup+', [status(thm)], ['12', '22'])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.20/0.48         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      ((((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0)))
% 0.20/0.48         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.48      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.48  thf(t100_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((k4_xboole_0 @ X0 @ X1)
% 0.20/0.48           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      ((((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.20/0.48          = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0)))
% 0.20/0.48         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.48      inference('sup+', [status(thm)], ['25', '26'])).
% 0.20/0.48  thf(t92_xboole_1, axiom,
% 0.20/0.48    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.48  thf('28', plain, (![X2 : $i]: ((k5_xboole_0 @ X2 @ X2) = (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      ((((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0)))
% 0.20/0.48         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.48      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.20/0.48         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 0.20/0.48  thf(t20_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.48         ( k1_tarski @ A ) ) <=>
% 0.20/0.48       ( ( A ) != ( B ) ) ))).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      (![X36 : $i, X37 : $i]:
% 0.20/0.48         (((X37) != (X36))
% 0.20/0.48          | ((k4_xboole_0 @ (k1_tarski @ X37) @ (k1_tarski @ X36))
% 0.20/0.48              != (k1_tarski @ X37)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      (![X36 : $i]:
% 0.20/0.48         ((k4_xboole_0 @ (k1_tarski @ X36) @ (k1_tarski @ X36))
% 0.20/0.48           != (k1_tarski @ X36))),
% 0.20/0.48      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.48  thf('33', plain,
% 0.20/0.48      ((((k4_xboole_0 @ k1_xboole_0 @ (k1_tarski @ sk_B)) != (k1_tarski @ sk_B)))
% 0.20/0.48         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['30', '32'])).
% 0.20/0.48  thf('34', plain,
% 0.20/0.48      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.20/0.48         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.20/0.48         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      ((((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.48         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.48      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.20/0.48  thf('37', plain,
% 0.20/0.48      (~ (((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['29', '36'])).
% 0.20/0.48  thf('38', plain,
% 0.20/0.48      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))) | 
% 0.20/0.48       (((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('split', [status(esa)], ['1'])).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['37', '38'])).
% 0.20/0.48  thf('40', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((k3_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_B @ X0)) = (k1_xboole_0))),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['11', '39'])).
% 0.20/0.48  thf('41', plain,
% 0.20/0.48      (((k3_xboole_0 @ k1_xboole_0 @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['0', '40'])).
% 0.20/0.48  thf('42', plain,
% 0.20/0.48      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.20/0.48         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf('43', plain,
% 0.20/0.48      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['37', '38'])).
% 0.20/0.48  thf('44', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['42', '43'])).
% 0.20/0.48  thf('45', plain,
% 0.20/0.48      (((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.48      inference('demod', [status(thm)], ['41', '44'])).
% 0.20/0.48  thf('46', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((k4_xboole_0 @ X0 @ X1)
% 0.20/0.48           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.48  thf('47', plain,
% 0.20/0.48      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.20/0.48         = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['45', '46'])).
% 0.20/0.48  thf('48', plain, (![X2 : $i]: ((k5_xboole_0 @ X2 @ X2) = (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.48  thf('49', plain,
% 0.20/0.48      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.48      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.48  thf('50', plain,
% 0.20/0.48      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.20/0.48         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf('51', plain,
% 0.20/0.48      (![X36 : $i]:
% 0.20/0.48         ((k4_xboole_0 @ (k1_tarski @ X36) @ (k1_tarski @ X36))
% 0.20/0.48           != (k1_tarski @ X36))),
% 0.20/0.48      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.48  thf('52', plain,
% 0.20/0.48      ((((k4_xboole_0 @ k1_xboole_0 @ (k1_tarski @ sk_B)) != (k1_tarski @ sk_B)))
% 0.20/0.48         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.48  thf('53', plain,
% 0.20/0.48      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.20/0.48         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf('54', plain,
% 0.20/0.48      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.20/0.48         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf('55', plain,
% 0.20/0.48      ((((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.48         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.48      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.20/0.48  thf('56', plain,
% 0.20/0.48      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['37', '38'])).
% 0.20/0.48  thf('57', plain,
% 0.20/0.48      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['55', '56'])).
% 0.20/0.48  thf('58', plain, ($false),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['49', '57'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

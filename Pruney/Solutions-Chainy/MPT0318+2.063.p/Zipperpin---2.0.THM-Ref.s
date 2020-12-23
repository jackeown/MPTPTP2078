%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6EisV4pUkk

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:29 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 348 expanded)
%              Number of leaves         :   18 ( 102 expanded)
%              Depth                    :   20
%              Number of atoms          :  625 (3548 expanded)
%              Number of equality atoms :  103 ( 635 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

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
    ! [X4: $i,X5: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X5 @ X4 )
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

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('8',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t27_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
     => ( ( k2_tarski @ A @ B )
        = ( k1_tarski @ C ) ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k2_tarski @ X8 @ X9 )
        = ( k1_tarski @ X7 ) )
      | ~ ( r1_tarski @ ( k2_tarski @ X8 @ X9 ) @ ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t27_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( ( k2_tarski @ X0 @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( ( k1_tarski @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        | ( ( k1_tarski @ sk_B )
          = ( k1_tarski @ X0 ) ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t42_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('15',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ ( k2_tarski @ X10 @ X13 ) )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t42_zfmisc_1])).

thf('16',plain,(
    ! [X10: $i,X13: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k2_tarski @ X10 @ X13 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','16'])).

thf('18',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('19',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k1_tarski @ X0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','17','18'])).

thf('20',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t73_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = k1_xboole_0 )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X14 @ X15 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X14 @ X16 ) @ X15 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t73_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
       != k1_xboole_0 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
         != k1_xboole_0 )
        | ( r2_hidden @ X1 @ X0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('24',plain,(
    ! [X2: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('25',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ( r2_hidden @ X1 @ X0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ! [X0: $i,X1: $i] :
        ( r2_hidden @ X1 @ X0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['1'])).

thf('28',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X5 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('29',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( ( k1_tarski @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        | ( ( k1_tarski @ sk_B )
          = ( k1_tarski @ X0 ) ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','16'])).

thf('36',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['30','31'])).

thf('37',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k1_tarski @ X0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
       != k1_xboole_0 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('39',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
         != k1_xboole_0 )
        | ( r2_hidden @ X1 @ X0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X2: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('41',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ( r2_hidden @ X1 @ X0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ! [X0: $i,X1: $i] :
        ( r2_hidden @ X1 @ X0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('44',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
        | ( X1 = X0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ! [X0: $i,X1: $i] :
        ( r2_hidden @ X1 @ X0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('46',plain,
    ( ! [X0: $i,X1: $i] : ( X1 = X0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ! [X0: $i] : ( sk_A != X0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
 != k1_xboole_0 ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['1'])).

thf('51',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ X0 ) ),
    inference(simpl_trail,[status(thm)],['26','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ X0 ) ),
    inference(simpl_trail,[status(thm)],['26','51'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] : ( X1 = X0 ) ),
    inference(demod,[status(thm)],['0','52','53'])).

thf('55',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] : ( sk_A != X0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    $false ),
    inference(simplify,[status(thm)],['56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6EisV4pUkk
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:37:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.53  % Solved by: fo/fo7.sh
% 0.35/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.53  % done 105 iterations in 0.070s
% 0.35/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.53  % SZS output start Refutation
% 0.35/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.35/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.35/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.35/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.35/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.53  thf(t2_tarski, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.35/0.53       ( ( A ) = ( B ) ) ))).
% 0.35/0.53  thf('0', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         (((X1) = (X0))
% 0.35/0.53          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.35/0.53          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 0.35/0.53      inference('cnf', [status(esa)], [t2_tarski])).
% 0.35/0.53  thf(t130_zfmisc_1, conjecture,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.35/0.53       ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.35/0.53         ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.35/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.53    (~( ![A:$i,B:$i]:
% 0.35/0.53        ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.35/0.53          ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.35/0.53            ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ) )),
% 0.35/0.53    inference('cnf.neg', [status(esa)], [t130_zfmisc_1])).
% 0.35/0.53  thf('1', plain,
% 0.35/0.53      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))
% 0.35/0.53        | ((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('2', plain,
% 0.35/0.53      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))
% 0.35/0.53         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.35/0.53      inference('split', [status(esa)], ['1'])).
% 0.35/0.53  thf(t113_zfmisc_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.35/0.53       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.35/0.53  thf('3', plain,
% 0.35/0.53      (![X4 : $i, X5 : $i]:
% 0.35/0.53         (((X4) = (k1_xboole_0))
% 0.35/0.53          | ((X5) = (k1_xboole_0))
% 0.35/0.53          | ((k2_zfmisc_1 @ X5 @ X4) != (k1_xboole_0)))),
% 0.35/0.53      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.35/0.53  thf('4', plain,
% 0.35/0.53      (((((k1_xboole_0) != (k1_xboole_0))
% 0.35/0.53         | ((sk_A) = (k1_xboole_0))
% 0.35/0.53         | ((k1_tarski @ sk_B) = (k1_xboole_0))))
% 0.35/0.53         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.35/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.35/0.53  thf('5', plain,
% 0.35/0.53      (((((k1_tarski @ sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.35/0.53         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.35/0.53      inference('simplify', [status(thm)], ['4'])).
% 0.35/0.53  thf('6', plain, (((sk_A) != (k1_xboole_0))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('7', plain,
% 0.35/0.53      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.35/0.53         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.35/0.53      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.35/0.53  thf(t69_enumset1, axiom,
% 0.35/0.53    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.35/0.53  thf('8', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.35/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.35/0.53  thf(t27_zfmisc_1, axiom,
% 0.35/0.53    (![A:$i,B:$i,C:$i]:
% 0.35/0.53     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.35/0.53       ( ( k2_tarski @ A @ B ) = ( k1_tarski @ C ) ) ))).
% 0.35/0.53  thf('9', plain,
% 0.35/0.53      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.35/0.53         (((k2_tarski @ X8 @ X9) = (k1_tarski @ X7))
% 0.35/0.53          | ~ (r1_tarski @ (k2_tarski @ X8 @ X9) @ (k1_tarski @ X7)))),
% 0.35/0.53      inference('cnf', [status(esa)], [t27_zfmisc_1])).
% 0.35/0.53  thf('10', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         (~ (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.35/0.53          | ((k2_tarski @ X0 @ X0) = (k1_tarski @ X1)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['8', '9'])).
% 0.35/0.53  thf('11', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.35/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.35/0.53  thf('12', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         (~ (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.35/0.53          | ((k1_tarski @ X0) = (k1_tarski @ X1)))),
% 0.35/0.53      inference('demod', [status(thm)], ['10', '11'])).
% 0.35/0.53  thf('13', plain,
% 0.35/0.53      ((![X0 : $i]:
% 0.35/0.53          (~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 0.35/0.53           | ((k1_tarski @ sk_B) = (k1_tarski @ X0))))
% 0.35/0.53         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.35/0.53      inference('sup-', [status(thm)], ['7', '12'])).
% 0.35/0.53  thf('14', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.35/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.35/0.53  thf(t42_zfmisc_1, axiom,
% 0.35/0.53    (![A:$i,B:$i,C:$i]:
% 0.35/0.53     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.35/0.53       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.35/0.53            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.35/0.53  thf('15', plain,
% 0.35/0.53      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.35/0.53         ((r1_tarski @ X12 @ (k2_tarski @ X10 @ X13))
% 0.35/0.53          | ((X12) != (k1_xboole_0)))),
% 0.35/0.53      inference('cnf', [status(esa)], [t42_zfmisc_1])).
% 0.35/0.53  thf('16', plain,
% 0.35/0.53      (![X10 : $i, X13 : $i]:
% 0.35/0.53         (r1_tarski @ k1_xboole_0 @ (k2_tarski @ X10 @ X13))),
% 0.35/0.53      inference('simplify', [status(thm)], ['15'])).
% 0.35/0.53  thf('17', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0))),
% 0.35/0.53      inference('sup+', [status(thm)], ['14', '16'])).
% 0.35/0.53  thf('18', plain,
% 0.35/0.53      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.35/0.53         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.35/0.53      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.35/0.53  thf('19', plain,
% 0.35/0.53      ((![X0 : $i]: ((k1_xboole_0) = (k1_tarski @ X0)))
% 0.35/0.53         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.35/0.53      inference('demod', [status(thm)], ['13', '17', '18'])).
% 0.35/0.53  thf('20', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.35/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.35/0.53  thf(t73_zfmisc_1, axiom,
% 0.35/0.53    (![A:$i,B:$i,C:$i]:
% 0.35/0.53     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_xboole_0 ) ) <=>
% 0.35/0.53       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.35/0.53  thf('21', plain,
% 0.35/0.53      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.35/0.53         ((r2_hidden @ X14 @ X15)
% 0.35/0.53          | ((k4_xboole_0 @ (k2_tarski @ X14 @ X16) @ X15) != (k1_xboole_0)))),
% 0.35/0.53      inference('cnf', [status(esa)], [t73_zfmisc_1])).
% 0.35/0.53  thf('22', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) != (k1_xboole_0))
% 0.35/0.53          | (r2_hidden @ X0 @ X1))),
% 0.35/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.35/0.53  thf('23', plain,
% 0.35/0.53      ((![X0 : $i, X1 : $i]:
% 0.35/0.53          (((k4_xboole_0 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 0.35/0.53           | (r2_hidden @ X1 @ X0)))
% 0.35/0.53         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.35/0.53      inference('sup-', [status(thm)], ['19', '22'])).
% 0.35/0.53  thf(t4_boole, axiom,
% 0.35/0.53    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.35/0.53  thf('24', plain,
% 0.35/0.53      (![X2 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.35/0.53      inference('cnf', [status(esa)], [t4_boole])).
% 0.35/0.53  thf('25', plain,
% 0.35/0.53      ((![X0 : $i, X1 : $i]:
% 0.35/0.53          (((k1_xboole_0) != (k1_xboole_0)) | (r2_hidden @ X1 @ X0)))
% 0.35/0.53         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.35/0.53      inference('demod', [status(thm)], ['23', '24'])).
% 0.35/0.53  thf('26', plain,
% 0.35/0.53      ((![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ X0))
% 0.35/0.53         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.35/0.53      inference('simplify', [status(thm)], ['25'])).
% 0.35/0.53  thf('27', plain,
% 0.35/0.53      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))
% 0.35/0.53         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.35/0.53      inference('split', [status(esa)], ['1'])).
% 0.35/0.53  thf('28', plain,
% 0.35/0.53      (![X4 : $i, X5 : $i]:
% 0.35/0.53         (((X4) = (k1_xboole_0))
% 0.35/0.53          | ((X5) = (k1_xboole_0))
% 0.35/0.53          | ((k2_zfmisc_1 @ X5 @ X4) != (k1_xboole_0)))),
% 0.35/0.53      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.35/0.53  thf('29', plain,
% 0.35/0.53      (((((k1_xboole_0) != (k1_xboole_0))
% 0.35/0.53         | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.35/0.53         | ((sk_A) = (k1_xboole_0))))
% 0.35/0.53         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.35/0.53      inference('sup-', [status(thm)], ['27', '28'])).
% 0.35/0.53  thf('30', plain,
% 0.35/0.53      (((((sk_A) = (k1_xboole_0)) | ((k1_tarski @ sk_B) = (k1_xboole_0))))
% 0.35/0.53         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.35/0.53      inference('simplify', [status(thm)], ['29'])).
% 0.35/0.53  thf('31', plain, (((sk_A) != (k1_xboole_0))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('32', plain,
% 0.35/0.53      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.35/0.53         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.35/0.53      inference('simplify_reflect-', [status(thm)], ['30', '31'])).
% 0.35/0.53  thf('33', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         (~ (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.35/0.53          | ((k1_tarski @ X0) = (k1_tarski @ X1)))),
% 0.35/0.53      inference('demod', [status(thm)], ['10', '11'])).
% 0.35/0.53  thf('34', plain,
% 0.35/0.53      ((![X0 : $i]:
% 0.35/0.53          (~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 0.35/0.53           | ((k1_tarski @ sk_B) = (k1_tarski @ X0))))
% 0.35/0.53         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.35/0.53      inference('sup-', [status(thm)], ['32', '33'])).
% 0.35/0.53  thf('35', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0))),
% 0.35/0.53      inference('sup+', [status(thm)], ['14', '16'])).
% 0.35/0.53  thf('36', plain,
% 0.35/0.53      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.35/0.53         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.35/0.53      inference('simplify_reflect-', [status(thm)], ['30', '31'])).
% 0.35/0.53  thf('37', plain,
% 0.35/0.53      ((![X0 : $i]: ((k1_xboole_0) = (k1_tarski @ X0)))
% 0.35/0.53         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.35/0.53      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.35/0.53  thf('38', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) != (k1_xboole_0))
% 0.35/0.53          | (r2_hidden @ X0 @ X1))),
% 0.35/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.35/0.53  thf('39', plain,
% 0.35/0.53      ((![X0 : $i, X1 : $i]:
% 0.35/0.53          (((k4_xboole_0 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 0.35/0.53           | (r2_hidden @ X1 @ X0)))
% 0.35/0.53         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.35/0.53      inference('sup-', [status(thm)], ['37', '38'])).
% 0.35/0.53  thf('40', plain,
% 0.35/0.53      (![X2 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.35/0.53      inference('cnf', [status(esa)], [t4_boole])).
% 0.35/0.53  thf('41', plain,
% 0.35/0.53      ((![X0 : $i, X1 : $i]:
% 0.35/0.53          (((k1_xboole_0) != (k1_xboole_0)) | (r2_hidden @ X1 @ X0)))
% 0.35/0.53         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.35/0.53      inference('demod', [status(thm)], ['39', '40'])).
% 0.35/0.53  thf('42', plain,
% 0.35/0.53      ((![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ X0))
% 0.35/0.53         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.35/0.53      inference('simplify', [status(thm)], ['41'])).
% 0.35/0.53  thf('43', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         (((X1) = (X0))
% 0.35/0.53          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.35/0.53          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 0.35/0.53      inference('cnf', [status(esa)], [t2_tarski])).
% 0.35/0.53  thf('44', plain,
% 0.35/0.53      ((![X0 : $i, X1 : $i]:
% 0.35/0.53          (~ (r2_hidden @ (sk_C @ X0 @ X1) @ X1) | ((X1) = (X0))))
% 0.35/0.53         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.35/0.53      inference('sup-', [status(thm)], ['42', '43'])).
% 0.35/0.53  thf('45', plain,
% 0.35/0.53      ((![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ X0))
% 0.35/0.53         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.35/0.53      inference('simplify', [status(thm)], ['41'])).
% 0.35/0.53  thf('46', plain,
% 0.35/0.53      ((![X0 : $i, X1 : $i]: ((X1) = (X0)))
% 0.35/0.53         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.35/0.53      inference('demod', [status(thm)], ['44', '45'])).
% 0.35/0.53  thf('47', plain, (((sk_A) != (k1_xboole_0))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('48', plain,
% 0.35/0.53      ((![X0 : $i]: ((sk_A) != (X0)))
% 0.35/0.53         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.35/0.53      inference('sup-', [status(thm)], ['46', '47'])).
% 0.35/0.53  thf('49', plain,
% 0.35/0.53      (~ (((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))),
% 0.35/0.53      inference('simplify', [status(thm)], ['48'])).
% 0.35/0.53  thf('50', plain,
% 0.35/0.53      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))) | 
% 0.35/0.53       (((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))),
% 0.35/0.53      inference('split', [status(esa)], ['1'])).
% 0.35/0.53  thf('51', plain,
% 0.35/0.53      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))),
% 0.35/0.53      inference('sat_resolution*', [status(thm)], ['49', '50'])).
% 0.35/0.53  thf('52', plain, (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ X0)),
% 0.35/0.53      inference('simpl_trail', [status(thm)], ['26', '51'])).
% 0.35/0.53  thf('53', plain, (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ X0)),
% 0.35/0.53      inference('simpl_trail', [status(thm)], ['26', '51'])).
% 0.35/0.53  thf('54', plain, (![X0 : $i, X1 : $i]: ((X1) = (X0))),
% 0.35/0.53      inference('demod', [status(thm)], ['0', '52', '53'])).
% 0.35/0.53  thf('55', plain, (((sk_A) != (k1_xboole_0))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('56', plain, (![X0 : $i]: ((sk_A) != (X0))),
% 0.35/0.53      inference('sup-', [status(thm)], ['54', '55'])).
% 0.35/0.53  thf('57', plain, ($false), inference('simplify', [status(thm)], ['56'])).
% 0.35/0.53  
% 0.35/0.53  % SZS output end Refutation
% 0.35/0.53  
% 0.40/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

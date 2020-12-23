%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5tyAkPLWM5

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:27 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 169 expanded)
%              Number of leaves         :   26 (  56 expanded)
%              Depth                    :   12
%              Number of atoms          :  601 (1572 expanded)
%              Number of equality atoms :  104 ( 291 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(t82_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_enumset1 @ A @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X31: $i] :
      ( ( k2_enumset1 @ X31 @ X31 @ X31 @ X31 )
      = ( k1_tarski @ X31 ) ) ),
    inference(cnf,[status(esa)],[t82_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X11 @ X11 @ X12 @ X13 )
      = ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('2',plain,(
    ! [X31: $i] :
      ( ( k1_enumset1 @ X31 @ X31 @ X31 )
      = ( k1_tarski @ X31 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('3',plain,(
    ! [X38: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X38 ) )
      = X38 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_enumset1 @ X0 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_enumset1 @ X9 @ X9 @ X10 )
      = ( k2_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t93_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X39 @ X40 ) )
      = ( k2_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t93_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['4','7'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k3_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('10',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X3 @ X4 ) @ X5 )
      = ( k5_xboole_0 @ X3 @ ( k5_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('11',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k3_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k5_xboole_0 @ X8 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('13',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('14',plain,(
    ! [X2: $i] :
      ( ( k5_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['12','15'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X2: $i] :
      ( ( k5_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('20',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['18','19'])).

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

thf('21',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('23',plain,(
    ! [X32: $i,X33: $i] :
      ( ( X32 = k1_xboole_0 )
      | ( X33 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X33 @ X32 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('24',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('28',plain,(
    ! [X35: $i,X36: $i] :
      ( ( X36 != X35 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X36 ) @ ( k1_tarski @ X35 ) )
       != ( k1_tarski @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('29',plain,(
    ! [X35: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X35 ) @ ( k1_tarski @ X35 ) )
     != ( k1_tarski @ X35 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
     != ( k1_tarski @ sk_B ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

thf('32',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

thf('33',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','33'])).

thf('35',plain,
    ( $false
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['18','19'])).

thf('37',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('38',plain,(
    ! [X32: $i,X33: $i] :
      ( ( X32 = k1_xboole_0 )
      | ( X33 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X33 @ X32 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('39',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X35: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X35 ) @ ( k1_tarski @ X35 ) )
     != ( k1_tarski @ X35 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('44',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
     != ( k1_tarski @ sk_B ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

thf('46',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

thf('47',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','47'])).

thf('49',plain,(
    ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
 != k1_xboole_0 ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('51',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['49','50'])).

thf('52',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['35','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5tyAkPLWM5
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:22:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.56  % Solved by: fo/fo7.sh
% 0.38/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.56  % done 191 iterations in 0.066s
% 0.38/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.56  % SZS output start Refutation
% 0.38/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.56  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.38/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.56  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.38/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.56  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.38/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.56  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.38/0.56  thf(t82_enumset1, axiom,
% 0.38/0.56    (![A:$i]: ( ( k2_enumset1 @ A @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.38/0.56  thf('0', plain,
% 0.38/0.56      (![X31 : $i]: ((k2_enumset1 @ X31 @ X31 @ X31 @ X31) = (k1_tarski @ X31))),
% 0.38/0.56      inference('cnf', [status(esa)], [t82_enumset1])).
% 0.38/0.56  thf(t71_enumset1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.38/0.56  thf('1', plain,
% 0.38/0.56      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.38/0.56         ((k2_enumset1 @ X11 @ X11 @ X12 @ X13)
% 0.38/0.56           = (k1_enumset1 @ X11 @ X12 @ X13))),
% 0.38/0.56      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.38/0.56  thf('2', plain,
% 0.38/0.56      (![X31 : $i]: ((k1_enumset1 @ X31 @ X31 @ X31) = (k1_tarski @ X31))),
% 0.38/0.56      inference('demod', [status(thm)], ['0', '1'])).
% 0.38/0.56  thf(t31_zfmisc_1, axiom,
% 0.38/0.56    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.38/0.56  thf('3', plain, (![X38 : $i]: ((k3_tarski @ (k1_tarski @ X38)) = (X38))),
% 0.38/0.56      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.38/0.56  thf('4', plain,
% 0.38/0.56      (![X0 : $i]: ((k3_tarski @ (k1_enumset1 @ X0 @ X0 @ X0)) = (X0))),
% 0.38/0.56      inference('sup+', [status(thm)], ['2', '3'])).
% 0.38/0.56  thf(t70_enumset1, axiom,
% 0.38/0.56    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.38/0.56  thf('5', plain,
% 0.38/0.56      (![X9 : $i, X10 : $i]:
% 0.38/0.56         ((k1_enumset1 @ X9 @ X9 @ X10) = (k2_tarski @ X9 @ X10))),
% 0.38/0.56      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.38/0.56  thf(t93_zfmisc_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.38/0.56  thf('6', plain,
% 0.38/0.56      (![X39 : $i, X40 : $i]:
% 0.38/0.56         ((k3_tarski @ (k2_tarski @ X39 @ X40)) = (k2_xboole_0 @ X39 @ X40))),
% 0.38/0.56      inference('cnf', [status(esa)], [t93_zfmisc_1])).
% 0.38/0.56  thf('7', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((k3_tarski @ (k1_enumset1 @ X1 @ X1 @ X0)) = (k2_xboole_0 @ X1 @ X0))),
% 0.38/0.56      inference('sup+', [status(thm)], ['5', '6'])).
% 0.38/0.56  thf('8', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.38/0.56      inference('demod', [status(thm)], ['4', '7'])).
% 0.38/0.56  thf(t95_xboole_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( k3_xboole_0 @ A @ B ) =
% 0.38/0.56       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.38/0.56  thf('9', plain,
% 0.38/0.56      (![X7 : $i, X8 : $i]:
% 0.38/0.56         ((k3_xboole_0 @ X7 @ X8)
% 0.38/0.56           = (k5_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ (k2_xboole_0 @ X7 @ X8)))),
% 0.38/0.56      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.38/0.56  thf(t91_xboole_1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.38/0.56       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.38/0.56  thf('10', plain,
% 0.38/0.56      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.38/0.56         ((k5_xboole_0 @ (k5_xboole_0 @ X3 @ X4) @ X5)
% 0.38/0.56           = (k5_xboole_0 @ X3 @ (k5_xboole_0 @ X4 @ X5)))),
% 0.38/0.56      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.38/0.56  thf('11', plain,
% 0.38/0.56      (![X7 : $i, X8 : $i]:
% 0.38/0.56         ((k3_xboole_0 @ X7 @ X8)
% 0.38/0.56           = (k5_xboole_0 @ X7 @ (k5_xboole_0 @ X8 @ (k2_xboole_0 @ X7 @ X8))))),
% 0.38/0.56      inference('demod', [status(thm)], ['9', '10'])).
% 0.38/0.56  thf('12', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((k3_xboole_0 @ X0 @ X0)
% 0.38/0.56           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.38/0.56      inference('sup+', [status(thm)], ['8', '11'])).
% 0.38/0.56  thf(t92_xboole_1, axiom,
% 0.38/0.56    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.38/0.56  thf('13', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ X6) = (k1_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.38/0.56  thf(t5_boole, axiom,
% 0.38/0.56    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.38/0.56  thf('14', plain, (![X2 : $i]: ((k5_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.38/0.56      inference('cnf', [status(esa)], [t5_boole])).
% 0.38/0.56  thf('15', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 0.38/0.56      inference('sup+', [status(thm)], ['13', '14'])).
% 0.38/0.56  thf('16', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.38/0.56      inference('demod', [status(thm)], ['12', '15'])).
% 0.38/0.56  thf(t100_xboole_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.38/0.56  thf('17', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((k4_xboole_0 @ X0 @ X1)
% 0.38/0.56           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.38/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.56  thf('18', plain,
% 0.38/0.56      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.38/0.56      inference('sup+', [status(thm)], ['16', '17'])).
% 0.38/0.56  thf('19', plain, (![X2 : $i]: ((k5_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.38/0.56      inference('cnf', [status(esa)], [t5_boole])).
% 0.38/0.56  thf('20', plain,
% 0.38/0.56      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.56      inference('sup+', [status(thm)], ['18', '19'])).
% 0.38/0.56  thf(t130_zfmisc_1, conjecture,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.38/0.56       ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.38/0.56         ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.38/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.56    (~( ![A:$i,B:$i]:
% 0.38/0.56        ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.38/0.56          ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.38/0.56            ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ) )),
% 0.38/0.56    inference('cnf.neg', [status(esa)], [t130_zfmisc_1])).
% 0.38/0.56  thf('21', plain,
% 0.38/0.56      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))
% 0.38/0.56        | ((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('22', plain,
% 0.38/0.56      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))
% 0.38/0.56         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.38/0.56      inference('split', [status(esa)], ['21'])).
% 0.38/0.56  thf(t113_zfmisc_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.38/0.56       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.38/0.56  thf('23', plain,
% 0.38/0.56      (![X32 : $i, X33 : $i]:
% 0.38/0.56         (((X32) = (k1_xboole_0))
% 0.38/0.56          | ((X33) = (k1_xboole_0))
% 0.38/0.56          | ((k2_zfmisc_1 @ X33 @ X32) != (k1_xboole_0)))),
% 0.38/0.56      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.38/0.56  thf('24', plain,
% 0.38/0.56      (((((k1_xboole_0) != (k1_xboole_0))
% 0.38/0.56         | ((sk_A) = (k1_xboole_0))
% 0.38/0.56         | ((k1_tarski @ sk_B) = (k1_xboole_0))))
% 0.38/0.56         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['22', '23'])).
% 0.38/0.56  thf('25', plain,
% 0.38/0.56      (((((k1_tarski @ sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.38/0.56         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.38/0.56      inference('simplify', [status(thm)], ['24'])).
% 0.38/0.56  thf('26', plain, (((sk_A) != (k1_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('27', plain,
% 0.38/0.56      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.38/0.56         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.38/0.56      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 0.38/0.56  thf(t20_zfmisc_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.38/0.56         ( k1_tarski @ A ) ) <=>
% 0.38/0.56       ( ( A ) != ( B ) ) ))).
% 0.38/0.56  thf('28', plain,
% 0.38/0.56      (![X35 : $i, X36 : $i]:
% 0.38/0.56         (((X36) != (X35))
% 0.38/0.56          | ((k4_xboole_0 @ (k1_tarski @ X36) @ (k1_tarski @ X35))
% 0.38/0.56              != (k1_tarski @ X36)))),
% 0.38/0.56      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.38/0.56  thf('29', plain,
% 0.38/0.56      (![X35 : $i]:
% 0.38/0.56         ((k4_xboole_0 @ (k1_tarski @ X35) @ (k1_tarski @ X35))
% 0.38/0.56           != (k1_tarski @ X35))),
% 0.38/0.56      inference('simplify', [status(thm)], ['28'])).
% 0.38/0.56  thf('30', plain,
% 0.38/0.56      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0) != (k1_tarski @ sk_B)))
% 0.38/0.56         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['27', '29'])).
% 0.38/0.56  thf('31', plain,
% 0.38/0.56      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.38/0.56         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.38/0.56      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 0.38/0.56  thf('32', plain,
% 0.38/0.56      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.38/0.56         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.38/0.56      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 0.38/0.56  thf('33', plain,
% 0.38/0.56      ((((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0)))
% 0.38/0.56         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.38/0.56      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.38/0.56  thf('34', plain,
% 0.38/0.56      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.38/0.56         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['20', '33'])).
% 0.38/0.56  thf('35', plain,
% 0.38/0.56      (($false)
% 0.38/0.56         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.38/0.56      inference('simplify', [status(thm)], ['34'])).
% 0.38/0.56  thf('36', plain,
% 0.38/0.56      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.56      inference('sup+', [status(thm)], ['18', '19'])).
% 0.38/0.56  thf('37', plain,
% 0.38/0.56      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))
% 0.38/0.56         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.38/0.56      inference('split', [status(esa)], ['21'])).
% 0.38/0.56  thf('38', plain,
% 0.38/0.56      (![X32 : $i, X33 : $i]:
% 0.38/0.56         (((X32) = (k1_xboole_0))
% 0.38/0.56          | ((X33) = (k1_xboole_0))
% 0.38/0.56          | ((k2_zfmisc_1 @ X33 @ X32) != (k1_xboole_0)))),
% 0.38/0.56      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.38/0.56  thf('39', plain,
% 0.38/0.56      (((((k1_xboole_0) != (k1_xboole_0))
% 0.38/0.56         | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.38/0.56         | ((sk_A) = (k1_xboole_0))))
% 0.38/0.56         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['37', '38'])).
% 0.38/0.56  thf('40', plain,
% 0.38/0.56      (((((sk_A) = (k1_xboole_0)) | ((k1_tarski @ sk_B) = (k1_xboole_0))))
% 0.38/0.56         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.38/0.56      inference('simplify', [status(thm)], ['39'])).
% 0.38/0.56  thf('41', plain, (((sk_A) != (k1_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('42', plain,
% 0.38/0.56      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.38/0.56         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.38/0.56      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 0.38/0.56  thf('43', plain,
% 0.38/0.56      (![X35 : $i]:
% 0.38/0.56         ((k4_xboole_0 @ (k1_tarski @ X35) @ (k1_tarski @ X35))
% 0.38/0.56           != (k1_tarski @ X35))),
% 0.38/0.56      inference('simplify', [status(thm)], ['28'])).
% 0.38/0.56  thf('44', plain,
% 0.38/0.56      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0) != (k1_tarski @ sk_B)))
% 0.38/0.56         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['42', '43'])).
% 0.38/0.56  thf('45', plain,
% 0.38/0.56      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.38/0.56         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.38/0.56      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 0.38/0.56  thf('46', plain,
% 0.38/0.56      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.38/0.56         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.38/0.56      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 0.38/0.56  thf('47', plain,
% 0.38/0.56      ((((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0)))
% 0.38/0.56         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.38/0.56      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.38/0.56  thf('48', plain,
% 0.38/0.56      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.38/0.56         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['36', '47'])).
% 0.38/0.56  thf('49', plain,
% 0.38/0.56      (~ (((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['48'])).
% 0.38/0.56  thf('50', plain,
% 0.38/0.56      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))) | 
% 0.38/0.56       (((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))),
% 0.38/0.56      inference('split', [status(esa)], ['21'])).
% 0.38/0.56  thf('51', plain,
% 0.38/0.56      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))),
% 0.38/0.56      inference('sat_resolution*', [status(thm)], ['49', '50'])).
% 0.38/0.56  thf('52', plain, ($false),
% 0.38/0.56      inference('simpl_trail', [status(thm)], ['35', '51'])).
% 0.38/0.56  
% 0.38/0.56  % SZS output end Refutation
% 0.38/0.56  
% 0.38/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

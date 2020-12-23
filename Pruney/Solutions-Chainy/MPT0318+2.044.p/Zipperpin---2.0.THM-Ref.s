%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HcOC9qKBKJ

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:26 EST 2020

% Result     : Theorem 0.57s
% Output     : Refutation 0.57s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 397 expanded)
%              Number of leaves         :   26 ( 128 expanded)
%              Depth                    :   13
%              Number of atoms          :  919 (3714 expanded)
%              Number of equality atoms :  147 ( 605 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X25: $i,X26: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X26 @ X25 )
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

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_enumset1 @ X14 @ X14 @ X15 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('8',plain,(
    ! [X13: $i] :
      ( ( k2_tarski @ X13 @ X13 )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('10',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k2_enumset1 @ X16 @ X16 @ X17 @ X18 )
      = ( k1_enumset1 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k2_enumset1 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k1_tarski @ X9 ) @ ( k1_enumset1 @ X10 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('16',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X3 @ X4 ) @ X5 )
      = ( k5_xboole_0 @ X3 @ ( k5_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('20',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('21',plain,(
    ! [X2: $i] :
      ( ( k5_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','23'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k3_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('26',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X3 @ X4 ) @ X5 )
      = ( k5_xboole_0 @ X3 @ ( k5_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('27',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k3_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k5_xboole_0 @ X8 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X13: $i] :
      ( ( k2_tarski @ X13 @ X13 )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('30',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X23 @ X24 ) )
      = ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
      = ( k3_tarski @ ( k1_tarski @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['15','28','33'])).

thf('35',plain,
    ( ( ( k1_tarski @ sk_B )
      = ( k3_tarski @ ( k1_tarski @ k1_xboole_0 ) ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['6','34'])).

thf('36',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf('37',plain,
    ( ( k1_xboole_0
      = ( k3_tarski @ ( k1_tarski @ k1_xboole_0 ) ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('39',plain,(
    ! [X2: $i] :
      ( ( k5_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('40',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X3 @ X4 ) @ X5 )
      = ( k5_xboole_0 @ X3 @ ( k5_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k3_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k5_xboole_0 @ X8 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = ( k5_xboole_0 @ k1_xboole_0 @ ( k3_tarski @ ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('46',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = ( k3_tarski @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('48',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k3_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k5_xboole_0 @ X8 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('49',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = ( k5_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('51',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('53',plain,(
    ! [X28: $i,X29: $i] :
      ( ( X29 != X28 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X29 ) @ ( k1_tarski @ X28 ) )
       != ( k1_tarski @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('54',plain,(
    ! [X28: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X28 ) @ ( k1_tarski @ X28 ) )
     != ( k1_tarski @ X28 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
     != ( k1_tarski @ sk_B ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf('57',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf('58',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','58'])).

thf('60',plain,
    ( ( ( k3_tarski @ ( k1_tarski @ k1_xboole_0 ) )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','59'])).

thf('61',plain,
    ( $false
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['37','60'])).

thf('62',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('63',plain,(
    ! [X25: $i,X26: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X26 @ X25 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('64',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
      = ( k3_tarski @ ( k1_tarski @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['15','28','33'])).

thf('69',plain,
    ( ( ( k1_tarski @ sk_B )
      = ( k3_tarski @ ( k1_tarski @ k1_xboole_0 ) ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['65','66'])).

thf('71',plain,
    ( ( k1_xboole_0
      = ( k3_tarski @ ( k1_tarski @ k1_xboole_0 ) ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = ( k3_tarski @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('73',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('74',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['65','66'])).

thf('75',plain,(
    ! [X28: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X28 ) @ ( k1_tarski @ X28 ) )
     != ( k1_tarski @ X28 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('76',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
     != ( k1_tarski @ sk_B ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['65','66'])).

thf('78',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['65','66'])).

thf('79',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,
    ( ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','79'])).

thf('81',plain,
    ( ( ( k3_tarski @ ( k1_tarski @ k1_xboole_0 ) )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','80'])).

thf('82',plain,(
    ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['71','81'])).

thf('83',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('84',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['82','83'])).

thf('85',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['61','84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HcOC9qKBKJ
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:44:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.57/0.77  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.57/0.77  % Solved by: fo/fo7.sh
% 0.57/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.57/0.77  % done 1084 iterations in 0.324s
% 0.57/0.77  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.57/0.77  % SZS output start Refutation
% 0.57/0.77  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.57/0.77  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.57/0.77  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.57/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.57/0.77  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.57/0.77  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.57/0.77  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.57/0.77  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.57/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.57/0.77  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.57/0.77  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.57/0.77  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.57/0.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.57/0.77  thf(t130_zfmisc_1, conjecture,
% 0.57/0.77    (![A:$i,B:$i]:
% 0.57/0.77     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.57/0.77       ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.57/0.77         ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.57/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.57/0.77    (~( ![A:$i,B:$i]:
% 0.57/0.77        ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.57/0.77          ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.57/0.77            ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ) )),
% 0.57/0.77    inference('cnf.neg', [status(esa)], [t130_zfmisc_1])).
% 0.57/0.77  thf('0', plain,
% 0.57/0.77      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))
% 0.57/0.77        | ((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('1', plain,
% 0.57/0.77      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))
% 0.57/0.77         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.57/0.77      inference('split', [status(esa)], ['0'])).
% 0.57/0.77  thf(t113_zfmisc_1, axiom,
% 0.57/0.77    (![A:$i,B:$i]:
% 0.57/0.77     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.57/0.77       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.57/0.77  thf('2', plain,
% 0.57/0.77      (![X25 : $i, X26 : $i]:
% 0.57/0.77         (((X25) = (k1_xboole_0))
% 0.57/0.77          | ((X26) = (k1_xboole_0))
% 0.57/0.77          | ((k2_zfmisc_1 @ X26 @ X25) != (k1_xboole_0)))),
% 0.57/0.77      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.57/0.77  thf('3', plain,
% 0.57/0.77      (((((k1_xboole_0) != (k1_xboole_0))
% 0.57/0.77         | ((sk_A) = (k1_xboole_0))
% 0.57/0.77         | ((k1_tarski @ sk_B) = (k1_xboole_0))))
% 0.57/0.77         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.57/0.77      inference('sup-', [status(thm)], ['1', '2'])).
% 0.57/0.77  thf('4', plain,
% 0.57/0.77      (((((k1_tarski @ sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.57/0.77         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.57/0.77      inference('simplify', [status(thm)], ['3'])).
% 0.57/0.77  thf('5', plain, (((sk_A) != (k1_xboole_0))),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('6', plain,
% 0.57/0.77      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.57/0.77         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.57/0.77      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.57/0.77  thf(t70_enumset1, axiom,
% 0.57/0.77    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.57/0.77  thf('7', plain,
% 0.57/0.77      (![X14 : $i, X15 : $i]:
% 0.57/0.77         ((k1_enumset1 @ X14 @ X14 @ X15) = (k2_tarski @ X14 @ X15))),
% 0.57/0.77      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.57/0.77  thf(t69_enumset1, axiom,
% 0.57/0.77    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.57/0.77  thf('8', plain, (![X13 : $i]: ((k2_tarski @ X13 @ X13) = (k1_tarski @ X13))),
% 0.57/0.77      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.57/0.77  thf('9', plain,
% 0.57/0.77      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.57/0.77      inference('sup+', [status(thm)], ['7', '8'])).
% 0.57/0.77  thf(t71_enumset1, axiom,
% 0.57/0.77    (![A:$i,B:$i,C:$i]:
% 0.57/0.77     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.57/0.77  thf('10', plain,
% 0.57/0.77      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.57/0.77         ((k2_enumset1 @ X16 @ X16 @ X17 @ X18)
% 0.57/0.77           = (k1_enumset1 @ X16 @ X17 @ X18))),
% 0.57/0.77      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.57/0.77  thf('11', plain,
% 0.57/0.77      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.57/0.77      inference('sup+', [status(thm)], ['9', '10'])).
% 0.57/0.77  thf('12', plain,
% 0.57/0.77      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.57/0.77      inference('sup+', [status(thm)], ['7', '8'])).
% 0.57/0.77  thf(t44_enumset1, axiom,
% 0.57/0.77    (![A:$i,B:$i,C:$i,D:$i]:
% 0.57/0.77     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.57/0.77       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 0.57/0.77  thf('13', plain,
% 0.57/0.77      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.57/0.77         ((k2_enumset1 @ X9 @ X10 @ X11 @ X12)
% 0.57/0.77           = (k2_xboole_0 @ (k1_tarski @ X9) @ (k1_enumset1 @ X10 @ X11 @ X12)))),
% 0.57/0.77      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.57/0.77  thf('14', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         ((k2_enumset1 @ X1 @ X0 @ X0 @ X0)
% 0.57/0.77           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.57/0.77      inference('sup+', [status(thm)], ['12', '13'])).
% 0.57/0.77  thf('15', plain,
% 0.57/0.77      (![X0 : $i]:
% 0.57/0.77         ((k1_tarski @ X0)
% 0.57/0.77           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 0.57/0.77      inference('sup+', [status(thm)], ['11', '14'])).
% 0.57/0.77  thf(t92_xboole_1, axiom,
% 0.57/0.77    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.57/0.77  thf('16', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ X6) = (k1_xboole_0))),
% 0.57/0.77      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.57/0.77  thf(t91_xboole_1, axiom,
% 0.57/0.77    (![A:$i,B:$i,C:$i]:
% 0.57/0.77     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.57/0.77       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.57/0.77  thf('17', plain,
% 0.57/0.77      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.57/0.77         ((k5_xboole_0 @ (k5_xboole_0 @ X3 @ X4) @ X5)
% 0.57/0.77           = (k5_xboole_0 @ X3 @ (k5_xboole_0 @ X4 @ X5)))),
% 0.57/0.77      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.57/0.77  thf('18', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.57/0.77           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.57/0.77      inference('sup+', [status(thm)], ['16', '17'])).
% 0.57/0.77  thf('19', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.57/0.77           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.57/0.77      inference('sup+', [status(thm)], ['16', '17'])).
% 0.57/0.77  thf('20', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ X6) = (k1_xboole_0))),
% 0.57/0.77      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.57/0.77  thf(t5_boole, axiom,
% 0.57/0.77    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.57/0.77  thf('21', plain, (![X2 : $i]: ((k5_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.57/0.77      inference('cnf', [status(esa)], [t5_boole])).
% 0.57/0.77  thf('22', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 0.57/0.77      inference('sup+', [status(thm)], ['20', '21'])).
% 0.57/0.77  thf('23', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.57/0.77      inference('sup+', [status(thm)], ['19', '22'])).
% 0.57/0.77  thf('24', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.57/0.77      inference('demod', [status(thm)], ['18', '23'])).
% 0.57/0.77  thf(t95_xboole_1, axiom,
% 0.57/0.77    (![A:$i,B:$i]:
% 0.57/0.77     ( ( k3_xboole_0 @ A @ B ) =
% 0.57/0.77       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.57/0.77  thf('25', plain,
% 0.57/0.77      (![X7 : $i, X8 : $i]:
% 0.57/0.77         ((k3_xboole_0 @ X7 @ X8)
% 0.57/0.77           = (k5_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ (k2_xboole_0 @ X7 @ X8)))),
% 0.57/0.77      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.57/0.77  thf('26', plain,
% 0.57/0.77      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.57/0.77         ((k5_xboole_0 @ (k5_xboole_0 @ X3 @ X4) @ X5)
% 0.57/0.77           = (k5_xboole_0 @ X3 @ (k5_xboole_0 @ X4 @ X5)))),
% 0.57/0.77      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.57/0.77  thf('27', plain,
% 0.57/0.77      (![X7 : $i, X8 : $i]:
% 0.57/0.77         ((k3_xboole_0 @ X7 @ X8)
% 0.57/0.77           = (k5_xboole_0 @ X7 @ (k5_xboole_0 @ X8 @ (k2_xboole_0 @ X7 @ X8))))),
% 0.57/0.77      inference('demod', [status(thm)], ['25', '26'])).
% 0.57/0.77  thf('28', plain,
% 0.57/0.77      (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (k2_xboole_0 @ X0 @ X0))),
% 0.57/0.77      inference('sup+', [status(thm)], ['24', '27'])).
% 0.57/0.77  thf('29', plain,
% 0.57/0.77      (![X13 : $i]: ((k2_tarski @ X13 @ X13) = (k1_tarski @ X13))),
% 0.57/0.77      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.57/0.77  thf(l51_zfmisc_1, axiom,
% 0.57/0.77    (![A:$i,B:$i]:
% 0.57/0.77     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.57/0.77  thf('30', plain,
% 0.57/0.77      (![X23 : $i, X24 : $i]:
% 0.57/0.77         ((k3_tarski @ (k2_tarski @ X23 @ X24)) = (k2_xboole_0 @ X23 @ X24))),
% 0.57/0.77      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.57/0.77  thf('31', plain,
% 0.57/0.77      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.57/0.77      inference('sup+', [status(thm)], ['29', '30'])).
% 0.57/0.77  thf('32', plain,
% 0.57/0.77      (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (k2_xboole_0 @ X0 @ X0))),
% 0.57/0.77      inference('sup+', [status(thm)], ['24', '27'])).
% 0.57/0.77  thf('33', plain,
% 0.57/0.77      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k3_xboole_0 @ X0 @ X0))),
% 0.57/0.77      inference('demod', [status(thm)], ['31', '32'])).
% 0.57/0.77  thf('34', plain,
% 0.57/0.77      (![X0 : $i]:
% 0.57/0.77         ((k1_tarski @ X0) = (k3_tarski @ (k1_tarski @ (k1_tarski @ X0))))),
% 0.57/0.77      inference('demod', [status(thm)], ['15', '28', '33'])).
% 0.57/0.77  thf('35', plain,
% 0.57/0.77      ((((k1_tarski @ sk_B) = (k3_tarski @ (k1_tarski @ k1_xboole_0))))
% 0.57/0.77         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.57/0.77      inference('sup+', [status(thm)], ['6', '34'])).
% 0.57/0.77  thf('36', plain,
% 0.57/0.77      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.57/0.77         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.57/0.77      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.57/0.77  thf('37', plain,
% 0.57/0.77      ((((k1_xboole_0) = (k3_tarski @ (k1_tarski @ k1_xboole_0))))
% 0.57/0.77         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.57/0.77      inference('demod', [status(thm)], ['35', '36'])).
% 0.57/0.77  thf('38', plain,
% 0.57/0.77      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.57/0.77      inference('sup+', [status(thm)], ['29', '30'])).
% 0.57/0.77  thf('39', plain, (![X2 : $i]: ((k5_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.57/0.77      inference('cnf', [status(esa)], [t5_boole])).
% 0.57/0.77  thf('40', plain,
% 0.57/0.77      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.57/0.77         ((k5_xboole_0 @ (k5_xboole_0 @ X3 @ X4) @ X5)
% 0.57/0.77           = (k5_xboole_0 @ X3 @ (k5_xboole_0 @ X4 @ X5)))),
% 0.57/0.77      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.57/0.77  thf('41', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         ((k5_xboole_0 @ X0 @ X1)
% 0.57/0.77           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ X1)))),
% 0.57/0.77      inference('sup+', [status(thm)], ['39', '40'])).
% 0.57/0.77  thf('42', plain,
% 0.57/0.77      (![X7 : $i, X8 : $i]:
% 0.57/0.77         ((k3_xboole_0 @ X7 @ X8)
% 0.57/0.77           = (k5_xboole_0 @ X7 @ (k5_xboole_0 @ X8 @ (k2_xboole_0 @ X7 @ X8))))),
% 0.57/0.77      inference('demod', [status(thm)], ['25', '26'])).
% 0.57/0.77  thf('43', plain,
% 0.57/0.77      (![X0 : $i]:
% 0.57/0.77         ((k3_xboole_0 @ X0 @ k1_xboole_0)
% 0.57/0.77           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.57/0.77      inference('sup+', [status(thm)], ['41', '42'])).
% 0.57/0.77  thf('44', plain,
% 0.57/0.77      (((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.57/0.77         = (k5_xboole_0 @ k1_xboole_0 @ (k3_tarski @ (k1_tarski @ k1_xboole_0))))),
% 0.57/0.77      inference('sup+', [status(thm)], ['38', '43'])).
% 0.57/0.77  thf('45', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.57/0.77      inference('sup+', [status(thm)], ['19', '22'])).
% 0.57/0.77  thf('46', plain,
% 0.57/0.77      (((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.57/0.77         = (k3_tarski @ (k1_tarski @ k1_xboole_0)))),
% 0.57/0.77      inference('demod', [status(thm)], ['44', '45'])).
% 0.57/0.77  thf('47', plain,
% 0.57/0.77      (![X0 : $i]:
% 0.57/0.77         ((k3_xboole_0 @ X0 @ k1_xboole_0)
% 0.57/0.77           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.57/0.77      inference('sup+', [status(thm)], ['41', '42'])).
% 0.57/0.77  thf('48', plain,
% 0.57/0.77      (![X7 : $i, X8 : $i]:
% 0.57/0.77         ((k3_xboole_0 @ X7 @ X8)
% 0.57/0.77           = (k5_xboole_0 @ X7 @ (k5_xboole_0 @ X8 @ (k2_xboole_0 @ X7 @ X8))))),
% 0.57/0.77      inference('demod', [status(thm)], ['25', '26'])).
% 0.57/0.77  thf('49', plain,
% 0.57/0.77      (((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.57/0.77         = (k5_xboole_0 @ k1_xboole_0 @ 
% 0.57/0.77            (k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.57/0.77      inference('sup+', [status(thm)], ['47', '48'])).
% 0.57/0.77  thf(t100_xboole_1, axiom,
% 0.57/0.77    (![A:$i,B:$i]:
% 0.57/0.77     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.57/0.77  thf('50', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         ((k4_xboole_0 @ X0 @ X1)
% 0.57/0.77           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.57/0.77      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.57/0.77  thf('51', plain,
% 0.57/0.77      (((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.57/0.77         = (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.57/0.77      inference('demod', [status(thm)], ['49', '50'])).
% 0.57/0.77  thf('52', plain,
% 0.57/0.77      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.57/0.77         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.57/0.77      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.57/0.77  thf(t20_zfmisc_1, axiom,
% 0.57/0.77    (![A:$i,B:$i]:
% 0.57/0.77     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.57/0.77         ( k1_tarski @ A ) ) <=>
% 0.57/0.77       ( ( A ) != ( B ) ) ))).
% 0.57/0.77  thf('53', plain,
% 0.57/0.77      (![X28 : $i, X29 : $i]:
% 0.57/0.77         (((X29) != (X28))
% 0.57/0.77          | ((k4_xboole_0 @ (k1_tarski @ X29) @ (k1_tarski @ X28))
% 0.57/0.77              != (k1_tarski @ X29)))),
% 0.57/0.77      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.57/0.77  thf('54', plain,
% 0.57/0.77      (![X28 : $i]:
% 0.57/0.77         ((k4_xboole_0 @ (k1_tarski @ X28) @ (k1_tarski @ X28))
% 0.57/0.77           != (k1_tarski @ X28))),
% 0.57/0.77      inference('simplify', [status(thm)], ['53'])).
% 0.57/0.77  thf('55', plain,
% 0.57/0.77      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0) != (k1_tarski @ sk_B)))
% 0.57/0.77         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.57/0.77      inference('sup-', [status(thm)], ['52', '54'])).
% 0.57/0.77  thf('56', plain,
% 0.57/0.77      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.57/0.77         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.57/0.77      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.57/0.77  thf('57', plain,
% 0.57/0.77      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.57/0.77         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.57/0.77      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.57/0.77  thf('58', plain,
% 0.57/0.77      ((((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0)))
% 0.57/0.77         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.57/0.77      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.57/0.77  thf('59', plain,
% 0.57/0.77      ((((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0)))
% 0.57/0.77         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.57/0.77      inference('sup-', [status(thm)], ['51', '58'])).
% 0.57/0.77  thf('60', plain,
% 0.57/0.77      ((((k3_tarski @ (k1_tarski @ k1_xboole_0)) != (k1_xboole_0)))
% 0.57/0.77         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.57/0.77      inference('sup-', [status(thm)], ['46', '59'])).
% 0.57/0.77  thf('61', plain,
% 0.57/0.77      (($false)
% 0.57/0.77         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.57/0.77      inference('simplify_reflect-', [status(thm)], ['37', '60'])).
% 0.57/0.77  thf('62', plain,
% 0.57/0.77      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))
% 0.57/0.77         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.57/0.77      inference('split', [status(esa)], ['0'])).
% 0.57/0.77  thf('63', plain,
% 0.57/0.77      (![X25 : $i, X26 : $i]:
% 0.57/0.77         (((X25) = (k1_xboole_0))
% 0.57/0.77          | ((X26) = (k1_xboole_0))
% 0.57/0.77          | ((k2_zfmisc_1 @ X26 @ X25) != (k1_xboole_0)))),
% 0.57/0.77      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.57/0.77  thf('64', plain,
% 0.57/0.77      (((((k1_xboole_0) != (k1_xboole_0))
% 0.57/0.77         | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.57/0.77         | ((sk_A) = (k1_xboole_0))))
% 0.57/0.77         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.57/0.77      inference('sup-', [status(thm)], ['62', '63'])).
% 0.57/0.77  thf('65', plain,
% 0.57/0.77      (((((sk_A) = (k1_xboole_0)) | ((k1_tarski @ sk_B) = (k1_xboole_0))))
% 0.57/0.77         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.57/0.77      inference('simplify', [status(thm)], ['64'])).
% 0.57/0.77  thf('66', plain, (((sk_A) != (k1_xboole_0))),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('67', plain,
% 0.57/0.77      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.57/0.77         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.57/0.77      inference('simplify_reflect-', [status(thm)], ['65', '66'])).
% 0.57/0.77  thf('68', plain,
% 0.57/0.77      (![X0 : $i]:
% 0.57/0.77         ((k1_tarski @ X0) = (k3_tarski @ (k1_tarski @ (k1_tarski @ X0))))),
% 0.57/0.77      inference('demod', [status(thm)], ['15', '28', '33'])).
% 0.57/0.77  thf('69', plain,
% 0.57/0.77      ((((k1_tarski @ sk_B) = (k3_tarski @ (k1_tarski @ k1_xboole_0))))
% 0.57/0.77         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.57/0.77      inference('sup+', [status(thm)], ['67', '68'])).
% 0.57/0.77  thf('70', plain,
% 0.57/0.77      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.57/0.77         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.57/0.77      inference('simplify_reflect-', [status(thm)], ['65', '66'])).
% 0.57/0.77  thf('71', plain,
% 0.57/0.77      ((((k1_xboole_0) = (k3_tarski @ (k1_tarski @ k1_xboole_0))))
% 0.57/0.77         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.57/0.77      inference('demod', [status(thm)], ['69', '70'])).
% 0.57/0.77  thf('72', plain,
% 0.57/0.77      (((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.57/0.77         = (k3_tarski @ (k1_tarski @ k1_xboole_0)))),
% 0.57/0.77      inference('demod', [status(thm)], ['44', '45'])).
% 0.57/0.77  thf('73', plain,
% 0.57/0.77      (((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.57/0.77         = (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.57/0.77      inference('demod', [status(thm)], ['49', '50'])).
% 0.57/0.77  thf('74', plain,
% 0.57/0.77      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.57/0.77         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.57/0.77      inference('simplify_reflect-', [status(thm)], ['65', '66'])).
% 0.57/0.77  thf('75', plain,
% 0.57/0.77      (![X28 : $i]:
% 0.57/0.77         ((k4_xboole_0 @ (k1_tarski @ X28) @ (k1_tarski @ X28))
% 0.57/0.77           != (k1_tarski @ X28))),
% 0.57/0.77      inference('simplify', [status(thm)], ['53'])).
% 0.57/0.77  thf('76', plain,
% 0.57/0.77      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0) != (k1_tarski @ sk_B)))
% 0.57/0.77         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.57/0.77      inference('sup-', [status(thm)], ['74', '75'])).
% 0.57/0.77  thf('77', plain,
% 0.57/0.77      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.57/0.77         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.57/0.77      inference('simplify_reflect-', [status(thm)], ['65', '66'])).
% 0.57/0.77  thf('78', plain,
% 0.57/0.77      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.57/0.77         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.57/0.77      inference('simplify_reflect-', [status(thm)], ['65', '66'])).
% 0.57/0.77  thf('79', plain,
% 0.57/0.77      ((((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0)))
% 0.57/0.77         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.57/0.77      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.57/0.77  thf('80', plain,
% 0.57/0.77      ((((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0)))
% 0.57/0.77         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.57/0.77      inference('sup-', [status(thm)], ['73', '79'])).
% 0.57/0.77  thf('81', plain,
% 0.57/0.77      ((((k3_tarski @ (k1_tarski @ k1_xboole_0)) != (k1_xboole_0)))
% 0.57/0.77         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.57/0.77      inference('sup-', [status(thm)], ['72', '80'])).
% 0.57/0.77  thf('82', plain,
% 0.57/0.77      (~ (((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))),
% 0.57/0.77      inference('simplify_reflect-', [status(thm)], ['71', '81'])).
% 0.57/0.77  thf('83', plain,
% 0.57/0.77      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))) | 
% 0.57/0.77       (((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))),
% 0.57/0.77      inference('split', [status(esa)], ['0'])).
% 0.57/0.77  thf('84', plain,
% 0.57/0.77      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))),
% 0.57/0.77      inference('sat_resolution*', [status(thm)], ['82', '83'])).
% 0.57/0.77  thf('85', plain, ($false),
% 0.57/0.77      inference('simpl_trail', [status(thm)], ['61', '84'])).
% 0.57/0.77  
% 0.57/0.77  % SZS output end Refutation
% 0.57/0.77  
% 0.57/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

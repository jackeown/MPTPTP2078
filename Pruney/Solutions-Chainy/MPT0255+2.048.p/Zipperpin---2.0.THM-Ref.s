%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zdYjMxdGEF

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:02 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 344 expanded)
%              Number of leaves         :   22 ( 116 expanded)
%              Depth                    :   21
%              Number of atoms          :  664 (2490 expanded)
%              Number of equality atoms :   74 ( 281 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(t50_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t50_zfmisc_1])).

thf('5',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('7',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['5','6'])).

thf('12',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ ( k2_tarski @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ ( k2_tarski @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('16',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('17',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ ( k2_tarski @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['14','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ ( k2_tarski @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ sk_C )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('26',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ sk_C )
      = X0 ) ),
    inference(demod,[status(thm)],['24','33'])).

thf('35',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_C @ X0 )
      = ( k5_xboole_0 @ sk_C @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['7','36'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('38',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ sk_C @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('41',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ sk_C @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_C @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ ( k2_tarski @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ sk_C )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('50',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ k1_xboole_0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['47','48','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
      = X0 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ sk_C @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['46','54'])).

thf('56',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['3','55'])).

thf('57',plain,
    ( ( k5_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['7','36'])).

thf('58',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('60',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ X21 @ X22 )
      | ~ ( r1_tarski @ ( k2_tarski @ X21 @ X23 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('63',plain,(
    ! [X21: $i,X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X21 @ X23 ) @ X24 )
      | ~ ( r2_hidden @ X23 @ X24 )
      | ~ ( r2_hidden @ X21 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X2 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X1 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('66',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['58','67'])).

thf('69',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('70',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ sk_A ) )
    | ( k1_xboole_0
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('72',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('74',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X25 ) @ X26 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['72','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zdYjMxdGEF
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:08:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.62  % Solved by: fo/fo7.sh
% 0.36/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.62  % done 228 iterations in 0.167s
% 0.36/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.62  % SZS output start Refutation
% 0.36/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.62  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.36/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.62  thf(d10_xboole_0, axiom,
% 0.36/0.62    (![A:$i,B:$i]:
% 0.36/0.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.62  thf('0', plain,
% 0.36/0.62      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.36/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.62  thf('1', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.36/0.62      inference('simplify', [status(thm)], ['0'])).
% 0.36/0.62  thf(t12_xboole_1, axiom,
% 0.36/0.62    (![A:$i,B:$i]:
% 0.36/0.62     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.36/0.62  thf('2', plain,
% 0.36/0.62      (![X5 : $i, X6 : $i]:
% 0.36/0.62         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 0.36/0.62      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.36/0.62  thf('3', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.36/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.62  thf(t98_xboole_1, axiom,
% 0.36/0.62    (![A:$i,B:$i]:
% 0.36/0.62     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.36/0.62  thf('4', plain,
% 0.36/0.62      (![X14 : $i, X15 : $i]:
% 0.36/0.62         ((k2_xboole_0 @ X14 @ X15)
% 0.36/0.62           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 0.36/0.62      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.36/0.62  thf(t50_zfmisc_1, conjecture,
% 0.36/0.62    (![A:$i,B:$i,C:$i]:
% 0.36/0.62     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 0.36/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.62    (~( ![A:$i,B:$i,C:$i]:
% 0.36/0.62        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) )),
% 0.36/0.62    inference('cnf.neg', [status(esa)], [t50_zfmisc_1])).
% 0.36/0.62  thf('5', plain,
% 0.36/0.62      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf(commutativity_k2_xboole_0, axiom,
% 0.36/0.62    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.36/0.62  thf('6', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.36/0.62      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.36/0.62  thf('7', plain,
% 0.36/0.62      (((k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.36/0.62      inference('demod', [status(thm)], ['5', '6'])).
% 0.36/0.62  thf('8', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.36/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.62  thf(t41_xboole_1, axiom,
% 0.36/0.62    (![A:$i,B:$i,C:$i]:
% 0.36/0.62     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.36/0.62       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.36/0.62  thf('9', plain,
% 0.36/0.62      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.36/0.62         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 0.36/0.62           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 0.36/0.62      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.36/0.62  thf('10', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.36/0.62           = (k4_xboole_0 @ X1 @ X0))),
% 0.36/0.62      inference('sup+', [status(thm)], ['8', '9'])).
% 0.36/0.62  thf('11', plain,
% 0.36/0.62      (((k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.36/0.62      inference('demod', [status(thm)], ['5', '6'])).
% 0.36/0.62  thf('12', plain,
% 0.36/0.62      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.36/0.62         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 0.36/0.62           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 0.36/0.62      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.36/0.62  thf('13', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ (k2_tarski @ sk_A @ sk_B))
% 0.36/0.62           = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.36/0.62      inference('sup+', [status(thm)], ['11', '12'])).
% 0.36/0.62  thf('14', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ (k2_tarski @ sk_A @ sk_B))
% 0.36/0.62           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ k1_xboole_0))),
% 0.36/0.62      inference('sup+', [status(thm)], ['10', '13'])).
% 0.36/0.62  thf('15', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.36/0.62      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.36/0.62  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.36/0.62  thf('16', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.36/0.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.62  thf('17', plain,
% 0.36/0.62      (![X5 : $i, X6 : $i]:
% 0.36/0.62         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 0.36/0.62      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.36/0.62  thf('18', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.36/0.62      inference('sup-', [status(thm)], ['16', '17'])).
% 0.36/0.62  thf('19', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.36/0.62      inference('sup+', [status(thm)], ['15', '18'])).
% 0.36/0.62  thf('20', plain,
% 0.36/0.62      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.36/0.62         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 0.36/0.62           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 0.36/0.62      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.36/0.62  thf('21', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 0.36/0.62           = (k4_xboole_0 @ X1 @ X0))),
% 0.36/0.62      inference('sup+', [status(thm)], ['19', '20'])).
% 0.36/0.62  thf('22', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ (k2_tarski @ sk_A @ sk_B))
% 0.36/0.62           = (k4_xboole_0 @ X0 @ sk_C))),
% 0.36/0.62      inference('demod', [status(thm)], ['14', '21'])).
% 0.36/0.62  thf('23', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ (k2_tarski @ sk_A @ sk_B))
% 0.36/0.62           = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.36/0.62      inference('sup+', [status(thm)], ['11', '12'])).
% 0.36/0.62  thf('24', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         ((k4_xboole_0 @ X0 @ sk_C) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.36/0.62      inference('sup+', [status(thm)], ['22', '23'])).
% 0.36/0.62  thf('25', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.36/0.62           = (k4_xboole_0 @ X1 @ X0))),
% 0.36/0.62      inference('sup+', [status(thm)], ['8', '9'])).
% 0.36/0.62  thf('26', plain,
% 0.36/0.62      (![X14 : $i, X15 : $i]:
% 0.36/0.62         ((k2_xboole_0 @ X14 @ X15)
% 0.36/0.62           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 0.36/0.62      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.36/0.62  thf('27', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.36/0.62           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.36/0.62      inference('sup+', [status(thm)], ['25', '26'])).
% 0.36/0.62  thf('28', plain,
% 0.36/0.62      (![X14 : $i, X15 : $i]:
% 0.36/0.62         ((k2_xboole_0 @ X14 @ X15)
% 0.36/0.62           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 0.36/0.62      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.36/0.62  thf('29', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.36/0.62           = (k2_xboole_0 @ X0 @ X1))),
% 0.36/0.62      inference('demod', [status(thm)], ['27', '28'])).
% 0.36/0.62  thf('30', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.36/0.62      inference('sup-', [status(thm)], ['16', '17'])).
% 0.36/0.62  thf('31', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.36/0.62      inference('sup+', [status(thm)], ['29', '30'])).
% 0.36/0.62  thf('32', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.36/0.62      inference('sup-', [status(thm)], ['16', '17'])).
% 0.36/0.62  thf('33', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.36/0.62      inference('sup+', [status(thm)], ['31', '32'])).
% 0.36/0.62  thf('34', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ sk_C) = (X0))),
% 0.36/0.62      inference('demod', [status(thm)], ['24', '33'])).
% 0.36/0.62  thf('35', plain,
% 0.36/0.62      (![X14 : $i, X15 : $i]:
% 0.36/0.62         ((k2_xboole_0 @ X14 @ X15)
% 0.36/0.62           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 0.36/0.62      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.36/0.62  thf('36', plain,
% 0.36/0.62      (![X0 : $i]: ((k2_xboole_0 @ sk_C @ X0) = (k5_xboole_0 @ sk_C @ X0))),
% 0.36/0.62      inference('sup+', [status(thm)], ['34', '35'])).
% 0.36/0.62  thf('37', plain,
% 0.36/0.62      (((k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.36/0.62      inference('demod', [status(thm)], ['7', '36'])).
% 0.36/0.62  thf(t91_xboole_1, axiom,
% 0.36/0.62    (![A:$i,B:$i,C:$i]:
% 0.36/0.62     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.36/0.62       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.36/0.62  thf('38', plain,
% 0.36/0.62      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.36/0.62         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 0.36/0.62           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 0.36/0.62      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.36/0.62  thf('39', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.36/0.62           = (k5_xboole_0 @ sk_C @ 
% 0.36/0.62              (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0)))),
% 0.36/0.62      inference('sup+', [status(thm)], ['37', '38'])).
% 0.36/0.62  thf('40', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.36/0.62      inference('sup+', [status(thm)], ['31', '32'])).
% 0.36/0.62  thf('41', plain,
% 0.36/0.62      (![X14 : $i, X15 : $i]:
% 0.36/0.62         ((k2_xboole_0 @ X14 @ X15)
% 0.36/0.62           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 0.36/0.62      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.36/0.62  thf('42', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.36/0.62      inference('sup+', [status(thm)], ['40', '41'])).
% 0.36/0.62  thf('43', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.36/0.62      inference('sup-', [status(thm)], ['16', '17'])).
% 0.36/0.62  thf('44', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.36/0.62      inference('sup+', [status(thm)], ['42', '43'])).
% 0.36/0.62  thf('45', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         ((X0)
% 0.36/0.62           = (k5_xboole_0 @ sk_C @ 
% 0.36/0.62              (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0)))),
% 0.36/0.62      inference('demod', [status(thm)], ['39', '44'])).
% 0.36/0.62  thf('46', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         ((k4_xboole_0 @ X0 @ (k2_tarski @ sk_A @ sk_B))
% 0.36/0.62           = (k5_xboole_0 @ sk_C @ 
% 0.36/0.62              (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0)))),
% 0.36/0.62      inference('sup+', [status(thm)], ['4', '45'])).
% 0.36/0.62  thf('47', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ (k2_tarski @ sk_A @ sk_B))
% 0.36/0.62           = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.36/0.62      inference('sup+', [status(thm)], ['11', '12'])).
% 0.36/0.62  thf('48', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         ((k4_xboole_0 @ X0 @ sk_C) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.36/0.62      inference('sup+', [status(thm)], ['22', '23'])).
% 0.36/0.62  thf('49', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.36/0.62      inference('sup-', [status(thm)], ['16', '17'])).
% 0.36/0.62  thf('50', plain,
% 0.36/0.62      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.36/0.62         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 0.36/0.62           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 0.36/0.62      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.36/0.62  thf('51', plain,
% 0.36/0.62      (![X0 : $i, X1 : $i]:
% 0.36/0.62         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ k1_xboole_0) @ X0)
% 0.36/0.62           = (k4_xboole_0 @ X1 @ X0))),
% 0.36/0.62      inference('sup+', [status(thm)], ['49', '50'])).
% 0.36/0.62  thf('52', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         ((k4_xboole_0 @ X0 @ (k2_tarski @ sk_A @ sk_B))
% 0.36/0.62           = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.36/0.62      inference('demod', [status(thm)], ['47', '48', '51'])).
% 0.36/0.62  thf('53', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.36/0.62      inference('sup+', [status(thm)], ['31', '32'])).
% 0.36/0.62  thf('54', plain,
% 0.36/0.62      (![X0 : $i]: ((k4_xboole_0 @ X0 @ (k2_tarski @ sk_A @ sk_B)) = (X0))),
% 0.36/0.63      inference('demod', [status(thm)], ['52', '53'])).
% 0.36/0.63  thf('55', plain,
% 0.36/0.63      (![X0 : $i]:
% 0.36/0.63         ((X0)
% 0.36/0.63           = (k5_xboole_0 @ sk_C @ 
% 0.36/0.63              (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0)))),
% 0.36/0.63      inference('demod', [status(thm)], ['46', '54'])).
% 0.36/0.63  thf('56', plain,
% 0.36/0.63      (((k2_tarski @ sk_A @ sk_B)
% 0.36/0.63         = (k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 0.36/0.63      inference('sup+', [status(thm)], ['3', '55'])).
% 0.36/0.63  thf('57', plain,
% 0.36/0.63      (((k5_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.36/0.63      inference('demod', [status(thm)], ['7', '36'])).
% 0.36/0.63  thf('58', plain, (((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.36/0.63      inference('sup+', [status(thm)], ['56', '57'])).
% 0.36/0.63  thf('59', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.36/0.63      inference('simplify', [status(thm)], ['0'])).
% 0.36/0.63  thf(t38_zfmisc_1, axiom,
% 0.36/0.63    (![A:$i,B:$i,C:$i]:
% 0.36/0.63     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.36/0.63       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.36/0.63  thf('60', plain,
% 0.36/0.63      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.36/0.63         ((r2_hidden @ X21 @ X22)
% 0.36/0.63          | ~ (r1_tarski @ (k2_tarski @ X21 @ X23) @ X22))),
% 0.36/0.63      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.36/0.63  thf('61', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.36/0.63      inference('sup-', [status(thm)], ['59', '60'])).
% 0.36/0.63  thf('62', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.36/0.63      inference('sup-', [status(thm)], ['59', '60'])).
% 0.36/0.63  thf('63', plain,
% 0.36/0.63      (![X21 : $i, X23 : $i, X24 : $i]:
% 0.36/0.63         ((r1_tarski @ (k2_tarski @ X21 @ X23) @ X24)
% 0.36/0.63          | ~ (r2_hidden @ X23 @ X24)
% 0.36/0.63          | ~ (r2_hidden @ X21 @ X24))),
% 0.36/0.63      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.36/0.63  thf('64', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.63         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.36/0.63          | (r1_tarski @ (k2_tarski @ X2 @ X1) @ (k2_tarski @ X1 @ X0)))),
% 0.36/0.63      inference('sup-', [status(thm)], ['62', '63'])).
% 0.36/0.63  thf('65', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i]:
% 0.36/0.63         (r1_tarski @ (k2_tarski @ X1 @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.36/0.63      inference('sup-', [status(thm)], ['61', '64'])).
% 0.36/0.63  thf(t69_enumset1, axiom,
% 0.36/0.63    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.36/0.63  thf('66', plain,
% 0.36/0.63      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.36/0.63      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.63  thf('67', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i]:
% 0.36/0.63         (r1_tarski @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.36/0.63      inference('demod', [status(thm)], ['65', '66'])).
% 0.36/0.63  thf('68', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ k1_xboole_0)),
% 0.36/0.63      inference('sup+', [status(thm)], ['58', '67'])).
% 0.36/0.63  thf('69', plain,
% 0.36/0.63      (![X2 : $i, X4 : $i]:
% 0.36/0.63         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.36/0.63      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.63  thf('70', plain,
% 0.36/0.63      ((~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ sk_A))
% 0.36/0.63        | ((k1_xboole_0) = (k1_tarski @ sk_A)))),
% 0.36/0.63      inference('sup-', [status(thm)], ['68', '69'])).
% 0.36/0.63  thf('71', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.36/0.63      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.63  thf('72', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.36/0.63      inference('demod', [status(thm)], ['70', '71'])).
% 0.36/0.63  thf('73', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.36/0.63      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.63  thf(t49_zfmisc_1, axiom,
% 0.36/0.63    (![A:$i,B:$i]:
% 0.36/0.63     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.36/0.63  thf('74', plain,
% 0.36/0.63      (![X25 : $i, X26 : $i]:
% 0.36/0.63         ((k2_xboole_0 @ (k1_tarski @ X25) @ X26) != (k1_xboole_0))),
% 0.36/0.63      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.36/0.63  thf('75', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.36/0.63      inference('sup-', [status(thm)], ['73', '74'])).
% 0.36/0.63  thf('76', plain, ($false),
% 0.36/0.63      inference('simplify_reflect-', [status(thm)], ['72', '75'])).
% 0.36/0.63  
% 0.36/0.63  % SZS output end Refutation
% 0.36/0.63  
% 0.45/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

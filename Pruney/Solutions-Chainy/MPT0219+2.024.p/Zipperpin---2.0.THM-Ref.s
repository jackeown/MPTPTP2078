%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.e2oSv9xxWE

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:07 EST 2020

% Result     : Theorem 55.31s
% Output     : Refutation 55.31s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 296 expanded)
%              Number of leaves         :   40 ( 110 expanded)
%              Depth                    :   25
%              Number of atoms          :  929 (2097 expanded)
%              Number of equality atoms :  106 ( 269 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t13_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t13_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('2',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('7',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['9','20'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','25'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('27',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','30'])).

thf('32',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['0','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','25'])).

thf('34',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('36',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['9','20'])).

thf('38',plain,
    ( ( k1_tarski @ sk_B )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('40',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('44',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('46',plain,
    ( ( k1_tarski @ sk_A )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('48',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('49',plain,(
    ! [X42: $i] :
      ( ( k2_tarski @ X42 @ X42 )
      = ( k1_tarski @ X42 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('50',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( k2_enumset1 @ X45 @ X45 @ X46 @ X47 )
      = ( k1_enumset1 @ X45 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('51',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k1_enumset1 @ X43 @ X43 @ X44 )
      = ( k2_tarski @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('53',plain,(
    ! [X57: $i,X58: $i,X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ( k5_enumset1 @ X57 @ X57 @ X58 @ X59 @ X60 @ X61 @ X62 )
      = ( k4_enumset1 @ X57 @ X58 @ X59 @ X60 @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('54',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ( k4_enumset1 @ X52 @ X52 @ X53 @ X54 @ X55 @ X56 )
      = ( k3_enumset1 @ X52 @ X53 @ X54 @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ( k4_enumset1 @ X52 @ X52 @ X53 @ X54 @ X55 @ X56 )
      = ( k3_enumset1 @ X52 @ X53 @ X54 @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t61_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ) )).

thf('57',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( k5_enumset1 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 ) @ ( k1_tarski @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t61_enumset1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','58'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('60',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( k3_enumset1 @ X48 @ X48 @ X49 @ X50 @ X51 )
      = ( k2_enumset1 @ X48 @ X49 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['52','61'])).

thf('63',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( k3_enumset1 @ X48 @ X48 @ X49 @ X50 @ X51 )
      = ( k2_enumset1 @ X48 @ X49 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['49','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_tarski @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['48','67'])).

thf('69',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k1_enumset1 @ X43 @ X43 @ X44 )
      = ( k2_tarski @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('70',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 @ X25 @ X26 )
      | ( r2_hidden @ X23 @ X27 )
      | ( X27
       != ( k1_enumset1 @ X26 @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('71',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( r2_hidden @ X23 @ ( k1_enumset1 @ X26 @ X25 @ X24 ) )
      | ( zip_tseitin_0 @ X23 @ X24 @ X25 @ X26 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['69','71'])).

thf('73',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X19 != X18 )
      | ~ ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('74',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ~ ( zip_tseitin_0 @ X18 @ X20 @ X21 @ X18 ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['72','74'])).

thf('76',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['68','75'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('77',plain,(
    ! [X30: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X33 @ X32 )
      | ( X33 = X30 )
      | ( X32
       != ( k1_tarski @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('78',plain,(
    ! [X30: $i,X33: $i] :
      ( ( X33 = X30 )
      | ~ ( r2_hidden @ X33 @ ( k1_tarski @ X30 ) ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['76','78'])).

thf('80',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['79','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.e2oSv9xxWE
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:03:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 55.31/55.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 55.31/55.51  % Solved by: fo/fo7.sh
% 55.31/55.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 55.31/55.51  % done 10329 iterations in 55.048s
% 55.31/55.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 55.31/55.51  % SZS output start Refutation
% 55.31/55.51  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 55.31/55.51  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 55.31/55.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 55.31/55.51  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 55.31/55.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 55.31/55.51  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 55.31/55.51  thf(sk_B_type, type, sk_B: $i).
% 55.31/55.51  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 55.31/55.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 55.31/55.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 55.31/55.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 55.31/55.51  thf(sk_A_type, type, sk_A: $i).
% 55.31/55.51  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 55.31/55.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 55.31/55.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 55.31/55.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 55.31/55.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 55.31/55.51  thf(t13_zfmisc_1, conjecture,
% 55.31/55.51    (![A:$i,B:$i]:
% 55.31/55.51     ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 55.31/55.51         ( k1_tarski @ A ) ) =>
% 55.31/55.51       ( ( A ) = ( B ) ) ))).
% 55.31/55.51  thf(zf_stmt_0, negated_conjecture,
% 55.31/55.51    (~( ![A:$i,B:$i]:
% 55.31/55.51        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 55.31/55.51            ( k1_tarski @ A ) ) =>
% 55.31/55.51          ( ( A ) = ( B ) ) ) )),
% 55.31/55.51    inference('cnf.neg', [status(esa)], [t13_zfmisc_1])).
% 55.31/55.51  thf('0', plain,
% 55.31/55.51      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 55.31/55.51         = (k1_tarski @ sk_A))),
% 55.31/55.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.31/55.51  thf(t98_xboole_1, axiom,
% 55.31/55.51    (![A:$i,B:$i]:
% 55.31/55.51     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 55.31/55.51  thf('1', plain,
% 55.31/55.51      (![X16 : $i, X17 : $i]:
% 55.31/55.51         ((k2_xboole_0 @ X16 @ X17)
% 55.31/55.51           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 55.31/55.51      inference('cnf', [status(esa)], [t98_xboole_1])).
% 55.31/55.51  thf(idempotence_k3_xboole_0, axiom,
% 55.31/55.51    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 55.31/55.51  thf('2', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 55.31/55.51      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 55.31/55.51  thf(t100_xboole_1, axiom,
% 55.31/55.51    (![A:$i,B:$i]:
% 55.31/55.51     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 55.31/55.51  thf('3', plain,
% 55.31/55.51      (![X5 : $i, X6 : $i]:
% 55.31/55.51         ((k4_xboole_0 @ X5 @ X6)
% 55.31/55.51           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 55.31/55.51      inference('cnf', [status(esa)], [t100_xboole_1])).
% 55.31/55.51  thf('4', plain,
% 55.31/55.51      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 55.31/55.51      inference('sup+', [status(thm)], ['2', '3'])).
% 55.31/55.51  thf('5', plain,
% 55.31/55.51      (![X16 : $i, X17 : $i]:
% 55.31/55.51         ((k2_xboole_0 @ X16 @ X17)
% 55.31/55.51           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 55.31/55.51      inference('cnf', [status(esa)], [t98_xboole_1])).
% 55.31/55.51  thf(commutativity_k5_xboole_0, axiom,
% 55.31/55.51    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 55.31/55.51  thf('6', plain,
% 55.31/55.51      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 55.31/55.51      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 55.31/55.51  thf(t5_boole, axiom,
% 55.31/55.51    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 55.31/55.51  thf('7', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 55.31/55.51      inference('cnf', [status(esa)], [t5_boole])).
% 55.31/55.51  thf('8', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 55.31/55.51      inference('sup+', [status(thm)], ['6', '7'])).
% 55.31/55.51  thf('9', plain,
% 55.31/55.51      (![X0 : $i]:
% 55.31/55.51         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 55.31/55.51      inference('sup+', [status(thm)], ['5', '8'])).
% 55.31/55.51  thf(t17_xboole_1, axiom,
% 55.31/55.51    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 55.31/55.51  thf('10', plain,
% 55.31/55.51      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 55.31/55.51      inference('cnf', [status(esa)], [t17_xboole_1])).
% 55.31/55.51  thf(t3_xboole_1, axiom,
% 55.31/55.51    (![A:$i]:
% 55.31/55.51     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 55.31/55.51  thf('11', plain,
% 55.31/55.51      (![X9 : $i]: (((X9) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ k1_xboole_0))),
% 55.31/55.51      inference('cnf', [status(esa)], [t3_xboole_1])).
% 55.31/55.51  thf('12', plain,
% 55.31/55.51      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 55.31/55.51      inference('sup-', [status(thm)], ['10', '11'])).
% 55.31/55.51  thf(commutativity_k3_xboole_0, axiom,
% 55.31/55.51    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 55.31/55.51  thf('13', plain,
% 55.31/55.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 55.31/55.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 55.31/55.51  thf('14', plain,
% 55.31/55.51      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 55.31/55.51      inference('sup+', [status(thm)], ['12', '13'])).
% 55.31/55.51  thf('15', plain,
% 55.31/55.51      (![X5 : $i, X6 : $i]:
% 55.31/55.51         ((k4_xboole_0 @ X5 @ X6)
% 55.31/55.51           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 55.31/55.51      inference('cnf', [status(esa)], [t100_xboole_1])).
% 55.31/55.51  thf('16', plain,
% 55.31/55.51      (![X0 : $i]:
% 55.31/55.51         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 55.31/55.51      inference('sup+', [status(thm)], ['14', '15'])).
% 55.31/55.51  thf('17', plain,
% 55.31/55.51      (![X0 : $i]:
% 55.31/55.51         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 55.31/55.51      inference('sup+', [status(thm)], ['5', '8'])).
% 55.31/55.51  thf('18', plain,
% 55.31/55.51      (![X0 : $i]:
% 55.31/55.51         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 55.31/55.51      inference('demod', [status(thm)], ['16', '17'])).
% 55.31/55.51  thf('19', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 55.31/55.51      inference('cnf', [status(esa)], [t5_boole])).
% 55.31/55.51  thf('20', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 55.31/55.51      inference('sup+', [status(thm)], ['18', '19'])).
% 55.31/55.51  thf('21', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 55.31/55.51      inference('demod', [status(thm)], ['9', '20'])).
% 55.31/55.51  thf(t48_xboole_1, axiom,
% 55.31/55.51    (![A:$i,B:$i]:
% 55.31/55.51     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 55.31/55.51  thf('22', plain,
% 55.31/55.51      (![X10 : $i, X11 : $i]:
% 55.31/55.51         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 55.31/55.51           = (k3_xboole_0 @ X10 @ X11))),
% 55.31/55.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 55.31/55.51  thf('23', plain,
% 55.31/55.51      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 55.31/55.51      inference('sup+', [status(thm)], ['21', '22'])).
% 55.31/55.51  thf('24', plain,
% 55.31/55.51      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 55.31/55.51      inference('sup+', [status(thm)], ['12', '13'])).
% 55.31/55.51  thf('25', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 55.31/55.51      inference('demod', [status(thm)], ['23', '24'])).
% 55.31/55.51  thf('26', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 55.31/55.51      inference('demod', [status(thm)], ['4', '25'])).
% 55.31/55.51  thf(t91_xboole_1, axiom,
% 55.31/55.51    (![A:$i,B:$i,C:$i]:
% 55.31/55.51     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 55.31/55.51       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 55.31/55.51  thf('27', plain,
% 55.31/55.51      (![X13 : $i, X14 : $i, X15 : $i]:
% 55.31/55.51         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 55.31/55.51           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 55.31/55.51      inference('cnf', [status(esa)], [t91_xboole_1])).
% 55.31/55.51  thf('28', plain,
% 55.31/55.51      (![X0 : $i, X1 : $i]:
% 55.31/55.51         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 55.31/55.51           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 55.31/55.51      inference('sup+', [status(thm)], ['26', '27'])).
% 55.31/55.51  thf('29', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 55.31/55.51      inference('sup+', [status(thm)], ['6', '7'])).
% 55.31/55.51  thf('30', plain,
% 55.31/55.51      (![X0 : $i, X1 : $i]:
% 55.31/55.51         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 55.31/55.51      inference('demod', [status(thm)], ['28', '29'])).
% 55.31/55.51  thf('31', plain,
% 55.31/55.51      (![X0 : $i, X1 : $i]:
% 55.31/55.51         ((k4_xboole_0 @ X0 @ X1)
% 55.31/55.51           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 55.31/55.51      inference('sup+', [status(thm)], ['1', '30'])).
% 55.31/55.51  thf('32', plain,
% 55.31/55.51      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 55.31/55.51         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 55.31/55.51      inference('sup+', [status(thm)], ['0', '31'])).
% 55.31/55.51  thf('33', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 55.31/55.51      inference('demod', [status(thm)], ['4', '25'])).
% 55.31/55.51  thf('34', plain,
% 55.31/55.51      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 55.31/55.51      inference('demod', [status(thm)], ['32', '33'])).
% 55.31/55.51  thf('35', plain,
% 55.31/55.51      (![X10 : $i, X11 : $i]:
% 55.31/55.51         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 55.31/55.51           = (k3_xboole_0 @ X10 @ X11))),
% 55.31/55.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 55.31/55.51  thf('36', plain,
% 55.31/55.51      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0)
% 55.31/55.51         = (k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 55.31/55.51      inference('sup+', [status(thm)], ['34', '35'])).
% 55.31/55.51  thf('37', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 55.31/55.51      inference('demod', [status(thm)], ['9', '20'])).
% 55.31/55.51  thf('38', plain,
% 55.31/55.51      (((k1_tarski @ sk_B)
% 55.31/55.51         = (k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 55.31/55.51      inference('demod', [status(thm)], ['36', '37'])).
% 55.31/55.51  thf('39', plain,
% 55.31/55.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 55.31/55.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 55.31/55.51  thf('40', plain,
% 55.31/55.51      (![X5 : $i, X6 : $i]:
% 55.31/55.51         ((k4_xboole_0 @ X5 @ X6)
% 55.31/55.51           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 55.31/55.51      inference('cnf', [status(esa)], [t100_xboole_1])).
% 55.31/55.51  thf('41', plain,
% 55.31/55.51      (![X0 : $i, X1 : $i]:
% 55.31/55.51         ((k4_xboole_0 @ X0 @ X1)
% 55.31/55.51           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 55.31/55.51      inference('sup+', [status(thm)], ['39', '40'])).
% 55.31/55.51  thf('42', plain,
% 55.31/55.51      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 55.31/55.51         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))),
% 55.31/55.51      inference('sup+', [status(thm)], ['38', '41'])).
% 55.31/55.51  thf('43', plain,
% 55.31/55.51      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 55.31/55.51      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 55.31/55.51  thf('44', plain,
% 55.31/55.51      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 55.31/55.51         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 55.31/55.51      inference('demod', [status(thm)], ['42', '43'])).
% 55.31/55.51  thf('45', plain,
% 55.31/55.51      (![X0 : $i, X1 : $i]:
% 55.31/55.51         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 55.31/55.51      inference('demod', [status(thm)], ['28', '29'])).
% 55.31/55.52  thf('46', plain,
% 55.31/55.52      (((k1_tarski @ sk_A)
% 55.31/55.52         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ 
% 55.31/55.52            (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))))),
% 55.31/55.52      inference('sup+', [status(thm)], ['44', '45'])).
% 55.31/55.52  thf('47', plain,
% 55.31/55.52      (![X16 : $i, X17 : $i]:
% 55.31/55.52         ((k2_xboole_0 @ X16 @ X17)
% 55.31/55.52           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 55.31/55.52      inference('cnf', [status(esa)], [t98_xboole_1])).
% 55.31/55.52  thf('48', plain,
% 55.31/55.52      (((k1_tarski @ sk_A)
% 55.31/55.52         = (k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 55.31/55.52      inference('demod', [status(thm)], ['46', '47'])).
% 55.31/55.52  thf(t69_enumset1, axiom,
% 55.31/55.52    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 55.31/55.52  thf('49', plain,
% 55.31/55.52      (![X42 : $i]: ((k2_tarski @ X42 @ X42) = (k1_tarski @ X42))),
% 55.31/55.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 55.31/55.52  thf(t71_enumset1, axiom,
% 55.31/55.52    (![A:$i,B:$i,C:$i]:
% 55.31/55.52     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 55.31/55.52  thf('50', plain,
% 55.31/55.52      (![X45 : $i, X46 : $i, X47 : $i]:
% 55.31/55.52         ((k2_enumset1 @ X45 @ X45 @ X46 @ X47)
% 55.31/55.52           = (k1_enumset1 @ X45 @ X46 @ X47))),
% 55.31/55.52      inference('cnf', [status(esa)], [t71_enumset1])).
% 55.31/55.52  thf(t70_enumset1, axiom,
% 55.31/55.52    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 55.31/55.52  thf('51', plain,
% 55.31/55.52      (![X43 : $i, X44 : $i]:
% 55.31/55.52         ((k1_enumset1 @ X43 @ X43 @ X44) = (k2_tarski @ X43 @ X44))),
% 55.31/55.52      inference('cnf', [status(esa)], [t70_enumset1])).
% 55.31/55.52  thf('52', plain,
% 55.31/55.52      (![X0 : $i, X1 : $i]:
% 55.31/55.52         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 55.31/55.52      inference('sup+', [status(thm)], ['50', '51'])).
% 55.31/55.52  thf(t74_enumset1, axiom,
% 55.31/55.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 55.31/55.52     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 55.31/55.52       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 55.31/55.52  thf('53', plain,
% 55.31/55.52      (![X57 : $i, X58 : $i, X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 55.31/55.52         ((k5_enumset1 @ X57 @ X57 @ X58 @ X59 @ X60 @ X61 @ X62)
% 55.31/55.52           = (k4_enumset1 @ X57 @ X58 @ X59 @ X60 @ X61 @ X62))),
% 55.31/55.52      inference('cnf', [status(esa)], [t74_enumset1])).
% 55.31/55.52  thf(t73_enumset1, axiom,
% 55.31/55.52    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 55.31/55.52     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 55.31/55.52       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 55.31/55.52  thf('54', plain,
% 55.31/55.52      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 55.31/55.52         ((k4_enumset1 @ X52 @ X52 @ X53 @ X54 @ X55 @ X56)
% 55.31/55.52           = (k3_enumset1 @ X52 @ X53 @ X54 @ X55 @ X56))),
% 55.31/55.52      inference('cnf', [status(esa)], [t73_enumset1])).
% 55.31/55.52  thf('55', plain,
% 55.31/55.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 55.31/55.52         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 55.31/55.52           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 55.31/55.52      inference('sup+', [status(thm)], ['53', '54'])).
% 55.31/55.52  thf('56', plain,
% 55.31/55.52      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 55.31/55.52         ((k4_enumset1 @ X52 @ X52 @ X53 @ X54 @ X55 @ X56)
% 55.31/55.52           = (k3_enumset1 @ X52 @ X53 @ X54 @ X55 @ X56))),
% 55.31/55.52      inference('cnf', [status(esa)], [t73_enumset1])).
% 55.31/55.52  thf(t61_enumset1, axiom,
% 55.31/55.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 55.31/55.52     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 55.31/55.52       ( k2_xboole_0 @
% 55.31/55.52         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ))).
% 55.31/55.52  thf('57', plain,
% 55.31/55.52      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 55.31/55.52         ((k5_enumset1 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41)
% 55.31/55.52           = (k2_xboole_0 @ 
% 55.31/55.52              (k4_enumset1 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40) @ 
% 55.31/55.52              (k1_tarski @ X41)))),
% 55.31/55.52      inference('cnf', [status(esa)], [t61_enumset1])).
% 55.31/55.52  thf('58', plain,
% 55.31/55.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 55.31/55.52         ((k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5)
% 55.31/55.52           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 55.31/55.52              (k1_tarski @ X5)))),
% 55.31/55.52      inference('sup+', [status(thm)], ['56', '57'])).
% 55.31/55.52  thf('59', plain,
% 55.31/55.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 55.31/55.52         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 55.31/55.52           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1) @ 
% 55.31/55.52              (k1_tarski @ X0)))),
% 55.31/55.52      inference('sup+', [status(thm)], ['55', '58'])).
% 55.31/55.52  thf(t72_enumset1, axiom,
% 55.31/55.52    (![A:$i,B:$i,C:$i,D:$i]:
% 55.31/55.52     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 55.31/55.52  thf('60', plain,
% 55.31/55.52      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 55.31/55.52         ((k3_enumset1 @ X48 @ X48 @ X49 @ X50 @ X51)
% 55.31/55.52           = (k2_enumset1 @ X48 @ X49 @ X50 @ X51))),
% 55.31/55.52      inference('cnf', [status(esa)], [t72_enumset1])).
% 55.31/55.52  thf('61', plain,
% 55.31/55.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 55.31/55.52         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 55.31/55.52           = (k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ 
% 55.31/55.52              (k1_tarski @ X0)))),
% 55.31/55.52      inference('demod', [status(thm)], ['59', '60'])).
% 55.31/55.52  thf('62', plain,
% 55.31/55.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 55.31/55.52         ((k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2)
% 55.31/55.52           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 55.31/55.52      inference('sup+', [status(thm)], ['52', '61'])).
% 55.31/55.52  thf('63', plain,
% 55.31/55.52      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 55.31/55.52         ((k3_enumset1 @ X48 @ X48 @ X49 @ X50 @ X51)
% 55.31/55.52           = (k2_enumset1 @ X48 @ X49 @ X50 @ X51))),
% 55.31/55.52      inference('cnf', [status(esa)], [t72_enumset1])).
% 55.31/55.52  thf('64', plain,
% 55.31/55.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 55.31/55.52         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 55.31/55.52           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 55.31/55.52      inference('demod', [status(thm)], ['62', '63'])).
% 55.31/55.52  thf('65', plain,
% 55.31/55.52      (![X0 : $i, X1 : $i]:
% 55.31/55.52         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 55.31/55.52           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 55.31/55.52      inference('sup+', [status(thm)], ['49', '64'])).
% 55.31/55.52  thf('66', plain,
% 55.31/55.52      (![X0 : $i, X1 : $i]:
% 55.31/55.52         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 55.31/55.52      inference('sup+', [status(thm)], ['50', '51'])).
% 55.31/55.52  thf('67', plain,
% 55.31/55.52      (![X0 : $i, X1 : $i]:
% 55.31/55.52         ((k2_tarski @ X0 @ X1)
% 55.31/55.52           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 55.31/55.52      inference('demod', [status(thm)], ['65', '66'])).
% 55.31/55.52  thf('68', plain, (((k1_tarski @ sk_A) = (k2_tarski @ sk_B @ sk_A))),
% 55.31/55.52      inference('demod', [status(thm)], ['48', '67'])).
% 55.31/55.52  thf('69', plain,
% 55.31/55.52      (![X43 : $i, X44 : $i]:
% 55.31/55.52         ((k1_enumset1 @ X43 @ X43 @ X44) = (k2_tarski @ X43 @ X44))),
% 55.31/55.52      inference('cnf', [status(esa)], [t70_enumset1])).
% 55.31/55.52  thf(d1_enumset1, axiom,
% 55.31/55.52    (![A:$i,B:$i,C:$i,D:$i]:
% 55.31/55.52     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 55.31/55.52       ( ![E:$i]:
% 55.31/55.52         ( ( r2_hidden @ E @ D ) <=>
% 55.31/55.52           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 55.31/55.52  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 55.31/55.52  thf(zf_stmt_2, axiom,
% 55.31/55.52    (![E:$i,C:$i,B:$i,A:$i]:
% 55.31/55.52     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 55.31/55.52       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 55.31/55.52  thf(zf_stmt_3, axiom,
% 55.31/55.52    (![A:$i,B:$i,C:$i,D:$i]:
% 55.31/55.52     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 55.31/55.52       ( ![E:$i]:
% 55.31/55.52         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 55.31/55.52  thf('70', plain,
% 55.31/55.52      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 55.31/55.52         ((zip_tseitin_0 @ X23 @ X24 @ X25 @ X26)
% 55.31/55.52          | (r2_hidden @ X23 @ X27)
% 55.31/55.52          | ((X27) != (k1_enumset1 @ X26 @ X25 @ X24)))),
% 55.31/55.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 55.31/55.52  thf('71', plain,
% 55.31/55.52      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 55.31/55.52         ((r2_hidden @ X23 @ (k1_enumset1 @ X26 @ X25 @ X24))
% 55.31/55.52          | (zip_tseitin_0 @ X23 @ X24 @ X25 @ X26))),
% 55.31/55.52      inference('simplify', [status(thm)], ['70'])).
% 55.31/55.52  thf('72', plain,
% 55.31/55.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 55.31/55.52         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 55.31/55.52          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 55.31/55.52      inference('sup+', [status(thm)], ['69', '71'])).
% 55.31/55.52  thf('73', plain,
% 55.31/55.52      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 55.31/55.52         (((X19) != (X18)) | ~ (zip_tseitin_0 @ X19 @ X20 @ X21 @ X18))),
% 55.31/55.52      inference('cnf', [status(esa)], [zf_stmt_2])).
% 55.31/55.52  thf('74', plain,
% 55.31/55.52      (![X18 : $i, X20 : $i, X21 : $i]:
% 55.31/55.52         ~ (zip_tseitin_0 @ X18 @ X20 @ X21 @ X18)),
% 55.31/55.52      inference('simplify', [status(thm)], ['73'])).
% 55.31/55.52  thf('75', plain,
% 55.31/55.52      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 55.31/55.52      inference('sup-', [status(thm)], ['72', '74'])).
% 55.31/55.52  thf('76', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 55.31/55.52      inference('sup+', [status(thm)], ['68', '75'])).
% 55.31/55.52  thf(d1_tarski, axiom,
% 55.31/55.52    (![A:$i,B:$i]:
% 55.31/55.52     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 55.31/55.52       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 55.31/55.52  thf('77', plain,
% 55.31/55.52      (![X30 : $i, X32 : $i, X33 : $i]:
% 55.31/55.52         (~ (r2_hidden @ X33 @ X32)
% 55.31/55.52          | ((X33) = (X30))
% 55.31/55.52          | ((X32) != (k1_tarski @ X30)))),
% 55.31/55.52      inference('cnf', [status(esa)], [d1_tarski])).
% 55.31/55.52  thf('78', plain,
% 55.31/55.52      (![X30 : $i, X33 : $i]:
% 55.31/55.52         (((X33) = (X30)) | ~ (r2_hidden @ X33 @ (k1_tarski @ X30)))),
% 55.31/55.52      inference('simplify', [status(thm)], ['77'])).
% 55.31/55.52  thf('79', plain, (((sk_B) = (sk_A))),
% 55.31/55.52      inference('sup-', [status(thm)], ['76', '78'])).
% 55.31/55.52  thf('80', plain, (((sk_A) != (sk_B))),
% 55.31/55.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 55.31/55.52  thf('81', plain, ($false),
% 55.31/55.52      inference('simplify_reflect-', [status(thm)], ['79', '80'])).
% 55.31/55.52  
% 55.31/55.52  % SZS output end Refutation
% 55.31/55.52  
% 55.31/55.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

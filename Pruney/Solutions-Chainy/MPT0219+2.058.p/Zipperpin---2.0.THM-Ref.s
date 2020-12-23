%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KZigbTYolB

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:11 EST 2020

% Result     : Theorem 44.04s
% Output     : Refutation 44.04s
% Verified   : 
% Statistics : Number of formulae       :  331 (12317 expanded)
%              Number of leaves         :   39 (4123 expanded)
%              Depth                    :   42
%              Number of atoms          : 3045 (84400 expanded)
%              Number of equality atoms :  314 (11008 expanded)
%              Maximal formula depth    :   18 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

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
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('2',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','19'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('24',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','19'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','32'])).

thf('34',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['0','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','19'])).

thf('36',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['34','35'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('37',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( k2_enumset1 @ X52 @ X52 @ X53 @ X54 )
      = ( k1_enumset1 @ X52 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('38',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k1_enumset1 @ X50 @ X50 @ X51 )
      = ( k2_tarski @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('40',plain,(
    ! [X64: $i,X65: $i,X66: $i,X67: $i,X68: $i,X69: $i] :
      ( ( k5_enumset1 @ X64 @ X64 @ X65 @ X66 @ X67 @ X68 @ X69 )
      = ( k4_enumset1 @ X64 @ X65 @ X66 @ X67 @ X68 @ X69 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('41',plain,(
    ! [X59: $i,X60: $i,X61: $i,X62: $i,X63: $i] :
      ( ( k4_enumset1 @ X59 @ X59 @ X60 @ X61 @ X62 @ X63 )
      = ( k3_enumset1 @ X59 @ X60 @ X61 @ X62 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X59: $i,X60: $i,X61: $i,X62: $i,X63: $i] :
      ( ( k4_enumset1 @ X59 @ X59 @ X60 @ X61 @ X62 @ X63 )
      = ( k3_enumset1 @ X59 @ X60 @ X61 @ X62 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t61_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ) )).

thf('44',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( k5_enumset1 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 ) @ ( k1_tarski @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t61_enumset1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('47',plain,(
    ! [X55: $i,X56: $i,X57: $i,X58: $i] :
      ( ( k3_enumset1 @ X55 @ X55 @ X56 @ X57 @ X58 )
      = ( k2_enumset1 @ X55 @ X56 @ X57 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['39','48'])).

thf('50',plain,(
    ! [X55: $i,X56: $i,X57: $i,X58: $i] :
      ( ( k3_enumset1 @ X55 @ X55 @ X56 @ X57 @ X58 )
      = ( k2_enumset1 @ X55 @ X56 @ X57 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('52',plain,(
    ! [X49: $i] :
      ( ( k2_tarski @ X49 @ X49 )
      = ( k1_tarski @ X49 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('53',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','19'])).

thf('54',plain,(
    ! [X64: $i,X65: $i,X66: $i,X67: $i,X68: $i,X69: $i] :
      ( ( k5_enumset1 @ X64 @ X64 @ X65 @ X66 @ X67 @ X68 @ X69 )
      = ( k4_enumset1 @ X64 @ X65 @ X66 @ X67 @ X68 @ X69 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('55',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( k5_enumset1 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 ) @ ( k1_tarski @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t61_enumset1])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 )
      = ( k2_xboole_0 @ ( k5_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','32'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k5_enumset1 @ X6 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ ( k5_enumset1 @ X6 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k5_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['53','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('61',plain,(
    ! [X55: $i,X56: $i,X57: $i,X58: $i] :
      ( ( k3_enumset1 @ X55 @ X55 @ X56 @ X57 @ X58 )
      = ( k2_enumset1 @ X55 @ X56 @ X57 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k5_enumset1 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('66',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('67',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','19'])).

thf('70',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('71',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('77',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['75','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','31'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('84',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['82','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['79','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','19'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['68','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['65','97'])).

thf('99',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) ) )
      = ( k5_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['98','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('104',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','19'])).

thf('105',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['103','106'])).

thf('108',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','31'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','31'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','31'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('121',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['111','118','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('125',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','31'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['124','127'])).

thf('129',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','19'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['123','140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['102','122','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) ) @ k1_xboole_0 )
      = ( k5_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['64','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('145',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k5_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['143','144','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','19'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k3_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['123','140'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('158',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('159',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k5_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k5_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ) ),
    inference('sup+',[status(thm)],['156','159'])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','31'])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','31'])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['160','165','166','169'])).

thf('171',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['170','171'])).

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('174',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('175',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('176',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['173','176'])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['167','168'])).

thf('179',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['167','168'])).

thf('181',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('182',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['180','181'])).

thf('183',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['179','182'])).

thf('184',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X2 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['172','183'])).

thf('185',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['160','165','166','169'])).

thf('186',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('187',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['185','186'])).

thf('188',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['185','186'])).

thf('189',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['163','164'])).

thf('190',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['184','187','188','189'])).

thf('191',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('192',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X2 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['190','191'])).

thf('193',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('194',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('195',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('196',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X2 ) @ ( k5_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['194','195'])).

thf('197',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('198',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( X0
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X2 ) @ ( k5_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['196','197'])).

thf('199',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X2 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['193','198'])).

thf('200',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 ) @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['192','199'])).

thf('201',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) ) @ X1 ) @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['155','200'])).

thf('202',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','62','63'])).

thf('203',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('204',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k5_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['202','203'])).

thf('205',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('206',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['204','205'])).

thf('207',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ X1 ) @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['201','206'])).

thf('208',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('209',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('210',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['208','209'])).

thf('211',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('212',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('213',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = ( k5_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['211','212'])).

thf('214',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X2 @ X0 ) )
      = ( k5_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['210','213'])).

thf('215',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = ( k5_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['211','212'])).

thf('216',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('217',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('218',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','19'])).

thf('219',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['34','35'])).

thf('220',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('221',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['219','220'])).

thf('222',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('223',plain,
    ( ( k1_tarski @ sk_B )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['221','222'])).

thf('224',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('225',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['223','224'])).

thf('226',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('227',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ X0 )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['225','226'])).

thf('228',plain,
    ( ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['218','227'])).

thf('229',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('230',plain,
    ( ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['228','229'])).

thf('231',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','31'])).

thf('232',plain,
    ( ( k1_tarski @ sk_B )
    = ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['230','231'])).

thf('233',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['223','224'])).

thf('234',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','31'])).

thf('235',plain,
    ( ( k1_tarski @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['233','234'])).

thf('236',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('237',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['235','236'])).

thf('238',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['232','237'])).

thf('239',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('240',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ X0 )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['238','239'])).

thf('241',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('242',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ X0 )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['225','226'])).

thf('243',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['240','241','242'])).

thf('244',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ ( k5_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['217','243'])).

thf('245',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','31'])).

thf('246',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['244','245'])).

thf('247',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('248',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('249',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['247','248'])).

thf('250',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) @ X1 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) @ ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['246','249'])).

thf('251',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['247','248'])).

thf('252',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['247','248'])).

thf('253',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('254',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','19'])).

thf('255',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['235','236'])).

thf('256',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['254','255'])).

thf('257',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('258',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('259',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['256','257','258'])).

thf('260',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['250','251','252','253','259'])).

thf('261',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['216','260'])).

thf('262',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) @ X2 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['215','261'])).

thf('263',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['247','248'])).

thf('264',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['247','248'])).

thf('265',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','31'])).

thf('266',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['262','263','264','265'])).

thf('267',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) )
      = ( k5_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['214','266'])).

thf('268',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ X0 ) @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['207','267'])).

thf('269',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('270',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ X0 ) @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['268','269'])).

thf('271',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_tarski @ X0 )
      = ( k5_xboole_0 @ ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['51','270'])).

thf('272',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('273',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_tarski @ X0 )
      = ( k5_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['271','272'])).

thf('274',plain,
    ( ( k1_tarski @ sk_A )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['36','273'])).

thf('275',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('276',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('277',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_tarski @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['274','275','276'])).

thf('278',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k1_enumset1 @ X50 @ X50 @ X51 )
      = ( k2_tarski @ X50 @ X51 ) ) ),
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

thf('279',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X24 )
      | ( r2_hidden @ X21 @ X25 )
      | ( X25
       != ( k1_enumset1 @ X24 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('280',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ X21 @ ( k1_enumset1 @ X24 @ X23 @ X22 ) )
      | ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X24 ) ) ),
    inference(simplify,[status(thm)],['279'])).

thf('281',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['278','280'])).

thf('282',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X17 != X16 )
      | ~ ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('283',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ~ ( zip_tseitin_0 @ X16 @ X18 @ X19 @ X16 ) ),
    inference(simplify,[status(thm)],['282'])).

thf('284',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['281','283'])).

thf('285',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['277','284'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('286',plain,(
    ! [X28: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X31 @ X30 )
      | ( X31 = X28 )
      | ( X30
       != ( k1_tarski @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('287',plain,(
    ! [X28: $i,X31: $i] :
      ( ( X31 = X28 )
      | ~ ( r2_hidden @ X31 @ ( k1_tarski @ X28 ) ) ) ),
    inference(simplify,[status(thm)],['286'])).

thf('288',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['285','287'])).

thf('289',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('290',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['288','289'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KZigbTYolB
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:22:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 44.04/44.31  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 44.04/44.31  % Solved by: fo/fo7.sh
% 44.04/44.31  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 44.04/44.31  % done 15506 iterations in 43.839s
% 44.04/44.31  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 44.04/44.31  % SZS output start Refutation
% 44.04/44.31  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 44.04/44.31  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 44.04/44.31  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 44.04/44.31  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 44.04/44.31  thf(sk_A_type, type, sk_A: $i).
% 44.04/44.31  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 44.04/44.31  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 44.04/44.31  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 44.04/44.31  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 44.04/44.31  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 44.04/44.31  thf(sk_B_type, type, sk_B: $i).
% 44.04/44.31  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 44.04/44.31  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 44.04/44.31  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 44.04/44.31  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 44.04/44.31  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 44.04/44.31  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 44.04/44.31  thf(t13_zfmisc_1, conjecture,
% 44.04/44.31    (![A:$i,B:$i]:
% 44.04/44.31     ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 44.04/44.31         ( k1_tarski @ A ) ) =>
% 44.04/44.31       ( ( A ) = ( B ) ) ))).
% 44.04/44.31  thf(zf_stmt_0, negated_conjecture,
% 44.04/44.31    (~( ![A:$i,B:$i]:
% 44.04/44.31        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 44.04/44.31            ( k1_tarski @ A ) ) =>
% 44.04/44.31          ( ( A ) = ( B ) ) ) )),
% 44.04/44.31    inference('cnf.neg', [status(esa)], [t13_zfmisc_1])).
% 44.04/44.31  thf('0', plain,
% 44.04/44.31      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 44.04/44.31         = (k1_tarski @ sk_A))),
% 44.04/44.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.04/44.31  thf(t98_xboole_1, axiom,
% 44.04/44.31    (![A:$i,B:$i]:
% 44.04/44.31     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 44.04/44.31  thf('1', plain,
% 44.04/44.31      (![X14 : $i, X15 : $i]:
% 44.04/44.31         ((k2_xboole_0 @ X14 @ X15)
% 44.04/44.31           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 44.04/44.31      inference('cnf', [status(esa)], [t98_xboole_1])).
% 44.04/44.31  thf(idempotence_k3_xboole_0, axiom,
% 44.04/44.31    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 44.04/44.31  thf('2', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 44.04/44.31      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 44.04/44.31  thf(t100_xboole_1, axiom,
% 44.04/44.31    (![A:$i,B:$i]:
% 44.04/44.31     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 44.04/44.31  thf('3', plain,
% 44.04/44.31      (![X3 : $i, X4 : $i]:
% 44.04/44.31         ((k4_xboole_0 @ X3 @ X4)
% 44.04/44.31           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 44.04/44.31      inference('cnf', [status(esa)], [t100_xboole_1])).
% 44.04/44.31  thf('4', plain,
% 44.04/44.31      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 44.04/44.31      inference('sup+', [status(thm)], ['2', '3'])).
% 44.04/44.31  thf(t17_xboole_1, axiom,
% 44.04/44.31    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 44.04/44.31  thf('5', plain,
% 44.04/44.31      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 44.04/44.31      inference('cnf', [status(esa)], [t17_xboole_1])).
% 44.04/44.31  thf(t3_xboole_1, axiom,
% 44.04/44.31    (![A:$i]:
% 44.04/44.31     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 44.04/44.31  thf('6', plain,
% 44.04/44.31      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ k1_xboole_0))),
% 44.04/44.31      inference('cnf', [status(esa)], [t3_xboole_1])).
% 44.04/44.31  thf('7', plain,
% 44.04/44.31      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 44.04/44.31      inference('sup-', [status(thm)], ['5', '6'])).
% 44.04/44.31  thf(commutativity_k3_xboole_0, axiom,
% 44.04/44.31    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 44.04/44.31  thf('8', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 44.04/44.31      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 44.04/44.31  thf('9', plain,
% 44.04/44.31      (![X3 : $i, X4 : $i]:
% 44.04/44.31         ((k4_xboole_0 @ X3 @ X4)
% 44.04/44.31           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 44.04/44.31      inference('cnf', [status(esa)], [t100_xboole_1])).
% 44.04/44.31  thf('10', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k4_xboole_0 @ X0 @ X1)
% 44.04/44.31           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['8', '9'])).
% 44.04/44.31  thf('11', plain,
% 44.04/44.31      (![X0 : $i]:
% 44.04/44.31         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 44.04/44.31      inference('sup+', [status(thm)], ['7', '10'])).
% 44.04/44.31  thf(t5_boole, axiom,
% 44.04/44.31    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 44.04/44.31  thf('12', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 44.04/44.31      inference('cnf', [status(esa)], [t5_boole])).
% 44.04/44.31  thf('13', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 44.04/44.31      inference('sup+', [status(thm)], ['11', '12'])).
% 44.04/44.31  thf(t48_xboole_1, axiom,
% 44.04/44.31    (![A:$i,B:$i]:
% 44.04/44.31     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 44.04/44.31  thf('14', plain,
% 44.04/44.31      (![X8 : $i, X9 : $i]:
% 44.04/44.31         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 44.04/44.31           = (k3_xboole_0 @ X8 @ X9))),
% 44.04/44.31      inference('cnf', [status(esa)], [t48_xboole_1])).
% 44.04/44.31  thf('15', plain,
% 44.04/44.31      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 44.04/44.31      inference('sup+', [status(thm)], ['13', '14'])).
% 44.04/44.31  thf('16', plain,
% 44.04/44.31      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 44.04/44.31      inference('sup-', [status(thm)], ['5', '6'])).
% 44.04/44.31  thf('17', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 44.04/44.31      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 44.04/44.31  thf('18', plain,
% 44.04/44.31      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 44.04/44.31      inference('sup+', [status(thm)], ['16', '17'])).
% 44.04/44.31  thf('19', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 44.04/44.31      inference('demod', [status(thm)], ['15', '18'])).
% 44.04/44.31  thf('20', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 44.04/44.31      inference('demod', [status(thm)], ['4', '19'])).
% 44.04/44.31  thf(t91_xboole_1, axiom,
% 44.04/44.31    (![A:$i,B:$i,C:$i]:
% 44.04/44.31     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 44.04/44.31       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 44.04/44.31  thf('21', plain,
% 44.04/44.31      (![X11 : $i, X12 : $i, X13 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 44.04/44.31           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 44.04/44.31      inference('cnf', [status(esa)], [t91_xboole_1])).
% 44.04/44.31  thf('22', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 44.04/44.31           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['20', '21'])).
% 44.04/44.31  thf('23', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 44.04/44.31      inference('sup+', [status(thm)], ['11', '12'])).
% 44.04/44.31  thf('24', plain,
% 44.04/44.31      (![X14 : $i, X15 : $i]:
% 44.04/44.31         ((k2_xboole_0 @ X14 @ X15)
% 44.04/44.31           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 44.04/44.31      inference('cnf', [status(esa)], [t98_xboole_1])).
% 44.04/44.31  thf('25', plain,
% 44.04/44.31      (![X0 : $i]:
% 44.04/44.31         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 44.04/44.31      inference('sup+', [status(thm)], ['23', '24'])).
% 44.04/44.31  thf('26', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 44.04/44.31           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 44.04/44.31      inference('demod', [status(thm)], ['22', '25'])).
% 44.04/44.31  thf('27', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 44.04/44.31      inference('demod', [status(thm)], ['4', '19'])).
% 44.04/44.31  thf('28', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 44.04/44.31           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 44.04/44.31      inference('demod', [status(thm)], ['22', '25'])).
% 44.04/44.31  thf('29', plain,
% 44.04/44.31      (![X0 : $i]:
% 44.04/44.31         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 44.04/44.31      inference('sup+', [status(thm)], ['27', '28'])).
% 44.04/44.31  thf('30', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 44.04/44.31      inference('cnf', [status(esa)], [t5_boole])).
% 44.04/44.31  thf('31', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 44.04/44.31      inference('sup+', [status(thm)], ['29', '30'])).
% 44.04/44.31  thf('32', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 44.04/44.31      inference('demod', [status(thm)], ['26', '31'])).
% 44.04/44.31  thf('33', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k4_xboole_0 @ X0 @ X1)
% 44.04/44.31           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['1', '32'])).
% 44.04/44.31  thf('34', plain,
% 44.04/44.31      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 44.04/44.31         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['0', '33'])).
% 44.04/44.31  thf('35', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 44.04/44.31      inference('demod', [status(thm)], ['4', '19'])).
% 44.04/44.31  thf('36', plain,
% 44.04/44.31      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 44.04/44.31      inference('demod', [status(thm)], ['34', '35'])).
% 44.04/44.31  thf(t71_enumset1, axiom,
% 44.04/44.31    (![A:$i,B:$i,C:$i]:
% 44.04/44.31     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 44.04/44.31  thf('37', plain,
% 44.04/44.31      (![X52 : $i, X53 : $i, X54 : $i]:
% 44.04/44.31         ((k2_enumset1 @ X52 @ X52 @ X53 @ X54)
% 44.04/44.31           = (k1_enumset1 @ X52 @ X53 @ X54))),
% 44.04/44.31      inference('cnf', [status(esa)], [t71_enumset1])).
% 44.04/44.31  thf(t70_enumset1, axiom,
% 44.04/44.31    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 44.04/44.31  thf('38', plain,
% 44.04/44.31      (![X50 : $i, X51 : $i]:
% 44.04/44.31         ((k1_enumset1 @ X50 @ X50 @ X51) = (k2_tarski @ X50 @ X51))),
% 44.04/44.31      inference('cnf', [status(esa)], [t70_enumset1])).
% 44.04/44.31  thf('39', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 44.04/44.31      inference('sup+', [status(thm)], ['37', '38'])).
% 44.04/44.31  thf(t74_enumset1, axiom,
% 44.04/44.31    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 44.04/44.31     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 44.04/44.31       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 44.04/44.31  thf('40', plain,
% 44.04/44.31      (![X64 : $i, X65 : $i, X66 : $i, X67 : $i, X68 : $i, X69 : $i]:
% 44.04/44.31         ((k5_enumset1 @ X64 @ X64 @ X65 @ X66 @ X67 @ X68 @ X69)
% 44.04/44.31           = (k4_enumset1 @ X64 @ X65 @ X66 @ X67 @ X68 @ X69))),
% 44.04/44.31      inference('cnf', [status(esa)], [t74_enumset1])).
% 44.04/44.31  thf(t73_enumset1, axiom,
% 44.04/44.31    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 44.04/44.31     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 44.04/44.31       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 44.04/44.31  thf('41', plain,
% 44.04/44.31      (![X59 : $i, X60 : $i, X61 : $i, X62 : $i, X63 : $i]:
% 44.04/44.31         ((k4_enumset1 @ X59 @ X59 @ X60 @ X61 @ X62 @ X63)
% 44.04/44.31           = (k3_enumset1 @ X59 @ X60 @ X61 @ X62 @ X63))),
% 44.04/44.31      inference('cnf', [status(esa)], [t73_enumset1])).
% 44.04/44.31  thf('42', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 44.04/44.31         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 44.04/44.31           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 44.04/44.31      inference('sup+', [status(thm)], ['40', '41'])).
% 44.04/44.31  thf('43', plain,
% 44.04/44.31      (![X59 : $i, X60 : $i, X61 : $i, X62 : $i, X63 : $i]:
% 44.04/44.31         ((k4_enumset1 @ X59 @ X59 @ X60 @ X61 @ X62 @ X63)
% 44.04/44.31           = (k3_enumset1 @ X59 @ X60 @ X61 @ X62 @ X63))),
% 44.04/44.31      inference('cnf', [status(esa)], [t73_enumset1])).
% 44.04/44.31  thf(t61_enumset1, axiom,
% 44.04/44.31    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 44.04/44.31     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 44.04/44.31       ( k2_xboole_0 @
% 44.04/44.31         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ))).
% 44.04/44.31  thf('44', plain,
% 44.04/44.31      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 44.04/44.31         ((k5_enumset1 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48)
% 44.04/44.31           = (k2_xboole_0 @ 
% 44.04/44.31              (k4_enumset1 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47) @ 
% 44.04/44.31              (k1_tarski @ X48)))),
% 44.04/44.31      inference('cnf', [status(esa)], [t61_enumset1])).
% 44.04/44.31  thf('45', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 44.04/44.31         ((k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5)
% 44.04/44.31           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 44.04/44.31              (k1_tarski @ X5)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['43', '44'])).
% 44.04/44.31  thf('46', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 44.04/44.31         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 44.04/44.31           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1) @ 
% 44.04/44.31              (k1_tarski @ X0)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['42', '45'])).
% 44.04/44.31  thf(t72_enumset1, axiom,
% 44.04/44.31    (![A:$i,B:$i,C:$i,D:$i]:
% 44.04/44.31     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 44.04/44.31  thf('47', plain,
% 44.04/44.31      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i]:
% 44.04/44.31         ((k3_enumset1 @ X55 @ X55 @ X56 @ X57 @ X58)
% 44.04/44.31           = (k2_enumset1 @ X55 @ X56 @ X57 @ X58))),
% 44.04/44.31      inference('cnf', [status(esa)], [t72_enumset1])).
% 44.04/44.31  thf('48', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 44.04/44.31         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 44.04/44.31           = (k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ 
% 44.04/44.31              (k1_tarski @ X0)))),
% 44.04/44.31      inference('demod', [status(thm)], ['46', '47'])).
% 44.04/44.31  thf('49', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.04/44.31         ((k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2)
% 44.04/44.31           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['39', '48'])).
% 44.04/44.31  thf('50', plain,
% 44.04/44.31      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i]:
% 44.04/44.31         ((k3_enumset1 @ X55 @ X55 @ X56 @ X57 @ X58)
% 44.04/44.31           = (k2_enumset1 @ X55 @ X56 @ X57 @ X58))),
% 44.04/44.31      inference('cnf', [status(esa)], [t72_enumset1])).
% 44.04/44.31  thf('51', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.04/44.31         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 44.04/44.31           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 44.04/44.31      inference('demod', [status(thm)], ['49', '50'])).
% 44.04/44.31  thf(t69_enumset1, axiom,
% 44.04/44.31    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 44.04/44.31  thf('52', plain,
% 44.04/44.31      (![X49 : $i]: ((k2_tarski @ X49 @ X49) = (k1_tarski @ X49))),
% 44.04/44.31      inference('cnf', [status(esa)], [t69_enumset1])).
% 44.04/44.31  thf('53', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 44.04/44.31      inference('demod', [status(thm)], ['4', '19'])).
% 44.04/44.31  thf('54', plain,
% 44.04/44.31      (![X64 : $i, X65 : $i, X66 : $i, X67 : $i, X68 : $i, X69 : $i]:
% 44.04/44.31         ((k5_enumset1 @ X64 @ X64 @ X65 @ X66 @ X67 @ X68 @ X69)
% 44.04/44.31           = (k4_enumset1 @ X64 @ X65 @ X66 @ X67 @ X68 @ X69))),
% 44.04/44.31      inference('cnf', [status(esa)], [t74_enumset1])).
% 44.04/44.31  thf('55', plain,
% 44.04/44.31      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 44.04/44.31         ((k5_enumset1 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48)
% 44.04/44.31           = (k2_xboole_0 @ 
% 44.04/44.31              (k4_enumset1 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47) @ 
% 44.04/44.31              (k1_tarski @ X48)))),
% 44.04/44.31      inference('cnf', [status(esa)], [t61_enumset1])).
% 44.04/44.31  thf('56', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 44.04/44.31         ((k5_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6)
% 44.04/44.31           = (k2_xboole_0 @ (k5_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 44.04/44.31              (k1_tarski @ X6)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['54', '55'])).
% 44.04/44.31  thf('57', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k4_xboole_0 @ X0 @ X1)
% 44.04/44.31           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['1', '32'])).
% 44.04/44.31  thf('58', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 44.04/44.31         ((k4_xboole_0 @ (k1_tarski @ X0) @ 
% 44.04/44.31           (k5_enumset1 @ X6 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1))
% 44.04/44.31           = (k5_xboole_0 @ (k5_enumset1 @ X6 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 44.04/44.31              (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['56', '57'])).
% 44.04/44.31  thf('59', plain,
% 44.04/44.31      (![X0 : $i]:
% 44.04/44.31         ((k4_xboole_0 @ (k1_tarski @ X0) @ 
% 44.04/44.31           (k5_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0)) = (k1_xboole_0))),
% 44.04/44.31      inference('sup+', [status(thm)], ['53', '58'])).
% 44.04/44.31  thf('60', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 44.04/44.31         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 44.04/44.31           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 44.04/44.31      inference('sup+', [status(thm)], ['40', '41'])).
% 44.04/44.31  thf('61', plain,
% 44.04/44.31      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i]:
% 44.04/44.31         ((k3_enumset1 @ X55 @ X55 @ X56 @ X57 @ X58)
% 44.04/44.31           = (k2_enumset1 @ X55 @ X56 @ X57 @ X58))),
% 44.04/44.31      inference('cnf', [status(esa)], [t72_enumset1])).
% 44.04/44.31  thf('62', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 44.04/44.31         ((k5_enumset1 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 44.04/44.31           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 44.04/44.31      inference('sup+', [status(thm)], ['60', '61'])).
% 44.04/44.31  thf('63', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 44.04/44.31      inference('sup+', [status(thm)], ['37', '38'])).
% 44.04/44.31  thf('64', plain,
% 44.04/44.31      (![X0 : $i]:
% 44.04/44.31         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X0))
% 44.04/44.31           = (k1_xboole_0))),
% 44.04/44.31      inference('demod', [status(thm)], ['59', '62', '63'])).
% 44.04/44.31  thf('65', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 44.04/44.31      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 44.04/44.31  thf('66', plain,
% 44.04/44.31      (![X8 : $i, X9 : $i]:
% 44.04/44.31         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 44.04/44.31           = (k3_xboole_0 @ X8 @ X9))),
% 44.04/44.31      inference('cnf', [status(esa)], [t48_xboole_1])).
% 44.04/44.31  thf('67', plain,
% 44.04/44.31      (![X8 : $i, X9 : $i]:
% 44.04/44.31         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 44.04/44.31           = (k3_xboole_0 @ X8 @ X9))),
% 44.04/44.31      inference('cnf', [status(esa)], [t48_xboole_1])).
% 44.04/44.31  thf('68', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 44.04/44.31           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['66', '67'])).
% 44.04/44.31  thf('69', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 44.04/44.31      inference('demod', [status(thm)], ['4', '19'])).
% 44.04/44.31  thf('70', plain,
% 44.04/44.31      (![X3 : $i, X4 : $i]:
% 44.04/44.31         ((k4_xboole_0 @ X3 @ X4)
% 44.04/44.31           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 44.04/44.31      inference('cnf', [status(esa)], [t100_xboole_1])).
% 44.04/44.31  thf('71', plain,
% 44.04/44.31      (![X11 : $i, X12 : $i, X13 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 44.04/44.31           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 44.04/44.31      inference('cnf', [status(esa)], [t91_xboole_1])).
% 44.04/44.31  thf('72', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 44.04/44.31           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['70', '71'])).
% 44.04/44.31  thf('73', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 44.04/44.31           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 44.04/44.31      inference('sup+', [status(thm)], ['69', '72'])).
% 44.04/44.31  thf('74', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 44.04/44.31      inference('cnf', [status(esa)], [t5_boole])).
% 44.04/44.31  thf('75', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 44.04/44.31           = (X1))),
% 44.04/44.31      inference('demod', [status(thm)], ['73', '74'])).
% 44.04/44.31  thf('76', plain,
% 44.04/44.31      (![X8 : $i, X9 : $i]:
% 44.04/44.31         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 44.04/44.31           = (k3_xboole_0 @ X8 @ X9))),
% 44.04/44.31      inference('cnf', [status(esa)], [t48_xboole_1])).
% 44.04/44.31  thf('77', plain,
% 44.04/44.31      (![X14 : $i, X15 : $i]:
% 44.04/44.31         ((k2_xboole_0 @ X14 @ X15)
% 44.04/44.31           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 44.04/44.31      inference('cnf', [status(esa)], [t98_xboole_1])).
% 44.04/44.31  thf('78', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 44.04/44.31           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['76', '77'])).
% 44.04/44.31  thf('79', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 44.04/44.31      inference('sup+', [status(thm)], ['75', '78'])).
% 44.04/44.31  thf('80', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 44.04/44.31           = (X1))),
% 44.04/44.31      inference('demod', [status(thm)], ['73', '74'])).
% 44.04/44.31  thf('81', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 44.04/44.31      inference('demod', [status(thm)], ['26', '31'])).
% 44.04/44.31  thf('82', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k3_xboole_0 @ X0 @ X1)
% 44.04/44.31           = (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 44.04/44.31      inference('sup+', [status(thm)], ['80', '81'])).
% 44.04/44.31  thf('83', plain,
% 44.04/44.31      (![X14 : $i, X15 : $i]:
% 44.04/44.31         ((k2_xboole_0 @ X14 @ X15)
% 44.04/44.31           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 44.04/44.31      inference('cnf', [status(esa)], [t98_xboole_1])).
% 44.04/44.31  thf('84', plain,
% 44.04/44.31      (![X11 : $i, X12 : $i, X13 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 44.04/44.31           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 44.04/44.31      inference('cnf', [status(esa)], [t91_xboole_1])).
% 44.04/44.31  thf('85', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 44.04/44.31           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['83', '84'])).
% 44.04/44.31  thf('86', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X1)
% 44.04/44.31           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['82', '85'])).
% 44.04/44.31  thf('87', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k4_xboole_0 @ X0 @ X1)
% 44.04/44.31           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['8', '9'])).
% 44.04/44.31  thf('88', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X1)
% 44.04/44.31           = (k4_xboole_0 @ X0 @ X1))),
% 44.04/44.31      inference('demod', [status(thm)], ['86', '87'])).
% 44.04/44.31  thf('89', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ X0 @ X0)
% 44.04/44.31           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 44.04/44.31      inference('sup+', [status(thm)], ['79', '88'])).
% 44.04/44.31  thf('90', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 44.04/44.31      inference('demod', [status(thm)], ['4', '19'])).
% 44.04/44.31  thf('91', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k1_xboole_0) = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 44.04/44.31      inference('demod', [status(thm)], ['89', '90'])).
% 44.04/44.31  thf('92', plain,
% 44.04/44.31      (![X8 : $i, X9 : $i]:
% 44.04/44.31         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 44.04/44.31           = (k3_xboole_0 @ X8 @ X9))),
% 44.04/44.31      inference('cnf', [status(esa)], [t48_xboole_1])).
% 44.04/44.31  thf('93', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 44.04/44.31           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 44.04/44.31      inference('sup+', [status(thm)], ['91', '92'])).
% 44.04/44.31  thf('94', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 44.04/44.31      inference('sup+', [status(thm)], ['11', '12'])).
% 44.04/44.31  thf('95', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 44.04/44.31      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 44.04/44.31  thf('96', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k4_xboole_0 @ X0 @ X1)
% 44.04/44.31           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 44.04/44.31      inference('demod', [status(thm)], ['93', '94', '95'])).
% 44.04/44.31  thf('97', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 44.04/44.31           = (k4_xboole_0 @ X1 @ X0))),
% 44.04/44.31      inference('demod', [status(thm)], ['68', '96'])).
% 44.04/44.31  thf('98', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 44.04/44.31           = (k4_xboole_0 @ X0 @ X1))),
% 44.04/44.31      inference('sup+', [status(thm)], ['65', '97'])).
% 44.04/44.31  thf('99', plain,
% 44.04/44.31      (![X14 : $i, X15 : $i]:
% 44.04/44.31         ((k2_xboole_0 @ X14 @ X15)
% 44.04/44.31           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 44.04/44.31      inference('cnf', [status(esa)], [t98_xboole_1])).
% 44.04/44.31  thf('100', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 44.04/44.31           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['70', '71'])).
% 44.04/44.31  thf('101', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ 
% 44.04/44.31           (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1)))
% 44.04/44.31           = (k5_xboole_0 @ X2 @ (k2_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['99', '100'])).
% 44.04/44.31  thf('102', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 44.04/44.31           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X1)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['98', '101'])).
% 44.04/44.31  thf('103', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X1)
% 44.04/44.31           = (k4_xboole_0 @ X0 @ X1))),
% 44.04/44.31      inference('demod', [status(thm)], ['86', '87'])).
% 44.04/44.31  thf('104', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 44.04/44.31      inference('demod', [status(thm)], ['4', '19'])).
% 44.04/44.31  thf('105', plain,
% 44.04/44.31      (![X11 : $i, X12 : $i, X13 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 44.04/44.31           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 44.04/44.31      inference('cnf', [status(esa)], [t91_xboole_1])).
% 44.04/44.31  thf('106', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k1_xboole_0)
% 44.04/44.31           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 44.04/44.31      inference('sup+', [status(thm)], ['104', '105'])).
% 44.04/44.31  thf('107', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k1_xboole_0)
% 44.04/44.31           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 44.04/44.31              (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 44.04/44.31      inference('sup+', [status(thm)], ['103', '106'])).
% 44.04/44.31  thf('108', plain,
% 44.04/44.31      (![X14 : $i, X15 : $i]:
% 44.04/44.31         ((k2_xboole_0 @ X14 @ X15)
% 44.04/44.31           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 44.04/44.31      inference('cnf', [status(esa)], [t98_xboole_1])).
% 44.04/44.31  thf('109', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k1_xboole_0)
% 44.04/44.31           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X1)))),
% 44.04/44.31      inference('demod', [status(thm)], ['107', '108'])).
% 44.04/44.31  thf('110', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 44.04/44.31      inference('demod', [status(thm)], ['26', '31'])).
% 44.04/44.31  thf('111', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k2_xboole_0 @ X1 @ X0)
% 44.04/44.31           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ k1_xboole_0))),
% 44.04/44.31      inference('sup+', [status(thm)], ['109', '110'])).
% 44.04/44.31  thf('112', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k1_xboole_0)
% 44.04/44.31           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 44.04/44.31      inference('sup+', [status(thm)], ['104', '105'])).
% 44.04/44.31  thf('113', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 44.04/44.31      inference('demod', [status(thm)], ['26', '31'])).
% 44.04/44.31  thf('114', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 44.04/44.31           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 44.04/44.31      inference('sup+', [status(thm)], ['112', '113'])).
% 44.04/44.31  thf('115', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 44.04/44.31      inference('cnf', [status(esa)], [t5_boole])).
% 44.04/44.31  thf('116', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 44.04/44.31      inference('demod', [status(thm)], ['114', '115'])).
% 44.04/44.31  thf('117', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 44.04/44.31      inference('demod', [status(thm)], ['26', '31'])).
% 44.04/44.31  thf('118', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 44.04/44.31      inference('sup+', [status(thm)], ['116', '117'])).
% 44.04/44.31  thf('119', plain,
% 44.04/44.31      (![X0 : $i]:
% 44.04/44.31         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 44.04/44.31      inference('sup+', [status(thm)], ['23', '24'])).
% 44.04/44.31  thf('120', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 44.04/44.31      inference('sup+', [status(thm)], ['29', '30'])).
% 44.04/44.31  thf('121', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 44.04/44.31      inference('demod', [status(thm)], ['119', '120'])).
% 44.04/44.31  thf('122', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 44.04/44.31      inference('demod', [status(thm)], ['111', '118', '121'])).
% 44.04/44.31  thf('123', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 44.04/44.31      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 44.04/44.31  thf('124', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 44.04/44.31           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['66', '67'])).
% 44.04/44.31  thf('125', plain,
% 44.04/44.31      (![X3 : $i, X4 : $i]:
% 44.04/44.31         ((k4_xboole_0 @ X3 @ X4)
% 44.04/44.31           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 44.04/44.31      inference('cnf', [status(esa)], [t100_xboole_1])).
% 44.04/44.31  thf('126', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 44.04/44.31      inference('demod', [status(thm)], ['26', '31'])).
% 44.04/44.31  thf('127', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k3_xboole_0 @ X1 @ X0)
% 44.04/44.31           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['125', '126'])).
% 44.04/44.31  thf('128', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 44.04/44.31           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))))),
% 44.04/44.31      inference('sup+', [status(thm)], ['124', '127'])).
% 44.04/44.31  thf('129', plain,
% 44.04/44.31      (![X3 : $i, X4 : $i]:
% 44.04/44.31         ((k4_xboole_0 @ X3 @ X4)
% 44.04/44.31           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 44.04/44.31      inference('cnf', [status(esa)], [t100_xboole_1])).
% 44.04/44.31  thf('130', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 44.04/44.31           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 44.04/44.31      inference('demod', [status(thm)], ['128', '129'])).
% 44.04/44.31  thf('131', plain,
% 44.04/44.31      (![X8 : $i, X9 : $i]:
% 44.04/44.31         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 44.04/44.31           = (k3_xboole_0 @ X8 @ X9))),
% 44.04/44.31      inference('cnf', [status(esa)], [t48_xboole_1])).
% 44.04/44.31  thf('132', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 44.04/44.31           = (k3_xboole_0 @ X1 @ X0))),
% 44.04/44.31      inference('demod', [status(thm)], ['130', '131'])).
% 44.04/44.31  thf('133', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k4_xboole_0 @ X0 @ X1)
% 44.04/44.31           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['8', '9'])).
% 44.04/44.31  thf('134', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 44.04/44.31           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['132', '133'])).
% 44.04/44.31  thf('135', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 44.04/44.31      inference('demod', [status(thm)], ['4', '19'])).
% 44.04/44.31  thf('136', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 44.04/44.31      inference('demod', [status(thm)], ['134', '135'])).
% 44.04/44.31  thf('137', plain,
% 44.04/44.31      (![X14 : $i, X15 : $i]:
% 44.04/44.31         ((k2_xboole_0 @ X14 @ X15)
% 44.04/44.31           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 44.04/44.31      inference('cnf', [status(esa)], [t98_xboole_1])).
% 44.04/44.31  thf('138', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 44.04/44.31           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 44.04/44.31      inference('sup+', [status(thm)], ['136', '137'])).
% 44.04/44.31  thf('139', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 44.04/44.31      inference('cnf', [status(esa)], [t5_boole])).
% 44.04/44.31  thf('140', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) = (X0))),
% 44.04/44.31      inference('demod', [status(thm)], ['138', '139'])).
% 44.04/44.31  thf('141', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 44.04/44.31      inference('sup+', [status(thm)], ['123', '140'])).
% 44.04/44.31  thf('142', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 44.04/44.31           = (k5_xboole_0 @ X0 @ X1))),
% 44.04/44.31      inference('demod', [status(thm)], ['102', '122', '141'])).
% 44.04/44.31  thf('143', plain,
% 44.04/44.31      (![X0 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ 
% 44.04/44.31           (k4_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0)) @ 
% 44.04/44.31           k1_xboole_0)
% 44.04/44.31           = (k5_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['64', '142'])).
% 44.04/44.31  thf('144', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 44.04/44.31      inference('sup+', [status(thm)], ['116', '117'])).
% 44.04/44.31  thf('145', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 44.04/44.31      inference('demod', [status(thm)], ['119', '120'])).
% 44.04/44.31  thf('146', plain,
% 44.04/44.31      (![X0 : $i]:
% 44.04/44.31         ((k4_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0))
% 44.04/44.31           = (k5_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0)))),
% 44.04/44.31      inference('demod', [status(thm)], ['143', '144', '145'])).
% 44.04/44.31  thf('147', plain,
% 44.04/44.31      (![X0 : $i]:
% 44.04/44.31         ((k4_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0))
% 44.04/44.31           = (k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['52', '146'])).
% 44.04/44.31  thf('148', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 44.04/44.31      inference('demod', [status(thm)], ['4', '19'])).
% 44.04/44.31  thf('149', plain,
% 44.04/44.31      (![X0 : $i]:
% 44.04/44.31         ((k4_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0))
% 44.04/44.31           = (k1_xboole_0))),
% 44.04/44.31      inference('demod', [status(thm)], ['147', '148'])).
% 44.04/44.31  thf('150', plain,
% 44.04/44.31      (![X8 : $i, X9 : $i]:
% 44.04/44.31         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 44.04/44.31           = (k3_xboole_0 @ X8 @ X9))),
% 44.04/44.31      inference('cnf', [status(esa)], [t48_xboole_1])).
% 44.04/44.31  thf('151', plain,
% 44.04/44.31      (![X0 : $i]:
% 44.04/44.31         ((k4_xboole_0 @ (k2_tarski @ X0 @ X0) @ k1_xboole_0)
% 44.04/44.31           = (k3_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['149', '150'])).
% 44.04/44.31  thf('152', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 44.04/44.31      inference('sup+', [status(thm)], ['11', '12'])).
% 44.04/44.31  thf('153', plain,
% 44.04/44.31      (![X0 : $i]:
% 44.04/44.31         ((k2_tarski @ X0 @ X0)
% 44.04/44.31           = (k3_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0)))),
% 44.04/44.31      inference('demod', [status(thm)], ['151', '152'])).
% 44.04/44.31  thf('154', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 44.04/44.31      inference('sup+', [status(thm)], ['123', '140'])).
% 44.04/44.31  thf('155', plain,
% 44.04/44.31      (![X0 : $i]:
% 44.04/44.31         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X0))
% 44.04/44.31           = (k1_tarski @ X0))),
% 44.04/44.31      inference('sup+', [status(thm)], ['153', '154'])).
% 44.04/44.31  thf('156', plain,
% 44.04/44.31      (![X14 : $i, X15 : $i]:
% 44.04/44.31         ((k2_xboole_0 @ X14 @ X15)
% 44.04/44.31           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 44.04/44.31      inference('cnf', [status(esa)], [t98_xboole_1])).
% 44.04/44.31  thf('157', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k3_xboole_0 @ X1 @ X0)
% 44.04/44.31           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['125', '126'])).
% 44.04/44.31  thf('158', plain,
% 44.04/44.31      (![X11 : $i, X12 : $i, X13 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 44.04/44.31           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 44.04/44.31      inference('cnf', [status(esa)], [t91_xboole_1])).
% 44.04/44.31  thf('159', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.04/44.31         ((k3_xboole_0 @ (k5_xboole_0 @ X2 @ X1) @ X0)
% 44.04/44.31           = (k5_xboole_0 @ X2 @ 
% 44.04/44.31              (k5_xboole_0 @ X1 @ (k4_xboole_0 @ (k5_xboole_0 @ X2 @ X1) @ X0))))),
% 44.04/44.31      inference('sup+', [status(thm)], ['157', '158'])).
% 44.04/44.31  thf('160', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.04/44.31         ((k3_xboole_0 @ (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) @ X2)
% 44.04/44.31           = (k5_xboole_0 @ X1 @ 
% 44.04/44.31              (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 44.04/44.31               (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))))),
% 44.04/44.31      inference('sup+', [status(thm)], ['156', '159'])).
% 44.04/44.31  thf('161', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X1)
% 44.04/44.31           = (k4_xboole_0 @ X0 @ X1))),
% 44.04/44.31      inference('demod', [status(thm)], ['86', '87'])).
% 44.04/44.31  thf('162', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 44.04/44.31      inference('sup+', [status(thm)], ['116', '117'])).
% 44.04/44.31  thf('163', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1))
% 44.04/44.31           = (k4_xboole_0 @ X0 @ X1))),
% 44.04/44.31      inference('demod', [status(thm)], ['161', '162'])).
% 44.04/44.31  thf('164', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 44.04/44.31      inference('demod', [status(thm)], ['26', '31'])).
% 44.04/44.31  thf('165', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k2_xboole_0 @ X1 @ X0)
% 44.04/44.31           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['163', '164'])).
% 44.04/44.31  thf('166', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 44.04/44.31           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['83', '84'])).
% 44.04/44.31  thf('167', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k4_xboole_0 @ X0 @ X1)
% 44.04/44.31           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['8', '9'])).
% 44.04/44.31  thf('168', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 44.04/44.31      inference('demod', [status(thm)], ['26', '31'])).
% 44.04/44.31  thf('169', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k3_xboole_0 @ X0 @ X1)
% 44.04/44.31           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['167', '168'])).
% 44.04/44.31  thf('170', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.04/44.31         ((k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 44.04/44.31           = (k3_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 44.04/44.31      inference('demod', [status(thm)], ['160', '165', '166', '169'])).
% 44.04/44.31  thf('171', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 44.04/44.31      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 44.04/44.31  thf('172', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 44.04/44.31           = (k2_xboole_0 @ X1 @ X0))),
% 44.04/44.31      inference('sup+', [status(thm)], ['170', '171'])).
% 44.04/44.31  thf('173', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k3_xboole_0 @ X1 @ X0)
% 44.04/44.31           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['125', '126'])).
% 44.04/44.31  thf('174', plain,
% 44.04/44.31      (![X11 : $i, X12 : $i, X13 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 44.04/44.31           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 44.04/44.31      inference('cnf', [status(esa)], [t91_xboole_1])).
% 44.04/44.31  thf('175', plain,
% 44.04/44.31      (![X14 : $i, X15 : $i]:
% 44.04/44.31         ((k2_xboole_0 @ X14 @ X15)
% 44.04/44.31           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 44.04/44.31      inference('cnf', [status(esa)], [t98_xboole_1])).
% 44.04/44.31  thf('176', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.04/44.31         ((k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 44.04/44.31           = (k5_xboole_0 @ X1 @ 
% 44.04/44.31              (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))))),
% 44.04/44.31      inference('sup+', [status(thm)], ['174', '175'])).
% 44.04/44.31  thf('177', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.04/44.31         ((k2_xboole_0 @ (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) @ X2)
% 44.04/44.31           = (k5_xboole_0 @ X1 @ 
% 44.04/44.31              (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 44.04/44.31               (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))))),
% 44.04/44.31      inference('sup+', [status(thm)], ['173', '176'])).
% 44.04/44.31  thf('178', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k3_xboole_0 @ X0 @ X1)
% 44.04/44.31           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['167', '168'])).
% 44.04/44.31  thf('179', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.04/44.31         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2)
% 44.04/44.31           = (k5_xboole_0 @ X1 @ 
% 44.04/44.31              (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 44.04/44.31               (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))))),
% 44.04/44.31      inference('demod', [status(thm)], ['177', '178'])).
% 44.04/44.31  thf('180', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k3_xboole_0 @ X0 @ X1)
% 44.04/44.31           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['167', '168'])).
% 44.04/44.31  thf('181', plain,
% 44.04/44.31      (![X11 : $i, X12 : $i, X13 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 44.04/44.31           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 44.04/44.31      inference('cnf', [status(esa)], [t91_xboole_1])).
% 44.04/44.31  thf('182', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 44.04/44.31           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['180', '181'])).
% 44.04/44.31  thf('183', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.04/44.31         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2)
% 44.04/44.31           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ 
% 44.04/44.31              (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 44.04/44.31      inference('demod', [status(thm)], ['179', '182'])).
% 44.04/44.31  thf('184', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.04/44.31         ((k2_xboole_0 @ 
% 44.04/44.31           (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0)) @ 
% 44.04/44.31           X2)
% 44.04/44.31           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 44.04/44.31              (k4_xboole_0 @ X2 @ 
% 44.04/44.31               (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X1)))))),
% 44.04/44.31      inference('sup+', [status(thm)], ['172', '183'])).
% 44.04/44.31  thf('185', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.04/44.31         ((k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 44.04/44.31           = (k3_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 44.04/44.31      inference('demod', [status(thm)], ['160', '165', '166', '169'])).
% 44.04/44.31  thf('186', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 44.04/44.31      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 44.04/44.31  thf('187', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 44.04/44.31           = (k2_xboole_0 @ X0 @ X1))),
% 44.04/44.31      inference('sup+', [status(thm)], ['185', '186'])).
% 44.04/44.31  thf('188', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 44.04/44.31           = (k2_xboole_0 @ X0 @ X1))),
% 44.04/44.31      inference('sup+', [status(thm)], ['185', '186'])).
% 44.04/44.31  thf('189', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k2_xboole_0 @ X1 @ X0)
% 44.04/44.31           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['163', '164'])).
% 44.04/44.31  thf('190', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.04/44.31         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 44.04/44.31           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 44.04/44.31      inference('demod', [status(thm)], ['184', '187', '188', '189'])).
% 44.04/44.31  thf('191', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k1_xboole_0)
% 44.04/44.31           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X1)))),
% 44.04/44.31      inference('demod', [status(thm)], ['107', '108'])).
% 44.04/44.31  thf('192', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.04/44.31         ((k1_xboole_0)
% 44.04/44.31           = (k5_xboole_0 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0) @ 
% 44.04/44.31              (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ X0)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['190', '191'])).
% 44.04/44.31  thf('193', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 44.04/44.31      inference('demod', [status(thm)], ['114', '115'])).
% 44.04/44.31  thf('194', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k1_xboole_0)
% 44.04/44.31           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X1)))),
% 44.04/44.31      inference('demod', [status(thm)], ['107', '108'])).
% 44.04/44.31  thf('195', plain,
% 44.04/44.31      (![X11 : $i, X12 : $i, X13 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 44.04/44.31           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 44.04/44.31      inference('cnf', [status(esa)], [t91_xboole_1])).
% 44.04/44.31  thf('196', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 44.04/44.31           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ 
% 44.04/44.31              (k5_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['194', '195'])).
% 44.04/44.31  thf('197', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 44.04/44.31      inference('demod', [status(thm)], ['119', '120'])).
% 44.04/44.31  thf('198', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.04/44.31         ((X0)
% 44.04/44.31           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ 
% 44.04/44.31              (k5_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)))),
% 44.04/44.31      inference('demod', [status(thm)], ['196', '197'])).
% 44.04/44.31  thf('199', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1))
% 44.04/44.31           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ X0))),
% 44.04/44.31      inference('sup+', [status(thm)], ['193', '198'])).
% 44.04/44.31  thf('200', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2) @ 
% 44.04/44.31           (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))) = (k1_xboole_0))),
% 44.04/44.31      inference('sup+', [status(thm)], ['192', '199'])).
% 44.04/44.31  thf('201', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ 
% 44.04/44.31           (k2_xboole_0 @ 
% 44.04/44.31            (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0)) @ X1) @ 
% 44.04/44.31           (k2_xboole_0 @ X1 @ (k1_tarski @ X0))) = (k1_xboole_0))),
% 44.04/44.31      inference('sup+', [status(thm)], ['155', '200'])).
% 44.04/44.31  thf('202', plain,
% 44.04/44.31      (![X0 : $i]:
% 44.04/44.31         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X0))
% 44.04/44.31           = (k1_xboole_0))),
% 44.04/44.31      inference('demod', [status(thm)], ['59', '62', '63'])).
% 44.04/44.31  thf('203', plain,
% 44.04/44.31      (![X14 : $i, X15 : $i]:
% 44.04/44.31         ((k2_xboole_0 @ X14 @ X15)
% 44.04/44.31           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 44.04/44.31      inference('cnf', [status(esa)], [t98_xboole_1])).
% 44.04/44.31  thf('204', plain,
% 44.04/44.31      (![X0 : $i]:
% 44.04/44.31         ((k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0))
% 44.04/44.31           = (k5_xboole_0 @ (k2_tarski @ X0 @ X0) @ k1_xboole_0))),
% 44.04/44.31      inference('sup+', [status(thm)], ['202', '203'])).
% 44.04/44.31  thf('205', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 44.04/44.31      inference('cnf', [status(esa)], [t5_boole])).
% 44.04/44.31  thf('206', plain,
% 44.04/44.31      (![X0 : $i]:
% 44.04/44.31         ((k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0))
% 44.04/44.31           = (k2_tarski @ X0 @ X0))),
% 44.04/44.31      inference('demod', [status(thm)], ['204', '205'])).
% 44.04/44.31  thf('207', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ X1) @ 
% 44.04/44.31           (k2_xboole_0 @ X1 @ (k1_tarski @ X0))) = (k1_xboole_0))),
% 44.04/44.31      inference('demod', [status(thm)], ['201', '206'])).
% 44.04/44.31  thf('208', plain,
% 44.04/44.31      (![X14 : $i, X15 : $i]:
% 44.04/44.31         ((k2_xboole_0 @ X14 @ X15)
% 44.04/44.31           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 44.04/44.31      inference('cnf', [status(esa)], [t98_xboole_1])).
% 44.04/44.31  thf('209', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 44.04/44.31      inference('demod', [status(thm)], ['114', '115'])).
% 44.04/44.31  thf('210', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 44.04/44.31           = (X1))),
% 44.04/44.31      inference('sup+', [status(thm)], ['208', '209'])).
% 44.04/44.31  thf('211', plain,
% 44.04/44.31      (![X11 : $i, X12 : $i, X13 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 44.04/44.31           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 44.04/44.31      inference('cnf', [status(esa)], [t91_xboole_1])).
% 44.04/44.31  thf('212', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 44.04/44.31      inference('demod', [status(thm)], ['114', '115'])).
% 44.04/44.31  thf('213', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))
% 44.04/44.31           = (k5_xboole_0 @ X2 @ X1))),
% 44.04/44.31      inference('sup+', [status(thm)], ['211', '212'])).
% 44.04/44.31  thf('214', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X2 @ X0))
% 44.04/44.31           = (k5_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['210', '213'])).
% 44.04/44.31  thf('215', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))
% 44.04/44.31           = (k5_xboole_0 @ X2 @ X1))),
% 44.04/44.31      inference('sup+', [status(thm)], ['211', '212'])).
% 44.04/44.31  thf('216', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 44.04/44.31      inference('sup+', [status(thm)], ['116', '117'])).
% 44.04/44.31  thf('217', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 44.04/44.31      inference('demod', [status(thm)], ['114', '115'])).
% 44.04/44.31  thf('218', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 44.04/44.31      inference('demod', [status(thm)], ['4', '19'])).
% 44.04/44.31  thf('219', plain,
% 44.04/44.31      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 44.04/44.31      inference('demod', [status(thm)], ['34', '35'])).
% 44.04/44.31  thf('220', plain,
% 44.04/44.31      (![X8 : $i, X9 : $i]:
% 44.04/44.31         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 44.04/44.31           = (k3_xboole_0 @ X8 @ X9))),
% 44.04/44.31      inference('cnf', [status(esa)], [t48_xboole_1])).
% 44.04/44.31  thf('221', plain,
% 44.04/44.31      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0)
% 44.04/44.31         = (k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['219', '220'])).
% 44.04/44.31  thf('222', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 44.04/44.31      inference('sup+', [status(thm)], ['11', '12'])).
% 44.04/44.31  thf('223', plain,
% 44.04/44.31      (((k1_tarski @ sk_B)
% 44.04/44.31         = (k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 44.04/44.31      inference('demod', [status(thm)], ['221', '222'])).
% 44.04/44.31  thf('224', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k4_xboole_0 @ X0 @ X1)
% 44.04/44.31           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['8', '9'])).
% 44.04/44.31  thf('225', plain,
% 44.04/44.31      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 44.04/44.31         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['223', '224'])).
% 44.04/44.31  thf('226', plain,
% 44.04/44.31      (![X11 : $i, X12 : $i, X13 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 44.04/44.31           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 44.04/44.31      inference('cnf', [status(esa)], [t91_xboole_1])).
% 44.04/44.31  thf('227', plain,
% 44.04/44.31      (![X0 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ 
% 44.04/44.31           (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ X0)
% 44.04/44.31           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 44.04/44.31              (k5_xboole_0 @ (k1_tarski @ sk_B) @ X0)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['225', '226'])).
% 44.04/44.31  thf('228', plain,
% 44.04/44.31      (((k5_xboole_0 @ 
% 44.04/44.31         (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ 
% 44.04/44.31         (k1_tarski @ sk_B)) = (k5_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0))),
% 44.04/44.31      inference('sup+', [status(thm)], ['218', '227'])).
% 44.04/44.31  thf('229', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 44.04/44.31      inference('cnf', [status(esa)], [t5_boole])).
% 44.04/44.31  thf('230', plain,
% 44.04/44.31      (((k5_xboole_0 @ 
% 44.04/44.31         (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ 
% 44.04/44.31         (k1_tarski @ sk_B)) = (k1_tarski @ sk_A))),
% 44.04/44.31      inference('demod', [status(thm)], ['228', '229'])).
% 44.04/44.31  thf('231', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 44.04/44.31      inference('demod', [status(thm)], ['26', '31'])).
% 44.04/44.31  thf('232', plain,
% 44.04/44.31      (((k1_tarski @ sk_B)
% 44.04/44.31         = (k5_xboole_0 @ 
% 44.04/44.31            (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ 
% 44.04/44.31            (k1_tarski @ sk_A)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['230', '231'])).
% 44.04/44.31  thf('233', plain,
% 44.04/44.31      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 44.04/44.31         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['223', '224'])).
% 44.04/44.31  thf('234', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 44.04/44.31      inference('demod', [status(thm)], ['26', '31'])).
% 44.04/44.31  thf('235', plain,
% 44.04/44.31      (((k1_tarski @ sk_B)
% 44.04/44.31         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 44.04/44.31            (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))))),
% 44.04/44.31      inference('sup+', [status(thm)], ['233', '234'])).
% 44.04/44.31  thf('236', plain,
% 44.04/44.31      (![X11 : $i, X12 : $i, X13 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 44.04/44.31           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 44.04/44.31      inference('cnf', [status(esa)], [t91_xboole_1])).
% 44.04/44.31  thf('237', plain,
% 44.04/44.31      (![X0 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k1_tarski @ sk_B) @ X0)
% 44.04/44.31           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 44.04/44.31              (k5_xboole_0 @ 
% 44.04/44.31               (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ X0)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['235', '236'])).
% 44.04/44.31  thf('238', plain,
% 44.04/44.31      (((k5_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 44.04/44.31         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['232', '237'])).
% 44.04/44.31  thf('239', plain,
% 44.04/44.31      (![X11 : $i, X12 : $i, X13 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 44.04/44.31           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 44.04/44.31      inference('cnf', [status(esa)], [t91_xboole_1])).
% 44.04/44.31  thf('240', plain,
% 44.04/44.31      (![X0 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ 
% 44.04/44.31           (k5_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ X0)
% 44.04/44.31           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 44.04/44.31              (k5_xboole_0 @ (k1_tarski @ sk_B) @ X0)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['238', '239'])).
% 44.04/44.31  thf('241', plain,
% 44.04/44.31      (![X11 : $i, X12 : $i, X13 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 44.04/44.31           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 44.04/44.31      inference('cnf', [status(esa)], [t91_xboole_1])).
% 44.04/44.31  thf('242', plain,
% 44.04/44.31      (![X0 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ 
% 44.04/44.31           (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ X0)
% 44.04/44.31           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 44.04/44.31              (k5_xboole_0 @ (k1_tarski @ sk_B) @ X0)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['225', '226'])).
% 44.04/44.31  thf('243', plain,
% 44.04/44.31      (![X0 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k1_tarski @ sk_B) @ 
% 44.04/44.31           (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0))
% 44.04/44.31           = (k5_xboole_0 @ 
% 44.04/44.31              (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ X0))),
% 44.04/44.31      inference('demod', [status(thm)], ['240', '241', '242'])).
% 44.04/44.31  thf('244', plain,
% 44.04/44.31      (![X0 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k1_tarski @ sk_B) @ X0)
% 44.04/44.31           = (k5_xboole_0 @ 
% 44.04/44.31              (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ 
% 44.04/44.31              (k5_xboole_0 @ X0 @ (k1_tarski @ sk_A))))),
% 44.04/44.31      inference('sup+', [status(thm)], ['217', '243'])).
% 44.04/44.31  thf('245', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 44.04/44.31      inference('demod', [status(thm)], ['26', '31'])).
% 44.04/44.31  thf('246', plain,
% 44.04/44.31      (![X0 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ X0 @ (k1_tarski @ sk_A))
% 44.04/44.31           = (k5_xboole_0 @ 
% 44.04/44.31              (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ 
% 44.04/44.31              (k5_xboole_0 @ (k1_tarski @ sk_B) @ X0)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['244', '245'])).
% 44.04/44.31  thf('247', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 44.04/44.31      inference('sup+', [status(thm)], ['116', '117'])).
% 44.04/44.31  thf('248', plain,
% 44.04/44.31      (![X11 : $i, X12 : $i, X13 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 44.04/44.31           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 44.04/44.31      inference('cnf', [status(esa)], [t91_xboole_1])).
% 44.04/44.31  thf('249', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 44.04/44.31           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['247', '248'])).
% 44.04/44.31  thf('250', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k5_xboole_0 @ X0 @ (k1_tarski @ sk_A)) @ X1)
% 44.04/44.31           = (k5_xboole_0 @ (k5_xboole_0 @ (k1_tarski @ sk_B) @ X0) @ 
% 44.04/44.31              (k5_xboole_0 @ 
% 44.04/44.31               (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ X1)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['246', '249'])).
% 44.04/44.31  thf('251', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 44.04/44.31           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['247', '248'])).
% 44.04/44.31  thf('252', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 44.04/44.31           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['247', '248'])).
% 44.04/44.31  thf('253', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 44.04/44.31           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['83', '84'])).
% 44.04/44.31  thf('254', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 44.04/44.31      inference('demod', [status(thm)], ['4', '19'])).
% 44.04/44.31  thf('255', plain,
% 44.04/44.31      (![X0 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k1_tarski @ sk_B) @ X0)
% 44.04/44.31           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 44.04/44.31              (k5_xboole_0 @ 
% 44.04/44.31               (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ X0)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['235', '236'])).
% 44.04/44.31  thf('256', plain,
% 44.04/44.31      (((k5_xboole_0 @ (k1_tarski @ sk_B) @ 
% 44.04/44.31         (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 44.04/44.31         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0))),
% 44.04/44.31      inference('sup+', [status(thm)], ['254', '255'])).
% 44.04/44.31  thf('257', plain,
% 44.04/44.31      (![X14 : $i, X15 : $i]:
% 44.04/44.31         ((k2_xboole_0 @ X14 @ X15)
% 44.04/44.31           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 44.04/44.31      inference('cnf', [status(esa)], [t98_xboole_1])).
% 44.04/44.31  thf('258', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 44.04/44.31      inference('cnf', [status(esa)], [t5_boole])).
% 44.04/44.31  thf('259', plain,
% 44.04/44.31      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 44.04/44.31         = (k1_tarski @ sk_A))),
% 44.04/44.31      inference('demod', [status(thm)], ['256', '257', '258'])).
% 44.04/44.31  thf('260', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k1_tarski @ sk_A) @ (k5_xboole_0 @ X0 @ X1))
% 44.04/44.31           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X1)))),
% 44.04/44.31      inference('demod', [status(thm)], ['250', '251', '252', '253', '259'])).
% 44.04/44.31  thf('261', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k1_tarski @ sk_A) @ (k5_xboole_0 @ X1 @ X0))
% 44.04/44.31           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X1)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['216', '260'])).
% 44.04/44.31  thf('262', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 44.04/44.31           (k5_xboole_0 @ 
% 44.04/44.31            (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k1_tarski @ sk_A))) @ X2))
% 44.04/44.31           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['215', '261'])).
% 44.04/44.31  thf('263', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 44.04/44.31           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['247', '248'])).
% 44.04/44.31  thf('264', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 44.04/44.31           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['247', '248'])).
% 44.04/44.31  thf('265', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 44.04/44.31      inference('demod', [status(thm)], ['26', '31'])).
% 44.04/44.31  thf('266', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2))
% 44.04/44.31           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 44.04/44.31      inference('demod', [status(thm)], ['262', '263', '264', '265'])).
% 44.04/44.31  thf('267', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1)))
% 44.04/44.31           = (k5_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 44.04/44.31      inference('demod', [status(thm)], ['214', '266'])).
% 44.04/44.31  thf('268', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k5_xboole_0 @ X0 @ k1_xboole_0)
% 44.04/44.31           = (k5_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ X1 @ X1) @ X0) @ 
% 44.04/44.31              (k4_xboole_0 @ (k1_tarski @ X1) @ X0)))),
% 44.04/44.31      inference('sup+', [status(thm)], ['207', '267'])).
% 44.04/44.31  thf('269', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 44.04/44.31      inference('cnf', [status(esa)], [t5_boole])).
% 44.04/44.31  thf('270', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((X0)
% 44.04/44.31           = (k5_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ X1 @ X1) @ X0) @ 
% 44.04/44.31              (k4_xboole_0 @ (k1_tarski @ X1) @ X0)))),
% 44.04/44.31      inference('demod', [status(thm)], ['268', '269'])).
% 44.04/44.31  thf('271', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k1_tarski @ X0)
% 44.04/44.31           = (k5_xboole_0 @ (k2_enumset1 @ X1 @ X1 @ X1 @ X0) @ 
% 44.04/44.31              (k4_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))))),
% 44.04/44.31      inference('sup+', [status(thm)], ['51', '270'])).
% 44.04/44.31  thf('272', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 44.04/44.31      inference('sup+', [status(thm)], ['37', '38'])).
% 44.04/44.31  thf('273', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]:
% 44.04/44.31         ((k1_tarski @ X0)
% 44.04/44.31           = (k5_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 44.04/44.31              (k4_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))))),
% 44.04/44.31      inference('demod', [status(thm)], ['271', '272'])).
% 44.04/44.31  thf('274', plain,
% 44.04/44.31      (((k1_tarski @ sk_A)
% 44.04/44.31         = (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ k1_xboole_0))),
% 44.04/44.31      inference('sup+', [status(thm)], ['36', '273'])).
% 44.04/44.31  thf('275', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 44.04/44.31      inference('sup+', [status(thm)], ['116', '117'])).
% 44.04/44.31  thf('276', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 44.04/44.31      inference('demod', [status(thm)], ['119', '120'])).
% 44.04/44.31  thf('277', plain, (((k1_tarski @ sk_A) = (k2_tarski @ sk_B @ sk_A))),
% 44.04/44.31      inference('demod', [status(thm)], ['274', '275', '276'])).
% 44.04/44.31  thf('278', plain,
% 44.04/44.31      (![X50 : $i, X51 : $i]:
% 44.04/44.31         ((k1_enumset1 @ X50 @ X50 @ X51) = (k2_tarski @ X50 @ X51))),
% 44.04/44.31      inference('cnf', [status(esa)], [t70_enumset1])).
% 44.04/44.31  thf(d1_enumset1, axiom,
% 44.04/44.31    (![A:$i,B:$i,C:$i,D:$i]:
% 44.04/44.31     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 44.04/44.31       ( ![E:$i]:
% 44.04/44.31         ( ( r2_hidden @ E @ D ) <=>
% 44.04/44.31           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 44.04/44.31  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 44.04/44.31  thf(zf_stmt_2, axiom,
% 44.04/44.31    (![E:$i,C:$i,B:$i,A:$i]:
% 44.04/44.31     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 44.04/44.31       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 44.04/44.31  thf(zf_stmt_3, axiom,
% 44.04/44.31    (![A:$i,B:$i,C:$i,D:$i]:
% 44.04/44.31     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 44.04/44.31       ( ![E:$i]:
% 44.04/44.31         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 44.04/44.31  thf('279', plain,
% 44.04/44.31      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 44.04/44.31         ((zip_tseitin_0 @ X21 @ X22 @ X23 @ X24)
% 44.04/44.31          | (r2_hidden @ X21 @ X25)
% 44.04/44.31          | ((X25) != (k1_enumset1 @ X24 @ X23 @ X22)))),
% 44.04/44.31      inference('cnf', [status(esa)], [zf_stmt_3])).
% 44.04/44.31  thf('280', plain,
% 44.04/44.31      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 44.04/44.31         ((r2_hidden @ X21 @ (k1_enumset1 @ X24 @ X23 @ X22))
% 44.04/44.31          | (zip_tseitin_0 @ X21 @ X22 @ X23 @ X24))),
% 44.04/44.31      inference('simplify', [status(thm)], ['279'])).
% 44.04/44.31  thf('281', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.04/44.31         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 44.04/44.31          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 44.04/44.31      inference('sup+', [status(thm)], ['278', '280'])).
% 44.04/44.31  thf('282', plain,
% 44.04/44.31      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 44.04/44.31         (((X17) != (X16)) | ~ (zip_tseitin_0 @ X17 @ X18 @ X19 @ X16))),
% 44.04/44.31      inference('cnf', [status(esa)], [zf_stmt_2])).
% 44.04/44.31  thf('283', plain,
% 44.04/44.31      (![X16 : $i, X18 : $i, X19 : $i]:
% 44.04/44.31         ~ (zip_tseitin_0 @ X16 @ X18 @ X19 @ X16)),
% 44.04/44.31      inference('simplify', [status(thm)], ['282'])).
% 44.04/44.31  thf('284', plain,
% 44.04/44.31      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 44.04/44.31      inference('sup-', [status(thm)], ['281', '283'])).
% 44.04/44.31  thf('285', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 44.04/44.31      inference('sup+', [status(thm)], ['277', '284'])).
% 44.04/44.31  thf(d1_tarski, axiom,
% 44.04/44.31    (![A:$i,B:$i]:
% 44.04/44.31     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 44.04/44.31       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 44.04/44.31  thf('286', plain,
% 44.04/44.31      (![X28 : $i, X30 : $i, X31 : $i]:
% 44.04/44.31         (~ (r2_hidden @ X31 @ X30)
% 44.04/44.31          | ((X31) = (X28))
% 44.04/44.31          | ((X30) != (k1_tarski @ X28)))),
% 44.04/44.31      inference('cnf', [status(esa)], [d1_tarski])).
% 44.04/44.31  thf('287', plain,
% 44.04/44.31      (![X28 : $i, X31 : $i]:
% 44.04/44.31         (((X31) = (X28)) | ~ (r2_hidden @ X31 @ (k1_tarski @ X28)))),
% 44.04/44.31      inference('simplify', [status(thm)], ['286'])).
% 44.04/44.31  thf('288', plain, (((sk_B) = (sk_A))),
% 44.04/44.31      inference('sup-', [status(thm)], ['285', '287'])).
% 44.04/44.31  thf('289', plain, (((sk_A) != (sk_B))),
% 44.04/44.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.04/44.31  thf('290', plain, ($false),
% 44.04/44.31      inference('simplify_reflect-', [status(thm)], ['288', '289'])).
% 44.04/44.31  
% 44.04/44.31  % SZS output end Refutation
% 44.04/44.31  
% 44.04/44.32  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

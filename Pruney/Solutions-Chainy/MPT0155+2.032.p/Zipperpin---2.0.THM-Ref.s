%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pMEkguOIoZ

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:30 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 304 expanded)
%              Number of leaves         :   18 ( 108 expanded)
%              Depth                    :   18
%              Number of atoms          :  809 (3363 expanded)
%              Number of equality atoms :   71 ( 293 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t71_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_enumset1 @ A @ A @ B @ C )
        = ( k1_enumset1 @ A @ B @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t71_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_enumset1 @ X27 @ X27 @ X28 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k2_enumset1 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k1_enumset1 @ X6 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k1_enumset1 @ X2 @ X3 @ X4 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('6',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('7',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k1_enumset1 @ X2 @ X3 @ X4 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t47_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k3_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X9 ) @ ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X0 @ X4 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X1 @ X0 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X2 ) @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('15',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k2_enumset1 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k1_enumset1 @ X6 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k3_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X9 ) @ ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X2 ) @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('22',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_enumset1 @ X27 @ X27 @ X28 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t55_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ) )).

thf('25',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( k4_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 ) @ ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t55_enumset1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('28',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k3_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k1_tarski @ X9 ) @ ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k1_enumset1 @ X2 @ X3 @ X4 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X1 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(t51_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ) )).

thf('32',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k4_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k1_tarski @ X14 ) @ ( k3_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t51_enumset1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X2 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k2_enumset1 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k1_enumset1 @ X6 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X2 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','39'])).

thf('41',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('42',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k1_enumset1 @ X2 @ X3 @ X4 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','40','43'])).

thf('45',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_enumset1 @ X27 @ X27 @ X28 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','35'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
      = ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','35'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X1 @ X0 @ X0 ) @ ( k1_tarski @ X2 ) )
      = ( k2_enumset1 @ X1 @ X0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
      = ( k2_enumset1 @ X1 @ X0 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['51','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['48','59'])).

thf('61',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','60'])).

thf('62',plain,(
    $false ),
    inference(simplify,[status(thm)],['61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pMEkguOIoZ
% 0.11/0.32  % Computer   : n012.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 11:26:37 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running portfolio for 600 s
% 0.11/0.32  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.32  % Number of cores: 8
% 0.11/0.33  % Python version: Python 3.6.8
% 0.11/0.33  % Running in FO mode
% 0.17/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.17/0.53  % Solved by: fo/fo7.sh
% 0.17/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.17/0.53  % done 166 iterations in 0.088s
% 0.17/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.17/0.53  % SZS output start Refutation
% 0.17/0.53  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.17/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.17/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.17/0.53  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.17/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.17/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.17/0.53  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.17/0.53  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.17/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.17/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.17/0.53  thf(t71_enumset1, conjecture,
% 0.17/0.53    (![A:$i,B:$i,C:$i]:
% 0.17/0.53     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.17/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.17/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.17/0.53        ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ) )),
% 0.17/0.53    inference('cnf.neg', [status(esa)], [t71_enumset1])).
% 0.17/0.53  thf('0', plain,
% 0.17/0.53      (((k2_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.17/0.53         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.17/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.53  thf(t70_enumset1, axiom,
% 0.17/0.53    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.17/0.53  thf('1', plain,
% 0.17/0.53      (![X27 : $i, X28 : $i]:
% 0.17/0.53         ((k1_enumset1 @ X27 @ X27 @ X28) = (k2_tarski @ X27 @ X28))),
% 0.17/0.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.17/0.53  thf(t44_enumset1, axiom,
% 0.17/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.17/0.53     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.17/0.53       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 0.17/0.53  thf('2', plain,
% 0.17/0.53      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.17/0.53         ((k2_enumset1 @ X5 @ X6 @ X7 @ X8)
% 0.17/0.53           = (k2_xboole_0 @ (k1_tarski @ X5) @ (k1_enumset1 @ X6 @ X7 @ X8)))),
% 0.17/0.53      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.17/0.53  thf('3', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.17/0.53         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0)
% 0.17/0.53           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.17/0.53      inference('sup+', [status(thm)], ['1', '2'])).
% 0.17/0.53  thf(t42_enumset1, axiom,
% 0.17/0.53    (![A:$i,B:$i,C:$i]:
% 0.17/0.53     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.17/0.53       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.17/0.53  thf('4', plain,
% 0.17/0.53      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.17/0.53         ((k1_enumset1 @ X2 @ X3 @ X4)
% 0.17/0.53           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X3 @ X4)))),
% 0.17/0.53      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.17/0.53  thf('5', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.17/0.53         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.17/0.53      inference('demod', [status(thm)], ['3', '4'])).
% 0.17/0.53  thf(t69_enumset1, axiom,
% 0.17/0.53    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.17/0.53  thf('6', plain, (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 0.17/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.17/0.53  thf('7', plain,
% 0.17/0.53      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.17/0.53         ((k1_enumset1 @ X2 @ X3 @ X4)
% 0.17/0.53           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X3 @ X4)))),
% 0.17/0.53      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.17/0.53  thf('8', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i]:
% 0.17/0.53         ((k1_enumset1 @ X1 @ X0 @ X0)
% 0.17/0.53           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.17/0.53      inference('sup+', [status(thm)], ['6', '7'])).
% 0.17/0.53  thf('9', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i]:
% 0.17/0.53         ((k2_enumset1 @ X1 @ X0 @ X0 @ X0)
% 0.17/0.53           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.17/0.53      inference('sup+', [status(thm)], ['5', '8'])).
% 0.17/0.53  thf('10', plain,
% 0.17/0.53      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 0.17/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.17/0.53  thf(t47_enumset1, axiom,
% 0.17/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.17/0.53     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.17/0.53       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ))).
% 0.17/0.53  thf('11', plain,
% 0.17/0.53      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.17/0.53         ((k3_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13)
% 0.17/0.53           = (k2_xboole_0 @ (k1_tarski @ X9) @ 
% 0.17/0.53              (k2_enumset1 @ X10 @ X11 @ X12 @ X13)))),
% 0.17/0.53      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.17/0.53  thf('12', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.17/0.53         ((k3_enumset1 @ X0 @ X4 @ X3 @ X2 @ X1)
% 0.17/0.53           = (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ 
% 0.17/0.53              (k2_enumset1 @ X4 @ X3 @ X2 @ X1)))),
% 0.17/0.53      inference('sup+', [status(thm)], ['10', '11'])).
% 0.17/0.53  thf('13', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.17/0.53         ((k3_enumset1 @ X2 @ X1 @ X0 @ X0 @ X0)
% 0.17/0.53           = (k2_xboole_0 @ (k2_tarski @ X2 @ X2) @ 
% 0.17/0.53              (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))))),
% 0.17/0.53      inference('sup+', [status(thm)], ['9', '12'])).
% 0.17/0.53  thf('14', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.17/0.53         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.17/0.53      inference('demod', [status(thm)], ['3', '4'])).
% 0.17/0.53  thf('15', plain,
% 0.17/0.53      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.17/0.53         ((k2_enumset1 @ X5 @ X6 @ X7 @ X8)
% 0.17/0.53           = (k2_xboole_0 @ (k1_tarski @ X5) @ (k1_enumset1 @ X6 @ X7 @ X8)))),
% 0.17/0.53      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.17/0.53  thf('16', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.17/0.53         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 0.17/0.53           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 0.17/0.53              (k2_enumset1 @ X2 @ X1 @ X1 @ X0)))),
% 0.17/0.53      inference('sup+', [status(thm)], ['14', '15'])).
% 0.17/0.53  thf('17', plain,
% 0.17/0.53      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.17/0.53         ((k3_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13)
% 0.17/0.53           = (k2_xboole_0 @ (k1_tarski @ X9) @ 
% 0.17/0.53              (k2_enumset1 @ X10 @ X11 @ X12 @ X13)))),
% 0.17/0.53      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.17/0.53  thf('18', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.17/0.53         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 0.17/0.53           = (k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0))),
% 0.17/0.53      inference('demod', [status(thm)], ['16', '17'])).
% 0.17/0.53  thf('19', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.17/0.53         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0)
% 0.17/0.53           = (k2_xboole_0 @ (k2_tarski @ X2 @ X2) @ 
% 0.17/0.53              (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))))),
% 0.17/0.53      inference('demod', [status(thm)], ['13', '18'])).
% 0.17/0.53  thf('20', plain,
% 0.17/0.53      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 0.17/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.17/0.53  thf('21', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.17/0.53         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.17/0.53      inference('demod', [status(thm)], ['3', '4'])).
% 0.17/0.53  thf('22', plain,
% 0.17/0.53      (![X27 : $i, X28 : $i]:
% 0.17/0.53         ((k1_enumset1 @ X27 @ X27 @ X28) = (k2_tarski @ X27 @ X28))),
% 0.17/0.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.17/0.53  thf('23', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i]:
% 0.17/0.53         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.17/0.53      inference('sup+', [status(thm)], ['21', '22'])).
% 0.17/0.53  thf('24', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.17/0.53         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 0.17/0.53           = (k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0))),
% 0.17/0.53      inference('demod', [status(thm)], ['16', '17'])).
% 0.17/0.53  thf(t55_enumset1, axiom,
% 0.17/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.17/0.53     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.17/0.53       ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ))).
% 0.17/0.53  thf('25', plain,
% 0.17/0.53      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.17/0.53         ((k4_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25)
% 0.17/0.53           = (k2_xboole_0 @ (k3_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24) @ 
% 0.17/0.53              (k1_tarski @ X25)))),
% 0.17/0.53      inference('cnf', [status(esa)], [t55_enumset1])).
% 0.17/0.53  thf('26', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.17/0.53         ((k4_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0 @ X4)
% 0.17/0.53           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.17/0.53              (k1_tarski @ X4)))),
% 0.17/0.53      inference('sup+', [status(thm)], ['24', '25'])).
% 0.17/0.53  thf('27', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i]:
% 0.17/0.53         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.17/0.53      inference('sup+', [status(thm)], ['21', '22'])).
% 0.17/0.53  thf('28', plain,
% 0.17/0.53      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.17/0.53         ((k3_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13)
% 0.17/0.53           = (k2_xboole_0 @ (k1_tarski @ X9) @ 
% 0.17/0.53              (k2_enumset1 @ X10 @ X11 @ X12 @ X13)))),
% 0.17/0.53      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.17/0.53  thf('29', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.17/0.53         ((k3_enumset1 @ X2 @ X1 @ X1 @ X1 @ X0)
% 0.17/0.53           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.17/0.53      inference('sup+', [status(thm)], ['27', '28'])).
% 0.17/0.53  thf('30', plain,
% 0.17/0.53      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.17/0.53         ((k1_enumset1 @ X2 @ X3 @ X4)
% 0.17/0.53           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X3 @ X4)))),
% 0.17/0.53      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.17/0.53  thf('31', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.17/0.53         ((k3_enumset1 @ X2 @ X1 @ X1 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.17/0.53      inference('demod', [status(thm)], ['29', '30'])).
% 0.17/0.53  thf(t51_enumset1, axiom,
% 0.17/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.17/0.53     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.17/0.53       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ))).
% 0.17/0.53  thf('32', plain,
% 0.17/0.53      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.17/0.53         ((k4_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19)
% 0.17/0.53           = (k2_xboole_0 @ (k1_tarski @ X14) @ 
% 0.17/0.53              (k3_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19)))),
% 0.17/0.53      inference('cnf', [status(esa)], [t51_enumset1])).
% 0.17/0.53  thf('33', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.17/0.53         ((k4_enumset1 @ X3 @ X2 @ X1 @ X1 @ X1 @ X0)
% 0.17/0.53           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.17/0.53      inference('sup+', [status(thm)], ['31', '32'])).
% 0.17/0.53  thf('34', plain,
% 0.17/0.53      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.17/0.53         ((k2_enumset1 @ X5 @ X6 @ X7 @ X8)
% 0.17/0.53           = (k2_xboole_0 @ (k1_tarski @ X5) @ (k1_enumset1 @ X6 @ X7 @ X8)))),
% 0.17/0.53      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.17/0.53  thf('35', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.17/0.53         ((k4_enumset1 @ X3 @ X2 @ X1 @ X1 @ X1 @ X0)
% 0.17/0.53           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.17/0.53      inference('demod', [status(thm)], ['33', '34'])).
% 0.17/0.53  thf('36', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.17/0.53         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X1) @ (k1_tarski @ X0))
% 0.17/0.53           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.17/0.53      inference('sup+', [status(thm)], ['26', '35'])).
% 0.17/0.53  thf('37', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i]:
% 0.17/0.53         ((k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X1))
% 0.17/0.53           = (k2_enumset1 @ X0 @ X0 @ X0 @ X1))),
% 0.17/0.53      inference('sup+', [status(thm)], ['23', '36'])).
% 0.17/0.53  thf('38', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i]:
% 0.17/0.53         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.17/0.53      inference('sup+', [status(thm)], ['21', '22'])).
% 0.17/0.53  thf('39', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i]:
% 0.17/0.53         ((k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X1))
% 0.17/0.53           = (k2_tarski @ X0 @ X1))),
% 0.17/0.53      inference('demod', [status(thm)], ['37', '38'])).
% 0.17/0.53  thf('40', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i]:
% 0.17/0.53         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.17/0.53           = (k2_tarski @ X0 @ X1))),
% 0.17/0.53      inference('sup+', [status(thm)], ['20', '39'])).
% 0.17/0.53  thf('41', plain,
% 0.17/0.53      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 0.17/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.17/0.53  thf('42', plain,
% 0.17/0.53      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.17/0.53         ((k1_enumset1 @ X2 @ X3 @ X4)
% 0.17/0.53           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X3 @ X4)))),
% 0.17/0.53      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.17/0.53  thf('43', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.17/0.53         ((k1_enumset1 @ X0 @ X2 @ X1)
% 0.17/0.53           = (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k2_tarski @ X2 @ X1)))),
% 0.17/0.53      inference('sup+', [status(thm)], ['41', '42'])).
% 0.17/0.53  thf('44', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.17/0.53         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.17/0.53      inference('demod', [status(thm)], ['19', '40', '43'])).
% 0.17/0.53  thf('45', plain,
% 0.17/0.53      (![X27 : $i, X28 : $i]:
% 0.17/0.53         ((k1_enumset1 @ X27 @ X27 @ X28) = (k2_tarski @ X27 @ X28))),
% 0.17/0.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.17/0.53  thf('46', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i]:
% 0.17/0.53         ((k2_enumset1 @ X1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.17/0.53      inference('sup+', [status(thm)], ['44', '45'])).
% 0.17/0.53  thf('47', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.17/0.53         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X1) @ (k1_tarski @ X0))
% 0.17/0.53           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.17/0.53      inference('sup+', [status(thm)], ['26', '35'])).
% 0.17/0.53  thf('48', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.17/0.53         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2))
% 0.17/0.53           = (k2_enumset1 @ X1 @ X1 @ X0 @ X2))),
% 0.17/0.53      inference('sup+', [status(thm)], ['46', '47'])).
% 0.17/0.53  thf('49', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.17/0.53         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.17/0.53      inference('demod', [status(thm)], ['3', '4'])).
% 0.17/0.53  thf('50', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.17/0.53         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X1) @ (k1_tarski @ X0))
% 0.17/0.53           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.17/0.53      inference('sup+', [status(thm)], ['26', '35'])).
% 0.17/0.53  thf('51', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.17/0.53         ((k2_xboole_0 @ (k1_enumset1 @ X1 @ X0 @ X0) @ (k1_tarski @ X2))
% 0.17/0.53           = (k2_enumset1 @ X1 @ X0 @ X0 @ X2))),
% 0.17/0.53      inference('sup+', [status(thm)], ['49', '50'])).
% 0.17/0.53  thf('52', plain,
% 0.17/0.53      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 0.17/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.17/0.53  thf('53', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.17/0.53         ((k1_enumset1 @ X0 @ X2 @ X1)
% 0.17/0.53           = (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k2_tarski @ X2 @ X1)))),
% 0.17/0.53      inference('sup+', [status(thm)], ['41', '42'])).
% 0.17/0.53  thf('54', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i]:
% 0.17/0.53         ((k1_enumset1 @ X1 @ X0 @ X0)
% 0.17/0.53           = (k2_xboole_0 @ (k2_tarski @ X1 @ X1) @ (k1_tarski @ X0)))),
% 0.17/0.53      inference('sup+', [status(thm)], ['52', '53'])).
% 0.17/0.53  thf('55', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i]:
% 0.17/0.53         ((k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X1))
% 0.17/0.53           = (k2_tarski @ X0 @ X1))),
% 0.17/0.53      inference('demod', [status(thm)], ['37', '38'])).
% 0.17/0.53  thf('56', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i]:
% 0.17/0.53         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.17/0.53      inference('demod', [status(thm)], ['54', '55'])).
% 0.17/0.53  thf('57', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.17/0.53         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2))
% 0.17/0.53           = (k2_enumset1 @ X1 @ X0 @ X0 @ X2))),
% 0.17/0.53      inference('demod', [status(thm)], ['51', '56'])).
% 0.17/0.53  thf('58', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.17/0.53         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.17/0.53      inference('demod', [status(thm)], ['3', '4'])).
% 0.17/0.53  thf('59', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.17/0.53         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.17/0.53           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.17/0.53      inference('sup+', [status(thm)], ['57', '58'])).
% 0.17/0.53  thf('60', plain,
% 0.17/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.17/0.53         ((k1_enumset1 @ X1 @ X0 @ X2) = (k2_enumset1 @ X1 @ X1 @ X0 @ X2))),
% 0.17/0.53      inference('demod', [status(thm)], ['48', '59'])).
% 0.17/0.53  thf('61', plain,
% 0.17/0.53      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.17/0.53         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.17/0.53      inference('demod', [status(thm)], ['0', '60'])).
% 0.17/0.53  thf('62', plain, ($false), inference('simplify', [status(thm)], ['61'])).
% 0.17/0.53  
% 0.17/0.53  % SZS output end Refutation
% 0.17/0.53  
% 0.17/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

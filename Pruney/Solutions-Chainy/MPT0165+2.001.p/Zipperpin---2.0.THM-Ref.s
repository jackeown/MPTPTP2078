%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NpEizgZRDd

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:42 EST 2020

% Result     : Theorem 4.00s
% Output     : Refutation 4.00s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 300 expanded)
%              Number of leaves         :   26 ( 110 expanded)
%              Depth                    :   20
%              Number of atoms          : 1275 (3789 expanded)
%              Number of equality atoms :   92 ( 284 expanded)
%              Maximal formula depth    :   18 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(t81_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k6_enumset1 @ A @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
        ( ( k6_enumset1 @ A @ A @ A @ B @ C @ D @ E @ F )
        = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) ),
    inference('cnf.neg',[status(esa)],[t81_enumset1])).

thf('0',plain,(
    ( k6_enumset1 @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F )
 != ( k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t77_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_enumset1 @ A @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k2_enumset1 @ X44 @ X44 @ X44 @ X45 )
      = ( k2_tarski @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t77_enumset1])).

thf(l75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k6_enumset1 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X5 @ X6 @ X7 @ X8 ) @ ( k2_enumset1 @ X9 @ X10 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[l75_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X1 @ X1 @ X1 @ X0 @ X5 @ X4 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_enumset1 @ sk_C @ sk_D @ sk_E @ sk_F ) )
 != ( k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k2_enumset1 @ X44 @ X44 @ X44 @ X45 )
      = ( k2_tarski @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t77_enumset1])).

thf('6',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k2_enumset1 @ X44 @ X44 @ X44 @ X45 )
      = ( k2_tarski @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t77_enumset1])).

thf(t59_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_enumset1 @ E @ F @ G ) ) ) )).

thf('7',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k5_enumset1 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X36 @ X37 @ X38 @ X39 ) @ ( k1_enumset1 @ X40 @ X41 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t59_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X1 @ X1 @ X1 @ X0 @ X4 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_enumset1 @ X4 @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('9',plain,(
    ! [X43: $i] :
      ( ( k2_tarski @ X43 @ X43 )
      = ( k1_tarski @ X43 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('10',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k1_tarski @ X13 ) @ ( k1_enumset1 @ X14 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_enumset1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k5_enumset1 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k5_enumset1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','12'])).

thf('14',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k2_enumset1 @ X44 @ X44 @ X44 @ X45 )
      = ( k2_tarski @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t77_enumset1])).

thf(t58_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_enumset1 @ D @ E @ F @ G ) ) ) )).

thf('15',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k5_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X29 @ X30 @ X31 ) @ ( k2_enumset1 @ X32 @ X33 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t58_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X3 @ X2 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(l57_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X0 @ X1 @ X2 ) @ ( k2_tarski @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X3 @ X2 @ X1 @ X1 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','18'])).

thf(t78_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_enumset1 @ A @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('20',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( k3_enumset1 @ X46 @ X46 @ X46 @ X47 @ X48 )
      = ( k1_enumset1 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t78_enumset1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k5_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X29 @ X30 @ X31 ) @ ( k2_enumset1 @ X32 @ X33 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t58_enumset1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X1 @ X1 @ X0 @ X5 @ X4 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ( k5_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F )
 != ( k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['4','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','18'])).

thf('26',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( k3_enumset1 @ X46 @ X46 @ X46 @ X47 @ X48 )
      = ( k1_enumset1 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t78_enumset1])).

thf(t53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ) )).

thf('27',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k4_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X23 @ X24 @ X25 ) @ ( k1_enumset1 @ X26 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t53_enumset1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X5 @ X4 @ X3 ) @ ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X0 @ X1 @ X2 ) @ ( k2_tarski @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X43: $i] :
      ( ( k2_tarski @ X43 @ X43 )
      = ( k1_tarski @ X43 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X0 @ X1 @ X2 ) @ ( k2_tarski @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','18'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X0 @ X0 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('38',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( k3_enumset1 @ X46 @ X46 @ X46 @ X47 @ X48 )
      = ( k1_enumset1 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t78_enumset1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X1 @ X1 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k4_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X23 @ X24 @ X25 ) @ ( k1_enumset1 @ X26 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t53_enumset1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X0 @ X0 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_enumset1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_enumset1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X0 @ X0 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_enumset1 @ X0 @ X3 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','44'])).

thf('46',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( k3_enumset1 @ X46 @ X46 @ X46 @ X47 @ X48 )
      = ( k1_enumset1 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t78_enumset1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('49',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( k3_enumset1 @ X46 @ X46 @ X46 @ X47 @ X48 )
      = ( k1_enumset1 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t78_enumset1])).

thf(t51_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ) )).

thf('50',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( k4_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22 )
      = ( k2_xboole_0 @ ( k1_tarski @ X17 ) @ ( k3_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t51_enumset1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k1_tarski @ X13 ) @ ( k1_enumset1 @ X14 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X1 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','54'])).

thf('56',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k1_tarski @ X13 ) @ ( k1_enumset1 @ X14 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k3_enumset1 @ X2 @ X1 @ X1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( k4_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22 )
      = ( k2_xboole_0 @ ( k1_tarski @ X17 ) @ ( k3_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t51_enumset1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','18'])).

thf('62',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( k3_enumset1 @ X46 @ X46 @ X46 @ X47 @ X48 )
      = ( k1_enumset1 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t78_enumset1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X0 @ X1 @ X2 ) @ ( k2_tarski @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X2 @ X1 @ X0 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X1 @ X1 @ X1 @ X0 @ X4 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_enumset1 @ X4 @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X3 @ X2 @ X1 @ X1 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
      = ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( k3_enumset1 @ X46 @ X46 @ X46 @ X47 @ X48 )
      = ( k1_enumset1 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t78_enumset1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['66','73'])).

thf('75',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k4_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X23 @ X24 @ X25 ) @ ( k1_enumset1 @ X26 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t53_enumset1])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) @ ( k1_enumset1 @ X5 @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k5_enumset1 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X36 @ X37 @ X38 @ X39 ) @ ( k1_enumset1 @ X40 @ X41 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t59_enumset1])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3 )
      = ( k5_enumset1 @ X2 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ( k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F )
 != ( k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['24','78'])).

thf('80',plain,(
    $false ),
    inference(simplify,[status(thm)],['79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NpEizgZRDd
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:07:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 4.00/4.25  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.00/4.25  % Solved by: fo/fo7.sh
% 4.00/4.25  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.00/4.25  % done 5731 iterations in 3.795s
% 4.00/4.25  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.00/4.25  % SZS output start Refutation
% 4.00/4.25  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 4.00/4.25  thf(sk_F_type, type, sk_F: $i).
% 4.00/4.25  thf(sk_D_type, type, sk_D: $i).
% 4.00/4.25  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 4.00/4.25  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.00/4.25  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 4.00/4.25                                           $i > $i).
% 4.00/4.25  thf(sk_B_type, type, sk_B: $i).
% 4.00/4.25  thf(sk_C_type, type, sk_C: $i).
% 4.00/4.25  thf(sk_A_type, type, sk_A: $i).
% 4.00/4.25  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 4.00/4.25  thf(sk_E_type, type, sk_E: $i).
% 4.00/4.25  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 4.00/4.25  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 4.00/4.25  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 4.00/4.25  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 4.00/4.25  thf(t81_enumset1, conjecture,
% 4.00/4.25    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.00/4.25     ( ( k6_enumset1 @ A @ A @ A @ B @ C @ D @ E @ F ) =
% 4.00/4.25       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 4.00/4.25  thf(zf_stmt_0, negated_conjecture,
% 4.00/4.25    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.00/4.25        ( ( k6_enumset1 @ A @ A @ A @ B @ C @ D @ E @ F ) =
% 4.00/4.25          ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )),
% 4.00/4.25    inference('cnf.neg', [status(esa)], [t81_enumset1])).
% 4.00/4.25  thf('0', plain,
% 4.00/4.25      (((k6_enumset1 @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)
% 4.00/4.25         != (k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))),
% 4.00/4.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.25  thf(t77_enumset1, axiom,
% 4.00/4.25    (![A:$i,B:$i]: ( ( k2_enumset1 @ A @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 4.00/4.25  thf('1', plain,
% 4.00/4.25      (![X44 : $i, X45 : $i]:
% 4.00/4.25         ((k2_enumset1 @ X44 @ X44 @ X44 @ X45) = (k2_tarski @ X44 @ X45))),
% 4.00/4.25      inference('cnf', [status(esa)], [t77_enumset1])).
% 4.00/4.25  thf(l75_enumset1, axiom,
% 4.00/4.25    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 4.00/4.25     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 4.00/4.25       ( k2_xboole_0 @
% 4.00/4.25         ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ))).
% 4.00/4.25  thf('2', plain,
% 4.00/4.25      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, 
% 4.00/4.25         X12 : $i]:
% 4.00/4.25         ((k6_enumset1 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12)
% 4.00/4.25           = (k2_xboole_0 @ (k2_enumset1 @ X5 @ X6 @ X7 @ X8) @ 
% 4.00/4.25              (k2_enumset1 @ X9 @ X10 @ X11 @ X12)))),
% 4.00/4.25      inference('cnf', [status(esa)], [l75_enumset1])).
% 4.00/4.25  thf('3', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 4.00/4.25         ((k6_enumset1 @ X1 @ X1 @ X1 @ X0 @ X5 @ X4 @ X3 @ X2)
% 4.00/4.25           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 4.00/4.25              (k2_enumset1 @ X5 @ X4 @ X3 @ X2)))),
% 4.00/4.25      inference('sup+', [status(thm)], ['1', '2'])).
% 4.00/4.25  thf('4', plain,
% 4.00/4.25      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 4.00/4.25         (k2_enumset1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 4.00/4.25         != (k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))),
% 4.00/4.25      inference('demod', [status(thm)], ['0', '3'])).
% 4.00/4.25  thf('5', plain,
% 4.00/4.25      (![X44 : $i, X45 : $i]:
% 4.00/4.25         ((k2_enumset1 @ X44 @ X44 @ X44 @ X45) = (k2_tarski @ X44 @ X45))),
% 4.00/4.25      inference('cnf', [status(esa)], [t77_enumset1])).
% 4.00/4.25  thf('6', plain,
% 4.00/4.25      (![X44 : $i, X45 : $i]:
% 4.00/4.25         ((k2_enumset1 @ X44 @ X44 @ X44 @ X45) = (k2_tarski @ X44 @ X45))),
% 4.00/4.25      inference('cnf', [status(esa)], [t77_enumset1])).
% 4.00/4.25  thf(t59_enumset1, axiom,
% 4.00/4.25    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 4.00/4.25     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 4.00/4.25       ( k2_xboole_0 @
% 4.00/4.25         ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_enumset1 @ E @ F @ G ) ) ))).
% 4.00/4.25  thf('7', plain,
% 4.00/4.25      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 4.00/4.25         ((k5_enumset1 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42)
% 4.00/4.25           = (k2_xboole_0 @ (k2_enumset1 @ X36 @ X37 @ X38 @ X39) @ 
% 4.00/4.25              (k1_enumset1 @ X40 @ X41 @ X42)))),
% 4.00/4.25      inference('cnf', [status(esa)], [t59_enumset1])).
% 4.00/4.25  thf('8', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 4.00/4.25         ((k5_enumset1 @ X1 @ X1 @ X1 @ X0 @ X4 @ X3 @ X2)
% 4.00/4.25           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 4.00/4.25              (k1_enumset1 @ X4 @ X3 @ X2)))),
% 4.00/4.25      inference('sup+', [status(thm)], ['6', '7'])).
% 4.00/4.25  thf(t69_enumset1, axiom,
% 4.00/4.25    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 4.00/4.25  thf('9', plain, (![X43 : $i]: ((k2_tarski @ X43 @ X43) = (k1_tarski @ X43))),
% 4.00/4.25      inference('cnf', [status(esa)], [t69_enumset1])).
% 4.00/4.25  thf(t44_enumset1, axiom,
% 4.00/4.25    (![A:$i,B:$i,C:$i,D:$i]:
% 4.00/4.25     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 4.00/4.25       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 4.00/4.25  thf('10', plain,
% 4.00/4.25      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 4.00/4.25         ((k2_enumset1 @ X13 @ X14 @ X15 @ X16)
% 4.00/4.25           = (k2_xboole_0 @ (k1_tarski @ X13) @ (k1_enumset1 @ X14 @ X15 @ X16)))),
% 4.00/4.25      inference('cnf', [status(esa)], [t44_enumset1])).
% 4.00/4.25  thf('11', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.00/4.25         ((k2_enumset1 @ X0 @ X3 @ X2 @ X1)
% 4.00/4.25           = (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ 
% 4.00/4.25              (k1_enumset1 @ X3 @ X2 @ X1)))),
% 4.00/4.25      inference('sup+', [status(thm)], ['9', '10'])).
% 4.00/4.25  thf('12', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.00/4.25         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 4.00/4.25           = (k5_enumset1 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0))),
% 4.00/4.25      inference('sup+', [status(thm)], ['8', '11'])).
% 4.00/4.25  thf('13', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i]:
% 4.00/4.25         ((k2_tarski @ X1 @ X0)
% 4.00/4.25           = (k5_enumset1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X0))),
% 4.00/4.25      inference('sup+', [status(thm)], ['5', '12'])).
% 4.00/4.25  thf('14', plain,
% 4.00/4.25      (![X44 : $i, X45 : $i]:
% 4.00/4.25         ((k2_enumset1 @ X44 @ X44 @ X44 @ X45) = (k2_tarski @ X44 @ X45))),
% 4.00/4.25      inference('cnf', [status(esa)], [t77_enumset1])).
% 4.00/4.25  thf(t58_enumset1, axiom,
% 4.00/4.25    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 4.00/4.25     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 4.00/4.25       ( k2_xboole_0 @
% 4.00/4.25         ( k1_enumset1 @ A @ B @ C ) @ ( k2_enumset1 @ D @ E @ F @ G ) ) ))).
% 4.00/4.25  thf('15', plain,
% 4.00/4.25      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 4.00/4.25         ((k5_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35)
% 4.00/4.25           = (k2_xboole_0 @ (k1_enumset1 @ X29 @ X30 @ X31) @ 
% 4.00/4.25              (k2_enumset1 @ X32 @ X33 @ X34 @ X35)))),
% 4.00/4.25      inference('cnf', [status(esa)], [t58_enumset1])).
% 4.00/4.25  thf('16', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 4.00/4.25         ((k5_enumset1 @ X4 @ X3 @ X2 @ X1 @ X1 @ X1 @ X0)
% 4.00/4.25           = (k2_xboole_0 @ (k1_enumset1 @ X4 @ X3 @ X2) @ 
% 4.00/4.25              (k2_tarski @ X1 @ X0)))),
% 4.00/4.25      inference('sup+', [status(thm)], ['14', '15'])).
% 4.00/4.25  thf(l57_enumset1, axiom,
% 4.00/4.25    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 4.00/4.25     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 4.00/4.25       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ))).
% 4.00/4.25  thf('17', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 4.00/4.25         ((k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4)
% 4.00/4.25           = (k2_xboole_0 @ (k1_enumset1 @ X0 @ X1 @ X2) @ 
% 4.00/4.25              (k2_tarski @ X3 @ X4)))),
% 4.00/4.25      inference('cnf', [status(esa)], [l57_enumset1])).
% 4.00/4.25  thf('18', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 4.00/4.25         ((k5_enumset1 @ X4 @ X3 @ X2 @ X1 @ X1 @ X1 @ X0)
% 4.00/4.25           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 4.00/4.25      inference('demod', [status(thm)], ['16', '17'])).
% 4.00/4.25  thf('19', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i]:
% 4.00/4.25         ((k2_tarski @ X1 @ X0) = (k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0))),
% 4.00/4.25      inference('demod', [status(thm)], ['13', '18'])).
% 4.00/4.25  thf(t78_enumset1, axiom,
% 4.00/4.25    (![A:$i,B:$i,C:$i]:
% 4.00/4.25     ( ( k3_enumset1 @ A @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 4.00/4.25  thf('20', plain,
% 4.00/4.25      (![X46 : $i, X47 : $i, X48 : $i]:
% 4.00/4.25         ((k3_enumset1 @ X46 @ X46 @ X46 @ X47 @ X48)
% 4.00/4.25           = (k1_enumset1 @ X46 @ X47 @ X48))),
% 4.00/4.25      inference('cnf', [status(esa)], [t78_enumset1])).
% 4.00/4.25  thf('21', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i]:
% 4.00/4.25         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 4.00/4.25      inference('sup+', [status(thm)], ['19', '20'])).
% 4.00/4.25  thf('22', plain,
% 4.00/4.25      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 4.00/4.25         ((k5_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35)
% 4.00/4.25           = (k2_xboole_0 @ (k1_enumset1 @ X29 @ X30 @ X31) @ 
% 4.00/4.25              (k2_enumset1 @ X32 @ X33 @ X34 @ X35)))),
% 4.00/4.25      inference('cnf', [status(esa)], [t58_enumset1])).
% 4.00/4.25  thf('23', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 4.00/4.25         ((k5_enumset1 @ X1 @ X1 @ X0 @ X5 @ X4 @ X3 @ X2)
% 4.00/4.25           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 4.00/4.25              (k2_enumset1 @ X5 @ X4 @ X3 @ X2)))),
% 4.00/4.25      inference('sup+', [status(thm)], ['21', '22'])).
% 4.00/4.25  thf('24', plain,
% 4.00/4.25      (((k5_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)
% 4.00/4.25         != (k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))),
% 4.00/4.25      inference('demod', [status(thm)], ['4', '23'])).
% 4.00/4.25  thf('25', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i]:
% 4.00/4.25         ((k2_tarski @ X1 @ X0) = (k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0))),
% 4.00/4.25      inference('demod', [status(thm)], ['13', '18'])).
% 4.00/4.25  thf('26', plain,
% 4.00/4.25      (![X46 : $i, X47 : $i, X48 : $i]:
% 4.00/4.25         ((k3_enumset1 @ X46 @ X46 @ X46 @ X47 @ X48)
% 4.00/4.25           = (k1_enumset1 @ X46 @ X47 @ X48))),
% 4.00/4.25      inference('cnf', [status(esa)], [t78_enumset1])).
% 4.00/4.25  thf(t53_enumset1, axiom,
% 4.00/4.25    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.00/4.25     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 4.00/4.25       ( k2_xboole_0 @
% 4.00/4.25         ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ))).
% 4.00/4.25  thf('27', plain,
% 4.00/4.25      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 4.00/4.25         ((k4_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28)
% 4.00/4.25           = (k2_xboole_0 @ (k1_enumset1 @ X23 @ X24 @ X25) @ 
% 4.00/4.25              (k1_enumset1 @ X26 @ X27 @ X28)))),
% 4.00/4.25      inference('cnf', [status(esa)], [t53_enumset1])).
% 4.00/4.25  thf('28', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 4.00/4.25         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 4.00/4.25           = (k2_xboole_0 @ (k1_enumset1 @ X5 @ X4 @ X3) @ 
% 4.00/4.25              (k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0)))),
% 4.00/4.25      inference('sup+', [status(thm)], ['26', '27'])).
% 4.00/4.25  thf('29', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 4.00/4.25         ((k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X1 @ X0)
% 4.00/4.25           = (k2_xboole_0 @ (k1_enumset1 @ X4 @ X3 @ X2) @ 
% 4.00/4.25              (k2_tarski @ X1 @ X0)))),
% 4.00/4.25      inference('sup+', [status(thm)], ['25', '28'])).
% 4.00/4.25  thf('30', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 4.00/4.25         ((k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4)
% 4.00/4.25           = (k2_xboole_0 @ (k1_enumset1 @ X0 @ X1 @ X2) @ 
% 4.00/4.25              (k2_tarski @ X3 @ X4)))),
% 4.00/4.25      inference('cnf', [status(esa)], [l57_enumset1])).
% 4.00/4.25  thf('31', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 4.00/4.25         ((k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X1 @ X0)
% 4.00/4.25           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 4.00/4.25      inference('demod', [status(thm)], ['29', '30'])).
% 4.00/4.25  thf('32', plain,
% 4.00/4.25      (![X43 : $i]: ((k2_tarski @ X43 @ X43) = (k1_tarski @ X43))),
% 4.00/4.25      inference('cnf', [status(esa)], [t69_enumset1])).
% 4.00/4.25  thf('33', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 4.00/4.25         ((k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4)
% 4.00/4.25           = (k2_xboole_0 @ (k1_enumset1 @ X0 @ X1 @ X2) @ 
% 4.00/4.25              (k2_tarski @ X3 @ X4)))),
% 4.00/4.25      inference('cnf', [status(esa)], [l57_enumset1])).
% 4.00/4.25  thf('34', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.00/4.25         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0)
% 4.00/4.25           = (k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0)))),
% 4.00/4.25      inference('sup+', [status(thm)], ['32', '33'])).
% 4.00/4.25  thf('35', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i]:
% 4.00/4.25         ((k2_tarski @ X1 @ X0) = (k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0))),
% 4.00/4.25      inference('demod', [status(thm)], ['13', '18'])).
% 4.00/4.25  thf('36', plain,
% 4.00/4.25      (![X0 : $i]:
% 4.00/4.25         ((k2_tarski @ X0 @ X0)
% 4.00/4.25           = (k2_xboole_0 @ (k1_enumset1 @ X0 @ X0 @ X0) @ (k1_tarski @ X0)))),
% 4.00/4.25      inference('sup+', [status(thm)], ['34', '35'])).
% 4.00/4.25  thf('37', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.00/4.25         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0)
% 4.00/4.25           = (k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0)))),
% 4.00/4.25      inference('sup+', [status(thm)], ['32', '33'])).
% 4.00/4.25  thf('38', plain,
% 4.00/4.25      (![X46 : $i, X47 : $i, X48 : $i]:
% 4.00/4.25         ((k3_enumset1 @ X46 @ X46 @ X46 @ X47 @ X48)
% 4.00/4.25           = (k1_enumset1 @ X46 @ X47 @ X48))),
% 4.00/4.25      inference('cnf', [status(esa)], [t78_enumset1])).
% 4.00/4.25  thf('39', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i]:
% 4.00/4.25         ((k2_xboole_0 @ (k1_enumset1 @ X1 @ X1 @ X1) @ (k1_tarski @ X0))
% 4.00/4.25           = (k1_enumset1 @ X1 @ X0 @ X0))),
% 4.00/4.25      inference('sup+', [status(thm)], ['37', '38'])).
% 4.00/4.25  thf('40', plain,
% 4.00/4.25      (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_enumset1 @ X0 @ X0 @ X0))),
% 4.00/4.25      inference('demod', [status(thm)], ['36', '39'])).
% 4.00/4.25  thf('41', plain,
% 4.00/4.25      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 4.00/4.25         ((k4_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28)
% 4.00/4.25           = (k2_xboole_0 @ (k1_enumset1 @ X23 @ X24 @ X25) @ 
% 4.00/4.25              (k1_enumset1 @ X26 @ X27 @ X28)))),
% 4.00/4.25      inference('cnf', [status(esa)], [t53_enumset1])).
% 4.00/4.25  thf('42', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.00/4.25         ((k4_enumset1 @ X0 @ X0 @ X0 @ X3 @ X2 @ X1)
% 4.00/4.25           = (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ 
% 4.00/4.25              (k1_enumset1 @ X3 @ X2 @ X1)))),
% 4.00/4.25      inference('sup+', [status(thm)], ['40', '41'])).
% 4.00/4.25  thf('43', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.00/4.25         ((k2_enumset1 @ X0 @ X3 @ X2 @ X1)
% 4.00/4.25           = (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ 
% 4.00/4.25              (k1_enumset1 @ X3 @ X2 @ X1)))),
% 4.00/4.25      inference('sup+', [status(thm)], ['9', '10'])).
% 4.00/4.25  thf('44', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.00/4.25         ((k4_enumset1 @ X0 @ X0 @ X0 @ X3 @ X2 @ X1)
% 4.00/4.25           = (k2_enumset1 @ X0 @ X3 @ X2 @ X1))),
% 4.00/4.25      inference('demod', [status(thm)], ['42', '43'])).
% 4.00/4.25  thf('45', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.00/4.25         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0)
% 4.00/4.25           = (k2_enumset1 @ X2 @ X1 @ X1 @ X0))),
% 4.00/4.25      inference('sup+', [status(thm)], ['31', '44'])).
% 4.00/4.25  thf('46', plain,
% 4.00/4.25      (![X46 : $i, X47 : $i, X48 : $i]:
% 4.00/4.25         ((k3_enumset1 @ X46 @ X46 @ X46 @ X47 @ X48)
% 4.00/4.25           = (k1_enumset1 @ X46 @ X47 @ X48))),
% 4.00/4.25      inference('cnf', [status(esa)], [t78_enumset1])).
% 4.00/4.25  thf('47', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.00/4.25         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 4.00/4.25      inference('sup+', [status(thm)], ['45', '46'])).
% 4.00/4.25  thf('48', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 4.00/4.25         ((k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X1 @ X0)
% 4.00/4.25           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 4.00/4.25      inference('demod', [status(thm)], ['29', '30'])).
% 4.00/4.25  thf('49', plain,
% 4.00/4.25      (![X46 : $i, X47 : $i, X48 : $i]:
% 4.00/4.25         ((k3_enumset1 @ X46 @ X46 @ X46 @ X47 @ X48)
% 4.00/4.25           = (k1_enumset1 @ X46 @ X47 @ X48))),
% 4.00/4.25      inference('cnf', [status(esa)], [t78_enumset1])).
% 4.00/4.25  thf(t51_enumset1, axiom,
% 4.00/4.25    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.00/4.25     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 4.00/4.25       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ))).
% 4.00/4.25  thf('50', plain,
% 4.00/4.25      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 4.00/4.25         ((k4_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22)
% 4.00/4.25           = (k2_xboole_0 @ (k1_tarski @ X17) @ 
% 4.00/4.25              (k3_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22)))),
% 4.00/4.25      inference('cnf', [status(esa)], [t51_enumset1])).
% 4.00/4.25  thf('51', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.00/4.25         ((k4_enumset1 @ X3 @ X2 @ X2 @ X2 @ X1 @ X0)
% 4.00/4.25           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 4.00/4.25      inference('sup+', [status(thm)], ['49', '50'])).
% 4.00/4.25  thf('52', plain,
% 4.00/4.25      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 4.00/4.25         ((k2_enumset1 @ X13 @ X14 @ X15 @ X16)
% 4.00/4.25           = (k2_xboole_0 @ (k1_tarski @ X13) @ (k1_enumset1 @ X14 @ X15 @ X16)))),
% 4.00/4.25      inference('cnf', [status(esa)], [t44_enumset1])).
% 4.00/4.25  thf('53', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.00/4.25         ((k4_enumset1 @ X3 @ X2 @ X2 @ X2 @ X1 @ X0)
% 4.00/4.25           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 4.00/4.25      inference('demod', [status(thm)], ['51', '52'])).
% 4.00/4.25  thf('54', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.00/4.25         ((k3_enumset1 @ X2 @ X1 @ X1 @ X1 @ X0)
% 4.00/4.25           = (k2_enumset1 @ X2 @ X1 @ X1 @ X0))),
% 4.00/4.25      inference('sup+', [status(thm)], ['48', '53'])).
% 4.00/4.25  thf('55', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.00/4.25         ((k3_enumset1 @ X2 @ X1 @ X1 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 4.00/4.25      inference('sup+', [status(thm)], ['47', '54'])).
% 4.00/4.25  thf('56', plain,
% 4.00/4.25      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 4.00/4.25         ((k2_enumset1 @ X13 @ X14 @ X15 @ X16)
% 4.00/4.25           = (k2_xboole_0 @ (k1_tarski @ X13) @ (k1_enumset1 @ X14 @ X15 @ X16)))),
% 4.00/4.25      inference('cnf', [status(esa)], [t44_enumset1])).
% 4.00/4.25  thf('57', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.00/4.25         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 4.00/4.25           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 4.00/4.25              (k3_enumset1 @ X2 @ X1 @ X1 @ X1 @ X0)))),
% 4.00/4.25      inference('sup+', [status(thm)], ['55', '56'])).
% 4.00/4.25  thf('58', plain,
% 4.00/4.25      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 4.00/4.25         ((k4_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22)
% 4.00/4.25           = (k2_xboole_0 @ (k1_tarski @ X17) @ 
% 4.00/4.25              (k3_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22)))),
% 4.00/4.25      inference('cnf', [status(esa)], [t51_enumset1])).
% 4.00/4.25  thf('59', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 4.00/4.25         ((k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X1 @ X0)
% 4.00/4.25           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 4.00/4.25      inference('demod', [status(thm)], ['29', '30'])).
% 4.00/4.25  thf('60', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.00/4.25         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 4.00/4.25           = (k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0))),
% 4.00/4.25      inference('demod', [status(thm)], ['57', '58', '59'])).
% 4.00/4.25  thf('61', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i]:
% 4.00/4.25         ((k2_tarski @ X1 @ X0) = (k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0))),
% 4.00/4.25      inference('demod', [status(thm)], ['13', '18'])).
% 4.00/4.25  thf('62', plain,
% 4.00/4.25      (![X46 : $i, X47 : $i, X48 : $i]:
% 4.00/4.25         ((k3_enumset1 @ X46 @ X46 @ X46 @ X47 @ X48)
% 4.00/4.25           = (k1_enumset1 @ X46 @ X47 @ X48))),
% 4.00/4.25      inference('cnf', [status(esa)], [t78_enumset1])).
% 4.00/4.25  thf('63', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 4.00/4.25         ((k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4)
% 4.00/4.25           = (k2_xboole_0 @ (k1_enumset1 @ X0 @ X1 @ X2) @ 
% 4.00/4.25              (k2_tarski @ X3 @ X4)))),
% 4.00/4.25      inference('cnf', [status(esa)], [l57_enumset1])).
% 4.00/4.25  thf('64', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 4.00/4.25         ((k3_enumset1 @ X2 @ X1 @ X0 @ X4 @ X3)
% 4.00/4.25           = (k2_xboole_0 @ (k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) @ 
% 4.00/4.25              (k2_tarski @ X4 @ X3)))),
% 4.00/4.25      inference('sup+', [status(thm)], ['62', '63'])).
% 4.00/4.25  thf('65', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.00/4.25         ((k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2)
% 4.00/4.25           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 4.00/4.25      inference('sup+', [status(thm)], ['61', '64'])).
% 4.00/4.25  thf('66', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.00/4.25         ((k2_enumset1 @ X2 @ X2 @ X1 @ X0)
% 4.00/4.25           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k2_tarski @ X1 @ X0)))),
% 4.00/4.25      inference('sup+', [status(thm)], ['60', '65'])).
% 4.00/4.25  thf('67', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 4.00/4.25         ((k5_enumset1 @ X1 @ X1 @ X1 @ X0 @ X4 @ X3 @ X2)
% 4.00/4.25           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 4.00/4.25              (k1_enumset1 @ X4 @ X3 @ X2)))),
% 4.00/4.25      inference('sup+', [status(thm)], ['6', '7'])).
% 4.00/4.25  thf('68', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 4.00/4.25         ((k5_enumset1 @ X4 @ X3 @ X2 @ X1 @ X1 @ X1 @ X0)
% 4.00/4.25           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 4.00/4.25      inference('demod', [status(thm)], ['16', '17'])).
% 4.00/4.25  thf('69', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.00/4.25         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_enumset1 @ X1 @ X1 @ X0))
% 4.00/4.25           = (k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0))),
% 4.00/4.25      inference('sup+', [status(thm)], ['67', '68'])).
% 4.00/4.25  thf('70', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i]:
% 4.00/4.25         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 4.00/4.25      inference('sup+', [status(thm)], ['19', '20'])).
% 4.00/4.25  thf('71', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.00/4.25         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k2_tarski @ X1 @ X0))
% 4.00/4.25           = (k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0))),
% 4.00/4.25      inference('demod', [status(thm)], ['69', '70'])).
% 4.00/4.25  thf('72', plain,
% 4.00/4.25      (![X46 : $i, X47 : $i, X48 : $i]:
% 4.00/4.25         ((k3_enumset1 @ X46 @ X46 @ X46 @ X47 @ X48)
% 4.00/4.25           = (k1_enumset1 @ X46 @ X47 @ X48))),
% 4.00/4.25      inference('cnf', [status(esa)], [t78_enumset1])).
% 4.00/4.25  thf('73', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.00/4.25         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k2_tarski @ X1 @ X0))
% 4.00/4.25           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 4.00/4.25      inference('sup+', [status(thm)], ['71', '72'])).
% 4.00/4.25  thf('74', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.00/4.25         ((k2_enumset1 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 4.00/4.25      inference('demod', [status(thm)], ['66', '73'])).
% 4.00/4.25  thf('75', plain,
% 4.00/4.25      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 4.00/4.25         ((k4_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28)
% 4.00/4.25           = (k2_xboole_0 @ (k1_enumset1 @ X23 @ X24 @ X25) @ 
% 4.00/4.25              (k1_enumset1 @ X26 @ X27 @ X28)))),
% 4.00/4.25      inference('cnf', [status(esa)], [t53_enumset1])).
% 4.00/4.25  thf('76', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 4.00/4.25         ((k4_enumset1 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3)
% 4.00/4.25           = (k2_xboole_0 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0) @ 
% 4.00/4.25              (k1_enumset1 @ X5 @ X4 @ X3)))),
% 4.00/4.25      inference('sup+', [status(thm)], ['74', '75'])).
% 4.00/4.25  thf('77', plain,
% 4.00/4.25      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 4.00/4.25         ((k5_enumset1 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42)
% 4.00/4.25           = (k2_xboole_0 @ (k2_enumset1 @ X36 @ X37 @ X38 @ X39) @ 
% 4.00/4.25              (k1_enumset1 @ X40 @ X41 @ X42)))),
% 4.00/4.25      inference('cnf', [status(esa)], [t59_enumset1])).
% 4.00/4.25  thf('78', plain,
% 4.00/4.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 4.00/4.25         ((k4_enumset1 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3)
% 4.00/4.25           = (k5_enumset1 @ X2 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3))),
% 4.00/4.25      inference('demod', [status(thm)], ['76', '77'])).
% 4.00/4.25  thf('79', plain,
% 4.00/4.25      (((k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)
% 4.00/4.25         != (k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))),
% 4.00/4.25      inference('demod', [status(thm)], ['24', '78'])).
% 4.00/4.25  thf('80', plain, ($false), inference('simplify', [status(thm)], ['79'])).
% 4.00/4.25  
% 4.00/4.25  % SZS output end Refutation
% 4.00/4.25  
% 4.00/4.26  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

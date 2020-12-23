%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.W0zaUCKiav

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:16 EST 2020

% Result     : Theorem 8.27s
% Output     : Refutation 8.27s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 460 expanded)
%              Number of leaves         :   36 ( 168 expanded)
%              Depth                    :   20
%              Number of atoms          : 1333 (4077 expanded)
%              Number of equality atoms :  140 ( 443 expanded)
%              Maximal formula depth    :   16 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t50_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t50_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('2',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = ( k5_xboole_0 @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('3',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k5_xboole_0 @ X7 @ ( k5_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('9',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('11',plain,(
    ! [X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','13'])).

thf('15',plain,
    ( sk_C
    = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['4','14'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,
    ( sk_C
    = ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('19',plain,(
    ! [X73: $i,X74: $i,X75: $i,X76: $i,X77: $i] :
      ( ( k4_enumset1 @ X73 @ X73 @ X74 @ X75 @ X76 @ X77 )
      = ( k3_enumset1 @ X73 @ X74 @ X75 @ X76 @ X77 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('20',plain,(
    ! [X69: $i,X70: $i,X71: $i,X72: $i] :
      ( ( k3_enumset1 @ X69 @ X69 @ X70 @ X71 @ X72 )
      = ( k2_enumset1 @ X69 @ X70 @ X71 @ X72 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('22',plain,(
    ! [X78: $i,X79: $i,X80: $i,X81: $i,X82: $i,X83: $i] :
      ( ( k5_enumset1 @ X78 @ X78 @ X79 @ X80 @ X81 @ X82 @ X83 )
      = ( k4_enumset1 @ X78 @ X79 @ X80 @ X81 @ X82 @ X83 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('23',plain,(
    ! [X63: $i] :
      ( ( k2_tarski @ X63 @ X63 )
      = ( k1_tarski @ X63 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t60_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ) )).

thf('24',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( k5_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 ) @ ( k2_tarski @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t60_enumset1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X69: $i,X70: $i,X71: $i,X72: $i] :
      ( ( k3_enumset1 @ X69 @ X69 @ X70 @ X71 @ X72 )
      = ( k2_enumset1 @ X69 @ X70 @ X71 @ X72 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X2 @ X2 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','28'])).

thf(t112_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ B @ D @ A @ C ) ) )).

thf('30',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k2_enumset1 @ X15 @ X13 @ X16 @ X14 )
      = ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t112_enumset1])).

thf('31',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k2_enumset1 @ X15 @ X13 @ X16 @ X14 )
      = ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t112_enumset1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('33',plain,(
    ! [X66: $i,X67: $i,X68: $i] :
      ( ( k2_enumset1 @ X66 @ X66 @ X67 @ X68 )
      = ( k1_enumset1 @ X66 @ X67 @ X68 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k2_enumset1 @ X15 @ X13 @ X16 @ X14 )
      = ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t112_enumset1])).

thf('36',plain,(
    ! [X66: $i,X67: $i,X68: $i] :
      ( ( k2_enumset1 @ X66 @ X66 @ X67 @ X68 )
      = ( k1_enumset1 @ X66 @ X67 @ X68 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X2 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','34','37'])).

thf('39',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k2_enumset1 @ X15 @ X13 @ X16 @ X14 )
      = ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t112_enumset1])).

thf('40',plain,(
    ! [X66: $i,X67: $i,X68: $i] :
      ( ( k2_enumset1 @ X66 @ X66 @ X67 @ X68 )
      = ( k1_enumset1 @ X66 @ X67 @ X68 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('43',plain,(
    ! [X63: $i] :
      ( ( k2_tarski @ X63 @ X63 )
      = ( k1_tarski @ X63 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t57_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k3_enumset1 @ C @ D @ E @ F @ G ) ) ) )).

thf('44',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k5_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23 )
      = ( k2_xboole_0 @ ( k2_tarski @ X17 @ X18 ) @ ( k3_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t57_enumset1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X0 @ X0 @ X5 @ X4 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X78: $i,X79: $i,X80: $i,X81: $i,X82: $i,X83: $i] :
      ( ( k5_enumset1 @ X78 @ X78 @ X79 @ X80 @ X81 @ X82 @ X83 )
      = ( k4_enumset1 @ X78 @ X79 @ X80 @ X81 @ X82 @ X83 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X0 @ X5 @ X4 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('49',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k5_xboole_0 @ X7 @ ( k5_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('50',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','13'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k1_tarski @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k1_tarski @ X3 ) @ ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','55'])).

thf('57',plain,(
    ! [X69: $i,X70: $i,X71: $i,X72: $i] :
      ( ( k3_enumset1 @ X69 @ X69 @ X70 @ X71 @ X72 )
      = ( k2_enumset1 @ X69 @ X70 @ X71 @ X72 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('58',plain,(
    ! [X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('59',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('62',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X69: $i,X70: $i,X71: $i,X72: $i] :
      ( ( k3_enumset1 @ X69 @ X69 @ X70 @ X71 @ X72 )
      = ( k2_enumset1 @ X69 @ X70 @ X71 @ X72 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['56','57','60','63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','65'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('67',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X0 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('70',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X0 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['68','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','74'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('76',plain,(
    ! [X64: $i,X65: $i] :
      ( ( k1_enumset1 @ X64 @ X64 @ X65 )
      = ( k2_tarski @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('79',plain,(
    ! [X66: $i,X67: $i,X68: $i] :
      ( ( k2_enumset1 @ X66 @ X66 @ X67 @ X68 )
      = ( k1_enumset1 @ X66 @ X67 @ X68 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X64: $i,X65: $i] :
      ( ( k1_enumset1 @ X64 @ X64 @ X65 )
      = ( k2_tarski @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('82',plain,(
    ! [X91: $i,X92: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X91 @ X92 ) )
      = ( k2_xboole_0 @ X91 @ X92 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k1_enumset1 @ X0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['80','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['77','84'])).

thf('86',plain,(
    ! [X91: $i,X92: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X91 @ X92 ) )
      = ( k2_xboole_0 @ X91 @ X92 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['18','87'])).

thf('89',plain,
    ( sk_C
    = ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('90',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('91',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_C )
    = ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('93',plain,
    ( sk_C
    = ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup+',[status(thm)],['88','93'])).

thf('95',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup+',[status(thm)],['88','93'])).

thf('96',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('97',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,
    ( k1_xboole_0
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['17','94','95','106'])).

thf('108',plain,(
    ! [X64: $i,X65: $i] :
      ( ( k1_enumset1 @ X64 @ X64 @ X65 )
      = ( k2_tarski @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('109',plain,(
    ! [X66: $i,X67: $i,X68: $i] :
      ( ( k2_enumset1 @ X66 @ X66 @ X67 @ X68 )
      = ( k1_enumset1 @ X66 @ X67 @ X68 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('110',plain,(
    ! [X69: $i,X70: $i,X71: $i,X72: $i] :
      ( ( k3_enumset1 @ X69 @ X69 @ X70 @ X71 @ X72 )
      = ( k2_enumset1 @ X69 @ X70 @ X71 @ X72 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('111',plain,(
    ! [X73: $i,X74: $i,X75: $i,X76: $i,X77: $i] :
      ( ( k4_enumset1 @ X73 @ X73 @ X74 @ X75 @ X76 @ X77 )
      = ( k3_enumset1 @ X73 @ X74 @ X75 @ X76 @ X77 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X0 @ X5 @ X4 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('113',plain,(
    ! [X93: $i,X94: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X93 ) @ X94 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['111','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['110','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['109','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['108','117'])).

thf('119',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['107','118'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.W0zaUCKiav
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:06:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 8.27/8.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 8.27/8.48  % Solved by: fo/fo7.sh
% 8.27/8.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.27/8.48  % done 6651 iterations in 8.022s
% 8.27/8.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 8.27/8.48  % SZS output start Refutation
% 8.27/8.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 8.27/8.48  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 8.27/8.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 8.27/8.48  thf(sk_A_type, type, sk_A: $i).
% 8.27/8.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 8.27/8.48  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 8.27/8.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 8.27/8.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 8.27/8.48  thf(sk_B_type, type, sk_B: $i).
% 8.27/8.48  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 8.27/8.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 8.27/8.48  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 8.27/8.48  thf(sk_C_type, type, sk_C: $i).
% 8.27/8.48  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 8.27/8.48  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 8.27/8.48  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 8.27/8.48  thf(t50_zfmisc_1, conjecture,
% 8.27/8.48    (![A:$i,B:$i,C:$i]:
% 8.27/8.48     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 8.27/8.48  thf(zf_stmt_0, negated_conjecture,
% 8.27/8.48    (~( ![A:$i,B:$i,C:$i]:
% 8.27/8.48        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) )),
% 8.27/8.48    inference('cnf.neg', [status(esa)], [t50_zfmisc_1])).
% 8.27/8.48  thf('0', plain,
% 8.27/8.48      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))),
% 8.27/8.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.27/8.48  thf(t95_xboole_1, axiom,
% 8.27/8.48    (![A:$i,B:$i]:
% 8.27/8.48     ( ( k3_xboole_0 @ A @ B ) =
% 8.27/8.48       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 8.27/8.48  thf('1', plain,
% 8.27/8.48      (![X11 : $i, X12 : $i]:
% 8.27/8.48         ((k3_xboole_0 @ X11 @ X12)
% 8.27/8.48           = (k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ 
% 8.27/8.48              (k2_xboole_0 @ X11 @ X12)))),
% 8.27/8.48      inference('cnf', [status(esa)], [t95_xboole_1])).
% 8.27/8.48  thf('2', plain,
% 8.27/8.48      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 8.27/8.48         = (k5_xboole_0 @ (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ 
% 8.27/8.48            k1_xboole_0))),
% 8.27/8.48      inference('sup+', [status(thm)], ['0', '1'])).
% 8.27/8.48  thf(t5_boole, axiom,
% 8.27/8.48    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 8.27/8.48  thf('3', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 8.27/8.48      inference('cnf', [status(esa)], [t5_boole])).
% 8.27/8.48  thf('4', plain,
% 8.27/8.48      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 8.27/8.48         = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 8.27/8.48      inference('demod', [status(thm)], ['2', '3'])).
% 8.27/8.48  thf(t92_xboole_1, axiom,
% 8.27/8.48    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 8.27/8.48  thf('5', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ X10) = (k1_xboole_0))),
% 8.27/8.48      inference('cnf', [status(esa)], [t92_xboole_1])).
% 8.27/8.48  thf(t91_xboole_1, axiom,
% 8.27/8.48    (![A:$i,B:$i,C:$i]:
% 8.27/8.48     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 8.27/8.48       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 8.27/8.48  thf('6', plain,
% 8.27/8.48      (![X7 : $i, X8 : $i, X9 : $i]:
% 8.27/8.48         ((k5_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ X9)
% 8.27/8.48           = (k5_xboole_0 @ X7 @ (k5_xboole_0 @ X8 @ X9)))),
% 8.27/8.48      inference('cnf', [status(esa)], [t91_xboole_1])).
% 8.27/8.48  thf('7', plain,
% 8.27/8.48      (![X0 : $i, X1 : $i]:
% 8.27/8.48         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 8.27/8.48           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 8.27/8.48      inference('sup+', [status(thm)], ['5', '6'])).
% 8.27/8.48  thf('8', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ X10) = (k1_xboole_0))),
% 8.27/8.48      inference('cnf', [status(esa)], [t92_xboole_1])).
% 8.27/8.48  thf('9', plain,
% 8.27/8.48      (![X11 : $i, X12 : $i]:
% 8.27/8.48         ((k3_xboole_0 @ X11 @ X12)
% 8.27/8.48           = (k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ 
% 8.27/8.48              (k2_xboole_0 @ X11 @ X12)))),
% 8.27/8.48      inference('cnf', [status(esa)], [t95_xboole_1])).
% 8.27/8.48  thf('10', plain,
% 8.27/8.48      (![X0 : $i]:
% 8.27/8.48         ((k3_xboole_0 @ X0 @ X0)
% 8.27/8.48           = (k5_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X0)))),
% 8.27/8.48      inference('sup+', [status(thm)], ['8', '9'])).
% 8.27/8.48  thf(idempotence_k3_xboole_0, axiom,
% 8.27/8.48    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 8.27/8.48  thf('11', plain, (![X1 : $i]: ((k3_xboole_0 @ X1 @ X1) = (X1))),
% 8.27/8.48      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 8.27/8.48  thf(idempotence_k2_xboole_0, axiom,
% 8.27/8.48    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 8.27/8.48  thf('12', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 8.27/8.48      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 8.27/8.48  thf('13', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 8.27/8.48      inference('demod', [status(thm)], ['10', '11', '12'])).
% 8.27/8.48  thf('14', plain,
% 8.27/8.48      (![X0 : $i, X1 : $i]:
% 8.27/8.48         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 8.27/8.48      inference('demod', [status(thm)], ['7', '13'])).
% 8.27/8.48  thf('15', plain,
% 8.27/8.48      (((sk_C)
% 8.27/8.48         = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 8.27/8.48            (k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 8.27/8.48      inference('sup+', [status(thm)], ['4', '14'])).
% 8.27/8.48  thf(t100_xboole_1, axiom,
% 8.27/8.48    (![A:$i,B:$i]:
% 8.27/8.48     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 8.27/8.48  thf('16', plain,
% 8.27/8.48      (![X2 : $i, X3 : $i]:
% 8.27/8.48         ((k4_xboole_0 @ X2 @ X3)
% 8.27/8.48           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 8.27/8.48      inference('cnf', [status(esa)], [t100_xboole_1])).
% 8.27/8.48  thf('17', plain,
% 8.27/8.48      (((sk_C) = (k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 8.27/8.48      inference('demod', [status(thm)], ['15', '16'])).
% 8.27/8.48  thf('18', plain,
% 8.27/8.48      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))),
% 8.27/8.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.27/8.48  thf(t73_enumset1, axiom,
% 8.27/8.48    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 8.27/8.48     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 8.27/8.48       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 8.27/8.48  thf('19', plain,
% 8.27/8.48      (![X73 : $i, X74 : $i, X75 : $i, X76 : $i, X77 : $i]:
% 8.27/8.48         ((k4_enumset1 @ X73 @ X73 @ X74 @ X75 @ X76 @ X77)
% 8.27/8.48           = (k3_enumset1 @ X73 @ X74 @ X75 @ X76 @ X77))),
% 8.27/8.48      inference('cnf', [status(esa)], [t73_enumset1])).
% 8.27/8.48  thf(t72_enumset1, axiom,
% 8.27/8.48    (![A:$i,B:$i,C:$i,D:$i]:
% 8.27/8.48     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 8.27/8.48  thf('20', plain,
% 8.27/8.48      (![X69 : $i, X70 : $i, X71 : $i, X72 : $i]:
% 8.27/8.48         ((k3_enumset1 @ X69 @ X69 @ X70 @ X71 @ X72)
% 8.27/8.48           = (k2_enumset1 @ X69 @ X70 @ X71 @ X72))),
% 8.27/8.48      inference('cnf', [status(esa)], [t72_enumset1])).
% 8.27/8.48  thf('21', plain,
% 8.27/8.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.27/8.48         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 8.27/8.48           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 8.27/8.48      inference('sup+', [status(thm)], ['19', '20'])).
% 8.27/8.48  thf(t74_enumset1, axiom,
% 8.27/8.48    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 8.27/8.48     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 8.27/8.48       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 8.27/8.48  thf('22', plain,
% 8.27/8.48      (![X78 : $i, X79 : $i, X80 : $i, X81 : $i, X82 : $i, X83 : $i]:
% 8.27/8.48         ((k5_enumset1 @ X78 @ X78 @ X79 @ X80 @ X81 @ X82 @ X83)
% 8.27/8.48           = (k4_enumset1 @ X78 @ X79 @ X80 @ X81 @ X82 @ X83))),
% 8.27/8.48      inference('cnf', [status(esa)], [t74_enumset1])).
% 8.27/8.48  thf(t69_enumset1, axiom,
% 8.27/8.48    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 8.27/8.48  thf('23', plain,
% 8.27/8.48      (![X63 : $i]: ((k2_tarski @ X63 @ X63) = (k1_tarski @ X63))),
% 8.27/8.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 8.27/8.48  thf(t60_enumset1, axiom,
% 8.27/8.48    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 8.27/8.48     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 8.27/8.48       ( k2_xboole_0 @
% 8.27/8.48         ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ))).
% 8.27/8.48  thf('24', plain,
% 8.27/8.48      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 8.27/8.48         ((k5_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30)
% 8.27/8.48           = (k2_xboole_0 @ (k3_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28) @ 
% 8.27/8.48              (k2_tarski @ X29 @ X30)))),
% 8.27/8.48      inference('cnf', [status(esa)], [t60_enumset1])).
% 8.27/8.48  thf('25', plain,
% 8.27/8.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 8.27/8.48         ((k5_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 8.27/8.48           = (k2_xboole_0 @ (k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 8.27/8.48              (k1_tarski @ X0)))),
% 8.27/8.48      inference('sup+', [status(thm)], ['23', '24'])).
% 8.27/8.48  thf('26', plain,
% 8.27/8.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 8.27/8.48         ((k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 8.27/8.48           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1) @ 
% 8.27/8.48              (k1_tarski @ X0)))),
% 8.27/8.48      inference('sup+', [status(thm)], ['22', '25'])).
% 8.27/8.48  thf('27', plain,
% 8.27/8.48      (![X69 : $i, X70 : $i, X71 : $i, X72 : $i]:
% 8.27/8.48         ((k3_enumset1 @ X69 @ X69 @ X70 @ X71 @ X72)
% 8.27/8.48           = (k2_enumset1 @ X69 @ X70 @ X71 @ X72))),
% 8.27/8.48      inference('cnf', [status(esa)], [t72_enumset1])).
% 8.27/8.48  thf('28', plain,
% 8.27/8.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 8.27/8.48         ((k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 8.27/8.48           = (k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ 
% 8.27/8.48              (k1_tarski @ X0)))),
% 8.27/8.48      inference('demod', [status(thm)], ['26', '27'])).
% 8.27/8.48  thf('29', plain,
% 8.27/8.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.27/8.48         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0)
% 8.27/8.48           = (k2_xboole_0 @ (k2_enumset1 @ X2 @ X2 @ X2 @ X1) @ 
% 8.27/8.48              (k1_tarski @ X0)))),
% 8.27/8.48      inference('sup+', [status(thm)], ['21', '28'])).
% 8.27/8.48  thf(t112_enumset1, axiom,
% 8.27/8.48    (![A:$i,B:$i,C:$i,D:$i]:
% 8.27/8.48     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ B @ D @ A @ C ) ))).
% 8.27/8.48  thf('30', plain,
% 8.27/8.48      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 8.27/8.48         ((k2_enumset1 @ X15 @ X13 @ X16 @ X14)
% 8.27/8.48           = (k2_enumset1 @ X13 @ X14 @ X15 @ X16))),
% 8.27/8.48      inference('cnf', [status(esa)], [t112_enumset1])).
% 8.27/8.48  thf('31', plain,
% 8.27/8.48      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 8.27/8.48         ((k2_enumset1 @ X15 @ X13 @ X16 @ X14)
% 8.27/8.48           = (k2_enumset1 @ X13 @ X14 @ X15 @ X16))),
% 8.27/8.48      inference('cnf', [status(esa)], [t112_enumset1])).
% 8.27/8.48  thf('32', plain,
% 8.27/8.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.27/8.48         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 8.27/8.48      inference('sup+', [status(thm)], ['30', '31'])).
% 8.27/8.48  thf(t71_enumset1, axiom,
% 8.27/8.48    (![A:$i,B:$i,C:$i]:
% 8.27/8.48     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 8.27/8.48  thf('33', plain,
% 8.27/8.48      (![X66 : $i, X67 : $i, X68 : $i]:
% 8.27/8.48         ((k2_enumset1 @ X66 @ X66 @ X67 @ X68)
% 8.27/8.48           = (k1_enumset1 @ X66 @ X67 @ X68))),
% 8.27/8.48      inference('cnf', [status(esa)], [t71_enumset1])).
% 8.27/8.48  thf('34', plain,
% 8.27/8.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.27/8.48         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 8.27/8.48      inference('sup+', [status(thm)], ['32', '33'])).
% 8.27/8.48  thf('35', plain,
% 8.27/8.48      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 8.27/8.48         ((k2_enumset1 @ X15 @ X13 @ X16 @ X14)
% 8.27/8.48           = (k2_enumset1 @ X13 @ X14 @ X15 @ X16))),
% 8.27/8.48      inference('cnf', [status(esa)], [t112_enumset1])).
% 8.27/8.48  thf('36', plain,
% 8.27/8.48      (![X66 : $i, X67 : $i, X68 : $i]:
% 8.27/8.48         ((k2_enumset1 @ X66 @ X66 @ X67 @ X68)
% 8.27/8.48           = (k1_enumset1 @ X66 @ X67 @ X68))),
% 8.27/8.48      inference('cnf', [status(esa)], [t71_enumset1])).
% 8.27/8.48  thf('37', plain,
% 8.27/8.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.27/8.48         ((k2_enumset1 @ X1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 8.27/8.48      inference('sup+', [status(thm)], ['35', '36'])).
% 8.27/8.48  thf('38', plain,
% 8.27/8.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.27/8.48         ((k1_enumset1 @ X0 @ X1 @ X2)
% 8.27/8.48           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X2) @ (k1_tarski @ X0)))),
% 8.27/8.48      inference('demod', [status(thm)], ['29', '34', '37'])).
% 8.27/8.48  thf('39', plain,
% 8.27/8.48      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 8.27/8.48         ((k2_enumset1 @ X15 @ X13 @ X16 @ X14)
% 8.27/8.48           = (k2_enumset1 @ X13 @ X14 @ X15 @ X16))),
% 8.27/8.48      inference('cnf', [status(esa)], [t112_enumset1])).
% 8.27/8.48  thf('40', plain,
% 8.27/8.48      (![X66 : $i, X67 : $i, X68 : $i]:
% 8.27/8.48         ((k2_enumset1 @ X66 @ X66 @ X67 @ X68)
% 8.27/8.48           = (k1_enumset1 @ X66 @ X67 @ X68))),
% 8.27/8.48      inference('cnf', [status(esa)], [t71_enumset1])).
% 8.27/8.48  thf('41', plain,
% 8.27/8.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.27/8.48         ((k2_enumset1 @ X2 @ X0 @ X1 @ X0) = (k1_enumset1 @ X0 @ X2 @ X1))),
% 8.27/8.48      inference('sup+', [status(thm)], ['39', '40'])).
% 8.27/8.48  thf('42', plain,
% 8.27/8.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.27/8.48         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 8.27/8.48           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 8.27/8.48      inference('sup+', [status(thm)], ['19', '20'])).
% 8.27/8.48  thf('43', plain,
% 8.27/8.48      (![X63 : $i]: ((k2_tarski @ X63 @ X63) = (k1_tarski @ X63))),
% 8.27/8.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 8.27/8.48  thf(t57_enumset1, axiom,
% 8.27/8.48    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 8.27/8.48     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 8.27/8.48       ( k2_xboole_0 @
% 8.27/8.48         ( k2_tarski @ A @ B ) @ ( k3_enumset1 @ C @ D @ E @ F @ G ) ) ))).
% 8.27/8.48  thf('44', plain,
% 8.27/8.48      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 8.27/8.48         ((k5_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23)
% 8.27/8.48           = (k2_xboole_0 @ (k2_tarski @ X17 @ X18) @ 
% 8.27/8.48              (k3_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23)))),
% 8.27/8.48      inference('cnf', [status(esa)], [t57_enumset1])).
% 8.27/8.48  thf('45', plain,
% 8.27/8.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 8.27/8.48         ((k5_enumset1 @ X0 @ X0 @ X5 @ X4 @ X3 @ X2 @ X1)
% 8.27/8.48           = (k2_xboole_0 @ (k1_tarski @ X0) @ 
% 8.27/8.48              (k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1)))),
% 8.27/8.48      inference('sup+', [status(thm)], ['43', '44'])).
% 8.27/8.48  thf('46', plain,
% 8.27/8.48      (![X78 : $i, X79 : $i, X80 : $i, X81 : $i, X82 : $i, X83 : $i]:
% 8.27/8.48         ((k5_enumset1 @ X78 @ X78 @ X79 @ X80 @ X81 @ X82 @ X83)
% 8.27/8.48           = (k4_enumset1 @ X78 @ X79 @ X80 @ X81 @ X82 @ X83))),
% 8.27/8.48      inference('cnf', [status(esa)], [t74_enumset1])).
% 8.27/8.48  thf('47', plain,
% 8.27/8.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 8.27/8.48         ((k4_enumset1 @ X0 @ X5 @ X4 @ X3 @ X2 @ X1)
% 8.27/8.48           = (k2_xboole_0 @ (k1_tarski @ X0) @ 
% 8.27/8.48              (k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1)))),
% 8.27/8.48      inference('demod', [status(thm)], ['45', '46'])).
% 8.27/8.48  thf('48', plain,
% 8.27/8.48      (![X11 : $i, X12 : $i]:
% 8.27/8.48         ((k3_xboole_0 @ X11 @ X12)
% 8.27/8.48           = (k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ 
% 8.27/8.48              (k2_xboole_0 @ X11 @ X12)))),
% 8.27/8.48      inference('cnf', [status(esa)], [t95_xboole_1])).
% 8.27/8.48  thf('49', plain,
% 8.27/8.48      (![X7 : $i, X8 : $i, X9 : $i]:
% 8.27/8.48         ((k5_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ X9)
% 8.27/8.48           = (k5_xboole_0 @ X7 @ (k5_xboole_0 @ X8 @ X9)))),
% 8.27/8.48      inference('cnf', [status(esa)], [t91_xboole_1])).
% 8.27/8.48  thf('50', plain,
% 8.27/8.48      (![X11 : $i, X12 : $i]:
% 8.27/8.48         ((k3_xboole_0 @ X11 @ X12)
% 8.27/8.48           = (k5_xboole_0 @ X11 @ 
% 8.27/8.48              (k5_xboole_0 @ X12 @ (k2_xboole_0 @ X11 @ X12))))),
% 8.27/8.48      inference('demod', [status(thm)], ['48', '49'])).
% 8.27/8.48  thf('51', plain,
% 8.27/8.48      (![X0 : $i, X1 : $i]:
% 8.27/8.48         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 8.27/8.48      inference('demod', [status(thm)], ['7', '13'])).
% 8.27/8.48  thf('52', plain,
% 8.27/8.48      (![X0 : $i, X1 : $i]:
% 8.27/8.48         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 8.27/8.48           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 8.27/8.48      inference('sup+', [status(thm)], ['50', '51'])).
% 8.27/8.48  thf('53', plain,
% 8.27/8.48      (![X2 : $i, X3 : $i]:
% 8.27/8.48         ((k4_xboole_0 @ X2 @ X3)
% 8.27/8.48           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 8.27/8.48      inference('cnf', [status(esa)], [t100_xboole_1])).
% 8.27/8.48  thf('54', plain,
% 8.27/8.48      (![X0 : $i, X1 : $i]:
% 8.27/8.48         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 8.27/8.48           = (k4_xboole_0 @ X1 @ X0))),
% 8.27/8.48      inference('demod', [status(thm)], ['52', '53'])).
% 8.27/8.48  thf('55', plain,
% 8.27/8.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 8.27/8.48         ((k5_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 8.27/8.48           (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 8.27/8.48           = (k4_xboole_0 @ (k1_tarski @ X5) @ 
% 8.27/8.48              (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 8.27/8.48      inference('sup+', [status(thm)], ['47', '54'])).
% 8.27/8.48  thf('56', plain,
% 8.27/8.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.27/8.48         ((k5_xboole_0 @ (k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0) @ 
% 8.27/8.48           (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 8.27/8.48           = (k4_xboole_0 @ (k1_tarski @ X3) @ 
% 8.27/8.48              (k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0)))),
% 8.27/8.48      inference('sup+', [status(thm)], ['42', '55'])).
% 8.27/8.48  thf('57', plain,
% 8.27/8.48      (![X69 : $i, X70 : $i, X71 : $i, X72 : $i]:
% 8.27/8.48         ((k3_enumset1 @ X69 @ X69 @ X70 @ X71 @ X72)
% 8.27/8.48           = (k2_enumset1 @ X69 @ X70 @ X71 @ X72))),
% 8.27/8.48      inference('cnf', [status(esa)], [t72_enumset1])).
% 8.27/8.48  thf('58', plain, (![X1 : $i]: ((k3_xboole_0 @ X1 @ X1) = (X1))),
% 8.27/8.48      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 8.27/8.48  thf('59', plain,
% 8.27/8.48      (![X2 : $i, X3 : $i]:
% 8.27/8.48         ((k4_xboole_0 @ X2 @ X3)
% 8.27/8.48           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 8.27/8.48      inference('cnf', [status(esa)], [t100_xboole_1])).
% 8.27/8.48  thf('60', plain,
% 8.27/8.48      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 8.27/8.48      inference('sup+', [status(thm)], ['58', '59'])).
% 8.27/8.48  thf('61', plain,
% 8.27/8.48      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 8.27/8.48      inference('sup+', [status(thm)], ['58', '59'])).
% 8.27/8.48  thf('62', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ X10) = (k1_xboole_0))),
% 8.27/8.48      inference('cnf', [status(esa)], [t92_xboole_1])).
% 8.27/8.48  thf('63', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 8.27/8.48      inference('sup+', [status(thm)], ['61', '62'])).
% 8.27/8.48  thf('64', plain,
% 8.27/8.48      (![X69 : $i, X70 : $i, X71 : $i, X72 : $i]:
% 8.27/8.48         ((k3_enumset1 @ X69 @ X69 @ X70 @ X71 @ X72)
% 8.27/8.48           = (k2_enumset1 @ X69 @ X70 @ X71 @ X72))),
% 8.27/8.48      inference('cnf', [status(esa)], [t72_enumset1])).
% 8.27/8.48  thf('65', plain,
% 8.27/8.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.27/8.48         ((k1_xboole_0)
% 8.27/8.48           = (k4_xboole_0 @ (k1_tarski @ X3) @ 
% 8.27/8.48              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 8.27/8.48      inference('demod', [status(thm)], ['56', '57', '60', '63', '64'])).
% 8.27/8.48  thf('66', plain,
% 8.27/8.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.27/8.48         ((k1_xboole_0)
% 8.27/8.48           = (k4_xboole_0 @ (k1_tarski @ X1) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 8.27/8.48      inference('sup+', [status(thm)], ['41', '65'])).
% 8.27/8.48  thf(t39_xboole_1, axiom,
% 8.27/8.48    (![A:$i,B:$i]:
% 8.27/8.48     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 8.27/8.48  thf('67', plain,
% 8.27/8.48      (![X4 : $i, X5 : $i]:
% 8.27/8.48         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 8.27/8.48           = (k2_xboole_0 @ X4 @ X5))),
% 8.27/8.48      inference('cnf', [status(esa)], [t39_xboole_1])).
% 8.27/8.48  thf('68', plain,
% 8.27/8.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.27/8.48         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X0 @ X1) @ k1_xboole_0)
% 8.27/8.48           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X0 @ X1) @ (k1_tarski @ X0)))),
% 8.27/8.48      inference('sup+', [status(thm)], ['66', '67'])).
% 8.27/8.48  thf('69', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 8.27/8.48      inference('sup+', [status(thm)], ['61', '62'])).
% 8.27/8.48  thf('70', plain,
% 8.27/8.48      (![X4 : $i, X5 : $i]:
% 8.27/8.48         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 8.27/8.48           = (k2_xboole_0 @ X4 @ X5))),
% 8.27/8.48      inference('cnf', [status(esa)], [t39_xboole_1])).
% 8.27/8.48  thf('71', plain,
% 8.27/8.48      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 8.27/8.48      inference('sup+', [status(thm)], ['69', '70'])).
% 8.27/8.48  thf('72', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 8.27/8.48      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 8.27/8.48  thf('73', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 8.27/8.48      inference('demod', [status(thm)], ['71', '72'])).
% 8.27/8.48  thf('74', plain,
% 8.27/8.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.27/8.48         ((k1_enumset1 @ X2 @ X0 @ X1)
% 8.27/8.48           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X0 @ X1) @ (k1_tarski @ X0)))),
% 8.27/8.48      inference('demod', [status(thm)], ['68', '73'])).
% 8.27/8.48  thf('75', plain,
% 8.27/8.48      (![X0 : $i, X1 : $i]:
% 8.27/8.48         ((k1_enumset1 @ X0 @ X1 @ X0) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 8.27/8.48      inference('sup+', [status(thm)], ['38', '74'])).
% 8.27/8.48  thf(t70_enumset1, axiom,
% 8.27/8.48    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 8.27/8.48  thf('76', plain,
% 8.27/8.48      (![X64 : $i, X65 : $i]:
% 8.27/8.48         ((k1_enumset1 @ X64 @ X64 @ X65) = (k2_tarski @ X64 @ X65))),
% 8.27/8.48      inference('cnf', [status(esa)], [t70_enumset1])).
% 8.27/8.48  thf('77', plain,
% 8.27/8.48      (![X0 : $i, X1 : $i]:
% 8.27/8.48         ((k1_enumset1 @ X0 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 8.27/8.48      inference('sup+', [status(thm)], ['75', '76'])).
% 8.27/8.48  thf('78', plain,
% 8.27/8.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.27/8.48         ((k2_enumset1 @ X2 @ X0 @ X1 @ X0) = (k1_enumset1 @ X0 @ X2 @ X1))),
% 8.27/8.48      inference('sup+', [status(thm)], ['39', '40'])).
% 8.27/8.48  thf('79', plain,
% 8.27/8.48      (![X66 : $i, X67 : $i, X68 : $i]:
% 8.27/8.48         ((k2_enumset1 @ X66 @ X66 @ X67 @ X68)
% 8.27/8.48           = (k1_enumset1 @ X66 @ X67 @ X68))),
% 8.27/8.48      inference('cnf', [status(esa)], [t71_enumset1])).
% 8.27/8.48  thf('80', plain,
% 8.27/8.48      (![X0 : $i, X1 : $i]:
% 8.27/8.48         ((k1_enumset1 @ X1 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X1))),
% 8.27/8.48      inference('sup+', [status(thm)], ['78', '79'])).
% 8.27/8.48  thf('81', plain,
% 8.27/8.48      (![X64 : $i, X65 : $i]:
% 8.27/8.48         ((k1_enumset1 @ X64 @ X64 @ X65) = (k2_tarski @ X64 @ X65))),
% 8.27/8.48      inference('cnf', [status(esa)], [t70_enumset1])).
% 8.27/8.48  thf(l51_zfmisc_1, axiom,
% 8.27/8.48    (![A:$i,B:$i]:
% 8.27/8.48     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 8.27/8.48  thf('82', plain,
% 8.27/8.48      (![X91 : $i, X92 : $i]:
% 8.27/8.48         ((k3_tarski @ (k2_tarski @ X91 @ X92)) = (k2_xboole_0 @ X91 @ X92))),
% 8.27/8.48      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 8.27/8.48  thf('83', plain,
% 8.27/8.48      (![X0 : $i, X1 : $i]:
% 8.27/8.48         ((k3_tarski @ (k1_enumset1 @ X1 @ X1 @ X0)) = (k2_xboole_0 @ X1 @ X0))),
% 8.27/8.48      inference('sup+', [status(thm)], ['81', '82'])).
% 8.27/8.48  thf('84', plain,
% 8.27/8.48      (![X0 : $i, X1 : $i]:
% 8.27/8.48         ((k3_tarski @ (k1_enumset1 @ X0 @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 8.27/8.48      inference('sup+', [status(thm)], ['80', '83'])).
% 8.27/8.48  thf('85', plain,
% 8.27/8.48      (![X0 : $i, X1 : $i]:
% 8.27/8.48         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 8.27/8.48      inference('sup+', [status(thm)], ['77', '84'])).
% 8.27/8.48  thf('86', plain,
% 8.27/8.48      (![X91 : $i, X92 : $i]:
% 8.27/8.48         ((k3_tarski @ (k2_tarski @ X91 @ X92)) = (k2_xboole_0 @ X91 @ X92))),
% 8.27/8.48      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 8.27/8.48  thf('87', plain,
% 8.27/8.48      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 8.27/8.48      inference('sup+', [status(thm)], ['85', '86'])).
% 8.27/8.48  thf('88', plain,
% 8.27/8.48      (((k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) = (k1_xboole_0))),
% 8.27/8.48      inference('demod', [status(thm)], ['18', '87'])).
% 8.27/8.48  thf('89', plain,
% 8.27/8.48      (((sk_C) = (k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 8.27/8.48      inference('demod', [status(thm)], ['15', '16'])).
% 8.27/8.48  thf('90', plain,
% 8.27/8.48      (![X4 : $i, X5 : $i]:
% 8.27/8.48         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 8.27/8.48           = (k2_xboole_0 @ X4 @ X5))),
% 8.27/8.48      inference('cnf', [status(esa)], [t39_xboole_1])).
% 8.27/8.48  thf('91', plain,
% 8.27/8.48      (((k2_xboole_0 @ sk_C @ sk_C)
% 8.27/8.48         = (k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 8.27/8.48      inference('sup+', [status(thm)], ['89', '90'])).
% 8.27/8.48  thf('92', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 8.27/8.48      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 8.27/8.48  thf('93', plain,
% 8.27/8.48      (((sk_C) = (k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 8.27/8.48      inference('demod', [status(thm)], ['91', '92'])).
% 8.27/8.48  thf('94', plain, (((sk_C) = (k1_xboole_0))),
% 8.27/8.48      inference('sup+', [status(thm)], ['88', '93'])).
% 8.27/8.48  thf('95', plain, (((sk_C) = (k1_xboole_0))),
% 8.27/8.48      inference('sup+', [status(thm)], ['88', '93'])).
% 8.27/8.48  thf('96', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 8.27/8.48      inference('demod', [status(thm)], ['10', '11', '12'])).
% 8.27/8.48  thf('97', plain,
% 8.27/8.48      (![X11 : $i, X12 : $i]:
% 8.27/8.48         ((k3_xboole_0 @ X11 @ X12)
% 8.27/8.48           = (k5_xboole_0 @ X11 @ 
% 8.27/8.48              (k5_xboole_0 @ X12 @ (k2_xboole_0 @ X11 @ X12))))),
% 8.27/8.48      inference('demod', [status(thm)], ['48', '49'])).
% 8.27/8.48  thf('98', plain,
% 8.27/8.48      (![X0 : $i]:
% 8.27/8.48         ((k3_xboole_0 @ X0 @ k1_xboole_0)
% 8.27/8.48           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 8.27/8.48      inference('sup+', [status(thm)], ['96', '97'])).
% 8.27/8.48  thf('99', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 8.27/8.48      inference('demod', [status(thm)], ['71', '72'])).
% 8.27/8.48  thf('100', plain,
% 8.27/8.48      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 8.27/8.48      inference('demod', [status(thm)], ['98', '99'])).
% 8.27/8.48  thf('101', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ X10) = (k1_xboole_0))),
% 8.27/8.48      inference('cnf', [status(esa)], [t92_xboole_1])).
% 8.27/8.48  thf('102', plain,
% 8.27/8.48      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 8.27/8.48      inference('sup+', [status(thm)], ['100', '101'])).
% 8.27/8.48  thf('103', plain,
% 8.27/8.48      (![X2 : $i, X3 : $i]:
% 8.27/8.48         ((k4_xboole_0 @ X2 @ X3)
% 8.27/8.48           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 8.27/8.48      inference('cnf', [status(esa)], [t100_xboole_1])).
% 8.27/8.48  thf('104', plain,
% 8.27/8.48      (![X0 : $i]:
% 8.27/8.48         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 8.27/8.48      inference('sup+', [status(thm)], ['102', '103'])).
% 8.27/8.48  thf('105', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 8.27/8.48      inference('cnf', [status(esa)], [t5_boole])).
% 8.27/8.48  thf('106', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 8.27/8.48      inference('sup+', [status(thm)], ['104', '105'])).
% 8.27/8.48  thf('107', plain, (((k1_xboole_0) = (k2_tarski @ sk_A @ sk_B))),
% 8.27/8.48      inference('demod', [status(thm)], ['17', '94', '95', '106'])).
% 8.27/8.48  thf('108', plain,
% 8.27/8.48      (![X64 : $i, X65 : $i]:
% 8.27/8.48         ((k1_enumset1 @ X64 @ X64 @ X65) = (k2_tarski @ X64 @ X65))),
% 8.27/8.48      inference('cnf', [status(esa)], [t70_enumset1])).
% 8.27/8.48  thf('109', plain,
% 8.27/8.48      (![X66 : $i, X67 : $i, X68 : $i]:
% 8.27/8.48         ((k2_enumset1 @ X66 @ X66 @ X67 @ X68)
% 8.27/8.48           = (k1_enumset1 @ X66 @ X67 @ X68))),
% 8.27/8.48      inference('cnf', [status(esa)], [t71_enumset1])).
% 8.27/8.48  thf('110', plain,
% 8.27/8.48      (![X69 : $i, X70 : $i, X71 : $i, X72 : $i]:
% 8.27/8.48         ((k3_enumset1 @ X69 @ X69 @ X70 @ X71 @ X72)
% 8.27/8.48           = (k2_enumset1 @ X69 @ X70 @ X71 @ X72))),
% 8.27/8.48      inference('cnf', [status(esa)], [t72_enumset1])).
% 8.27/8.48  thf('111', plain,
% 8.27/8.48      (![X73 : $i, X74 : $i, X75 : $i, X76 : $i, X77 : $i]:
% 8.27/8.48         ((k4_enumset1 @ X73 @ X73 @ X74 @ X75 @ X76 @ X77)
% 8.27/8.48           = (k3_enumset1 @ X73 @ X74 @ X75 @ X76 @ X77))),
% 8.27/8.48      inference('cnf', [status(esa)], [t73_enumset1])).
% 8.27/8.48  thf('112', plain,
% 8.27/8.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 8.27/8.48         ((k4_enumset1 @ X0 @ X5 @ X4 @ X3 @ X2 @ X1)
% 8.27/8.48           = (k2_xboole_0 @ (k1_tarski @ X0) @ 
% 8.27/8.48              (k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1)))),
% 8.27/8.48      inference('demod', [status(thm)], ['45', '46'])).
% 8.27/8.48  thf(t49_zfmisc_1, axiom,
% 8.27/8.48    (![A:$i,B:$i]:
% 8.27/8.48     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 8.27/8.48  thf('113', plain,
% 8.27/8.48      (![X93 : $i, X94 : $i]:
% 8.27/8.48         ((k2_xboole_0 @ (k1_tarski @ X93) @ X94) != (k1_xboole_0))),
% 8.27/8.48      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 8.27/8.48  thf('114', plain,
% 8.27/8.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 8.27/8.48         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) != (k1_xboole_0))),
% 8.27/8.48      inference('sup-', [status(thm)], ['112', '113'])).
% 8.27/8.48  thf('115', plain,
% 8.27/8.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 8.27/8.48         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) != (k1_xboole_0))),
% 8.27/8.48      inference('sup-', [status(thm)], ['111', '114'])).
% 8.27/8.48  thf('116', plain,
% 8.27/8.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.27/8.48         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) != (k1_xboole_0))),
% 8.27/8.48      inference('sup-', [status(thm)], ['110', '115'])).
% 8.27/8.48  thf('117', plain,
% 8.27/8.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.27/8.48         ((k1_enumset1 @ X2 @ X1 @ X0) != (k1_xboole_0))),
% 8.27/8.48      inference('sup-', [status(thm)], ['109', '116'])).
% 8.27/8.48  thf('118', plain,
% 8.27/8.48      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) != (k1_xboole_0))),
% 8.27/8.48      inference('sup-', [status(thm)], ['108', '117'])).
% 8.27/8.48  thf('119', plain, ($false),
% 8.27/8.48      inference('simplify_reflect-', [status(thm)], ['107', '118'])).
% 8.27/8.48  
% 8.27/8.48  % SZS output end Refutation
% 8.27/8.48  
% 8.33/8.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

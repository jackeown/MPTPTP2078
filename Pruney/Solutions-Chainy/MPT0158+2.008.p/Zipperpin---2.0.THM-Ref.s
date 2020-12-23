%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.84GToIJ7MJ

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:36 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 223 expanded)
%              Number of leaves         :   21 (  83 expanded)
%              Depth                    :   16
%              Number of atoms          : 1160 (2943 expanded)
%              Number of equality atoms :   77 ( 209 expanded)
%              Maximal formula depth    :   16 (  11 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(t74_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
        ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
        = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) ),
    inference('cnf.neg',[status(esa)],[t74_enumset1])).

thf('0',plain,(
    ( k5_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F )
 != ( k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('1',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k3_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28 )
      = ( k2_enumset1 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k2_enumset1 @ X22 @ X22 @ X23 @ X24 )
      = ( k1_enumset1 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k2_enumset1 @ X22 @ X22 @ X23 @ X24 )
      = ( k1_enumset1 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(l68_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_enumset1 @ E @ F @ G ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) @ ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l68_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X2 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_enumset1 @ X5 @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X5 @ X4 @ X3 ) @ ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k3_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28 )
      = ( k2_enumset1 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t58_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_enumset1 @ D @ E @ F @ G ) ) ) )).

thf('9',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k5_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X13 @ X14 @ X15 ) @ ( k2_enumset1 @ X16 @ X17 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t58_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X6 @ X5 @ X4 ) @ ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k5_enumset1 @ X5 @ X4 @ X3 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,(
    ( k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_D @ sk_E @ sk_F )
 != ( k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['0','11'])).

thf('13',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k3_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28 )
      = ( k2_enumset1 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('14',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k2_enumset1 @ X22 @ X22 @ X23 @ X24 )
      = ( k1_enumset1 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_enumset1 @ X20 @ X20 @ X21 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('16',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k5_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X13 @ X14 @ X15 ) @ ( k2_enumset1 @ X16 @ X17 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t58_enumset1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X1 @ X1 @ X0 @ X5 @ X4 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_enumset1 @ X20 @ X20 @ X21 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) @ ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l68_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t54_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_tarski @ E @ F ) ) ) )).

thf('21',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k4_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X7 @ X8 @ X9 @ X10 ) @ ( k2_tarski @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t54_enumset1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('23',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( k4_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 @ X33 )
      = ( k3_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 ) )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
      = ( k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','25'])).

thf('27',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_enumset1 @ X20 @ X20 @ X21 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_enumset1 @ X20 @ X20 @ X21 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('30',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k2_enumset1 @ X22 @ X22 @ X23 @ X24 )
      = ( k1_enumset1 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('31',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k4_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X7 @ X8 @ X9 @ X10 ) @ ( k2_tarski @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t54_enumset1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X2 @ X2 @ X1 @ X0 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( k4_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 @ X33 )
      = ( k3_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X2 @ X1 @ X0 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X4 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k3_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28 )
      = ( k2_enumset1 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','38'])).

thf('40',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k2_enumset1 @ X22 @ X22 @ X23 @ X24 )
      = ( k1_enumset1 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) @ ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l68_enumset1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X6 @ X5 @ X4 @ X3 ) @ ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X2 @ X1 @ X1 @ X0 @ X5 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k3_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X6 @ X5 @ X4 ) @ ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X2 @ X1 @ X1 @ X0 @ X5 @ X4 @ X3 )
      = ( k5_enumset1 @ X2 @ X1 @ X0 @ X5 @ X5 @ X4 @ X3 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','37'])).

thf('49',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k3_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28 )
      = ( k2_enumset1 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) @ ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l68_enumset1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X3 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_enumset1 @ X6 @ X5 @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X2 @ X1 @ X1 @ X0 @ X5 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) @ ( k1_enumset1 @ X5 @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k2_enumset1 @ X22 @ X22 @ X23 @ X24 )
      = ( k1_enumset1 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X2 @ X1 @ X1 @ X0 @ X5 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_enumset1 @ X5 @ X4 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X1 @ X1 @ X0 @ X5 @ X4 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X2 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_enumset1 @ X5 @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X2 @ X1 @ X1 @ X0 @ X5 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_enumset1 @ X0 @ X5 @ X4 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('60',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k5_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X13 @ X14 @ X15 ) @ ( k2_enumset1 @ X16 @ X17 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t58_enumset1])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X2 @ X1 @ X1 @ X0 @ X5 @ X4 @ X3 )
      = ( k4_enumset1 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3 ) ) ),
    inference(demod,[status(thm)],['58','65'])).

thf('67',plain,(
    ( k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F )
 != ( k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['12','47','66'])).

thf('68',plain,(
    $false ),
    inference(simplify,[status(thm)],['67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.84GToIJ7MJ
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:47:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.58/0.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.76  % Solved by: fo/fo7.sh
% 0.58/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.76  % done 638 iterations in 0.301s
% 0.58/0.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.76  % SZS output start Refutation
% 0.58/0.76  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.58/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.76  thf(sk_C_type, type, sk_C: $i).
% 0.58/0.76  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.58/0.76  thf(sk_D_type, type, sk_D: $i).
% 0.58/0.76  thf(sk_E_type, type, sk_E: $i).
% 0.58/0.76  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.58/0.76  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.58/0.76  thf(sk_F_type, type, sk_F: $i).
% 0.58/0.76  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.58/0.76  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.58/0.76  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.58/0.76  thf(t74_enumset1, conjecture,
% 0.58/0.76    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.58/0.76     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.58/0.76       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.58/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.76    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.58/0.76        ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.58/0.76          ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )),
% 0.58/0.76    inference('cnf.neg', [status(esa)], [t74_enumset1])).
% 0.58/0.76  thf('0', plain,
% 0.58/0.76      (((k5_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)
% 0.58/0.76         != (k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf(t72_enumset1, axiom,
% 0.58/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.76     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.58/0.76  thf('1', plain,
% 0.58/0.76      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.58/0.76         ((k3_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28)
% 0.58/0.76           = (k2_enumset1 @ X25 @ X26 @ X27 @ X28))),
% 0.58/0.76      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.58/0.76  thf(t71_enumset1, axiom,
% 0.58/0.76    (![A:$i,B:$i,C:$i]:
% 0.58/0.76     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.58/0.76  thf('2', plain,
% 0.58/0.76      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.58/0.76         ((k2_enumset1 @ X22 @ X22 @ X23 @ X24)
% 0.58/0.76           = (k1_enumset1 @ X22 @ X23 @ X24))),
% 0.58/0.76      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.58/0.76  thf('3', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.76         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.58/0.76      inference('sup+', [status(thm)], ['1', '2'])).
% 0.58/0.76  thf('4', plain,
% 0.58/0.76      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.58/0.76         ((k2_enumset1 @ X22 @ X22 @ X23 @ X24)
% 0.58/0.76           = (k1_enumset1 @ X22 @ X23 @ X24))),
% 0.58/0.76      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.58/0.76  thf(l68_enumset1, axiom,
% 0.58/0.76    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.58/0.76     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.58/0.76       ( k2_xboole_0 @
% 0.58/0.76         ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_enumset1 @ E @ F @ G ) ) ))).
% 0.58/0.76  thf('5', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.58/0.76         ((k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6)
% 0.58/0.76           = (k2_xboole_0 @ (k2_enumset1 @ X0 @ X1 @ X2 @ X3) @ 
% 0.58/0.76              (k1_enumset1 @ X4 @ X5 @ X6)))),
% 0.58/0.76      inference('cnf', [status(esa)], [l68_enumset1])).
% 0.58/0.76  thf('6', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.58/0.76         ((k5_enumset1 @ X2 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3)
% 0.58/0.76           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 0.58/0.76              (k1_enumset1 @ X5 @ X4 @ X3)))),
% 0.58/0.76      inference('sup+', [status(thm)], ['4', '5'])).
% 0.58/0.76  thf('7', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.58/0.76         ((k5_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.58/0.76           = (k2_xboole_0 @ (k1_enumset1 @ X5 @ X4 @ X3) @ 
% 0.58/0.76              (k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0)))),
% 0.58/0.76      inference('sup+', [status(thm)], ['3', '6'])).
% 0.58/0.76  thf('8', plain,
% 0.58/0.76      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.58/0.76         ((k3_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28)
% 0.58/0.76           = (k2_enumset1 @ X25 @ X26 @ X27 @ X28))),
% 0.58/0.76      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.58/0.76  thf(t58_enumset1, axiom,
% 0.58/0.76    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.58/0.76     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.58/0.76       ( k2_xboole_0 @
% 0.58/0.76         ( k1_enumset1 @ A @ B @ C ) @ ( k2_enumset1 @ D @ E @ F @ G ) ) ))).
% 0.58/0.76  thf('9', plain,
% 0.58/0.76      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.58/0.76         ((k5_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19)
% 0.58/0.76           = (k2_xboole_0 @ (k1_enumset1 @ X13 @ X14 @ X15) @ 
% 0.58/0.76              (k2_enumset1 @ X16 @ X17 @ X18 @ X19)))),
% 0.58/0.76      inference('cnf', [status(esa)], [t58_enumset1])).
% 0.58/0.76  thf('10', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.58/0.76         ((k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.58/0.76           = (k2_xboole_0 @ (k1_enumset1 @ X6 @ X5 @ X4) @ 
% 0.58/0.76              (k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0)))),
% 0.58/0.76      inference('sup+', [status(thm)], ['8', '9'])).
% 0.58/0.76  thf('11', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.58/0.76         ((k5_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.58/0.76           = (k5_enumset1 @ X5 @ X4 @ X3 @ X2 @ X2 @ X1 @ X0))),
% 0.58/0.76      inference('demod', [status(thm)], ['7', '10'])).
% 0.58/0.76  thf('12', plain,
% 0.58/0.76      (((k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_D @ sk_E @ sk_F)
% 0.58/0.76         != (k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))),
% 0.58/0.76      inference('demod', [status(thm)], ['0', '11'])).
% 0.58/0.76  thf('13', plain,
% 0.58/0.76      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.58/0.76         ((k3_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28)
% 0.58/0.76           = (k2_enumset1 @ X25 @ X26 @ X27 @ X28))),
% 0.58/0.76      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.58/0.76  thf('14', plain,
% 0.58/0.76      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.58/0.76         ((k2_enumset1 @ X22 @ X22 @ X23 @ X24)
% 0.58/0.76           = (k1_enumset1 @ X22 @ X23 @ X24))),
% 0.58/0.76      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.58/0.76  thf(t70_enumset1, axiom,
% 0.58/0.76    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.58/0.76  thf('15', plain,
% 0.58/0.76      (![X20 : $i, X21 : $i]:
% 0.58/0.76         ((k1_enumset1 @ X20 @ X20 @ X21) = (k2_tarski @ X20 @ X21))),
% 0.58/0.76      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.58/0.76  thf('16', plain,
% 0.58/0.76      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.58/0.76         ((k5_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19)
% 0.58/0.76           = (k2_xboole_0 @ (k1_enumset1 @ X13 @ X14 @ X15) @ 
% 0.58/0.76              (k2_enumset1 @ X16 @ X17 @ X18 @ X19)))),
% 0.58/0.76      inference('cnf', [status(esa)], [t58_enumset1])).
% 0.58/0.76  thf('17', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.58/0.76         ((k5_enumset1 @ X1 @ X1 @ X0 @ X5 @ X4 @ X3 @ X2)
% 0.58/0.76           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 0.58/0.76              (k2_enumset1 @ X5 @ X4 @ X3 @ X2)))),
% 0.58/0.76      inference('sup+', [status(thm)], ['15', '16'])).
% 0.58/0.76  thf('18', plain,
% 0.58/0.76      (![X20 : $i, X21 : $i]:
% 0.58/0.76         ((k1_enumset1 @ X20 @ X20 @ X21) = (k2_tarski @ X20 @ X21))),
% 0.58/0.76      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.58/0.76  thf('19', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.58/0.76         ((k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6)
% 0.58/0.76           = (k2_xboole_0 @ (k2_enumset1 @ X0 @ X1 @ X2 @ X3) @ 
% 0.58/0.76              (k1_enumset1 @ X4 @ X5 @ X6)))),
% 0.58/0.76      inference('cnf', [status(esa)], [l68_enumset1])).
% 0.58/0.76  thf('20', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.58/0.76         ((k5_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X1 @ X0)
% 0.58/0.76           = (k2_xboole_0 @ (k2_enumset1 @ X5 @ X4 @ X3 @ X2) @ 
% 0.58/0.76              (k2_tarski @ X1 @ X0)))),
% 0.58/0.76      inference('sup+', [status(thm)], ['18', '19'])).
% 0.58/0.76  thf(t54_enumset1, axiom,
% 0.58/0.76    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.58/0.76     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.58/0.76       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_tarski @ E @ F ) ) ))).
% 0.58/0.76  thf('21', plain,
% 0.58/0.76      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.58/0.76         ((k4_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12)
% 0.58/0.76           = (k2_xboole_0 @ (k2_enumset1 @ X7 @ X8 @ X9 @ X10) @ 
% 0.58/0.76              (k2_tarski @ X11 @ X12)))),
% 0.58/0.76      inference('cnf', [status(esa)], [t54_enumset1])).
% 0.58/0.76  thf('22', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.58/0.76         ((k5_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X1 @ X0)
% 0.58/0.76           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.58/0.76      inference('demod', [status(thm)], ['20', '21'])).
% 0.58/0.76  thf(t73_enumset1, axiom,
% 0.58/0.76    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.58/0.76     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.58/0.76       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.58/0.76  thf('23', plain,
% 0.58/0.76      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.58/0.76         ((k4_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 @ X33)
% 0.58/0.76           = (k3_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33))),
% 0.58/0.76      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.58/0.76  thf('24', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.58/0.76         ((k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X1 @ X0)
% 0.58/0.76           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.58/0.76      inference('sup+', [status(thm)], ['22', '23'])).
% 0.58/0.76  thf('25', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.58/0.76         ((k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ 
% 0.58/0.76           (k2_enumset1 @ X2 @ X1 @ X1 @ X0))
% 0.58/0.76           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.58/0.76      inference('sup+', [status(thm)], ['17', '24'])).
% 0.58/0.76  thf('26', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.58/0.76         ((k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k1_enumset1 @ X1 @ X1 @ X0))
% 0.58/0.76           = (k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0))),
% 0.58/0.76      inference('sup+', [status(thm)], ['14', '25'])).
% 0.58/0.76  thf('27', plain,
% 0.58/0.76      (![X20 : $i, X21 : $i]:
% 0.58/0.76         ((k1_enumset1 @ X20 @ X20 @ X21) = (k2_tarski @ X20 @ X21))),
% 0.58/0.76      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.58/0.76  thf('28', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.58/0.76         ((k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0))
% 0.58/0.76           = (k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0))),
% 0.58/0.76      inference('demod', [status(thm)], ['26', '27'])).
% 0.58/0.76  thf('29', plain,
% 0.58/0.76      (![X20 : $i, X21 : $i]:
% 0.58/0.76         ((k1_enumset1 @ X20 @ X20 @ X21) = (k2_tarski @ X20 @ X21))),
% 0.58/0.76      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.58/0.76  thf('30', plain,
% 0.58/0.76      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.58/0.76         ((k2_enumset1 @ X22 @ X22 @ X23 @ X24)
% 0.58/0.76           = (k1_enumset1 @ X22 @ X23 @ X24))),
% 0.58/0.76      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.58/0.76  thf('31', plain,
% 0.58/0.76      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.58/0.76         ((k4_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12)
% 0.58/0.76           = (k2_xboole_0 @ (k2_enumset1 @ X7 @ X8 @ X9 @ X10) @ 
% 0.58/0.76              (k2_tarski @ X11 @ X12)))),
% 0.58/0.76      inference('cnf', [status(esa)], [t54_enumset1])).
% 0.58/0.76  thf('32', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.58/0.76         ((k4_enumset1 @ X2 @ X2 @ X1 @ X0 @ X4 @ X3)
% 0.58/0.76           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 0.58/0.76              (k2_tarski @ X4 @ X3)))),
% 0.58/0.76      inference('sup+', [status(thm)], ['30', '31'])).
% 0.58/0.76  thf('33', plain,
% 0.58/0.76      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.58/0.76         ((k4_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 @ X33)
% 0.58/0.76           = (k3_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33))),
% 0.58/0.76      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.58/0.76  thf('34', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.58/0.76         ((k3_enumset1 @ X2 @ X1 @ X0 @ X4 @ X3)
% 0.58/0.76           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 0.58/0.76              (k2_tarski @ X4 @ X3)))),
% 0.58/0.76      inference('demod', [status(thm)], ['32', '33'])).
% 0.58/0.76  thf('35', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.58/0.76         ((k3_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2)
% 0.58/0.76           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 0.58/0.76      inference('sup+', [status(thm)], ['29', '34'])).
% 0.58/0.76  thf('36', plain,
% 0.58/0.76      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.58/0.76         ((k3_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28)
% 0.58/0.76           = (k2_enumset1 @ X25 @ X26 @ X27 @ X28))),
% 0.58/0.76      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.58/0.76  thf('37', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.58/0.76         ((k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0))
% 0.58/0.76           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.58/0.76      inference('sup+', [status(thm)], ['35', '36'])).
% 0.58/0.76  thf('38', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.58/0.76         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 0.58/0.76           = (k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0))),
% 0.58/0.76      inference('demod', [status(thm)], ['28', '37'])).
% 0.58/0.76  thf('39', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.76         ((k2_enumset1 @ X2 @ X2 @ X1 @ X0) = (k2_enumset1 @ X2 @ X1 @ X1 @ X0))),
% 0.58/0.76      inference('sup+', [status(thm)], ['13', '38'])).
% 0.58/0.76  thf('40', plain,
% 0.58/0.76      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.58/0.76         ((k2_enumset1 @ X22 @ X22 @ X23 @ X24)
% 0.58/0.76           = (k1_enumset1 @ X22 @ X23 @ X24))),
% 0.58/0.76      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.58/0.76  thf('41', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.76         ((k1_enumset1 @ X2 @ X1 @ X0) = (k2_enumset1 @ X2 @ X1 @ X1 @ X0))),
% 0.58/0.76      inference('demod', [status(thm)], ['39', '40'])).
% 0.58/0.76  thf('42', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.76         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.58/0.76      inference('sup+', [status(thm)], ['1', '2'])).
% 0.58/0.76  thf('43', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.58/0.76         ((k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6)
% 0.58/0.76           = (k2_xboole_0 @ (k2_enumset1 @ X0 @ X1 @ X2 @ X3) @ 
% 0.58/0.76              (k1_enumset1 @ X4 @ X5 @ X6)))),
% 0.58/0.76      inference('cnf', [status(esa)], [l68_enumset1])).
% 0.58/0.76  thf('44', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.58/0.76         ((k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.58/0.76           = (k2_xboole_0 @ (k2_enumset1 @ X6 @ X5 @ X4 @ X3) @ 
% 0.58/0.76              (k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0)))),
% 0.58/0.76      inference('sup+', [status(thm)], ['42', '43'])).
% 0.58/0.76  thf('45', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.58/0.76         ((k5_enumset1 @ X2 @ X1 @ X1 @ X0 @ X5 @ X4 @ X3)
% 0.58/0.76           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 0.58/0.76              (k3_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3)))),
% 0.58/0.76      inference('sup+', [status(thm)], ['41', '44'])).
% 0.58/0.76  thf('46', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.58/0.76         ((k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.58/0.76           = (k2_xboole_0 @ (k1_enumset1 @ X6 @ X5 @ X4) @ 
% 0.58/0.76              (k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0)))),
% 0.58/0.76      inference('sup+', [status(thm)], ['8', '9'])).
% 0.58/0.76  thf('47', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.58/0.76         ((k5_enumset1 @ X2 @ X1 @ X1 @ X0 @ X5 @ X4 @ X3)
% 0.58/0.76           = (k5_enumset1 @ X2 @ X1 @ X0 @ X5 @ X5 @ X4 @ X3))),
% 0.58/0.76      inference('demod', [status(thm)], ['45', '46'])).
% 0.58/0.76  thf('48', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.58/0.76         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 0.58/0.76           = (k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0))),
% 0.58/0.76      inference('demod', [status(thm)], ['28', '37'])).
% 0.58/0.76  thf('49', plain,
% 0.58/0.76      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.58/0.76         ((k3_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28)
% 0.58/0.76           = (k2_enumset1 @ X25 @ X26 @ X27 @ X28))),
% 0.58/0.76      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.58/0.76  thf('50', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.58/0.76         ((k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6)
% 0.58/0.76           = (k2_xboole_0 @ (k2_enumset1 @ X0 @ X1 @ X2 @ X3) @ 
% 0.58/0.76              (k1_enumset1 @ X4 @ X5 @ X6)))),
% 0.58/0.76      inference('cnf', [status(esa)], [l68_enumset1])).
% 0.58/0.76  thf('51', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.58/0.76         ((k5_enumset1 @ X3 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4)
% 0.58/0.76           = (k2_xboole_0 @ (k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0) @ 
% 0.58/0.76              (k1_enumset1 @ X6 @ X5 @ X4)))),
% 0.58/0.76      inference('sup+', [status(thm)], ['49', '50'])).
% 0.58/0.76  thf('52', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.58/0.76         ((k5_enumset1 @ X2 @ X1 @ X1 @ X0 @ X5 @ X4 @ X3)
% 0.58/0.76           = (k2_xboole_0 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0) @ 
% 0.58/0.76              (k1_enumset1 @ X5 @ X4 @ X3)))),
% 0.58/0.76      inference('sup+', [status(thm)], ['48', '51'])).
% 0.58/0.76  thf('53', plain,
% 0.58/0.76      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.58/0.76         ((k2_enumset1 @ X22 @ X22 @ X23 @ X24)
% 0.58/0.76           = (k1_enumset1 @ X22 @ X23 @ X24))),
% 0.58/0.76      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.58/0.76  thf('54', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.58/0.76         ((k5_enumset1 @ X2 @ X1 @ X1 @ X0 @ X5 @ X4 @ X3)
% 0.58/0.76           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 0.58/0.76              (k1_enumset1 @ X5 @ X4 @ X3)))),
% 0.58/0.76      inference('demod', [status(thm)], ['52', '53'])).
% 0.58/0.76  thf('55', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.58/0.76         ((k5_enumset1 @ X1 @ X1 @ X0 @ X5 @ X4 @ X3 @ X2)
% 0.58/0.76           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 0.58/0.76              (k2_enumset1 @ X5 @ X4 @ X3 @ X2)))),
% 0.58/0.76      inference('sup+', [status(thm)], ['15', '16'])).
% 0.58/0.76  thf('56', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.58/0.76         ((k5_enumset1 @ X2 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3)
% 0.58/0.76           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 0.58/0.76              (k1_enumset1 @ X5 @ X4 @ X3)))),
% 0.58/0.76      inference('sup+', [status(thm)], ['4', '5'])).
% 0.58/0.76  thf('57', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.58/0.76         ((k2_xboole_0 @ (k2_tarski @ X5 @ X4) @ 
% 0.58/0.76           (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.58/0.76           = (k2_xboole_0 @ (k1_enumset1 @ X5 @ X4 @ X3) @ 
% 0.58/0.76              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.58/0.76      inference('sup+', [status(thm)], ['55', '56'])).
% 0.58/0.76  thf('58', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.58/0.76         ((k5_enumset1 @ X2 @ X1 @ X1 @ X0 @ X5 @ X4 @ X3)
% 0.58/0.76           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ 
% 0.58/0.76              (k2_enumset1 @ X0 @ X5 @ X4 @ X3)))),
% 0.58/0.76      inference('demod', [status(thm)], ['54', '57'])).
% 0.58/0.76  thf('59', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.76         ((k1_enumset1 @ X2 @ X1 @ X0) = (k2_enumset1 @ X2 @ X1 @ X1 @ X0))),
% 0.58/0.76      inference('demod', [status(thm)], ['39', '40'])).
% 0.58/0.76  thf('60', plain,
% 0.58/0.76      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.58/0.76         ((k5_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19)
% 0.58/0.76           = (k2_xboole_0 @ (k1_enumset1 @ X13 @ X14 @ X15) @ 
% 0.58/0.76              (k2_enumset1 @ X16 @ X17 @ X18 @ X19)))),
% 0.58/0.76      inference('cnf', [status(esa)], [t58_enumset1])).
% 0.58/0.76  thf('61', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.58/0.76         ((k5_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X1 @ X0)
% 0.58/0.76           = (k2_xboole_0 @ (k1_enumset1 @ X5 @ X4 @ X3) @ 
% 0.58/0.76              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.58/0.76      inference('sup+', [status(thm)], ['59', '60'])).
% 0.58/0.76  thf('62', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.58/0.76         ((k2_xboole_0 @ (k2_tarski @ X5 @ X4) @ 
% 0.58/0.76           (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.58/0.76           = (k2_xboole_0 @ (k1_enumset1 @ X5 @ X4 @ X3) @ 
% 0.58/0.76              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.58/0.76      inference('sup+', [status(thm)], ['55', '56'])).
% 0.58/0.76  thf('63', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.58/0.76         ((k5_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X1 @ X0)
% 0.58/0.76           = (k2_xboole_0 @ (k2_tarski @ X5 @ X4) @ 
% 0.58/0.76              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 0.58/0.76      inference('demod', [status(thm)], ['61', '62'])).
% 0.58/0.76  thf('64', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.58/0.76         ((k5_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X1 @ X0)
% 0.58/0.76           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.58/0.76      inference('demod', [status(thm)], ['20', '21'])).
% 0.58/0.76  thf('65', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.58/0.76         ((k2_xboole_0 @ (k2_tarski @ X5 @ X4) @ 
% 0.58/0.76           (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.58/0.76           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.58/0.76      inference('sup+', [status(thm)], ['63', '64'])).
% 0.58/0.76  thf('66', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.58/0.76         ((k5_enumset1 @ X2 @ X1 @ X1 @ X0 @ X5 @ X4 @ X3)
% 0.58/0.76           = (k4_enumset1 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3))),
% 0.58/0.76      inference('demod', [status(thm)], ['58', '65'])).
% 0.58/0.76  thf('67', plain,
% 0.58/0.76      (((k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)
% 0.58/0.76         != (k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))),
% 0.58/0.76      inference('demod', [status(thm)], ['12', '47', '66'])).
% 0.58/0.76  thf('68', plain, ($false), inference('simplify', [status(thm)], ['67'])).
% 0.58/0.76  
% 0.58/0.76  % SZS output end Refutation
% 0.58/0.76  
% 0.58/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

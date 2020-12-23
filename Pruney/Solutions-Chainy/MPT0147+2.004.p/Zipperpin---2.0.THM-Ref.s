%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0AbYjFs20y

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:13 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 213 expanded)
%              Number of leaves         :   28 (  82 expanded)
%              Depth                    :   16
%              Number of atoms          : 1266 (2608 expanded)
%              Number of equality atoms :   79 ( 195 expanded)
%              Maximal formula depth    :   19 (  11 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(t63_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k4_enumset1 @ C @ D @ E @ F @ G @ H ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
        ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
        = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k4_enumset1 @ C @ D @ E @ F @ G @ H ) ) ) ),
    inference('cnf.neg',[status(esa)],[t63_enumset1])).

thf('0',plain,(
    ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H )
 != ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k4_enumset1 @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t52_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_enumset1 @ C @ D @ E @ F ) ) ) )).

thf('1',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k4_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 )
      = ( k2_xboole_0 @ ( k2_tarski @ X32 @ X33 ) @ ( k2_enumset1 @ X34 @ X35 @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t52_enumset1])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X20 @ X21 @ X22 )
      = ( k2_xboole_0 @ ( k1_tarski @ X20 ) @ ( k2_tarski @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('3',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_tarski @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k1_tarski @ X18 ) @ ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k2_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('7',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k2_enumset1 @ X23 @ X24 @ X25 @ X26 )
      = ( k2_xboole_0 @ ( k1_tarski @ X23 ) @ ( k1_enumset1 @ X24 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k2_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X7 @ X6 @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X7 @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf('12',plain,(
    ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H )
 != ( k2_xboole_0 @ ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k2_enumset1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(demod,[status(thm)],['0','11'])).

thf(t47_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ) )).

thf('13',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k3_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_xboole_0 @ ( k1_tarski @ X27 ) @ ( k2_enumset1 @ X28 @ X29 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('14',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_tarski @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k1_tarski @ X18 ) @ ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X20 @ X21 @ X22 )
      = ( k2_xboole_0 @ ( k1_tarski @ X20 ) @ ( k2_tarski @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X20 @ X21 @ X22 )
      = ( k2_xboole_0 @ ( k1_tarski @ X20 ) @ ( k2_tarski @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('20',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k2_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k2_enumset1 @ X23 @ X24 @ X25 @ X26 )
      = ( k2_xboole_0 @ ( k1_tarski @ X23 ) @ ( k1_enumset1 @ X24 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k2_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X7 @ X6 @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X7 @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','26'])).

thf('28',plain,(
    ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H )
 != ( k2_xboole_0 @ ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) @ ( k3_enumset1 @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(demod,[status(thm)],['12','27'])).

thf(l62_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ) )).

thf('29',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k4_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X12 @ X13 @ X14 ) @ ( k1_enumset1 @ X15 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[l62_enumset1])).

thf('30',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X20 @ X21 @ X22 )
      = ( k2_xboole_0 @ ( k1_tarski @ X20 ) @ ( k2_tarski @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('32',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k2_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf(l57_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) )).

thf('35',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k3_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X7 @ X8 @ X9 ) @ ( k2_tarski @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k2_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X5 )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X7 @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k4_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 )
      = ( k2_xboole_0 @ ( k2_tarski @ X32 @ X33 ) @ ( k2_enumset1 @ X34 @ X35 @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t52_enumset1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k3_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_xboole_0 @ ( k1_tarski @ X27 ) @ ( k2_enumset1 @ X28 @ X29 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('46',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k2_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X5 )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf(t60_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ) )).

thf('49',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( k5_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42 ) @ ( k2_tarski @ X43 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t60_enumset1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X7 @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X7 @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','38'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf(t62_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k5_enumset1 @ B @ C @ D @ E @ F @ G @ H ) ) ) )).

thf('55',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ( k6_enumset1 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 )
      = ( k2_xboole_0 @ ( k1_tarski @ X45 ) @ ( k5_enumset1 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[t62_enumset1])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X7 @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k4_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X12 @ X13 @ X14 ) @ ( k1_enumset1 @ X15 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[l62_enumset1])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X7 @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X7 @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X7 @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['57','64'])).

thf('66',plain,(
    ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H )
 != ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['28','65'])).

thf('67',plain,(
    $false ),
    inference(simplify,[status(thm)],['66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0AbYjFs20y
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:58:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 101 iterations in 0.077s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.20/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.54  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.20/0.54  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.20/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.54  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.20/0.54                                           $i > $i).
% 0.20/0.54  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.20/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.54  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(sk_G_type, type, sk_G: $i).
% 0.20/0.54  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.54  thf(sk_H_type, type, sk_H: $i).
% 0.20/0.54  thf(t63_enumset1, conjecture,
% 0.20/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.20/0.54     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.20/0.54       ( k2_xboole_0 @
% 0.20/0.54         ( k2_tarski @ A @ B ) @ ( k4_enumset1 @ C @ D @ E @ F @ G @ H ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.20/0.54        ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.20/0.54          ( k2_xboole_0 @
% 0.20/0.54            ( k2_tarski @ A @ B ) @ ( k4_enumset1 @ C @ D @ E @ F @ G @ H ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t63_enumset1])).
% 0.20/0.54  thf('0', plain,
% 0.20/0.54      (((k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.20/0.54         != (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 0.20/0.54             (k4_enumset1 @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(t52_enumset1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.54     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.20/0.54       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_enumset1 @ C @ D @ E @ F ) ) ))).
% 0.20/0.54  thf('1', plain,
% 0.20/0.54      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.20/0.54         ((k4_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37)
% 0.20/0.54           = (k2_xboole_0 @ (k2_tarski @ X32 @ X33) @ 
% 0.20/0.54              (k2_enumset1 @ X34 @ X35 @ X36 @ X37)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t52_enumset1])).
% 0.20/0.54  thf(t42_enumset1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.20/0.54       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.20/0.54  thf('2', plain,
% 0.20/0.54      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.54         ((k1_enumset1 @ X20 @ X21 @ X22)
% 0.20/0.54           = (k2_xboole_0 @ (k1_tarski @ X20) @ (k2_tarski @ X21 @ X22)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.20/0.54  thf(t41_enumset1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( k2_tarski @ A @ B ) =
% 0.20/0.54       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.20/0.54  thf('3', plain,
% 0.20/0.54      (![X18 : $i, X19 : $i]:
% 0.20/0.54         ((k2_tarski @ X18 @ X19)
% 0.20/0.54           = (k2_xboole_0 @ (k1_tarski @ X18) @ (k1_tarski @ X19)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.20/0.54  thf(t4_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.54       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.20/0.54  thf('4', plain,
% 0.20/0.54      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ X6)
% 0.20/0.54           = (k2_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.20/0.54  thf('5', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.20/0.54           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.20/0.54              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['3', '4'])).
% 0.20/0.54  thf('6', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0))
% 0.20/0.54           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['2', '5'])).
% 0.20/0.54  thf(t44_enumset1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.54     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.20/0.54       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 0.20/0.54  thf('7', plain,
% 0.20/0.54      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.54         ((k2_enumset1 @ X23 @ X24 @ X25 @ X26)
% 0.20/0.54           = (k2_xboole_0 @ (k1_tarski @ X23) @ (k1_enumset1 @ X24 @ X25 @ X26)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.20/0.54  thf('8', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.54         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.54           = (k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['6', '7'])).
% 0.20/0.54  thf('9', plain,
% 0.20/0.54      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ X6)
% 0.20/0.54           = (k2_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.20/0.54  thf('10', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4)
% 0.20/0.54           = (k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ 
% 0.20/0.54              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X4)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['8', '9'])).
% 0.20/0.54  thf('11', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ (k2_enumset1 @ X7 @ X6 @ X5 @ X4) @ 
% 0.20/0.54           (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.54           = (k2_xboole_0 @ (k2_tarski @ X7 @ X6) @ 
% 0.20/0.54              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['1', '10'])).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      (((k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.20/0.54         != (k2_xboole_0 @ (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.20/0.54             (k2_enumset1 @ sk_E @ sk_F @ sk_G @ sk_H)))),
% 0.20/0.54      inference('demod', [status(thm)], ['0', '11'])).
% 0.20/0.54  thf(t47_enumset1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.54     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.20/0.54       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ))).
% 0.20/0.54  thf('13', plain,
% 0.20/0.54      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.20/0.54         ((k3_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31)
% 0.20/0.54           = (k2_xboole_0 @ (k1_tarski @ X27) @ 
% 0.20/0.54              (k2_enumset1 @ X28 @ X29 @ X30 @ X31)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.20/0.54  thf('14', plain,
% 0.20/0.54      (![X18 : $i, X19 : $i]:
% 0.20/0.54         ((k2_tarski @ X18 @ X19)
% 0.20/0.54           = (k2_xboole_0 @ (k1_tarski @ X18) @ (k1_tarski @ X19)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.20/0.54  thf('15', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.20/0.54           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.20/0.54              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['3', '4'])).
% 0.20/0.54  thf('16', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.20/0.54           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['14', '15'])).
% 0.20/0.54  thf('17', plain,
% 0.20/0.54      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.54         ((k1_enumset1 @ X20 @ X21 @ X22)
% 0.20/0.54           = (k2_xboole_0 @ (k1_tarski @ X20) @ (k2_tarski @ X21 @ X22)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.20/0.54  thf('18', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.20/0.54           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.20/0.54      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.54  thf('19', plain,
% 0.20/0.54      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.54         ((k1_enumset1 @ X20 @ X21 @ X22)
% 0.20/0.54           = (k2_xboole_0 @ (k1_tarski @ X20) @ (k2_tarski @ X21 @ X22)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.20/0.54  thf('20', plain,
% 0.20/0.54      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ X6)
% 0.20/0.54           = (k2_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.20/0.54  thf('21', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.20/0.54           = (k2_xboole_0 @ (k1_tarski @ X2) @ 
% 0.20/0.54              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X3)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['19', '20'])).
% 0.20/0.54  thf('22', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 0.20/0.54           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['18', '21'])).
% 0.20/0.54  thf('23', plain,
% 0.20/0.54      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.54         ((k2_enumset1 @ X23 @ X24 @ X25 @ X26)
% 0.20/0.54           = (k2_xboole_0 @ (k1_tarski @ X23) @ (k1_enumset1 @ X24 @ X25 @ X26)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.20/0.54  thf('24', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 0.20/0.54           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.20/0.54      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.54  thf('25', plain,
% 0.20/0.54      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ X6)
% 0.20/0.54           = (k2_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.20/0.54  thf('26', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4)
% 0.20/0.54           = (k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ 
% 0.20/0.54              (k2_xboole_0 @ (k1_tarski @ X0) @ X4)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['24', '25'])).
% 0.20/0.54  thf('27', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ (k2_enumset1 @ X7 @ X6 @ X5 @ X4) @ 
% 0.20/0.54           (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.54           = (k2_xboole_0 @ (k1_enumset1 @ X7 @ X6 @ X5) @ 
% 0.20/0.54              (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['13', '26'])).
% 0.20/0.54  thf('28', plain,
% 0.20/0.54      (((k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.20/0.54         != (k2_xboole_0 @ (k1_enumset1 @ sk_A @ sk_B @ sk_C) @ 
% 0.20/0.54             (k3_enumset1 @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)))),
% 0.20/0.54      inference('demod', [status(thm)], ['12', '27'])).
% 0.20/0.54  thf(l62_enumset1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.54     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.20/0.54       ( k2_xboole_0 @
% 0.20/0.54         ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ))).
% 0.20/0.54  thf('29', plain,
% 0.20/0.54      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.54         ((k4_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17)
% 0.20/0.54           = (k2_xboole_0 @ (k1_enumset1 @ X12 @ X13 @ X14) @ 
% 0.20/0.54              (k1_enumset1 @ X15 @ X16 @ X17)))),
% 0.20/0.54      inference('cnf', [status(esa)], [l62_enumset1])).
% 0.20/0.54  thf('30', plain,
% 0.20/0.54      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.54         ((k1_enumset1 @ X20 @ X21 @ X22)
% 0.20/0.54           = (k2_xboole_0 @ (k1_tarski @ X20) @ (k2_tarski @ X21 @ X22)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.20/0.54  thf('31', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.20/0.54           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.20/0.54      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.54  thf('32', plain,
% 0.20/0.54      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ X6)
% 0.20/0.54           = (k2_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.20/0.54  thf('33', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.20/0.54           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ 
% 0.20/0.54              (k2_xboole_0 @ (k1_tarski @ X0) @ X3)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['31', '32'])).
% 0.20/0.54  thf('34', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ (k1_enumset1 @ X4 @ X3 @ X2) @ (k2_tarski @ X1 @ X0))
% 0.20/0.54           = (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ 
% 0.20/0.54              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['30', '33'])).
% 0.20/0.54  thf(l57_enumset1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.54     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.20/0.54       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ))).
% 0.20/0.54  thf('35', plain,
% 0.20/0.54      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.54         ((k3_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11)
% 0.20/0.54           = (k2_xboole_0 @ (k1_enumset1 @ X7 @ X8 @ X9) @ 
% 0.20/0.54              (k2_tarski @ X10 @ X11)))),
% 0.20/0.54      inference('cnf', [status(esa)], [l57_enumset1])).
% 0.20/0.54  thf('36', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.54         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.54           = (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ 
% 0.20/0.54              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.20/0.54      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.54  thf('37', plain,
% 0.20/0.54      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ X6)
% 0.20/0.54           = (k2_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.20/0.54  thf('38', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ X5)
% 0.20/0.54           = (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ 
% 0.20/0.54              (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X5)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['36', '37'])).
% 0.20/0.54  thf('39', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ (k3_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3) @ 
% 0.20/0.54           (k1_enumset1 @ X2 @ X1 @ X0))
% 0.20/0.54           = (k2_xboole_0 @ (k2_tarski @ X7 @ X6) @ 
% 0.20/0.54              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['29', '38'])).
% 0.20/0.54  thf('40', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.54         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.54           = (k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['6', '7'])).
% 0.20/0.54  thf('41', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4)
% 0.20/0.54           = (k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ 
% 0.20/0.54              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X4)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['8', '9'])).
% 0.20/0.54  thf('42', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ (k2_enumset1 @ X5 @ X4 @ X3 @ X2) @ 
% 0.20/0.54           (k2_tarski @ X1 @ X0))
% 0.20/0.54           = (k2_xboole_0 @ (k2_tarski @ X5 @ X4) @ 
% 0.20/0.54              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['40', '41'])).
% 0.20/0.54  thf('43', plain,
% 0.20/0.54      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.20/0.54         ((k4_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37)
% 0.20/0.54           = (k2_xboole_0 @ (k2_tarski @ X32 @ X33) @ 
% 0.20/0.54              (k2_enumset1 @ X34 @ X35 @ X36 @ X37)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t52_enumset1])).
% 0.20/0.54  thf('44', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ (k2_enumset1 @ X5 @ X4 @ X3 @ X2) @ 
% 0.20/0.54           (k2_tarski @ X1 @ X0)) = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.20/0.54      inference('demod', [status(thm)], ['42', '43'])).
% 0.20/0.54  thf('45', plain,
% 0.20/0.54      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.20/0.54         ((k3_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31)
% 0.20/0.54           = (k2_xboole_0 @ (k1_tarski @ X27) @ 
% 0.20/0.54              (k2_enumset1 @ X28 @ X29 @ X30 @ X31)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.20/0.54  thf('46', plain,
% 0.20/0.54      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ X6)
% 0.20/0.54           = (k2_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.20/0.54  thf('47', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ X5)
% 0.20/0.54           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 0.20/0.54              (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X5)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['45', '46'])).
% 0.20/0.54  thf('48', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ (k3_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2) @ 
% 0.20/0.54           (k2_tarski @ X1 @ X0))
% 0.20/0.54           = (k2_xboole_0 @ (k1_tarski @ X6) @ 
% 0.20/0.54              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['44', '47'])).
% 0.20/0.54  thf(t60_enumset1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.20/0.54     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.20/0.54       ( k2_xboole_0 @
% 0.20/0.54         ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ))).
% 0.20/0.54  thf('49', plain,
% 0.20/0.54      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.20/0.54         ((k5_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44)
% 0.20/0.54           = (k2_xboole_0 @ (k3_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42) @ 
% 0.20/0.54              (k2_tarski @ X43 @ X44)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t60_enumset1])).
% 0.20/0.54  thf('50', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.54         ((k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.54           = (k2_xboole_0 @ (k1_tarski @ X6) @ 
% 0.20/0.54              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.20/0.54      inference('demod', [status(thm)], ['48', '49'])).
% 0.20/0.54  thf('51', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.20/0.54           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.20/0.54              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['3', '4'])).
% 0.20/0.54  thf('52', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ (k2_tarski @ X7 @ X6) @ 
% 0.20/0.54           (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.54           = (k2_xboole_0 @ (k1_tarski @ X7) @ 
% 0.20/0.54              (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['50', '51'])).
% 0.20/0.54  thf('53', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ (k3_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3) @ 
% 0.20/0.54           (k1_enumset1 @ X2 @ X1 @ X0))
% 0.20/0.54           = (k2_xboole_0 @ (k2_tarski @ X7 @ X6) @ 
% 0.20/0.54              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['29', '38'])).
% 0.20/0.54  thf('54', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ (k3_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3) @ 
% 0.20/0.54           (k1_enumset1 @ X2 @ X1 @ X0))
% 0.20/0.54           = (k2_xboole_0 @ (k1_tarski @ X7) @ 
% 0.20/0.54              (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.20/0.54      inference('demod', [status(thm)], ['52', '53'])).
% 0.20/0.54  thf(t62_enumset1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.20/0.54     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.20/0.54       ( k2_xboole_0 @
% 0.20/0.54         ( k1_tarski @ A ) @ ( k5_enumset1 @ B @ C @ D @ E @ F @ G @ H ) ) ))).
% 0.20/0.54  thf('55', plain,
% 0.20/0.54      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, 
% 0.20/0.54         X52 : $i]:
% 0.20/0.54         ((k6_enumset1 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52)
% 0.20/0.54           = (k2_xboole_0 @ (k1_tarski @ X45) @ 
% 0.20/0.54              (k5_enumset1 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t62_enumset1])).
% 0.20/0.54  thf('56', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.54         ((k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.54           = (k2_xboole_0 @ (k3_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3) @ 
% 0.20/0.54              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['54', '55'])).
% 0.20/0.54  thf('57', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.54         ((k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.54           = (k2_xboole_0 @ (k2_tarski @ X7 @ X6) @ 
% 0.20/0.54              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.20/0.54      inference('demod', [status(thm)], ['39', '56'])).
% 0.20/0.54  thf('58', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.54         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.54           = (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ 
% 0.20/0.54              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.20/0.54      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.54  thf('59', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.20/0.54           = (k2_xboole_0 @ (k1_tarski @ X2) @ 
% 0.20/0.54              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X3)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['19', '20'])).
% 0.20/0.54  thf('60', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ (k1_enumset1 @ X5 @ X4 @ X3) @ 
% 0.20/0.54           (k1_enumset1 @ X2 @ X1 @ X0))
% 0.20/0.54           = (k2_xboole_0 @ (k1_tarski @ X5) @ 
% 0.20/0.54              (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['58', '59'])).
% 0.20/0.54  thf('61', plain,
% 0.20/0.54      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.54         ((k4_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17)
% 0.20/0.54           = (k2_xboole_0 @ (k1_enumset1 @ X12 @ X13 @ X14) @ 
% 0.20/0.54              (k1_enumset1 @ X15 @ X16 @ X17)))),
% 0.20/0.54      inference('cnf', [status(esa)], [l62_enumset1])).
% 0.20/0.54  thf('62', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.54         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.54           = (k2_xboole_0 @ (k1_tarski @ X5) @ 
% 0.20/0.54              (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.20/0.54      inference('demod', [status(thm)], ['60', '61'])).
% 0.20/0.54  thf('63', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.20/0.54           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ 
% 0.20/0.54              (k2_xboole_0 @ (k1_tarski @ X0) @ X3)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['31', '32'])).
% 0.20/0.54  thf('64', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ (k1_enumset1 @ X7 @ X6 @ X5) @ 
% 0.20/0.54           (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.54           = (k2_xboole_0 @ (k2_tarski @ X7 @ X6) @ 
% 0.20/0.54              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['62', '63'])).
% 0.20/0.54  thf('65', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ (k1_enumset1 @ X7 @ X6 @ X5) @ 
% 0.20/0.54           (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.20/0.54           = (k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['57', '64'])).
% 0.20/0.54  thf('66', plain,
% 0.20/0.54      (((k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.20/0.54         != (k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ 
% 0.20/0.54             sk_H))),
% 0.20/0.54      inference('demod', [status(thm)], ['28', '65'])).
% 0.20/0.54  thf('67', plain, ($false), inference('simplify', [status(thm)], ['66'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.owyMfrRW0j

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:39 EST 2020

% Result     : Theorem 12.49s
% Output     : Refutation 12.49s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 390 expanded)
%              Number of leaves         :   21 ( 141 expanded)
%              Depth                    :   16
%              Number of atoms          : 1174 (4498 expanded)
%              Number of equality atoms :   99 ( 379 expanded)
%              Maximal formula depth    :   15 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t137_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) )
        = ( k1_enumset1 @ A @ B @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t137_enumset1])).

thf('0',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k2_tarski @ sk_C @ sk_A ) )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t100_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ B @ C @ A ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k1_enumset1 @ X12 @ X10 @ X11 )
      = ( k1_enumset1 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k1_enumset1 @ X12 @ X10 @ X11 )
      = ( k1_enumset1 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('3',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k2_tarski @ sk_C @ sk_A ) )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf('4',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k1_enumset1 @ X12 @ X10 @ X11 )
      = ( k1_enumset1 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_enumset1 @ X31 @ X31 @ X32 )
      = ( k2_tarski @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_enumset1 @ X31 @ X31 @ X32 )
      = ( k2_tarski @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(l62_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X5 @ X6 ) @ ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l62_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X1 @ X0 @ X1 @ X3 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_enumset1 @ X31 @ X31 @ X32 )
      = ( k2_tarski @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('12',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k1_enumset1 @ X12 @ X10 @ X11 )
      = ( k1_enumset1 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('13',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X5 @ X6 ) @ ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l62_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X1 @ X0 @ X2 @ X5 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_enumset1 @ X5 @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X1 @ X0 @ X1 @ X4 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_enumset1 @ X4 @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_enumset1 @ X31 @ X31 @ X32 )
      = ( k2_tarski @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('17',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X5 @ X6 ) @ ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l62_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X1 @ X1 @ X0 @ X4 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_enumset1 @ X4 @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('19',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( k4_enumset1 @ X40 @ X40 @ X41 @ X42 @ X43 @ X44 )
      = ( k3_enumset1 @ X40 @ X41 @ X42 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X1 @ X0 @ X4 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_enumset1 @ X4 @ X3 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X1 @ X0 @ X1 @ X4 @ X3 @ X2 )
      = ( k3_enumset1 @ X1 @ X0 @ X4 @ X3 @ X2 ) ) ),
    inference(demod,[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X0 @ X3 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['10','21'])).

thf('23',plain,(
    ( k3_enumset1 @ sk_B @ sk_A @ sk_C @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['3','22'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('24',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( k2_enumset1 @ X33 @ X33 @ X34 @ X35 )
      = ( k1_enumset1 @ X33 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('25',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_enumset1 @ X31 @ X31 @ X32 )
      = ( k2_tarski @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('28',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( k3_enumset1 @ X36 @ X36 @ X37 @ X38 @ X39 )
      = ( k2_enumset1 @ X36 @ X37 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t55_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ) )).

thf('29',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k4_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20 ) @ ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t55_enumset1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( k4_enumset1 @ X40 @ X40 @ X41 @ X42 @ X43 @ X44 )
      = ( k3_enumset1 @ X40 @ X41 @ X42 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( k3_enumset1 @ X36 @ X36 @ X37 @ X38 @ X39 )
      = ( k2_enumset1 @ X36 @ X37 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( k2_enumset1 @ X33 @ X33 @ X34 @ X35 )
      = ( k1_enumset1 @ X33 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['26','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('40',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k1_enumset1 @ X12 @ X10 @ X11 )
      = ( k1_enumset1 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('42',plain,(
    ! [X30: $i] :
      ( ( k2_tarski @ X30 @ X30 )
      = ( k1_tarski @ X30 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( k2_enumset1 @ X33 @ X33 @ X34 @ X35 )
      = ( k1_enumset1 @ X33 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('45',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X5 @ X6 ) @ ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l62_enumset1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) @ ( k1_enumset1 @ X5 @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X0 @ X0 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_enumset1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( k4_enumset1 @ X40 @ X40 @ X41 @ X42 @ X43 @ X44 )
      = ( k3_enumset1 @ X40 @ X41 @ X42 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('49',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( k3_enumset1 @ X36 @ X36 @ X37 @ X38 @ X39 )
      = ( k2_enumset1 @ X36 @ X37 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_enumset1 @ X3 @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_enumset1 @ X3 @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X0 @ X2 @ X1 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( k2_enumset1 @ X33 @ X33 @ X34 @ X35 )
      = ( k1_enumset1 @ X33 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf(t102_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ C @ B @ A ) ) )).

thf('56',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k1_enumset1 @ X15 @ X14 @ X13 )
      = ( k1_enumset1 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t102_enumset1])).

thf('57',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k1_enumset1 @ X12 @ X10 @ X11 )
      = ( k1_enumset1 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( k2_enumset1 @ X33 @ X33 @ X34 @ X35 )
      = ( k1_enumset1 @ X33 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X2 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X2 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( k3_enumset1 @ X36 @ X36 @ X37 @ X38 @ X39 )
      = ( k2_enumset1 @ X36 @ X37 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X2 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['55','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 )
      = ( k3_enumset1 @ X1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X1 @ X2 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['38','39','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X0 @ X2 @ X1 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X2 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( k2_enumset1 @ X33 @ X33 @ X34 @ X35 )
      = ( k1_enumset1 @ X33 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( k3_enumset1 @ X36 @ X36 @ X37 @ X38 @ X39 )
      = ( k2_enumset1 @ X36 @ X37 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X3 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['70','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X1 @ X3 )
      = ( k3_enumset1 @ X2 @ X1 @ X0 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X1 @ X2 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['38','39','67'])).

thf(t98_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ A @ C @ B ) ) )).

thf('80',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ( k1_enumset1 @ X58 @ X60 @ X59 )
      = ( k1_enumset1 @ X58 @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X0 @ X2 @ X1 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X2 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('85',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ( k1_enumset1 @ X58 @ X60 @ X59 )
      = ( k1_enumset1 @ X58 @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf('86',plain,(
    ( k1_enumset1 @ sk_B @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['23','78','83','84','85'])).

thf('87',plain,(
    $false ),
    inference(simplify,[status(thm)],['86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.owyMfrRW0j
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:57:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 12.49/12.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 12.49/12.74  % Solved by: fo/fo7.sh
% 12.49/12.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 12.49/12.74  % done 8655 iterations in 12.289s
% 12.49/12.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 12.49/12.74  % SZS output start Refutation
% 12.49/12.74  thf(sk_A_type, type, sk_A: $i).
% 12.49/12.74  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 12.49/12.74  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 12.49/12.74  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 12.49/12.74  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 12.49/12.74  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 12.49/12.74  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 12.49/12.74  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 12.49/12.74  thf(sk_B_type, type, sk_B: $i).
% 12.49/12.74  thf(sk_C_type, type, sk_C: $i).
% 12.49/12.74  thf(t137_enumset1, conjecture,
% 12.49/12.74    (![A:$i,B:$i,C:$i]:
% 12.49/12.74     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 12.49/12.74       ( k1_enumset1 @ A @ B @ C ) ))).
% 12.49/12.74  thf(zf_stmt_0, negated_conjecture,
% 12.49/12.74    (~( ![A:$i,B:$i,C:$i]:
% 12.49/12.74        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 12.49/12.74          ( k1_enumset1 @ A @ B @ C ) ) )),
% 12.49/12.74    inference('cnf.neg', [status(esa)], [t137_enumset1])).
% 12.49/12.74  thf('0', plain,
% 12.49/12.74      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 12.49/12.74         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 12.49/12.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.49/12.74  thf(t100_enumset1, axiom,
% 12.49/12.74    (![A:$i,B:$i,C:$i]:
% 12.49/12.74     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ B @ C @ A ) ))).
% 12.49/12.74  thf('1', plain,
% 12.49/12.74      (![X10 : $i, X11 : $i, X12 : $i]:
% 12.49/12.74         ((k1_enumset1 @ X12 @ X10 @ X11) = (k1_enumset1 @ X10 @ X11 @ X12))),
% 12.49/12.74      inference('cnf', [status(esa)], [t100_enumset1])).
% 12.49/12.74  thf('2', plain,
% 12.49/12.74      (![X10 : $i, X11 : $i, X12 : $i]:
% 12.49/12.74         ((k1_enumset1 @ X12 @ X10 @ X11) = (k1_enumset1 @ X10 @ X11 @ X12))),
% 12.49/12.74      inference('cnf', [status(esa)], [t100_enumset1])).
% 12.49/12.74  thf('3', plain,
% 12.49/12.74      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 12.49/12.74         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 12.49/12.74      inference('demod', [status(thm)], ['0', '1', '2'])).
% 12.49/12.74  thf('4', plain,
% 12.49/12.74      (![X10 : $i, X11 : $i, X12 : $i]:
% 12.49/12.74         ((k1_enumset1 @ X12 @ X10 @ X11) = (k1_enumset1 @ X10 @ X11 @ X12))),
% 12.49/12.74      inference('cnf', [status(esa)], [t100_enumset1])).
% 12.49/12.74  thf(t70_enumset1, axiom,
% 12.49/12.74    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 12.49/12.74  thf('5', plain,
% 12.49/12.74      (![X31 : $i, X32 : $i]:
% 12.49/12.74         ((k1_enumset1 @ X31 @ X31 @ X32) = (k2_tarski @ X31 @ X32))),
% 12.49/12.74      inference('cnf', [status(esa)], [t70_enumset1])).
% 12.49/12.74  thf('6', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i]:
% 12.49/12.74         ((k1_enumset1 @ X0 @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 12.49/12.74      inference('sup+', [status(thm)], ['4', '5'])).
% 12.49/12.74  thf('7', plain,
% 12.49/12.74      (![X31 : $i, X32 : $i]:
% 12.49/12.74         ((k1_enumset1 @ X31 @ X31 @ X32) = (k2_tarski @ X31 @ X32))),
% 12.49/12.74      inference('cnf', [status(esa)], [t70_enumset1])).
% 12.49/12.74  thf(l62_enumset1, axiom,
% 12.49/12.74    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 12.49/12.74     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 12.49/12.74       ( k2_xboole_0 @
% 12.49/12.74         ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ))).
% 12.49/12.74  thf('8', plain,
% 12.49/12.74      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 12.49/12.74         ((k4_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9)
% 12.49/12.74           = (k2_xboole_0 @ (k1_enumset1 @ X4 @ X5 @ X6) @ 
% 12.49/12.74              (k1_enumset1 @ X7 @ X8 @ X9)))),
% 12.49/12.74      inference('cnf', [status(esa)], [l62_enumset1])).
% 12.49/12.74  thf('9', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 12.49/12.74         ((k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X1 @ X0)
% 12.49/12.74           = (k2_xboole_0 @ (k1_enumset1 @ X4 @ X3 @ X2) @ 
% 12.49/12.74              (k2_tarski @ X1 @ X0)))),
% 12.49/12.74      inference('sup+', [status(thm)], ['7', '8'])).
% 12.49/12.74  thf('10', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.49/12.74         ((k4_enumset1 @ X1 @ X0 @ X1 @ X3 @ X3 @ X2)
% 12.49/12.74           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 12.49/12.74      inference('sup+', [status(thm)], ['6', '9'])).
% 12.49/12.74  thf('11', plain,
% 12.49/12.74      (![X31 : $i, X32 : $i]:
% 12.49/12.74         ((k1_enumset1 @ X31 @ X31 @ X32) = (k2_tarski @ X31 @ X32))),
% 12.49/12.74      inference('cnf', [status(esa)], [t70_enumset1])).
% 12.49/12.74  thf('12', plain,
% 12.49/12.74      (![X10 : $i, X11 : $i, X12 : $i]:
% 12.49/12.74         ((k1_enumset1 @ X12 @ X10 @ X11) = (k1_enumset1 @ X10 @ X11 @ X12))),
% 12.49/12.74      inference('cnf', [status(esa)], [t100_enumset1])).
% 12.49/12.74  thf('13', plain,
% 12.49/12.74      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 12.49/12.74         ((k4_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9)
% 12.49/12.74           = (k2_xboole_0 @ (k1_enumset1 @ X4 @ X5 @ X6) @ 
% 12.49/12.74              (k1_enumset1 @ X7 @ X8 @ X9)))),
% 12.49/12.74      inference('cnf', [status(esa)], [l62_enumset1])).
% 12.49/12.74  thf('14', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 12.49/12.74         ((k4_enumset1 @ X1 @ X0 @ X2 @ X5 @ X4 @ X3)
% 12.49/12.74           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 12.49/12.74              (k1_enumset1 @ X5 @ X4 @ X3)))),
% 12.49/12.74      inference('sup+', [status(thm)], ['12', '13'])).
% 12.49/12.74  thf('15', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 12.49/12.74         ((k4_enumset1 @ X1 @ X0 @ X1 @ X4 @ X3 @ X2)
% 12.49/12.74           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 12.49/12.74              (k1_enumset1 @ X4 @ X3 @ X2)))),
% 12.49/12.74      inference('sup+', [status(thm)], ['11', '14'])).
% 12.49/12.74  thf('16', plain,
% 12.49/12.74      (![X31 : $i, X32 : $i]:
% 12.49/12.74         ((k1_enumset1 @ X31 @ X31 @ X32) = (k2_tarski @ X31 @ X32))),
% 12.49/12.74      inference('cnf', [status(esa)], [t70_enumset1])).
% 12.49/12.74  thf('17', plain,
% 12.49/12.74      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 12.49/12.74         ((k4_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9)
% 12.49/12.74           = (k2_xboole_0 @ (k1_enumset1 @ X4 @ X5 @ X6) @ 
% 12.49/12.74              (k1_enumset1 @ X7 @ X8 @ X9)))),
% 12.49/12.74      inference('cnf', [status(esa)], [l62_enumset1])).
% 12.49/12.74  thf('18', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 12.49/12.74         ((k4_enumset1 @ X1 @ X1 @ X0 @ X4 @ X3 @ X2)
% 12.49/12.74           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 12.49/12.74              (k1_enumset1 @ X4 @ X3 @ X2)))),
% 12.49/12.74      inference('sup+', [status(thm)], ['16', '17'])).
% 12.49/12.74  thf(t73_enumset1, axiom,
% 12.49/12.74    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 12.49/12.74     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 12.49/12.74       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 12.49/12.74  thf('19', plain,
% 12.49/12.74      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 12.49/12.74         ((k4_enumset1 @ X40 @ X40 @ X41 @ X42 @ X43 @ X44)
% 12.49/12.74           = (k3_enumset1 @ X40 @ X41 @ X42 @ X43 @ X44))),
% 12.49/12.74      inference('cnf', [status(esa)], [t73_enumset1])).
% 12.49/12.74  thf('20', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 12.49/12.74         ((k3_enumset1 @ X1 @ X0 @ X4 @ X3 @ X2)
% 12.49/12.74           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 12.49/12.74              (k1_enumset1 @ X4 @ X3 @ X2)))),
% 12.49/12.74      inference('demod', [status(thm)], ['18', '19'])).
% 12.49/12.74  thf('21', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 12.49/12.74         ((k4_enumset1 @ X1 @ X0 @ X1 @ X4 @ X3 @ X2)
% 12.49/12.74           = (k3_enumset1 @ X1 @ X0 @ X4 @ X3 @ X2))),
% 12.49/12.74      inference('demod', [status(thm)], ['15', '20'])).
% 12.49/12.74  thf('22', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.49/12.74         ((k3_enumset1 @ X1 @ X0 @ X3 @ X3 @ X2)
% 12.49/12.74           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 12.49/12.74      inference('demod', [status(thm)], ['10', '21'])).
% 12.49/12.74  thf('23', plain,
% 12.49/12.74      (((k3_enumset1 @ sk_B @ sk_A @ sk_C @ sk_C @ sk_A)
% 12.49/12.74         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 12.49/12.74      inference('demod', [status(thm)], ['3', '22'])).
% 12.49/12.74  thf(t71_enumset1, axiom,
% 12.49/12.74    (![A:$i,B:$i,C:$i]:
% 12.49/12.74     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 12.49/12.74  thf('24', plain,
% 12.49/12.74      (![X33 : $i, X34 : $i, X35 : $i]:
% 12.49/12.74         ((k2_enumset1 @ X33 @ X33 @ X34 @ X35)
% 12.49/12.74           = (k1_enumset1 @ X33 @ X34 @ X35))),
% 12.49/12.74      inference('cnf', [status(esa)], [t71_enumset1])).
% 12.49/12.74  thf('25', plain,
% 12.49/12.74      (![X31 : $i, X32 : $i]:
% 12.49/12.74         ((k1_enumset1 @ X31 @ X31 @ X32) = (k2_tarski @ X31 @ X32))),
% 12.49/12.74      inference('cnf', [status(esa)], [t70_enumset1])).
% 12.49/12.74  thf('26', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i]:
% 12.49/12.74         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 12.49/12.74      inference('sup+', [status(thm)], ['24', '25'])).
% 12.49/12.74  thf('27', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i]:
% 12.49/12.74         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 12.49/12.74      inference('sup+', [status(thm)], ['24', '25'])).
% 12.49/12.74  thf(t72_enumset1, axiom,
% 12.49/12.74    (![A:$i,B:$i,C:$i,D:$i]:
% 12.49/12.74     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 12.49/12.74  thf('28', plain,
% 12.49/12.74      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 12.49/12.74         ((k3_enumset1 @ X36 @ X36 @ X37 @ X38 @ X39)
% 12.49/12.74           = (k2_enumset1 @ X36 @ X37 @ X38 @ X39))),
% 12.49/12.74      inference('cnf', [status(esa)], [t72_enumset1])).
% 12.49/12.74  thf(t55_enumset1, axiom,
% 12.49/12.74    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 12.49/12.74     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 12.49/12.74       ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ))).
% 12.49/12.74  thf('29', plain,
% 12.49/12.74      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 12.49/12.74         ((k4_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21)
% 12.49/12.74           = (k2_xboole_0 @ (k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20) @ 
% 12.49/12.74              (k1_tarski @ X21)))),
% 12.49/12.74      inference('cnf', [status(esa)], [t55_enumset1])).
% 12.49/12.74  thf('30', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 12.49/12.74         ((k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4)
% 12.49/12.74           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 12.49/12.74              (k1_tarski @ X4)))),
% 12.49/12.74      inference('sup+', [status(thm)], ['28', '29'])).
% 12.49/12.74  thf('31', plain,
% 12.49/12.74      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 12.49/12.74         ((k4_enumset1 @ X40 @ X40 @ X41 @ X42 @ X43 @ X44)
% 12.49/12.74           = (k3_enumset1 @ X40 @ X41 @ X42 @ X43 @ X44))),
% 12.49/12.74      inference('cnf', [status(esa)], [t73_enumset1])).
% 12.49/12.74  thf('32', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 12.49/12.74         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 12.49/12.74           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 12.49/12.74              (k1_tarski @ X4)))),
% 12.49/12.74      inference('demod', [status(thm)], ['30', '31'])).
% 12.49/12.74  thf('33', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.49/12.74         ((k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2)
% 12.49/12.74           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 12.49/12.74      inference('sup+', [status(thm)], ['27', '32'])).
% 12.49/12.74  thf('34', plain,
% 12.49/12.74      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 12.49/12.74         ((k3_enumset1 @ X36 @ X36 @ X37 @ X38 @ X39)
% 12.49/12.74           = (k2_enumset1 @ X36 @ X37 @ X38 @ X39))),
% 12.49/12.74      inference('cnf', [status(esa)], [t72_enumset1])).
% 12.49/12.74  thf('35', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.49/12.74         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 12.49/12.74           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 12.49/12.74      inference('demod', [status(thm)], ['33', '34'])).
% 12.49/12.74  thf('36', plain,
% 12.49/12.74      (![X33 : $i, X34 : $i, X35 : $i]:
% 12.49/12.74         ((k2_enumset1 @ X33 @ X33 @ X34 @ X35)
% 12.49/12.74           = (k1_enumset1 @ X33 @ X34 @ X35))),
% 12.49/12.74      inference('cnf', [status(esa)], [t71_enumset1])).
% 12.49/12.74  thf('37', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.49/12.74         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 12.49/12.74           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 12.49/12.74      inference('sup+', [status(thm)], ['35', '36'])).
% 12.49/12.74  thf('38', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.49/12.74         ((k2_xboole_0 @ (k2_enumset1 @ X1 @ X1 @ X1 @ X0) @ (k1_tarski @ X2))
% 12.49/12.74           = (k1_enumset1 @ X1 @ X0 @ X2))),
% 12.49/12.74      inference('sup+', [status(thm)], ['26', '37'])).
% 12.49/12.74  thf('39', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 12.49/12.74         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 12.49/12.74           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 12.49/12.74              (k1_tarski @ X4)))),
% 12.49/12.74      inference('demod', [status(thm)], ['30', '31'])).
% 12.49/12.74  thf('40', plain,
% 12.49/12.74      (![X10 : $i, X11 : $i, X12 : $i]:
% 12.49/12.74         ((k1_enumset1 @ X12 @ X10 @ X11) = (k1_enumset1 @ X10 @ X11 @ X12))),
% 12.49/12.74      inference('cnf', [status(esa)], [t100_enumset1])).
% 12.49/12.74  thf('41', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i]:
% 12.49/12.74         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 12.49/12.74      inference('sup+', [status(thm)], ['24', '25'])).
% 12.49/12.74  thf(t69_enumset1, axiom,
% 12.49/12.74    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 12.49/12.74  thf('42', plain,
% 12.49/12.74      (![X30 : $i]: ((k2_tarski @ X30 @ X30) = (k1_tarski @ X30))),
% 12.49/12.74      inference('cnf', [status(esa)], [t69_enumset1])).
% 12.49/12.74  thf('43', plain,
% 12.49/12.74      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 12.49/12.74      inference('sup+', [status(thm)], ['41', '42'])).
% 12.49/12.74  thf('44', plain,
% 12.49/12.74      (![X33 : $i, X34 : $i, X35 : $i]:
% 12.49/12.74         ((k2_enumset1 @ X33 @ X33 @ X34 @ X35)
% 12.49/12.74           = (k1_enumset1 @ X33 @ X34 @ X35))),
% 12.49/12.74      inference('cnf', [status(esa)], [t71_enumset1])).
% 12.49/12.74  thf('45', plain,
% 12.49/12.74      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 12.49/12.74         ((k4_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9)
% 12.49/12.74           = (k2_xboole_0 @ (k1_enumset1 @ X4 @ X5 @ X6) @ 
% 12.49/12.74              (k1_enumset1 @ X7 @ X8 @ X9)))),
% 12.49/12.74      inference('cnf', [status(esa)], [l62_enumset1])).
% 12.49/12.74  thf('46', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 12.49/12.74         ((k4_enumset1 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3)
% 12.49/12.74           = (k2_xboole_0 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0) @ 
% 12.49/12.74              (k1_enumset1 @ X5 @ X4 @ X3)))),
% 12.49/12.74      inference('sup+', [status(thm)], ['44', '45'])).
% 12.49/12.74  thf('47', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.49/12.74         ((k4_enumset1 @ X0 @ X0 @ X0 @ X3 @ X2 @ X1)
% 12.49/12.74           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_enumset1 @ X3 @ X2 @ X1)))),
% 12.49/12.74      inference('sup+', [status(thm)], ['43', '46'])).
% 12.49/12.74  thf('48', plain,
% 12.49/12.74      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 12.49/12.74         ((k4_enumset1 @ X40 @ X40 @ X41 @ X42 @ X43 @ X44)
% 12.49/12.74           = (k3_enumset1 @ X40 @ X41 @ X42 @ X43 @ X44))),
% 12.49/12.74      inference('cnf', [status(esa)], [t73_enumset1])).
% 12.49/12.74  thf('49', plain,
% 12.49/12.74      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 12.49/12.74         ((k3_enumset1 @ X36 @ X36 @ X37 @ X38 @ X39)
% 12.49/12.74           = (k2_enumset1 @ X36 @ X37 @ X38 @ X39))),
% 12.49/12.74      inference('cnf', [status(esa)], [t72_enumset1])).
% 12.49/12.74  thf('50', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.49/12.74         ((k2_enumset1 @ X0 @ X3 @ X2 @ X1)
% 12.49/12.74           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_enumset1 @ X3 @ X2 @ X1)))),
% 12.49/12.74      inference('demod', [status(thm)], ['47', '48', '49'])).
% 12.49/12.74  thf('51', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.49/12.74         ((k2_enumset1 @ X3 @ X1 @ X0 @ X2)
% 12.49/12.74           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 12.49/12.74      inference('sup+', [status(thm)], ['40', '50'])).
% 12.49/12.74  thf('52', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.49/12.74         ((k2_enumset1 @ X0 @ X3 @ X2 @ X1)
% 12.49/12.74           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_enumset1 @ X3 @ X2 @ X1)))),
% 12.49/12.74      inference('demod', [status(thm)], ['47', '48', '49'])).
% 12.49/12.74  thf('53', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.49/12.74         ((k2_enumset1 @ X3 @ X0 @ X2 @ X1) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 12.49/12.74      inference('sup+', [status(thm)], ['51', '52'])).
% 12.49/12.74  thf('54', plain,
% 12.49/12.74      (![X33 : $i, X34 : $i, X35 : $i]:
% 12.49/12.74         ((k2_enumset1 @ X33 @ X33 @ X34 @ X35)
% 12.49/12.74           = (k1_enumset1 @ X33 @ X34 @ X35))),
% 12.49/12.74      inference('cnf', [status(esa)], [t71_enumset1])).
% 12.49/12.74  thf('55', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.49/12.74         ((k2_enumset1 @ X1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 12.49/12.74      inference('sup+', [status(thm)], ['53', '54'])).
% 12.49/12.74  thf(t102_enumset1, axiom,
% 12.49/12.74    (![A:$i,B:$i,C:$i]:
% 12.49/12.74     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ C @ B @ A ) ))).
% 12.49/12.74  thf('56', plain,
% 12.49/12.74      (![X13 : $i, X14 : $i, X15 : $i]:
% 12.49/12.74         ((k1_enumset1 @ X15 @ X14 @ X13) = (k1_enumset1 @ X13 @ X14 @ X15))),
% 12.49/12.74      inference('cnf', [status(esa)], [t102_enumset1])).
% 12.49/12.74  thf('57', plain,
% 12.49/12.74      (![X10 : $i, X11 : $i, X12 : $i]:
% 12.49/12.74         ((k1_enumset1 @ X12 @ X10 @ X11) = (k1_enumset1 @ X10 @ X11 @ X12))),
% 12.49/12.74      inference('cnf', [status(esa)], [t100_enumset1])).
% 12.49/12.74  thf('58', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.49/12.74         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 12.49/12.74      inference('sup+', [status(thm)], ['56', '57'])).
% 12.49/12.74  thf('59', plain,
% 12.49/12.74      (![X33 : $i, X34 : $i, X35 : $i]:
% 12.49/12.74         ((k2_enumset1 @ X33 @ X33 @ X34 @ X35)
% 12.49/12.74           = (k1_enumset1 @ X33 @ X34 @ X35))),
% 12.49/12.74      inference('cnf', [status(esa)], [t71_enumset1])).
% 12.49/12.74  thf('60', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.49/12.74         ((k2_enumset1 @ X1 @ X1 @ X2 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 12.49/12.74      inference('sup+', [status(thm)], ['58', '59'])).
% 12.49/12.74  thf('61', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 12.49/12.74         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 12.49/12.74           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 12.49/12.74              (k1_tarski @ X4)))),
% 12.49/12.74      inference('demod', [status(thm)], ['30', '31'])).
% 12.49/12.74  thf('62', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.49/12.74         ((k3_enumset1 @ X1 @ X1 @ X2 @ X0 @ X3)
% 12.49/12.74           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 12.49/12.74      inference('sup+', [status(thm)], ['60', '61'])).
% 12.49/12.74  thf('63', plain,
% 12.49/12.74      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 12.49/12.74         ((k3_enumset1 @ X36 @ X36 @ X37 @ X38 @ X39)
% 12.49/12.74           = (k2_enumset1 @ X36 @ X37 @ X38 @ X39))),
% 12.49/12.74      inference('cnf', [status(esa)], [t72_enumset1])).
% 12.49/12.74  thf('64', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.49/12.74         ((k2_enumset1 @ X1 @ X2 @ X0 @ X3)
% 12.49/12.74           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 12.49/12.74      inference('demod', [status(thm)], ['62', '63'])).
% 12.49/12.74  thf('65', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.49/12.74         ((k2_enumset1 @ X0 @ X1 @ X2 @ X3)
% 12.49/12.74           = (k2_xboole_0 @ (k2_enumset1 @ X1 @ X2 @ X1 @ X0) @ 
% 12.49/12.74              (k1_tarski @ X3)))),
% 12.49/12.74      inference('sup+', [status(thm)], ['55', '64'])).
% 12.49/12.74  thf('66', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 12.49/12.74         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 12.49/12.74           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 12.49/12.74              (k1_tarski @ X4)))),
% 12.49/12.74      inference('demod', [status(thm)], ['30', '31'])).
% 12.49/12.74  thf('67', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.49/12.74         ((k2_enumset1 @ X0 @ X1 @ X2 @ X3)
% 12.49/12.74           = (k3_enumset1 @ X1 @ X2 @ X1 @ X0 @ X3))),
% 12.49/12.74      inference('demod', [status(thm)], ['65', '66'])).
% 12.49/12.74  thf('68', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.49/12.74         ((k2_enumset1 @ X0 @ X1 @ X1 @ X2) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 12.49/12.74      inference('demod', [status(thm)], ['38', '39', '67'])).
% 12.49/12.74  thf('69', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.49/12.74         ((k2_enumset1 @ X3 @ X0 @ X2 @ X1) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 12.49/12.74      inference('sup+', [status(thm)], ['51', '52'])).
% 12.49/12.74  thf('70', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.49/12.74         ((k2_enumset1 @ X1 @ X0 @ X2 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 12.49/12.74      inference('sup+', [status(thm)], ['68', '69'])).
% 12.49/12.74  thf('71', plain,
% 12.49/12.74      (![X33 : $i, X34 : $i, X35 : $i]:
% 12.49/12.74         ((k2_enumset1 @ X33 @ X33 @ X34 @ X35)
% 12.49/12.74           = (k1_enumset1 @ X33 @ X34 @ X35))),
% 12.49/12.74      inference('cnf', [status(esa)], [t71_enumset1])).
% 12.49/12.74  thf('72', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 12.49/12.74         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 12.49/12.74           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 12.49/12.74              (k1_tarski @ X4)))),
% 12.49/12.74      inference('demod', [status(thm)], ['30', '31'])).
% 12.49/12.74  thf('73', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.49/12.74         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3)
% 12.49/12.74           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 12.49/12.74      inference('sup+', [status(thm)], ['71', '72'])).
% 12.49/12.74  thf('74', plain,
% 12.49/12.74      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 12.49/12.74         ((k3_enumset1 @ X36 @ X36 @ X37 @ X38 @ X39)
% 12.49/12.74           = (k2_enumset1 @ X36 @ X37 @ X38 @ X39))),
% 12.49/12.74      inference('cnf', [status(esa)], [t72_enumset1])).
% 12.49/12.74  thf('75', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.49/12.74         ((k2_enumset1 @ X2 @ X1 @ X0 @ X3)
% 12.49/12.74           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 12.49/12.74      inference('demod', [status(thm)], ['73', '74'])).
% 12.49/12.74  thf('76', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.49/12.74         ((k2_enumset1 @ X0 @ X2 @ X1 @ X3)
% 12.49/12.74           = (k2_xboole_0 @ (k2_enumset1 @ X2 @ X1 @ X0 @ X0) @ 
% 12.49/12.74              (k1_tarski @ X3)))),
% 12.49/12.74      inference('sup+', [status(thm)], ['70', '75'])).
% 12.49/12.74  thf('77', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 12.49/12.74         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 12.49/12.74           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 12.49/12.74              (k1_tarski @ X4)))),
% 12.49/12.74      inference('demod', [status(thm)], ['30', '31'])).
% 12.49/12.74  thf('78', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.49/12.74         ((k2_enumset1 @ X0 @ X2 @ X1 @ X3)
% 12.49/12.74           = (k3_enumset1 @ X2 @ X1 @ X0 @ X0 @ X3))),
% 12.49/12.74      inference('demod', [status(thm)], ['76', '77'])).
% 12.49/12.74  thf('79', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.49/12.74         ((k2_enumset1 @ X0 @ X1 @ X1 @ X2) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 12.49/12.74      inference('demod', [status(thm)], ['38', '39', '67'])).
% 12.49/12.74  thf(t98_enumset1, axiom,
% 12.49/12.74    (![A:$i,B:$i,C:$i]:
% 12.49/12.74     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ A @ C @ B ) ))).
% 12.49/12.74  thf('80', plain,
% 12.49/12.74      (![X58 : $i, X59 : $i, X60 : $i]:
% 12.49/12.74         ((k1_enumset1 @ X58 @ X60 @ X59) = (k1_enumset1 @ X58 @ X59 @ X60))),
% 12.49/12.74      inference('cnf', [status(esa)], [t98_enumset1])).
% 12.49/12.74  thf('81', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.49/12.74         ((k1_enumset1 @ X1 @ X0 @ X2) = (k2_enumset1 @ X2 @ X1 @ X1 @ X0))),
% 12.49/12.74      inference('sup+', [status(thm)], ['79', '80'])).
% 12.49/12.74  thf('82', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.49/12.74         ((k2_enumset1 @ X3 @ X0 @ X2 @ X1) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 12.49/12.74      inference('sup+', [status(thm)], ['51', '52'])).
% 12.49/12.74  thf('83', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.49/12.74         ((k2_enumset1 @ X0 @ X1 @ X2 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 12.49/12.74      inference('sup+', [status(thm)], ['81', '82'])).
% 12.49/12.74  thf('84', plain,
% 12.49/12.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.49/12.74         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 12.49/12.74      inference('sup+', [status(thm)], ['56', '57'])).
% 12.49/12.74  thf('85', plain,
% 12.49/12.74      (![X58 : $i, X59 : $i, X60 : $i]:
% 12.49/12.74         ((k1_enumset1 @ X58 @ X60 @ X59) = (k1_enumset1 @ X58 @ X59 @ X60))),
% 12.49/12.74      inference('cnf', [status(esa)], [t98_enumset1])).
% 12.49/12.74  thf('86', plain,
% 12.49/12.74      (((k1_enumset1 @ sk_B @ sk_C @ sk_A)
% 12.49/12.74         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 12.49/12.74      inference('demod', [status(thm)], ['23', '78', '83', '84', '85'])).
% 12.49/12.74  thf('87', plain, ($false), inference('simplify', [status(thm)], ['86'])).
% 12.49/12.74  
% 12.49/12.74  % SZS output end Refutation
% 12.49/12.74  
% 12.49/12.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

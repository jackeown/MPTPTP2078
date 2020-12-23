%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.07pXBHDQvn

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:31 EST 2020

% Result     : Theorem 7.42s
% Output     : Refutation 7.42s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 295 expanded)
%              Number of leaves         :   22 ( 106 expanded)
%              Depth                    :   15
%              Number of atoms          : 1223 (3420 expanded)
%              Number of equality atoms :  103 ( 283 expanded)
%              Maximal formula depth    :   16 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_tarski @ X3 @ X2 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('2',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k2_enumset1 @ X31 @ X31 @ X32 @ X33 )
      = ( k1_enumset1 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_enumset1 @ X29 @ X29 @ X30 )
      = ( k2_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('5',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37 )
      = ( k2_enumset1 @ X34 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t55_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k4_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 ) @ ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t55_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('9',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k4_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 @ X42 )
      = ( k3_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('10',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37 )
      = ( k2_enumset1 @ X34 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k2_enumset1 @ X31 @ X31 @ X32 @ X33 )
      = ( k1_enumset1 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k2_tarski @ sk_C @ sk_A ) )
 != ( k1_enumset1 @ sk_B @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['0','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('20',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37 )
      = ( k2_enumset1 @ X34 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t60_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ) )).

thf('21',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k5_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 ) @ ( k2_tarski @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t60_enumset1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X5 @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k5_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('25',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( k5_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 )
      = ( k4_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k5_enumset1 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,(
    ( k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['18','27'])).

thf('29',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_tarski @ X3 @ X2 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('30',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_enumset1 @ X29 @ X29 @ X30 )
      = ( k2_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('31',plain,(
    ! [X28: $i] :
      ( ( k2_tarski @ X28 @ X28 )
      = ( k1_tarski @ X28 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k2_enumset1 @ X31 @ X31 @ X32 @ X33 )
      = ( k1_enumset1 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X5 @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k5_enumset1 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k2_enumset1 @ X31 @ X31 @ X32 @ X33 )
      = ( k1_enumset1 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ( k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['28','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(t47_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ) )).

thf('46',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_enumset1 @ X5 @ X6 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X1 @ X0 @ X0 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X1 @ X0 @ X0 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['47','54'])).

thf('56',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( k5_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 )
      = ( k4_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('57',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k4_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 @ X42 )
      = ( k3_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X28: $i] :
      ( ( k2_tarski @ X28 @ X28 )
      = ( k1_tarski @ X28 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('60',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k5_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 ) @ ( k2_tarski @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t60_enumset1])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k4_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 ) @ ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t55_enumset1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['55','66'])).

thf('68',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_tarski @ X3 @ X2 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('69',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_enumset1 @ X29 @ X29 @ X30 )
      = ( k2_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('70',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k2_enumset1 @ X31 @ X31 @ X32 @ X33 )
      = ( k1_enumset1 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('71',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_enumset1 @ X5 @ X6 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37 )
      = ( k2_enumset1 @ X34 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['69','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['68','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_enumset1 @ X1 @ X0 @ X0 @ X0 ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['67','78'])).

thf('80',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_enumset1 @ X5 @ X6 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_tarski @ X3 @ X2 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_enumset1 @ X0 @ X1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_enumset1 @ X0 @ X1 @ X0 @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_enumset1 @ X5 @ X6 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,(
    ( k1_enumset1 @ sk_B @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['44','89'])).

thf('91',plain,(
    $false ),
    inference(simplify,[status(thm)],['90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.07pXBHDQvn
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:02:33 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 7.42/7.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 7.42/7.59  % Solved by: fo/fo7.sh
% 7.42/7.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.42/7.59  % done 5921 iterations in 7.132s
% 7.42/7.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 7.42/7.59  % SZS output start Refutation
% 7.42/7.59  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 7.42/7.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 7.42/7.59  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 7.42/7.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 7.42/7.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 7.42/7.59  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 7.42/7.59  thf(sk_C_type, type, sk_C: $i).
% 7.42/7.59  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 7.42/7.59  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 7.42/7.59  thf(sk_B_type, type, sk_B: $i).
% 7.42/7.59  thf(sk_A_type, type, sk_A: $i).
% 7.42/7.59  thf(t137_enumset1, conjecture,
% 7.42/7.59    (![A:$i,B:$i,C:$i]:
% 7.42/7.59     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 7.42/7.59       ( k1_enumset1 @ A @ B @ C ) ))).
% 7.42/7.59  thf(zf_stmt_0, negated_conjecture,
% 7.42/7.59    (~( ![A:$i,B:$i,C:$i]:
% 7.42/7.59        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 7.42/7.59          ( k1_enumset1 @ A @ B @ C ) ) )),
% 7.42/7.59    inference('cnf.neg', [status(esa)], [t137_enumset1])).
% 7.42/7.59  thf('0', plain,
% 7.42/7.59      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 7.42/7.59         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 7.42/7.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.59  thf(commutativity_k2_tarski, axiom,
% 7.42/7.59    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 7.42/7.59  thf('1', plain,
% 7.42/7.59      (![X2 : $i, X3 : $i]: ((k2_tarski @ X3 @ X2) = (k2_tarski @ X2 @ X3))),
% 7.42/7.59      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 7.42/7.59  thf(t71_enumset1, axiom,
% 7.42/7.59    (![A:$i,B:$i,C:$i]:
% 7.42/7.59     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 7.42/7.59  thf('2', plain,
% 7.42/7.59      (![X31 : $i, X32 : $i, X33 : $i]:
% 7.42/7.59         ((k2_enumset1 @ X31 @ X31 @ X32 @ X33)
% 7.42/7.59           = (k1_enumset1 @ X31 @ X32 @ X33))),
% 7.42/7.59      inference('cnf', [status(esa)], [t71_enumset1])).
% 7.42/7.59  thf(t70_enumset1, axiom,
% 7.42/7.59    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 7.42/7.59  thf('3', plain,
% 7.42/7.59      (![X29 : $i, X30 : $i]:
% 7.42/7.59         ((k1_enumset1 @ X29 @ X29 @ X30) = (k2_tarski @ X29 @ X30))),
% 7.42/7.59      inference('cnf', [status(esa)], [t70_enumset1])).
% 7.42/7.59  thf('4', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i]:
% 7.42/7.59         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 7.42/7.59      inference('sup+', [status(thm)], ['2', '3'])).
% 7.42/7.59  thf(t72_enumset1, axiom,
% 7.42/7.59    (![A:$i,B:$i,C:$i,D:$i]:
% 7.42/7.59     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 7.42/7.59  thf('5', plain,
% 7.42/7.59      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 7.42/7.59         ((k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37)
% 7.42/7.59           = (k2_enumset1 @ X34 @ X35 @ X36 @ X37))),
% 7.42/7.59      inference('cnf', [status(esa)], [t72_enumset1])).
% 7.42/7.59  thf(t55_enumset1, axiom,
% 7.42/7.59    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 7.42/7.59     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 7.42/7.59       ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ))).
% 7.42/7.59  thf('6', plain,
% 7.42/7.59      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 7.42/7.59         ((k4_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20)
% 7.42/7.59           = (k2_xboole_0 @ (k3_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19) @ 
% 7.42/7.59              (k1_tarski @ X20)))),
% 7.42/7.59      inference('cnf', [status(esa)], [t55_enumset1])).
% 7.42/7.59  thf('7', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 7.42/7.59         ((k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4)
% 7.42/7.59           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 7.42/7.59              (k1_tarski @ X4)))),
% 7.42/7.59      inference('sup+', [status(thm)], ['5', '6'])).
% 7.42/7.59  thf('8', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.42/7.59         ((k4_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 @ X2)
% 7.42/7.59           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 7.42/7.59      inference('sup+', [status(thm)], ['4', '7'])).
% 7.42/7.59  thf(t73_enumset1, axiom,
% 7.42/7.59    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 7.42/7.59     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 7.42/7.59       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 7.42/7.59  thf('9', plain,
% 7.42/7.59      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 7.42/7.59         ((k4_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 @ X42)
% 7.42/7.59           = (k3_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42))),
% 7.42/7.59      inference('cnf', [status(esa)], [t73_enumset1])).
% 7.42/7.59  thf('10', plain,
% 7.42/7.59      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 7.42/7.59         ((k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37)
% 7.42/7.59           = (k2_enumset1 @ X34 @ X35 @ X36 @ X37))),
% 7.42/7.59      inference('cnf', [status(esa)], [t72_enumset1])).
% 7.42/7.59  thf('11', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.42/7.59         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 7.42/7.59           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 7.42/7.59      inference('sup+', [status(thm)], ['9', '10'])).
% 7.42/7.59  thf('12', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.42/7.59         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 7.42/7.59           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 7.42/7.59      inference('demod', [status(thm)], ['8', '11'])).
% 7.42/7.59  thf('13', plain,
% 7.42/7.59      (![X31 : $i, X32 : $i, X33 : $i]:
% 7.42/7.59         ((k2_enumset1 @ X31 @ X31 @ X32 @ X33)
% 7.42/7.59           = (k1_enumset1 @ X31 @ X32 @ X33))),
% 7.42/7.59      inference('cnf', [status(esa)], [t71_enumset1])).
% 7.42/7.59  thf('14', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.42/7.59         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 7.42/7.59           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 7.42/7.59      inference('sup+', [status(thm)], ['12', '13'])).
% 7.42/7.59  thf('15', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.42/7.59         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2))
% 7.42/7.59           = (k1_enumset1 @ X0 @ X1 @ X2))),
% 7.42/7.59      inference('sup+', [status(thm)], ['1', '14'])).
% 7.42/7.59  thf('16', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.42/7.59         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 7.42/7.59           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 7.42/7.59      inference('sup+', [status(thm)], ['12', '13'])).
% 7.42/7.59  thf('17', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.42/7.59         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 7.42/7.59      inference('sup+', [status(thm)], ['15', '16'])).
% 7.42/7.59  thf('18', plain,
% 7.42/7.59      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 7.42/7.59         != (k1_enumset1 @ sk_B @ sk_A @ sk_C))),
% 7.42/7.59      inference('demod', [status(thm)], ['0', '17'])).
% 7.42/7.59  thf('19', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i]:
% 7.42/7.59         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 7.42/7.59      inference('sup+', [status(thm)], ['2', '3'])).
% 7.42/7.59  thf('20', plain,
% 7.42/7.59      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 7.42/7.59         ((k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37)
% 7.42/7.59           = (k2_enumset1 @ X34 @ X35 @ X36 @ X37))),
% 7.42/7.59      inference('cnf', [status(esa)], [t72_enumset1])).
% 7.42/7.59  thf(t60_enumset1, axiom,
% 7.42/7.59    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 7.42/7.59     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 7.42/7.59       ( k2_xboole_0 @
% 7.42/7.59         ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ))).
% 7.42/7.59  thf('21', plain,
% 7.42/7.59      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 7.42/7.59         ((k5_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27)
% 7.42/7.59           = (k2_xboole_0 @ (k3_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25) @ 
% 7.42/7.59              (k2_tarski @ X26 @ X27)))),
% 7.42/7.59      inference('cnf', [status(esa)], [t60_enumset1])).
% 7.42/7.59  thf('22', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 7.42/7.59         ((k5_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4)
% 7.42/7.59           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 7.42/7.59              (k2_tarski @ X5 @ X4)))),
% 7.42/7.59      inference('sup+', [status(thm)], ['20', '21'])).
% 7.42/7.59  thf('23', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.42/7.59         ((k5_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 @ X3 @ X2)
% 7.42/7.59           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 7.42/7.59      inference('sup+', [status(thm)], ['19', '22'])).
% 7.42/7.59  thf('24', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.42/7.59         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 7.42/7.59           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 7.42/7.59      inference('sup+', [status(thm)], ['9', '10'])).
% 7.42/7.59  thf(t74_enumset1, axiom,
% 7.42/7.59    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 7.42/7.59     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 7.42/7.59       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 7.42/7.59  thf('25', plain,
% 7.42/7.59      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 7.42/7.59         ((k5_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48)
% 7.42/7.59           = (k4_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48))),
% 7.42/7.59      inference('cnf', [status(esa)], [t74_enumset1])).
% 7.42/7.59  thf('26', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.42/7.59         ((k5_enumset1 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 7.42/7.59           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 7.42/7.59      inference('sup+', [status(thm)], ['24', '25'])).
% 7.42/7.59  thf('27', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.42/7.59         ((k2_enumset1 @ X1 @ X0 @ X3 @ X2)
% 7.42/7.59           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 7.42/7.59      inference('demod', [status(thm)], ['23', '26'])).
% 7.42/7.59  thf('28', plain,
% 7.42/7.59      (((k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A)
% 7.42/7.59         != (k1_enumset1 @ sk_B @ sk_A @ sk_C))),
% 7.42/7.59      inference('demod', [status(thm)], ['18', '27'])).
% 7.42/7.59  thf('29', plain,
% 7.42/7.59      (![X2 : $i, X3 : $i]: ((k2_tarski @ X3 @ X2) = (k2_tarski @ X2 @ X3))),
% 7.42/7.59      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 7.42/7.59  thf('30', plain,
% 7.42/7.59      (![X29 : $i, X30 : $i]:
% 7.42/7.59         ((k1_enumset1 @ X29 @ X29 @ X30) = (k2_tarski @ X29 @ X30))),
% 7.42/7.59      inference('cnf', [status(esa)], [t70_enumset1])).
% 7.42/7.59  thf(t69_enumset1, axiom,
% 7.42/7.59    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 7.42/7.59  thf('31', plain,
% 7.42/7.59      (![X28 : $i]: ((k2_tarski @ X28 @ X28) = (k1_tarski @ X28))),
% 7.42/7.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 7.42/7.59  thf('32', plain,
% 7.42/7.59      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 7.42/7.59      inference('sup+', [status(thm)], ['30', '31'])).
% 7.42/7.59  thf('33', plain,
% 7.42/7.59      (![X31 : $i, X32 : $i, X33 : $i]:
% 7.42/7.59         ((k2_enumset1 @ X31 @ X31 @ X32 @ X33)
% 7.42/7.59           = (k1_enumset1 @ X31 @ X32 @ X33))),
% 7.42/7.59      inference('cnf', [status(esa)], [t71_enumset1])).
% 7.42/7.59  thf('34', plain,
% 7.42/7.59      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 7.42/7.59      inference('sup+', [status(thm)], ['32', '33'])).
% 7.42/7.59  thf('35', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 7.42/7.59         ((k5_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4)
% 7.42/7.59           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 7.42/7.59              (k2_tarski @ X5 @ X4)))),
% 7.42/7.59      inference('sup+', [status(thm)], ['20', '21'])).
% 7.42/7.59  thf('36', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.42/7.59         ((k5_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X2 @ X1)
% 7.42/7.59           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 7.42/7.59      inference('sup+', [status(thm)], ['34', '35'])).
% 7.42/7.59  thf('37', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.42/7.59         ((k5_enumset1 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 7.42/7.59           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 7.42/7.59      inference('sup+', [status(thm)], ['24', '25'])).
% 7.42/7.59  thf('38', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.42/7.59         ((k2_enumset1 @ X0 @ X0 @ X2 @ X1)
% 7.42/7.59           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 7.42/7.59      inference('demod', [status(thm)], ['36', '37'])).
% 7.42/7.59  thf('39', plain,
% 7.42/7.59      (![X31 : $i, X32 : $i, X33 : $i]:
% 7.42/7.59         ((k2_enumset1 @ X31 @ X31 @ X32 @ X33)
% 7.42/7.59           = (k1_enumset1 @ X31 @ X32 @ X33))),
% 7.42/7.59      inference('cnf', [status(esa)], [t71_enumset1])).
% 7.42/7.59  thf('40', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.42/7.59         ((k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0))
% 7.42/7.59           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 7.42/7.59      inference('sup+', [status(thm)], ['38', '39'])).
% 7.42/7.59  thf('41', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.42/7.59         ((k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0))
% 7.42/7.59           = (k1_enumset1 @ X2 @ X0 @ X1))),
% 7.42/7.59      inference('sup+', [status(thm)], ['29', '40'])).
% 7.42/7.59  thf('42', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.42/7.59         ((k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0))
% 7.42/7.59           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 7.42/7.59      inference('sup+', [status(thm)], ['38', '39'])).
% 7.42/7.59  thf('43', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.42/7.59         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 7.42/7.59      inference('sup+', [status(thm)], ['41', '42'])).
% 7.42/7.59  thf('44', plain,
% 7.42/7.59      (((k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A)
% 7.42/7.59         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 7.42/7.59      inference('demod', [status(thm)], ['28', '43'])).
% 7.42/7.59  thf('45', plain,
% 7.42/7.59      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 7.42/7.59      inference('sup+', [status(thm)], ['32', '33'])).
% 7.42/7.59  thf(t47_enumset1, axiom,
% 7.42/7.59    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 7.42/7.59     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 7.42/7.59       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ))).
% 7.42/7.59  thf('46', plain,
% 7.42/7.59      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 7.42/7.59         ((k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8)
% 7.42/7.59           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 7.42/7.59              (k2_enumset1 @ X5 @ X6 @ X7 @ X8)))),
% 7.42/7.59      inference('cnf', [status(esa)], [t47_enumset1])).
% 7.42/7.59  thf('47', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i]:
% 7.42/7.59         ((k3_enumset1 @ X1 @ X0 @ X0 @ X0 @ X0)
% 7.42/7.59           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 7.42/7.59      inference('sup+', [status(thm)], ['45', '46'])).
% 7.42/7.59  thf('48', plain,
% 7.42/7.59      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 7.42/7.59      inference('sup+', [status(thm)], ['32', '33'])).
% 7.42/7.59  thf('49', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 7.42/7.59         ((k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4)
% 7.42/7.59           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 7.42/7.59              (k1_tarski @ X4)))),
% 7.42/7.59      inference('sup+', [status(thm)], ['5', '6'])).
% 7.42/7.59  thf('50', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i]:
% 7.42/7.59         ((k4_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X1)
% 7.42/7.59           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 7.42/7.59      inference('sup+', [status(thm)], ['48', '49'])).
% 7.42/7.59  thf('51', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.42/7.59         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 7.42/7.59           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 7.42/7.59      inference('sup+', [status(thm)], ['9', '10'])).
% 7.42/7.59  thf('52', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i]:
% 7.42/7.59         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 7.42/7.59           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 7.42/7.59      inference('demod', [status(thm)], ['50', '51'])).
% 7.42/7.59  thf('53', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i]:
% 7.42/7.59         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 7.42/7.59      inference('sup+', [status(thm)], ['2', '3'])).
% 7.42/7.59  thf('54', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i]:
% 7.42/7.59         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 7.42/7.59           = (k2_tarski @ X1 @ X0))),
% 7.42/7.59      inference('sup+', [status(thm)], ['52', '53'])).
% 7.42/7.59  thf('55', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i]:
% 7.42/7.59         ((k3_enumset1 @ X1 @ X0 @ X0 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 7.42/7.59      inference('demod', [status(thm)], ['47', '54'])).
% 7.42/7.59  thf('56', plain,
% 7.42/7.59      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 7.42/7.59         ((k5_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48)
% 7.42/7.59           = (k4_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48))),
% 7.42/7.59      inference('cnf', [status(esa)], [t74_enumset1])).
% 7.42/7.59  thf('57', plain,
% 7.42/7.59      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 7.42/7.59         ((k4_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 @ X42)
% 7.42/7.59           = (k3_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42))),
% 7.42/7.59      inference('cnf', [status(esa)], [t73_enumset1])).
% 7.42/7.59  thf('58', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 7.42/7.59         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 7.42/7.59           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 7.42/7.59      inference('sup+', [status(thm)], ['56', '57'])).
% 7.42/7.59  thf('59', plain,
% 7.42/7.59      (![X28 : $i]: ((k2_tarski @ X28 @ X28) = (k1_tarski @ X28))),
% 7.42/7.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 7.42/7.59  thf('60', plain,
% 7.42/7.59      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 7.42/7.59         ((k5_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27)
% 7.42/7.59           = (k2_xboole_0 @ (k3_enumset1 @ X21 @ X22 @ X23 @ X24 @ X25) @ 
% 7.42/7.59              (k2_tarski @ X26 @ X27)))),
% 7.42/7.59      inference('cnf', [status(esa)], [t60_enumset1])).
% 7.42/7.59  thf('61', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 7.42/7.59         ((k5_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 7.42/7.59           = (k2_xboole_0 @ (k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 7.42/7.59              (k1_tarski @ X0)))),
% 7.42/7.59      inference('sup+', [status(thm)], ['59', '60'])).
% 7.42/7.59  thf('62', plain,
% 7.42/7.59      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 7.42/7.59         ((k4_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 @ X20)
% 7.42/7.59           = (k2_xboole_0 @ (k3_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19) @ 
% 7.42/7.59              (k1_tarski @ X20)))),
% 7.42/7.59      inference('cnf', [status(esa)], [t55_enumset1])).
% 7.42/7.59  thf('63', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 7.42/7.59         ((k5_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 7.42/7.59           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 7.42/7.59      inference('demod', [status(thm)], ['61', '62'])).
% 7.42/7.59  thf('64', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.42/7.59         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0)
% 7.42/7.59           = (k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0))),
% 7.42/7.59      inference('sup+', [status(thm)], ['58', '63'])).
% 7.42/7.59  thf('65', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.42/7.59         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 7.42/7.59           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 7.42/7.59      inference('sup+', [status(thm)], ['9', '10'])).
% 7.42/7.59  thf('66', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.42/7.59         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0)
% 7.42/7.59           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 7.42/7.59      inference('demod', [status(thm)], ['64', '65'])).
% 7.42/7.59  thf('67', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i]:
% 7.42/7.59         ((k2_enumset1 @ X1 @ X0 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 7.42/7.59      inference('demod', [status(thm)], ['55', '66'])).
% 7.42/7.59  thf('68', plain,
% 7.42/7.59      (![X2 : $i, X3 : $i]: ((k2_tarski @ X3 @ X2) = (k2_tarski @ X2 @ X3))),
% 7.42/7.59      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 7.42/7.59  thf('69', plain,
% 7.42/7.59      (![X29 : $i, X30 : $i]:
% 7.42/7.59         ((k1_enumset1 @ X29 @ X29 @ X30) = (k2_tarski @ X29 @ X30))),
% 7.42/7.59      inference('cnf', [status(esa)], [t70_enumset1])).
% 7.42/7.59  thf('70', plain,
% 7.42/7.59      (![X31 : $i, X32 : $i, X33 : $i]:
% 7.42/7.59         ((k2_enumset1 @ X31 @ X31 @ X32 @ X33)
% 7.42/7.59           = (k1_enumset1 @ X31 @ X32 @ X33))),
% 7.42/7.59      inference('cnf', [status(esa)], [t71_enumset1])).
% 7.42/7.59  thf('71', plain,
% 7.42/7.59      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 7.42/7.59         ((k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8)
% 7.42/7.59           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 7.42/7.59              (k2_enumset1 @ X5 @ X6 @ X7 @ X8)))),
% 7.42/7.59      inference('cnf', [status(esa)], [t47_enumset1])).
% 7.42/7.59  thf('72', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.42/7.59         ((k3_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0)
% 7.42/7.59           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 7.42/7.59      inference('sup+', [status(thm)], ['70', '71'])).
% 7.42/7.59  thf('73', plain,
% 7.42/7.59      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 7.42/7.59         ((k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37)
% 7.42/7.59           = (k2_enumset1 @ X34 @ X35 @ X36 @ X37))),
% 7.42/7.59      inference('cnf', [status(esa)], [t72_enumset1])).
% 7.42/7.59  thf('74', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.42/7.59         ((k2_xboole_0 @ (k1_tarski @ X2) @ (k1_enumset1 @ X2 @ X1 @ X0))
% 7.42/7.59           = (k2_enumset1 @ X2 @ X2 @ X1 @ X0))),
% 7.42/7.59      inference('sup+', [status(thm)], ['72', '73'])).
% 7.42/7.59  thf('75', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i]:
% 7.42/7.59         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 7.42/7.59           = (k2_enumset1 @ X1 @ X1 @ X1 @ X0))),
% 7.42/7.59      inference('sup+', [status(thm)], ['69', '74'])).
% 7.42/7.59  thf('76', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i]:
% 7.42/7.59         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 7.42/7.59      inference('sup+', [status(thm)], ['2', '3'])).
% 7.42/7.59  thf('77', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i]:
% 7.42/7.59         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 7.42/7.59           = (k2_tarski @ X1 @ X0))),
% 7.42/7.59      inference('sup+', [status(thm)], ['75', '76'])).
% 7.42/7.59  thf('78', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i]:
% 7.42/7.59         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))
% 7.42/7.59           = (k2_tarski @ X0 @ X1))),
% 7.42/7.59      inference('sup+', [status(thm)], ['68', '77'])).
% 7.42/7.59  thf('79', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i]:
% 7.42/7.59         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k2_enumset1 @ X1 @ X0 @ X0 @ X0))
% 7.42/7.59           = (k2_tarski @ X0 @ X1))),
% 7.42/7.59      inference('sup+', [status(thm)], ['67', '78'])).
% 7.42/7.59  thf('80', plain,
% 7.42/7.59      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 7.42/7.59         ((k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8)
% 7.42/7.59           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 7.42/7.59              (k2_enumset1 @ X5 @ X6 @ X7 @ X8)))),
% 7.42/7.59      inference('cnf', [status(esa)], [t47_enumset1])).
% 7.42/7.59  thf('81', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.42/7.59         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0)
% 7.42/7.59           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 7.42/7.59      inference('demod', [status(thm)], ['64', '65'])).
% 7.42/7.59  thf('82', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i]:
% 7.42/7.59         ((k2_enumset1 @ X0 @ X1 @ X0 @ X0) = (k2_tarski @ X0 @ X1))),
% 7.42/7.59      inference('demod', [status(thm)], ['79', '80', '81'])).
% 7.42/7.59  thf('83', plain,
% 7.42/7.59      (![X2 : $i, X3 : $i]: ((k2_tarski @ X3 @ X2) = (k2_tarski @ X2 @ X3))),
% 7.42/7.59      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 7.42/7.59  thf('84', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i]:
% 7.42/7.59         ((k2_tarski @ X1 @ X0) = (k2_enumset1 @ X0 @ X1 @ X0 @ X0))),
% 7.42/7.59      inference('sup+', [status(thm)], ['82', '83'])).
% 7.42/7.59  thf('85', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.42/7.59         ((k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0))
% 7.42/7.59           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 7.42/7.59      inference('sup+', [status(thm)], ['38', '39'])).
% 7.42/7.59  thf('86', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.42/7.59         ((k2_xboole_0 @ (k1_tarski @ X2) @ (k2_enumset1 @ X0 @ X1 @ X0 @ X0))
% 7.42/7.59           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 7.42/7.59      inference('sup+', [status(thm)], ['84', '85'])).
% 7.42/7.59  thf('87', plain,
% 7.42/7.59      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 7.42/7.59         ((k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8)
% 7.42/7.59           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 7.42/7.59              (k2_enumset1 @ X5 @ X6 @ X7 @ X8)))),
% 7.42/7.59      inference('cnf', [status(esa)], [t47_enumset1])).
% 7.42/7.59  thf('88', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.42/7.59         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0)
% 7.42/7.59           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 7.42/7.59      inference('demod', [status(thm)], ['64', '65'])).
% 7.42/7.59  thf('89', plain,
% 7.42/7.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.42/7.59         ((k2_enumset1 @ X2 @ X0 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 7.42/7.59      inference('demod', [status(thm)], ['86', '87', '88'])).
% 7.42/7.59  thf('90', plain,
% 7.42/7.59      (((k1_enumset1 @ sk_B @ sk_C @ sk_A)
% 7.42/7.59         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 7.42/7.59      inference('demod', [status(thm)], ['44', '89'])).
% 7.42/7.59  thf('91', plain, ($false), inference('simplify', [status(thm)], ['90'])).
% 7.42/7.59  
% 7.42/7.59  % SZS output end Refutation
% 7.42/7.59  
% 7.42/7.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

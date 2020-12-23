%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.26N2fBlrzr

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:47 EST 2020

% Result     : Theorem 5.34s
% Output     : Refutation 5.34s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 254 expanded)
%              Number of leaves         :   34 (  97 expanded)
%              Depth                    :   18
%              Number of atoms          :  825 (2076 expanded)
%              Number of equality atoms :   85 ( 230 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t63_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
     => ( r2_hidden @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          = ( k2_tarski @ A @ B ) )
       => ( r2_hidden @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t63_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X12 @ X13 ) @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k5_xboole_0 @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k5_xboole_0 @ X13 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('6',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k5_xboole_0 @ X13 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('10',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('12',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k5_xboole_0 @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','16'])).

thf('18',plain,
    ( ( k5_xboole_0 @ sk_C @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['1','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('20',plain,
    ( ( k5_xboole_0 @ sk_C @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('22',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = ( k5_xboole_0 @ sk_C @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('25',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['22','23','24'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('26',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37 )
      = ( k2_enumset1 @ X34 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t55_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ) )).

thf('27',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k4_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 ) @ ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t55_enumset1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('29',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k4_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 @ X42 )
      = ( k3_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('30',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37 )
      = ( k2_enumset1 @ X34 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('32',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k2_enumset1 @ X31 @ X31 @ X32 @ X33 )
      = ( k1_enumset1 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('33',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_enumset1 @ X29 @ X29 @ X30 )
      = ( k2_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_enumset1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X1 @ X1 @ X1 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','35'])).

thf('37',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_enumset1 @ X29 @ X29 @ X30 )
      = ( k2_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('38',plain,(
    ! [X28: $i] :
      ( ( k2_tarski @ X28 @ X28 )
      = ( k1_tarski @ X28 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k2_enumset1 @ X31 @ X31 @ X32 @ X33 )
      = ( k1_enumset1 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['36','41'])).

thf(t102_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ C @ B @ A ) ) )).

thf('43',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k1_enumset1 @ X21 @ X20 @ X19 )
      = ( k1_enumset1 @ X19 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t102_enumset1])).

thf('44',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_enumset1 @ X29 @ X29 @ X30 )
      = ( k2_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k2_enumset1 @ X31 @ X31 @ X32 @ X33 )
      = ( k1_enumset1 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X1 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf(l57_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) )).

thf('49',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X14 @ X15 @ X16 ) @ ( k2_tarski @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[l57_enumset1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37 )
      = ( k2_enumset1 @ X34 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['47','52'])).

thf('54',plain,(
    ! [X28: $i] :
      ( ( k2_tarski @ X28 @ X28 )
      = ( k1_tarski @ X28 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','55'])).

thf('57',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['25','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','55'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('59',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X43 @ X44 ) )
      = ( k2_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X43 @ X44 ) )
      = ( k2_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_B @ sk_A ) )
    = sk_C ),
    inference(demod,[status(thm)],['57','62'])).

thf('64',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k5_xboole_0 @ X13 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('65',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k2_tarski @ sk_B @ sk_A ) )
    = ( k5_xboole_0 @ sk_C @ ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('68',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k2_tarski @ sk_B @ sk_A ) )
    = ( k2_tarski @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('69',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('70',plain,(
    r1_tarski @ ( k2_tarski @ sk_B @ sk_A ) @ sk_C ),
    inference('sup+',[status(thm)],['68','69'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('71',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( r2_hidden @ X47 @ X46 )
      | ~ ( r1_tarski @ ( k2_tarski @ X45 @ X47 ) @ X46 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('72',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    $false ),
    inference(demod,[status(thm)],['0','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.26N2fBlrzr
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:35:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 5.34/5.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.34/5.57  % Solved by: fo/fo7.sh
% 5.34/5.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.34/5.57  % done 2549 iterations in 5.127s
% 5.34/5.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.34/5.57  % SZS output start Refutation
% 5.34/5.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 5.34/5.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 5.34/5.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.34/5.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.34/5.57  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 5.34/5.57  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 5.34/5.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.34/5.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 5.34/5.57  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 5.34/5.57  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 5.34/5.57  thf(sk_B_type, type, sk_B: $i).
% 5.34/5.57  thf(sk_C_type, type, sk_C: $i).
% 5.34/5.57  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 5.34/5.57  thf(sk_A_type, type, sk_A: $i).
% 5.34/5.57  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 5.34/5.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 5.34/5.57  thf(t63_zfmisc_1, conjecture,
% 5.34/5.57    (![A:$i,B:$i,C:$i]:
% 5.34/5.57     ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) =>
% 5.34/5.57       ( r2_hidden @ A @ C ) ))).
% 5.34/5.57  thf(zf_stmt_0, negated_conjecture,
% 5.34/5.57    (~( ![A:$i,B:$i,C:$i]:
% 5.34/5.57        ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) =>
% 5.34/5.57          ( r2_hidden @ A @ C ) ) )),
% 5.34/5.57    inference('cnf.neg', [status(esa)], [t63_zfmisc_1])).
% 5.34/5.57  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 5.34/5.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.34/5.57  thf('1', plain,
% 5.34/5.57      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 5.34/5.57         = (k2_tarski @ sk_A @ sk_B))),
% 5.34/5.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.34/5.57  thf(t95_xboole_1, axiom,
% 5.34/5.57    (![A:$i,B:$i]:
% 5.34/5.57     ( ( k3_xboole_0 @ A @ B ) =
% 5.34/5.57       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 5.34/5.57  thf('2', plain,
% 5.34/5.57      (![X12 : $i, X13 : $i]:
% 5.34/5.57         ((k3_xboole_0 @ X12 @ X13)
% 5.34/5.57           = (k5_xboole_0 @ (k5_xboole_0 @ X12 @ X13) @ 
% 5.34/5.57              (k2_xboole_0 @ X12 @ X13)))),
% 5.34/5.57      inference('cnf', [status(esa)], [t95_xboole_1])).
% 5.34/5.57  thf(t91_xboole_1, axiom,
% 5.34/5.57    (![A:$i,B:$i,C:$i]:
% 5.34/5.57     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 5.34/5.57       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 5.34/5.57  thf('3', plain,
% 5.34/5.57      (![X9 : $i, X10 : $i, X11 : $i]:
% 5.34/5.57         ((k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ X11)
% 5.34/5.57           = (k5_xboole_0 @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 5.34/5.57      inference('cnf', [status(esa)], [t91_xboole_1])).
% 5.34/5.57  thf('4', plain,
% 5.34/5.57      (![X12 : $i, X13 : $i]:
% 5.34/5.57         ((k3_xboole_0 @ X12 @ X13)
% 5.34/5.57           = (k5_xboole_0 @ X12 @ 
% 5.34/5.57              (k5_xboole_0 @ X13 @ (k2_xboole_0 @ X12 @ X13))))),
% 5.34/5.57      inference('demod', [status(thm)], ['2', '3'])).
% 5.34/5.57  thf(commutativity_k5_xboole_0, axiom,
% 5.34/5.57    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 5.34/5.57  thf('5', plain,
% 5.34/5.57      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 5.34/5.57      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 5.34/5.57  thf(t5_boole, axiom,
% 5.34/5.57    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 5.34/5.57  thf('6', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 5.34/5.57      inference('cnf', [status(esa)], [t5_boole])).
% 5.34/5.57  thf('7', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 5.34/5.57      inference('sup+', [status(thm)], ['5', '6'])).
% 5.34/5.57  thf('8', plain,
% 5.34/5.57      (![X12 : $i, X13 : $i]:
% 5.34/5.57         ((k3_xboole_0 @ X12 @ X13)
% 5.34/5.57           = (k5_xboole_0 @ X12 @ 
% 5.34/5.57              (k5_xboole_0 @ X13 @ (k2_xboole_0 @ X12 @ X13))))),
% 5.34/5.57      inference('demod', [status(thm)], ['2', '3'])).
% 5.34/5.57  thf('9', plain,
% 5.34/5.57      (![X0 : $i]:
% 5.34/5.57         ((k3_xboole_0 @ X0 @ k1_xboole_0)
% 5.34/5.57           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 5.34/5.57      inference('sup+', [status(thm)], ['7', '8'])).
% 5.34/5.57  thf(t2_boole, axiom,
% 5.34/5.57    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 5.34/5.57  thf('10', plain,
% 5.34/5.57      (![X7 : $i]: ((k3_xboole_0 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 5.34/5.57      inference('cnf', [status(esa)], [t2_boole])).
% 5.34/5.57  thf(t1_boole, axiom,
% 5.34/5.57    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 5.34/5.57  thf('11', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 5.34/5.57      inference('cnf', [status(esa)], [t1_boole])).
% 5.34/5.57  thf('12', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 5.34/5.57      inference('demod', [status(thm)], ['9', '10', '11'])).
% 5.34/5.57  thf('13', plain,
% 5.34/5.57      (![X9 : $i, X10 : $i, X11 : $i]:
% 5.34/5.57         ((k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ X11)
% 5.34/5.57           = (k5_xboole_0 @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 5.34/5.57      inference('cnf', [status(esa)], [t91_xboole_1])).
% 5.34/5.57  thf('14', plain,
% 5.34/5.57      (![X0 : $i, X1 : $i]:
% 5.34/5.57         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 5.34/5.57           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 5.34/5.57      inference('sup+', [status(thm)], ['12', '13'])).
% 5.34/5.57  thf('15', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 5.34/5.57      inference('sup+', [status(thm)], ['5', '6'])).
% 5.34/5.57  thf('16', plain,
% 5.34/5.57      (![X0 : $i, X1 : $i]:
% 5.34/5.57         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 5.34/5.57      inference('demod', [status(thm)], ['14', '15'])).
% 5.34/5.57  thf('17', plain,
% 5.34/5.57      (![X0 : $i, X1 : $i]:
% 5.34/5.57         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 5.34/5.57           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 5.34/5.57      inference('sup+', [status(thm)], ['4', '16'])).
% 5.34/5.57  thf('18', plain,
% 5.34/5.57      (((k5_xboole_0 @ sk_C @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))
% 5.34/5.57         = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_A @ sk_B)))),
% 5.34/5.57      inference('sup+', [status(thm)], ['1', '17'])).
% 5.34/5.57  thf('19', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 5.34/5.57      inference('demod', [status(thm)], ['9', '10', '11'])).
% 5.34/5.57  thf('20', plain,
% 5.34/5.57      (((k5_xboole_0 @ sk_C @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))
% 5.34/5.57         = (k1_xboole_0))),
% 5.34/5.57      inference('demod', [status(thm)], ['18', '19'])).
% 5.34/5.57  thf('21', plain,
% 5.34/5.57      (![X0 : $i, X1 : $i]:
% 5.34/5.57         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 5.34/5.57      inference('demod', [status(thm)], ['14', '15'])).
% 5.34/5.57  thf('22', plain,
% 5.34/5.57      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 5.34/5.57         = (k5_xboole_0 @ sk_C @ k1_xboole_0))),
% 5.34/5.57      inference('sup+', [status(thm)], ['20', '21'])).
% 5.34/5.57  thf('23', plain,
% 5.34/5.57      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 5.34/5.57      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 5.34/5.57  thf('24', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 5.34/5.57      inference('sup+', [status(thm)], ['5', '6'])).
% 5.34/5.57  thf('25', plain,
% 5.34/5.57      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (sk_C))),
% 5.34/5.57      inference('demod', [status(thm)], ['22', '23', '24'])).
% 5.34/5.57  thf(t72_enumset1, axiom,
% 5.34/5.57    (![A:$i,B:$i,C:$i,D:$i]:
% 5.34/5.57     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 5.34/5.57  thf('26', plain,
% 5.34/5.57      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 5.34/5.57         ((k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37)
% 5.34/5.57           = (k2_enumset1 @ X34 @ X35 @ X36 @ X37))),
% 5.34/5.57      inference('cnf', [status(esa)], [t72_enumset1])).
% 5.34/5.57  thf(t55_enumset1, axiom,
% 5.34/5.57    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 5.34/5.57     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 5.34/5.57       ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ))).
% 5.34/5.57  thf('27', plain,
% 5.34/5.57      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 5.34/5.57         ((k4_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27)
% 5.34/5.57           = (k2_xboole_0 @ (k3_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26) @ 
% 5.34/5.57              (k1_tarski @ X27)))),
% 5.34/5.57      inference('cnf', [status(esa)], [t55_enumset1])).
% 5.34/5.57  thf('28', plain,
% 5.34/5.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 5.34/5.57         ((k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4)
% 5.34/5.57           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 5.34/5.57              (k1_tarski @ X4)))),
% 5.34/5.57      inference('sup+', [status(thm)], ['26', '27'])).
% 5.34/5.57  thf(t73_enumset1, axiom,
% 5.34/5.57    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 5.34/5.57     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 5.34/5.57       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 5.34/5.57  thf('29', plain,
% 5.34/5.57      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 5.34/5.57         ((k4_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 @ X42)
% 5.34/5.57           = (k3_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42))),
% 5.34/5.57      inference('cnf', [status(esa)], [t73_enumset1])).
% 5.34/5.57  thf('30', plain,
% 5.34/5.57      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 5.34/5.57         ((k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37)
% 5.34/5.57           = (k2_enumset1 @ X34 @ X35 @ X36 @ X37))),
% 5.34/5.57      inference('cnf', [status(esa)], [t72_enumset1])).
% 5.34/5.57  thf('31', plain,
% 5.34/5.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.34/5.57         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 5.34/5.57           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 5.34/5.57      inference('sup+', [status(thm)], ['29', '30'])).
% 5.34/5.57  thf(t71_enumset1, axiom,
% 5.34/5.57    (![A:$i,B:$i,C:$i]:
% 5.34/5.57     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 5.34/5.57  thf('32', plain,
% 5.34/5.57      (![X31 : $i, X32 : $i, X33 : $i]:
% 5.34/5.57         ((k2_enumset1 @ X31 @ X31 @ X32 @ X33)
% 5.34/5.57           = (k1_enumset1 @ X31 @ X32 @ X33))),
% 5.34/5.57      inference('cnf', [status(esa)], [t71_enumset1])).
% 5.34/5.57  thf(t70_enumset1, axiom,
% 5.34/5.57    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 5.34/5.57  thf('33', plain,
% 5.34/5.57      (![X29 : $i, X30 : $i]:
% 5.34/5.57         ((k1_enumset1 @ X29 @ X29 @ X30) = (k2_tarski @ X29 @ X30))),
% 5.34/5.57      inference('cnf', [status(esa)], [t70_enumset1])).
% 5.34/5.57  thf('34', plain,
% 5.34/5.57      (![X0 : $i, X1 : $i]:
% 5.34/5.57         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 5.34/5.57      inference('sup+', [status(thm)], ['32', '33'])).
% 5.34/5.57  thf('35', plain,
% 5.34/5.57      (![X0 : $i, X1 : $i]:
% 5.34/5.57         ((k4_enumset1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 5.34/5.57      inference('sup+', [status(thm)], ['31', '34'])).
% 5.34/5.57  thf('36', plain,
% 5.34/5.57      (![X0 : $i, X1 : $i]:
% 5.34/5.57         ((k2_xboole_0 @ (k2_enumset1 @ X1 @ X1 @ X1 @ X1) @ (k1_tarski @ X0))
% 5.34/5.57           = (k2_tarski @ X1 @ X0))),
% 5.34/5.57      inference('sup+', [status(thm)], ['28', '35'])).
% 5.34/5.57  thf('37', plain,
% 5.34/5.57      (![X29 : $i, X30 : $i]:
% 5.34/5.57         ((k1_enumset1 @ X29 @ X29 @ X30) = (k2_tarski @ X29 @ X30))),
% 5.34/5.57      inference('cnf', [status(esa)], [t70_enumset1])).
% 5.34/5.57  thf(t69_enumset1, axiom,
% 5.34/5.57    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 5.34/5.57  thf('38', plain,
% 5.34/5.57      (![X28 : $i]: ((k2_tarski @ X28 @ X28) = (k1_tarski @ X28))),
% 5.34/5.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 5.34/5.57  thf('39', plain,
% 5.34/5.57      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 5.34/5.57      inference('sup+', [status(thm)], ['37', '38'])).
% 5.34/5.57  thf('40', plain,
% 5.34/5.57      (![X31 : $i, X32 : $i, X33 : $i]:
% 5.34/5.57         ((k2_enumset1 @ X31 @ X31 @ X32 @ X33)
% 5.34/5.57           = (k1_enumset1 @ X31 @ X32 @ X33))),
% 5.34/5.57      inference('cnf', [status(esa)], [t71_enumset1])).
% 5.34/5.57  thf('41', plain,
% 5.34/5.57      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 5.34/5.57      inference('sup+', [status(thm)], ['39', '40'])).
% 5.34/5.57  thf('42', plain,
% 5.34/5.57      (![X0 : $i, X1 : $i]:
% 5.34/5.57         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 5.34/5.57           = (k2_tarski @ X1 @ X0))),
% 5.34/5.57      inference('demod', [status(thm)], ['36', '41'])).
% 5.34/5.57  thf(t102_enumset1, axiom,
% 5.34/5.57    (![A:$i,B:$i,C:$i]:
% 5.34/5.57     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ C @ B @ A ) ))).
% 5.34/5.57  thf('43', plain,
% 5.34/5.57      (![X19 : $i, X20 : $i, X21 : $i]:
% 5.34/5.57         ((k1_enumset1 @ X21 @ X20 @ X19) = (k1_enumset1 @ X19 @ X20 @ X21))),
% 5.34/5.57      inference('cnf', [status(esa)], [t102_enumset1])).
% 5.34/5.57  thf('44', plain,
% 5.34/5.57      (![X29 : $i, X30 : $i]:
% 5.34/5.57         ((k1_enumset1 @ X29 @ X29 @ X30) = (k2_tarski @ X29 @ X30))),
% 5.34/5.57      inference('cnf', [status(esa)], [t70_enumset1])).
% 5.34/5.57  thf('45', plain,
% 5.34/5.57      (![X0 : $i, X1 : $i]:
% 5.34/5.57         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X0 @ X1))),
% 5.34/5.57      inference('sup+', [status(thm)], ['43', '44'])).
% 5.34/5.57  thf('46', plain,
% 5.34/5.57      (![X31 : $i, X32 : $i, X33 : $i]:
% 5.34/5.57         ((k2_enumset1 @ X31 @ X31 @ X32 @ X33)
% 5.34/5.57           = (k1_enumset1 @ X31 @ X32 @ X33))),
% 5.34/5.57      inference('cnf', [status(esa)], [t71_enumset1])).
% 5.34/5.57  thf('47', plain,
% 5.34/5.57      (![X0 : $i, X1 : $i]:
% 5.34/5.57         ((k2_enumset1 @ X0 @ X0 @ X1 @ X1) = (k2_tarski @ X1 @ X0))),
% 5.34/5.57      inference('sup+', [status(thm)], ['45', '46'])).
% 5.34/5.57  thf('48', plain,
% 5.34/5.57      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 5.34/5.57      inference('sup+', [status(thm)], ['37', '38'])).
% 5.34/5.57  thf(l57_enumset1, axiom,
% 5.34/5.57    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 5.34/5.57     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 5.34/5.57       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_tarski @ D @ E ) ) ))).
% 5.34/5.57  thf('49', plain,
% 5.34/5.57      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 5.34/5.57         ((k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18)
% 5.34/5.57           = (k2_xboole_0 @ (k1_enumset1 @ X14 @ X15 @ X16) @ 
% 5.34/5.57              (k2_tarski @ X17 @ X18)))),
% 5.34/5.57      inference('cnf', [status(esa)], [l57_enumset1])).
% 5.34/5.57  thf('50', plain,
% 5.34/5.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.34/5.57         ((k3_enumset1 @ X0 @ X0 @ X0 @ X2 @ X1)
% 5.34/5.57           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 5.34/5.57      inference('sup+', [status(thm)], ['48', '49'])).
% 5.34/5.57  thf('51', plain,
% 5.34/5.57      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 5.34/5.57         ((k3_enumset1 @ X34 @ X34 @ X35 @ X36 @ X37)
% 5.34/5.57           = (k2_enumset1 @ X34 @ X35 @ X36 @ X37))),
% 5.34/5.57      inference('cnf', [status(esa)], [t72_enumset1])).
% 5.34/5.57  thf('52', plain,
% 5.34/5.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.34/5.57         ((k2_enumset1 @ X0 @ X0 @ X2 @ X1)
% 5.34/5.57           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 5.34/5.57      inference('demod', [status(thm)], ['50', '51'])).
% 5.34/5.57  thf('53', plain,
% 5.34/5.57      (![X0 : $i, X1 : $i]:
% 5.34/5.57         ((k2_tarski @ X1 @ X0)
% 5.34/5.57           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X1)))),
% 5.34/5.57      inference('sup+', [status(thm)], ['47', '52'])).
% 5.34/5.57  thf('54', plain,
% 5.34/5.57      (![X28 : $i]: ((k2_tarski @ X28 @ X28) = (k1_tarski @ X28))),
% 5.34/5.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 5.34/5.57  thf('55', plain,
% 5.34/5.57      (![X0 : $i, X1 : $i]:
% 5.34/5.57         ((k2_tarski @ X1 @ X0)
% 5.34/5.57           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 5.34/5.57      inference('demod', [status(thm)], ['53', '54'])).
% 5.34/5.57  thf('56', plain,
% 5.34/5.57      (![X0 : $i, X1 : $i]: ((k2_tarski @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 5.34/5.57      inference('sup+', [status(thm)], ['42', '55'])).
% 5.34/5.57  thf('57', plain,
% 5.34/5.57      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ sk_C) = (sk_C))),
% 5.34/5.57      inference('demod', [status(thm)], ['25', '56'])).
% 5.34/5.57  thf('58', plain,
% 5.34/5.57      (![X0 : $i, X1 : $i]: ((k2_tarski @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 5.34/5.57      inference('sup+', [status(thm)], ['42', '55'])).
% 5.34/5.57  thf(l51_zfmisc_1, axiom,
% 5.34/5.57    (![A:$i,B:$i]:
% 5.34/5.57     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 5.34/5.57  thf('59', plain,
% 5.34/5.57      (![X43 : $i, X44 : $i]:
% 5.34/5.57         ((k3_tarski @ (k2_tarski @ X43 @ X44)) = (k2_xboole_0 @ X43 @ X44))),
% 5.34/5.57      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 5.34/5.57  thf('60', plain,
% 5.34/5.57      (![X0 : $i, X1 : $i]:
% 5.34/5.57         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 5.34/5.57      inference('sup+', [status(thm)], ['58', '59'])).
% 5.34/5.57  thf('61', plain,
% 5.34/5.57      (![X43 : $i, X44 : $i]:
% 5.34/5.57         ((k3_tarski @ (k2_tarski @ X43 @ X44)) = (k2_xboole_0 @ X43 @ X44))),
% 5.34/5.57      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 5.34/5.57  thf('62', plain,
% 5.34/5.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 5.34/5.57      inference('sup+', [status(thm)], ['60', '61'])).
% 5.34/5.57  thf('63', plain,
% 5.34/5.57      (((k2_xboole_0 @ sk_C @ (k2_tarski @ sk_B @ sk_A)) = (sk_C))),
% 5.34/5.57      inference('demod', [status(thm)], ['57', '62'])).
% 5.34/5.57  thf('64', plain,
% 5.34/5.57      (![X12 : $i, X13 : $i]:
% 5.34/5.57         ((k3_xboole_0 @ X12 @ X13)
% 5.34/5.57           = (k5_xboole_0 @ X12 @ 
% 5.34/5.57              (k5_xboole_0 @ X13 @ (k2_xboole_0 @ X12 @ X13))))),
% 5.34/5.57      inference('demod', [status(thm)], ['2', '3'])).
% 5.34/5.57  thf('65', plain,
% 5.34/5.57      (((k3_xboole_0 @ sk_C @ (k2_tarski @ sk_B @ sk_A))
% 5.34/5.57         = (k5_xboole_0 @ sk_C @ 
% 5.34/5.57            (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ sk_C)))),
% 5.34/5.57      inference('sup+', [status(thm)], ['63', '64'])).
% 5.34/5.57  thf('66', plain,
% 5.34/5.57      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 5.34/5.57      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 5.34/5.57  thf('67', plain,
% 5.34/5.57      (![X0 : $i, X1 : $i]:
% 5.34/5.57         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 5.34/5.57      inference('demod', [status(thm)], ['14', '15'])).
% 5.34/5.57  thf('68', plain,
% 5.34/5.57      (((k3_xboole_0 @ sk_C @ (k2_tarski @ sk_B @ sk_A))
% 5.34/5.57         = (k2_tarski @ sk_B @ sk_A))),
% 5.34/5.57      inference('demod', [status(thm)], ['65', '66', '67'])).
% 5.34/5.57  thf(t17_xboole_1, axiom,
% 5.34/5.57    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 5.34/5.57  thf('69', plain,
% 5.34/5.57      (![X4 : $i, X5 : $i]: (r1_tarski @ (k3_xboole_0 @ X4 @ X5) @ X4)),
% 5.34/5.57      inference('cnf', [status(esa)], [t17_xboole_1])).
% 5.34/5.57  thf('70', plain, ((r1_tarski @ (k2_tarski @ sk_B @ sk_A) @ sk_C)),
% 5.34/5.57      inference('sup+', [status(thm)], ['68', '69'])).
% 5.34/5.57  thf(t38_zfmisc_1, axiom,
% 5.34/5.57    (![A:$i,B:$i,C:$i]:
% 5.34/5.57     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 5.34/5.57       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 5.34/5.57  thf('71', plain,
% 5.34/5.57      (![X45 : $i, X46 : $i, X47 : $i]:
% 5.34/5.57         ((r2_hidden @ X47 @ X46)
% 5.34/5.57          | ~ (r1_tarski @ (k2_tarski @ X45 @ X47) @ X46))),
% 5.34/5.57      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 5.34/5.57  thf('72', plain, ((r2_hidden @ sk_A @ sk_C)),
% 5.34/5.57      inference('sup-', [status(thm)], ['70', '71'])).
% 5.34/5.57  thf('73', plain, ($false), inference('demod', [status(thm)], ['0', '72'])).
% 5.34/5.57  
% 5.34/5.57  % SZS output end Refutation
% 5.34/5.57  
% 5.34/5.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jhExWnZnpZ

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:47 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :  147 (2110 expanded)
%              Number of leaves         :   34 ( 744 expanded)
%              Depth                    :   22
%              Number of atoms          : 1075 (16793 expanded)
%              Number of equality atoms :  118 (2078 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('0',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('3',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t49_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t49_zfmisc_1])).

thf('9',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('13',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('16',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['9','18'])).

thf('20',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('21',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('27',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('31',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('32',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('34',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('37',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('38',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['31','32','35','36','37'])).

thf('39',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('40',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('41',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','44'])).

thf('46',plain,
    ( sk_B
    = ( k5_xboole_0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['38','45'])).

thf('47',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('49',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('52',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('56',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('58',plain,
    ( sk_B
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['46','47','54','55','56','57'])).

thf('59',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('60',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,
    ( sk_B
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['46','47','54','55','56','57'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('63',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('65',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,
    ( sk_B
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['46','47','54','55','56','57'])).

thf('67',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('68',plain,
    ( sk_B
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('70',plain,
    ( ( k1_tarski @ sk_A )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('73',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('75',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('76',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('78',plain,(
    ! [X36: $i] :
      ( ( k2_tarski @ X36 @ X36 )
      = ( k1_tarski @ X36 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('79',plain,(
    ! [X64: $i,X65: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X64 @ X65 ) )
      = ( k2_xboole_0 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['77','80','81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('85',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_tarski @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,
    ( sk_A
    = ( k3_tarski @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['74','85'])).

thf('87',plain,
    ( ( k1_tarski @ ( k3_tarski @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['73','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ ( k3_tarski @ ( k4_xboole_0 @ X0 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','87'])).

thf('89',plain,(
    ! [X36: $i] :
      ( ( k2_tarski @ X36 @ X36 )
      = ( k1_tarski @ X36 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('90',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_enumset1 @ X37 @ X37 @ X38 )
      = ( k2_tarski @ X37 @ X38 ) ) ),
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

thf('91',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 )
      | ( r2_hidden @ X29 @ X33 )
      | ( X33
       != ( k1_enumset1 @ X32 @ X31 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('92',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( r2_hidden @ X29 @ ( k1_enumset1 @ X32 @ X31 @ X30 ) )
      | ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['90','92'])).

thf('94',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X25 != X24 )
      | ~ ( zip_tseitin_0 @ X25 @ X26 @ X27 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('95',plain,(
    ! [X24: $i,X26: $i,X27: $i] :
      ~ ( zip_tseitin_0 @ X24 @ X26 @ X27 @ X24 ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['93','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['89','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('100',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['98','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['97','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ~ ( r1_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ ( k3_tarski @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['88','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ ( k3_tarski @ ( k4_xboole_0 @ X0 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','87'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('106',plain,(
    ! [X17: $i] :
      ( r1_xboole_0 @ X17 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('107',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['106','109'])).

thf('111',plain,(
    $false ),
    inference(demod,[status(thm)],['104','105','110'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jhExWnZnpZ
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:20:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.52/0.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.52/0.72  % Solved by: fo/fo7.sh
% 0.52/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.72  % done 623 iterations in 0.264s
% 0.52/0.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.52/0.72  % SZS output start Refutation
% 0.52/0.72  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.52/0.72  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.52/0.72  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.52/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.72  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.52/0.72  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.52/0.72  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.52/0.72  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.52/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.72  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.52/0.72  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.52/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.72  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.52/0.72  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.52/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.72  thf(t2_boole, axiom,
% 0.52/0.72    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.52/0.72  thf('0', plain,
% 0.52/0.72      (![X12 : $i]: ((k3_xboole_0 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.72      inference('cnf', [status(esa)], [t2_boole])).
% 0.52/0.72  thf(t100_xboole_1, axiom,
% 0.52/0.72    (![A:$i,B:$i]:
% 0.52/0.72     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.52/0.72  thf('1', plain,
% 0.52/0.72      (![X8 : $i, X9 : $i]:
% 0.52/0.72         ((k4_xboole_0 @ X8 @ X9)
% 0.52/0.72           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.52/0.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.52/0.72  thf('2', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.52/0.72      inference('sup+', [status(thm)], ['0', '1'])).
% 0.52/0.72  thf(t5_boole, axiom,
% 0.52/0.72    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.52/0.72  thf('3', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.52/0.72      inference('cnf', [status(esa)], [t5_boole])).
% 0.52/0.72  thf('4', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.52/0.72      inference('sup+', [status(thm)], ['2', '3'])).
% 0.52/0.72  thf(t48_xboole_1, axiom,
% 0.52/0.72    (![A:$i,B:$i]:
% 0.52/0.72     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.52/0.72  thf('5', plain,
% 0.52/0.72      (![X14 : $i, X15 : $i]:
% 0.52/0.72         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.52/0.72           = (k3_xboole_0 @ X14 @ X15))),
% 0.52/0.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.52/0.72  thf('6', plain,
% 0.52/0.72      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.52/0.72      inference('sup+', [status(thm)], ['4', '5'])).
% 0.52/0.72  thf('7', plain,
% 0.52/0.72      (![X12 : $i]: ((k3_xboole_0 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.72      inference('cnf', [status(esa)], [t2_boole])).
% 0.52/0.72  thf('8', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.52/0.72      inference('demod', [status(thm)], ['6', '7'])).
% 0.52/0.72  thf(t49_zfmisc_1, conjecture,
% 0.52/0.72    (![A:$i,B:$i]:
% 0.52/0.72     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.52/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.72    (~( ![A:$i,B:$i]:
% 0.52/0.72        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ) )),
% 0.52/0.72    inference('cnf.neg', [status(esa)], [t49_zfmisc_1])).
% 0.52/0.72  thf('9', plain,
% 0.52/0.72      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf(commutativity_k5_xboole_0, axiom,
% 0.52/0.72    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.52/0.72  thf('10', plain,
% 0.52/0.72      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.52/0.72      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.52/0.72  thf(t94_xboole_1, axiom,
% 0.52/0.72    (![A:$i,B:$i]:
% 0.52/0.72     ( ( k2_xboole_0 @ A @ B ) =
% 0.52/0.72       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.52/0.72  thf('11', plain,
% 0.52/0.72      (![X22 : $i, X23 : $i]:
% 0.52/0.72         ((k2_xboole_0 @ X22 @ X23)
% 0.52/0.72           = (k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ 
% 0.52/0.72              (k3_xboole_0 @ X22 @ X23)))),
% 0.52/0.72      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.52/0.72  thf('12', plain,
% 0.52/0.72      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.52/0.72      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.52/0.72  thf('13', plain,
% 0.52/0.72      (![X22 : $i, X23 : $i]:
% 0.52/0.72         ((k2_xboole_0 @ X22 @ X23)
% 0.52/0.72           = (k5_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ 
% 0.52/0.72              (k5_xboole_0 @ X22 @ X23)))),
% 0.52/0.72      inference('demod', [status(thm)], ['11', '12'])).
% 0.52/0.72  thf('14', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]:
% 0.52/0.72         ((k2_xboole_0 @ X0 @ X1)
% 0.52/0.72           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.52/0.72      inference('sup+', [status(thm)], ['10', '13'])).
% 0.52/0.72  thf(commutativity_k3_xboole_0, axiom,
% 0.52/0.72    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.52/0.72  thf('15', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.52/0.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.52/0.72  thf('16', plain,
% 0.52/0.72      (![X22 : $i, X23 : $i]:
% 0.52/0.72         ((k2_xboole_0 @ X22 @ X23)
% 0.52/0.72           = (k5_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ 
% 0.52/0.72              (k5_xboole_0 @ X22 @ X23)))),
% 0.52/0.72      inference('demod', [status(thm)], ['11', '12'])).
% 0.52/0.72  thf('17', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]:
% 0.52/0.72         ((k2_xboole_0 @ X0 @ X1)
% 0.52/0.72           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X0 @ X1)))),
% 0.52/0.72      inference('sup+', [status(thm)], ['15', '16'])).
% 0.52/0.72  thf('18', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 0.52/0.72      inference('sup+', [status(thm)], ['14', '17'])).
% 0.52/0.72  thf('19', plain,
% 0.52/0.72      (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.52/0.72      inference('demod', [status(thm)], ['9', '18'])).
% 0.52/0.72  thf('20', plain,
% 0.52/0.72      (![X22 : $i, X23 : $i]:
% 0.52/0.72         ((k2_xboole_0 @ X22 @ X23)
% 0.52/0.72           = (k5_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ 
% 0.52/0.72              (k5_xboole_0 @ X22 @ X23)))),
% 0.52/0.72      inference('demod', [status(thm)], ['11', '12'])).
% 0.52/0.72  thf('21', plain,
% 0.52/0.72      (![X22 : $i, X23 : $i]:
% 0.52/0.72         ((k2_xboole_0 @ X22 @ X23)
% 0.52/0.72           = (k5_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ 
% 0.52/0.72              (k5_xboole_0 @ X22 @ X23)))),
% 0.52/0.72      inference('demod', [status(thm)], ['11', '12'])).
% 0.52/0.72  thf('22', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]:
% 0.52/0.72         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.52/0.72           = (k5_xboole_0 @ 
% 0.52/0.72              (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)) @ 
% 0.52/0.72              (k2_xboole_0 @ X1 @ X0)))),
% 0.52/0.72      inference('sup+', [status(thm)], ['20', '21'])).
% 0.52/0.72  thf('23', plain,
% 0.52/0.72      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.52/0.72      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.52/0.72  thf('24', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]:
% 0.52/0.72         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 0.52/0.72           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 0.52/0.72              (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))))),
% 0.52/0.72      inference('demod', [status(thm)], ['22', '23'])).
% 0.52/0.72  thf('25', plain,
% 0.52/0.72      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.52/0.72         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.52/0.72         = (k5_xboole_0 @ k1_xboole_0 @ 
% 0.52/0.72            (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.52/0.72             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.52/0.72      inference('sup+', [status(thm)], ['19', '24'])).
% 0.52/0.72  thf('26', plain,
% 0.52/0.72      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.52/0.72      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.52/0.72  thf('27', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.52/0.72      inference('cnf', [status(esa)], [t5_boole])).
% 0.52/0.72  thf('28', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.52/0.72      inference('sup+', [status(thm)], ['26', '27'])).
% 0.52/0.72  thf('29', plain,
% 0.52/0.72      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.52/0.72         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.52/0.72         = (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.52/0.72            (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.52/0.72      inference('demod', [status(thm)], ['25', '28'])).
% 0.52/0.72  thf('30', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]:
% 0.52/0.72         ((k2_xboole_0 @ X0 @ X1)
% 0.52/0.72           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.52/0.72      inference('sup+', [status(thm)], ['10', '13'])).
% 0.52/0.72  thf('31', plain,
% 0.52/0.72      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.52/0.72         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.52/0.72         = (k5_xboole_0 @ 
% 0.52/0.72            (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.52/0.72             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 0.52/0.72            (k5_xboole_0 @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.52/0.72             (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.52/0.72      inference('sup+', [status(thm)], ['29', '30'])).
% 0.52/0.72  thf(t91_xboole_1, axiom,
% 0.52/0.72    (![A:$i,B:$i,C:$i]:
% 0.52/0.72     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.52/0.72       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.52/0.72  thf('32', plain,
% 0.52/0.72      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.52/0.72         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 0.52/0.72           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 0.52/0.72      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.52/0.72  thf('33', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.52/0.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.52/0.72  thf('34', plain,
% 0.52/0.72      (![X8 : $i, X9 : $i]:
% 0.52/0.72         ((k4_xboole_0 @ X8 @ X9)
% 0.52/0.72           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.52/0.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.52/0.72  thf('35', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]:
% 0.52/0.72         ((k4_xboole_0 @ X0 @ X1)
% 0.52/0.72           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.52/0.72      inference('sup+', [status(thm)], ['33', '34'])).
% 0.52/0.72  thf('36', plain,
% 0.52/0.72      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.52/0.72      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.52/0.72  thf('37', plain,
% 0.52/0.72      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.52/0.72         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 0.52/0.72           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 0.52/0.72      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.52/0.72  thf('38', plain,
% 0.52/0.72      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.52/0.72         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.52/0.72         = (k5_xboole_0 @ sk_B @ 
% 0.52/0.72            (k5_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.52/0.72             (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.52/0.72              (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))))),
% 0.52/0.72      inference('demod', [status(thm)], ['31', '32', '35', '36', '37'])).
% 0.52/0.72  thf('39', plain,
% 0.52/0.72      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.52/0.72      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.52/0.72  thf(t92_xboole_1, axiom,
% 0.52/0.72    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.52/0.72  thf('40', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ X21) = (k1_xboole_0))),
% 0.52/0.72      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.52/0.72  thf('41', plain,
% 0.52/0.72      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.52/0.72         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 0.52/0.72           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 0.52/0.72      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.52/0.72  thf('42', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]:
% 0.52/0.72         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.52/0.72           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.52/0.72      inference('sup+', [status(thm)], ['40', '41'])).
% 0.52/0.72  thf('43', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.52/0.72      inference('sup+', [status(thm)], ['26', '27'])).
% 0.52/0.72  thf('44', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]:
% 0.52/0.72         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.52/0.72      inference('demod', [status(thm)], ['42', '43'])).
% 0.52/0.72  thf('45', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]:
% 0.52/0.72         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.52/0.72      inference('sup+', [status(thm)], ['39', '44'])).
% 0.52/0.72  thf('46', plain,
% 0.52/0.72      (((sk_B)
% 0.52/0.72         = (k5_xboole_0 @ 
% 0.52/0.72            (k5_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 0.52/0.72             (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.52/0.72              (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))) @ 
% 0.52/0.72            (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.52/0.72             (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 0.52/0.72      inference('sup+', [status(thm)], ['38', '45'])).
% 0.52/0.72  thf('47', plain,
% 0.52/0.72      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.52/0.72         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 0.52/0.72           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 0.52/0.72      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.52/0.72  thf('48', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.52/0.72      inference('demod', [status(thm)], ['6', '7'])).
% 0.52/0.72  thf('49', plain,
% 0.52/0.72      (![X14 : $i, X15 : $i]:
% 0.52/0.72         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.52/0.72           = (k3_xboole_0 @ X14 @ X15))),
% 0.52/0.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.52/0.72  thf('50', plain,
% 0.52/0.72      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.52/0.72      inference('sup+', [status(thm)], ['48', '49'])).
% 0.52/0.72  thf('51', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.52/0.72      inference('sup+', [status(thm)], ['2', '3'])).
% 0.52/0.72  thf('52', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.52/0.72      inference('demod', [status(thm)], ['50', '51'])).
% 0.52/0.72  thf('53', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]:
% 0.52/0.72         ((k4_xboole_0 @ X0 @ X1)
% 0.52/0.72           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.52/0.72      inference('sup+', [status(thm)], ['33', '34'])).
% 0.52/0.72  thf('54', plain,
% 0.52/0.72      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.52/0.72      inference('sup+', [status(thm)], ['52', '53'])).
% 0.52/0.72  thf('55', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.52/0.72      inference('demod', [status(thm)], ['6', '7'])).
% 0.52/0.72  thf('56', plain,
% 0.52/0.72      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.52/0.72      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.52/0.72  thf('57', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.52/0.72      inference('sup+', [status(thm)], ['26', '27'])).
% 0.52/0.72  thf('58', plain, (((sk_B) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.52/0.72      inference('demod', [status(thm)], ['46', '47', '54', '55', '56', '57'])).
% 0.52/0.72  thf('59', plain,
% 0.52/0.72      (![X14 : $i, X15 : $i]:
% 0.52/0.72         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.52/0.72           = (k3_xboole_0 @ X14 @ X15))),
% 0.52/0.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.52/0.72  thf('60', plain,
% 0.52/0.72      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.52/0.72         = (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.52/0.72      inference('sup+', [status(thm)], ['58', '59'])).
% 0.52/0.72  thf('61', plain, (((sk_B) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.52/0.72      inference('demod', [status(thm)], ['46', '47', '54', '55', '56', '57'])).
% 0.52/0.72  thf('62', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.52/0.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.52/0.72  thf('63', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.52/0.72      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.52/0.72  thf('64', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]:
% 0.52/0.72         ((k4_xboole_0 @ X0 @ X1)
% 0.52/0.72           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.52/0.72      inference('sup+', [status(thm)], ['33', '34'])).
% 0.52/0.72  thf('65', plain,
% 0.52/0.72      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.52/0.72         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.52/0.72      inference('sup+', [status(thm)], ['63', '64'])).
% 0.52/0.72  thf('66', plain, (((sk_B) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.52/0.72      inference('demod', [status(thm)], ['46', '47', '54', '55', '56', '57'])).
% 0.52/0.72  thf('67', plain,
% 0.52/0.72      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.52/0.72      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.52/0.72  thf('68', plain, (((sk_B) = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.52/0.72      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.52/0.72  thf('69', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]:
% 0.52/0.72         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.52/0.72      inference('demod', [status(thm)], ['42', '43'])).
% 0.52/0.72  thf('70', plain, (((k1_tarski @ sk_A) = (k5_xboole_0 @ sk_B @ sk_B))),
% 0.52/0.72      inference('sup+', [status(thm)], ['68', '69'])).
% 0.52/0.72  thf('71', plain,
% 0.52/0.72      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.52/0.72      inference('sup+', [status(thm)], ['52', '53'])).
% 0.52/0.72  thf('72', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.52/0.72      inference('demod', [status(thm)], ['6', '7'])).
% 0.52/0.72  thf('73', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.52/0.72      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.52/0.72  thf('74', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.52/0.72      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.52/0.72  thf('75', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ X21) = (k1_xboole_0))),
% 0.52/0.72      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.52/0.72  thf('76', plain,
% 0.52/0.72      (![X22 : $i, X23 : $i]:
% 0.52/0.72         ((k2_xboole_0 @ X22 @ X23)
% 0.52/0.72           = (k5_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ 
% 0.52/0.72              (k5_xboole_0 @ X22 @ X23)))),
% 0.52/0.72      inference('demod', [status(thm)], ['11', '12'])).
% 0.52/0.72  thf('77', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         ((k2_xboole_0 @ X0 @ X0)
% 0.52/0.72           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ k1_xboole_0))),
% 0.52/0.72      inference('sup+', [status(thm)], ['75', '76'])).
% 0.52/0.72  thf(t69_enumset1, axiom,
% 0.52/0.72    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.52/0.72  thf('78', plain,
% 0.52/0.72      (![X36 : $i]: ((k2_tarski @ X36 @ X36) = (k1_tarski @ X36))),
% 0.52/0.72      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.52/0.72  thf(l51_zfmisc_1, axiom,
% 0.52/0.72    (![A:$i,B:$i]:
% 0.52/0.72     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.52/0.72  thf('79', plain,
% 0.52/0.72      (![X64 : $i, X65 : $i]:
% 0.52/0.72         ((k3_tarski @ (k2_tarski @ X64 @ X65)) = (k2_xboole_0 @ X64 @ X65))),
% 0.52/0.72      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.52/0.72  thf('80', plain,
% 0.52/0.72      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.52/0.72      inference('sup+', [status(thm)], ['78', '79'])).
% 0.52/0.72  thf('81', plain,
% 0.52/0.72      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.52/0.72      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.52/0.72  thf('82', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.52/0.72      inference('sup+', [status(thm)], ['26', '27'])).
% 0.52/0.72  thf('83', plain,
% 0.52/0.72      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k3_xboole_0 @ X0 @ X0))),
% 0.52/0.72      inference('demod', [status(thm)], ['77', '80', '81', '82'])).
% 0.52/0.72  thf('84', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.52/0.72      inference('demod', [status(thm)], ['50', '51'])).
% 0.52/0.72  thf('85', plain, (![X0 : $i]: ((X0) = (k3_tarski @ (k1_tarski @ X0)))),
% 0.52/0.72      inference('sup+', [status(thm)], ['83', '84'])).
% 0.52/0.72  thf('86', plain, (((sk_A) = (k3_tarski @ k1_xboole_0))),
% 0.52/0.72      inference('sup+', [status(thm)], ['74', '85'])).
% 0.52/0.72  thf('87', plain, (((k1_tarski @ (k3_tarski @ k1_xboole_0)) = (k1_xboole_0))),
% 0.52/0.72      inference('demod', [status(thm)], ['73', '86'])).
% 0.52/0.72  thf('88', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         ((k1_tarski @ (k3_tarski @ (k4_xboole_0 @ X0 @ X0))) = (k1_xboole_0))),
% 0.52/0.72      inference('sup+', [status(thm)], ['8', '87'])).
% 0.52/0.72  thf('89', plain,
% 0.52/0.72      (![X36 : $i]: ((k2_tarski @ X36 @ X36) = (k1_tarski @ X36))),
% 0.52/0.72      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.52/0.72  thf(t70_enumset1, axiom,
% 0.52/0.72    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.52/0.72  thf('90', plain,
% 0.52/0.72      (![X37 : $i, X38 : $i]:
% 0.52/0.72         ((k1_enumset1 @ X37 @ X37 @ X38) = (k2_tarski @ X37 @ X38))),
% 0.52/0.72      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.52/0.72  thf(d1_enumset1, axiom,
% 0.52/0.72    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.72     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.52/0.72       ( ![E:$i]:
% 0.52/0.72         ( ( r2_hidden @ E @ D ) <=>
% 0.52/0.72           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.52/0.72  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.52/0.72  thf(zf_stmt_2, axiom,
% 0.52/0.72    (![E:$i,C:$i,B:$i,A:$i]:
% 0.52/0.72     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.52/0.72       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.52/0.72  thf(zf_stmt_3, axiom,
% 0.52/0.72    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.72     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.52/0.72       ( ![E:$i]:
% 0.52/0.72         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.52/0.72  thf('91', plain,
% 0.52/0.72      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.52/0.72         ((zip_tseitin_0 @ X29 @ X30 @ X31 @ X32)
% 0.52/0.72          | (r2_hidden @ X29 @ X33)
% 0.52/0.72          | ((X33) != (k1_enumset1 @ X32 @ X31 @ X30)))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.52/0.72  thf('92', plain,
% 0.52/0.72      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.52/0.72         ((r2_hidden @ X29 @ (k1_enumset1 @ X32 @ X31 @ X30))
% 0.52/0.72          | (zip_tseitin_0 @ X29 @ X30 @ X31 @ X32))),
% 0.52/0.72      inference('simplify', [status(thm)], ['91'])).
% 0.52/0.72  thf('93', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.72         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.52/0.72          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.52/0.72      inference('sup+', [status(thm)], ['90', '92'])).
% 0.52/0.72  thf('94', plain,
% 0.52/0.72      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.52/0.72         (((X25) != (X24)) | ~ (zip_tseitin_0 @ X25 @ X26 @ X27 @ X24))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.52/0.72  thf('95', plain,
% 0.52/0.72      (![X24 : $i, X26 : $i, X27 : $i]:
% 0.52/0.72         ~ (zip_tseitin_0 @ X24 @ X26 @ X27 @ X24)),
% 0.52/0.72      inference('simplify', [status(thm)], ['94'])).
% 0.52/0.72  thf('96', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.52/0.72      inference('sup-', [status(thm)], ['93', '95'])).
% 0.52/0.72  thf('97', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.52/0.72      inference('sup+', [status(thm)], ['89', '96'])).
% 0.52/0.72  thf('98', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.52/0.72      inference('demod', [status(thm)], ['50', '51'])).
% 0.52/0.72  thf('99', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.52/0.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.52/0.72  thf(t4_xboole_0, axiom,
% 0.52/0.72    (![A:$i,B:$i]:
% 0.52/0.72     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.52/0.72            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.52/0.72       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.52/0.72            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.52/0.72  thf('100', plain,
% 0.52/0.72      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.52/0.72         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.52/0.72          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.52/0.72      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.52/0.72  thf('101', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.72         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.52/0.72          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.52/0.72      inference('sup-', [status(thm)], ['99', '100'])).
% 0.52/0.72  thf('102', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]:
% 0.52/0.72         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.52/0.72      inference('sup-', [status(thm)], ['98', '101'])).
% 0.52/0.72  thf('103', plain,
% 0.52/0.72      (![X0 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.52/0.72      inference('sup-', [status(thm)], ['97', '102'])).
% 0.52/0.72  thf('104', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         ~ (r1_xboole_0 @ k1_xboole_0 @ 
% 0.52/0.72            (k1_tarski @ (k3_tarski @ (k4_xboole_0 @ X0 @ X0))))),
% 0.52/0.72      inference('sup-', [status(thm)], ['88', '103'])).
% 0.52/0.72  thf('105', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         ((k1_tarski @ (k3_tarski @ (k4_xboole_0 @ X0 @ X0))) = (k1_xboole_0))),
% 0.52/0.72      inference('sup+', [status(thm)], ['8', '87'])).
% 0.52/0.72  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.52/0.72  thf('106', plain, (![X17 : $i]: (r1_xboole_0 @ X17 @ k1_xboole_0)),
% 0.52/0.72      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.52/0.72  thf('107', plain,
% 0.52/0.72      (![X4 : $i, X5 : $i]:
% 0.52/0.72         ((r1_xboole_0 @ X4 @ X5)
% 0.52/0.72          | (r2_hidden @ (sk_C @ X5 @ X4) @ (k3_xboole_0 @ X4 @ X5)))),
% 0.52/0.72      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.52/0.72  thf('108', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.72         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.52/0.72          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.52/0.72      inference('sup-', [status(thm)], ['99', '100'])).
% 0.52/0.72  thf('109', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]:
% 0.52/0.72         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.52/0.72      inference('sup-', [status(thm)], ['107', '108'])).
% 0.52/0.72  thf('110', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.52/0.72      inference('sup-', [status(thm)], ['106', '109'])).
% 0.52/0.72  thf('111', plain, ($false),
% 0.52/0.72      inference('demod', [status(thm)], ['104', '105', '110'])).
% 0.52/0.72  
% 0.52/0.72  % SZS output end Refutation
% 0.52/0.72  
% 0.52/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

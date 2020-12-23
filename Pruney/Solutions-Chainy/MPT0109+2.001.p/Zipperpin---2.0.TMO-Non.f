%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.V3XlUSeOkL

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:24 EST 2020

% Result     : Timeout 57.46s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   94 ( 191 expanded)
%              Number of leaves         :   26 (  73 expanded)
%              Depth                    :   13
%              Number of atoms          :  715 (1336 expanded)
%              Number of equality atoms :   84 ( 181 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(t102_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k4_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t102_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
 != ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('3',plain,(
    ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
 != ( k2_xboole_0 @ ( k3_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('4',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k3_xboole_0 @ X36 @ ( k4_xboole_0 @ X37 @ X38 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X36 @ X37 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('6',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('7',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('8',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ X21 @ o_0_0_xboole_0 )
      = X21 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('9',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( k4_xboole_0 @ X44 @ ( k4_xboole_0 @ X45 @ X46 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X44 @ X45 ) @ ( k3_xboole_0 @ X44 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ o_0_0_xboole_0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X4 )
      = ( k5_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X50: $i] :
      ( ( k5_xboole_0 @ X50 @ k1_xboole_0 )
      = X50 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('13',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('14',plain,(
    ! [X50: $i] :
      ( ( k5_xboole_0 @ X50 @ o_0_0_xboole_0 )
      = X50 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ o_0_0_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ o_0_0_xboole_0 @ X0 )
      = ( k3_xboole_0 @ o_0_0_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('19',plain,(
    ! [X18: $i] :
      ( ( k3_xboole_0 @ X18 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('20',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('21',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('22',plain,(
    ! [X18: $i] :
      ( ( k3_xboole_0 @ X18 @ o_0_0_xboole_0 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ o_0_0_xboole_0 @ X0 )
      = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ o_0_0_xboole_0 @ X0 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['17','23'])).

thf('25',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ X21 @ o_0_0_xboole_0 )
      = X21 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['10','24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','26'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('28',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X22 @ X23 ) @ X23 )
      = ( k4_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k4_xboole_0 @ X34 @ ( k4_xboole_0 @ X34 @ X35 ) )
      = ( k3_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('34',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k4_xboole_0 @ X30 @ ( k2_xboole_0 @ X30 @ X31 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('35',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('36',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k4_xboole_0 @ X30 @ ( k2_xboole_0 @ X30 @ X31 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k4_xboole_0 @ X34 @ ( k4_xboole_0 @ X34 @ X35 ) )
      = ( k3_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ o_0_0_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ X21 @ o_0_0_xboole_0 )
      = X21 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['32','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','42'])).

thf('44',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('45',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k4_xboole_0 @ X32 @ ( k3_xboole_0 @ X32 @ X33 ) )
      = ( k4_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['4','47'])).

thf('49',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k3_xboole_0 @ X36 @ ( k4_xboole_0 @ X37 @ X38 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X36 @ X37 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(t50_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('50',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( k3_xboole_0 @ X39 @ ( k4_xboole_0 @ X40 @ X41 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X39 @ X40 ) @ ( k3_xboole_0 @ X39 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t50_xboole_1])).

thf('51',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k3_xboole_0 @ X36 @ ( k4_xboole_0 @ X37 @ X38 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X36 @ X37 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('52',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( k3_xboole_0 @ X39 @ ( k4_xboole_0 @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X39 @ ( k4_xboole_0 @ X40 @ ( k3_xboole_0 @ X39 @ X41 ) ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','46'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['48','49','52','53'])).

thf('55',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('56',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( k4_xboole_0 @ X44 @ ( k4_xboole_0 @ X45 @ X46 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X44 @ X45 ) @ ( k3_xboole_0 @ X44 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(l98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('61',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k5_xboole_0 @ X11 @ X12 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X4 )
      = ( k5_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('65',plain,(
    ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
 != ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['3','54','55','58','63','64'])).

thf('66',plain,(
    $false ),
    inference(simplify,[status(thm)],['65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.V3XlUSeOkL
% 0.13/0.38  % Computer   : n023.cluster.edu
% 0.13/0.38  % Model      : x86_64 x86_64
% 0.13/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.38  % Memory     : 8042.1875MB
% 0.13/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.38  % CPULimit   : 60
% 0.13/0.38  % DateTime   : Tue Dec  1 12:32:51 EST 2020
% 0.13/0.38  % CPUTime    : 
% 0.13/0.38  % Running portfolio for 600 s
% 0.13/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.38  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 57.46/57.78  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 57.46/57.78  % Solved by: fo/fo7.sh
% 57.46/57.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 57.46/57.78  % done 15250 iterations in 57.289s
% 57.46/57.78  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 57.46/57.78  % SZS output start Refutation
% 57.46/57.78  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 57.46/57.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 57.46/57.78  thf(sk_A_type, type, sk_A: $i).
% 57.46/57.78  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 57.46/57.78  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 57.46/57.78  thf(sk_B_type, type, sk_B: $i).
% 57.46/57.78  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 57.46/57.78  thf(sk_C_type, type, sk_C: $i).
% 57.46/57.78  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 57.46/57.78  thf(t102_xboole_1, conjecture,
% 57.46/57.78    (![A:$i,B:$i,C:$i]:
% 57.46/57.78     ( ( k4_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) =
% 57.46/57.78       ( k2_xboole_0 @
% 57.46/57.78         ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) @ 
% 57.46/57.78         ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) ))).
% 57.46/57.78  thf(zf_stmt_0, negated_conjecture,
% 57.46/57.78    (~( ![A:$i,B:$i,C:$i]:
% 57.46/57.78        ( ( k4_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) =
% 57.46/57.78          ( k2_xboole_0 @
% 57.46/57.78            ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) @ 
% 57.46/57.78            ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) ) )),
% 57.46/57.78    inference('cnf.neg', [status(esa)], [t102_xboole_1])).
% 57.46/57.78  thf('0', plain,
% 57.46/57.78      (((k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))
% 57.46/57.78         != (k2_xboole_0 @ 
% 57.46/57.78             (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) @ 
% 57.46/57.78             (k3_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ sk_C)))),
% 57.46/57.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.46/57.78  thf(commutativity_k3_xboole_0, axiom,
% 57.46/57.78    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 57.46/57.78  thf('1', plain,
% 57.46/57.78      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 57.46/57.78      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 57.46/57.78  thf(commutativity_k2_xboole_0, axiom,
% 57.46/57.78    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 57.46/57.78  thf('2', plain,
% 57.46/57.78      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 57.46/57.78      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 57.46/57.78  thf('3', plain,
% 57.46/57.78      (((k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))
% 57.46/57.78         != (k2_xboole_0 @ 
% 57.46/57.78             (k3_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 57.46/57.78             (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 57.46/57.78      inference('demod', [status(thm)], ['0', '1', '2'])).
% 57.46/57.78  thf(t49_xboole_1, axiom,
% 57.46/57.78    (![A:$i,B:$i,C:$i]:
% 57.46/57.78     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 57.46/57.78       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 57.46/57.78  thf('4', plain,
% 57.46/57.78      (![X36 : $i, X37 : $i, X38 : $i]:
% 57.46/57.78         ((k3_xboole_0 @ X36 @ (k4_xboole_0 @ X37 @ X38))
% 57.46/57.78           = (k4_xboole_0 @ (k3_xboole_0 @ X36 @ X37) @ X38))),
% 57.46/57.78      inference('cnf', [status(esa)], [t49_xboole_1])).
% 57.46/57.78  thf('5', plain,
% 57.46/57.78      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 57.46/57.78      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 57.46/57.78  thf(t3_boole, axiom,
% 57.46/57.78    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 57.46/57.78  thf('6', plain, (![X21 : $i]: ((k4_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 57.46/57.78      inference('cnf', [status(esa)], [t3_boole])).
% 57.46/57.78  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 57.46/57.78  thf('7', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 57.46/57.78      inference('cnf', [status(esa)], [d2_xboole_0])).
% 57.46/57.78  thf('8', plain,
% 57.46/57.78      (![X21 : $i]: ((k4_xboole_0 @ X21 @ o_0_0_xboole_0) = (X21))),
% 57.46/57.78      inference('demod', [status(thm)], ['6', '7'])).
% 57.46/57.78  thf(t52_xboole_1, axiom,
% 57.46/57.78    (![A:$i,B:$i,C:$i]:
% 57.46/57.78     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 57.46/57.78       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 57.46/57.78  thf('9', plain,
% 57.46/57.78      (![X44 : $i, X45 : $i, X46 : $i]:
% 57.46/57.78         ((k4_xboole_0 @ X44 @ (k4_xboole_0 @ X45 @ X46))
% 57.46/57.78           = (k2_xboole_0 @ (k4_xboole_0 @ X44 @ X45) @ 
% 57.46/57.78              (k3_xboole_0 @ X44 @ X46)))),
% 57.46/57.78      inference('cnf', [status(esa)], [t52_xboole_1])).
% 57.46/57.78  thf('10', plain,
% 57.46/57.78      (![X0 : $i, X1 : $i]:
% 57.46/57.78         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ o_0_0_xboole_0 @ X1))
% 57.46/57.78           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 57.46/57.78      inference('sup+', [status(thm)], ['8', '9'])).
% 57.46/57.78  thf(commutativity_k5_xboole_0, axiom,
% 57.46/57.78    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 57.46/57.78  thf('11', plain,
% 57.46/57.78      (![X4 : $i, X5 : $i]: ((k5_xboole_0 @ X5 @ X4) = (k5_xboole_0 @ X4 @ X5))),
% 57.46/57.78      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 57.46/57.78  thf(t5_boole, axiom,
% 57.46/57.78    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 57.46/57.78  thf('12', plain, (![X50 : $i]: ((k5_xboole_0 @ X50 @ k1_xboole_0) = (X50))),
% 57.46/57.78      inference('cnf', [status(esa)], [t5_boole])).
% 57.46/57.78  thf('13', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 57.46/57.78      inference('cnf', [status(esa)], [d2_xboole_0])).
% 57.46/57.78  thf('14', plain,
% 57.46/57.78      (![X50 : $i]: ((k5_xboole_0 @ X50 @ o_0_0_xboole_0) = (X50))),
% 57.46/57.78      inference('demod', [status(thm)], ['12', '13'])).
% 57.46/57.78  thf('15', plain, (![X0 : $i]: ((k5_xboole_0 @ o_0_0_xboole_0 @ X0) = (X0))),
% 57.46/57.78      inference('sup+', [status(thm)], ['11', '14'])).
% 57.46/57.78  thf(t100_xboole_1, axiom,
% 57.46/57.78    (![A:$i,B:$i]:
% 57.46/57.78     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 57.46/57.78  thf('16', plain,
% 57.46/57.78      (![X13 : $i, X14 : $i]:
% 57.46/57.78         ((k4_xboole_0 @ X13 @ X14)
% 57.46/57.78           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 57.46/57.78      inference('cnf', [status(esa)], [t100_xboole_1])).
% 57.46/57.78  thf('17', plain,
% 57.46/57.78      (![X0 : $i]:
% 57.46/57.78         ((k4_xboole_0 @ o_0_0_xboole_0 @ X0)
% 57.46/57.78           = (k3_xboole_0 @ o_0_0_xboole_0 @ X0))),
% 57.46/57.78      inference('sup+', [status(thm)], ['15', '16'])).
% 57.46/57.78  thf('18', plain,
% 57.46/57.78      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 57.46/57.78      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 57.46/57.78  thf(t2_boole, axiom,
% 57.46/57.78    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 57.46/57.78  thf('19', plain,
% 57.46/57.78      (![X18 : $i]: ((k3_xboole_0 @ X18 @ k1_xboole_0) = (k1_xboole_0))),
% 57.46/57.78      inference('cnf', [status(esa)], [t2_boole])).
% 57.46/57.78  thf('20', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 57.46/57.78      inference('cnf', [status(esa)], [d2_xboole_0])).
% 57.46/57.78  thf('21', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 57.46/57.78      inference('cnf', [status(esa)], [d2_xboole_0])).
% 57.46/57.78  thf('22', plain,
% 57.46/57.78      (![X18 : $i]: ((k3_xboole_0 @ X18 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 57.46/57.78      inference('demod', [status(thm)], ['19', '20', '21'])).
% 57.46/57.78  thf('23', plain,
% 57.46/57.78      (![X0 : $i]: ((k3_xboole_0 @ o_0_0_xboole_0 @ X0) = (o_0_0_xboole_0))),
% 57.46/57.78      inference('sup+', [status(thm)], ['18', '22'])).
% 57.46/57.78  thf('24', plain,
% 57.46/57.78      (![X0 : $i]: ((k4_xboole_0 @ o_0_0_xboole_0 @ X0) = (o_0_0_xboole_0))),
% 57.46/57.78      inference('demod', [status(thm)], ['17', '23'])).
% 57.46/57.78  thf('25', plain,
% 57.46/57.78      (![X21 : $i]: ((k4_xboole_0 @ X21 @ o_0_0_xboole_0) = (X21))),
% 57.46/57.78      inference('demod', [status(thm)], ['6', '7'])).
% 57.46/57.78  thf('26', plain,
% 57.46/57.78      (![X0 : $i, X1 : $i]:
% 57.46/57.78         ((X0) = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 57.46/57.78      inference('demod', [status(thm)], ['10', '24', '25'])).
% 57.46/57.78  thf('27', plain,
% 57.46/57.78      (![X0 : $i, X1 : $i]:
% 57.46/57.78         ((X0) = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 57.46/57.78      inference('sup+', [status(thm)], ['5', '26'])).
% 57.46/57.78  thf(t40_xboole_1, axiom,
% 57.46/57.78    (![A:$i,B:$i]:
% 57.46/57.78     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 57.46/57.78  thf('28', plain,
% 57.46/57.78      (![X22 : $i, X23 : $i]:
% 57.46/57.78         ((k4_xboole_0 @ (k2_xboole_0 @ X22 @ X23) @ X23)
% 57.46/57.78           = (k4_xboole_0 @ X22 @ X23))),
% 57.46/57.78      inference('cnf', [status(esa)], [t40_xboole_1])).
% 57.46/57.78  thf(t48_xboole_1, axiom,
% 57.46/57.78    (![A:$i,B:$i]:
% 57.46/57.78     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 57.46/57.78  thf('29', plain,
% 57.46/57.78      (![X34 : $i, X35 : $i]:
% 57.46/57.78         ((k4_xboole_0 @ X34 @ (k4_xboole_0 @ X34 @ X35))
% 57.46/57.78           = (k3_xboole_0 @ X34 @ X35))),
% 57.46/57.78      inference('cnf', [status(esa)], [t48_xboole_1])).
% 57.46/57.78  thf('30', plain,
% 57.46/57.78      (![X0 : $i, X1 : $i]:
% 57.46/57.78         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 57.46/57.78           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 57.46/57.78      inference('sup+', [status(thm)], ['28', '29'])).
% 57.46/57.78  thf('31', plain,
% 57.46/57.78      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 57.46/57.78      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 57.46/57.78  thf('32', plain,
% 57.46/57.78      (![X0 : $i, X1 : $i]:
% 57.46/57.78         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 57.46/57.78           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 57.46/57.78      inference('demod', [status(thm)], ['30', '31'])).
% 57.46/57.78  thf('33', plain,
% 57.46/57.78      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 57.46/57.78      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 57.46/57.78  thf(t46_xboole_1, axiom,
% 57.46/57.78    (![A:$i,B:$i]:
% 57.46/57.78     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 57.46/57.78  thf('34', plain,
% 57.46/57.78      (![X30 : $i, X31 : $i]:
% 57.46/57.78         ((k4_xboole_0 @ X30 @ (k2_xboole_0 @ X30 @ X31)) = (k1_xboole_0))),
% 57.46/57.78      inference('cnf', [status(esa)], [t46_xboole_1])).
% 57.46/57.78  thf('35', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 57.46/57.78      inference('cnf', [status(esa)], [d2_xboole_0])).
% 57.46/57.78  thf('36', plain,
% 57.46/57.78      (![X30 : $i, X31 : $i]:
% 57.46/57.78         ((k4_xboole_0 @ X30 @ (k2_xboole_0 @ X30 @ X31)) = (o_0_0_xboole_0))),
% 57.46/57.78      inference('demod', [status(thm)], ['34', '35'])).
% 57.46/57.78  thf('37', plain,
% 57.46/57.78      (![X0 : $i, X1 : $i]:
% 57.46/57.78         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (o_0_0_xboole_0))),
% 57.46/57.78      inference('sup+', [status(thm)], ['33', '36'])).
% 57.46/57.78  thf('38', plain,
% 57.46/57.78      (![X34 : $i, X35 : $i]:
% 57.46/57.78         ((k4_xboole_0 @ X34 @ (k4_xboole_0 @ X34 @ X35))
% 57.46/57.78           = (k3_xboole_0 @ X34 @ X35))),
% 57.46/57.78      inference('cnf', [status(esa)], [t48_xboole_1])).
% 57.46/57.78  thf('39', plain,
% 57.46/57.78      (![X0 : $i, X1 : $i]:
% 57.46/57.78         ((k4_xboole_0 @ X0 @ o_0_0_xboole_0)
% 57.46/57.78           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 57.46/57.78      inference('sup+', [status(thm)], ['37', '38'])).
% 57.46/57.78  thf('40', plain,
% 57.46/57.78      (![X21 : $i]: ((k4_xboole_0 @ X21 @ o_0_0_xboole_0) = (X21))),
% 57.46/57.78      inference('demod', [status(thm)], ['6', '7'])).
% 57.46/57.78  thf('41', plain,
% 57.46/57.78      (![X0 : $i, X1 : $i]:
% 57.46/57.78         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 57.46/57.78      inference('demod', [status(thm)], ['39', '40'])).
% 57.46/57.78  thf('42', plain,
% 57.46/57.78      (![X0 : $i, X1 : $i]:
% 57.46/57.78         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 57.46/57.78           = (X0))),
% 57.46/57.78      inference('demod', [status(thm)], ['32', '41'])).
% 57.46/57.78  thf('43', plain,
% 57.46/57.78      (![X0 : $i, X1 : $i]:
% 57.46/57.78         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 57.46/57.78           = (k3_xboole_0 @ X1 @ X0))),
% 57.46/57.78      inference('sup+', [status(thm)], ['27', '42'])).
% 57.46/57.78  thf('44', plain,
% 57.46/57.78      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 57.46/57.78      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 57.46/57.78  thf(t47_xboole_1, axiom,
% 57.46/57.78    (![A:$i,B:$i]:
% 57.46/57.78     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 57.46/57.78  thf('45', plain,
% 57.46/57.78      (![X32 : $i, X33 : $i]:
% 57.46/57.78         ((k4_xboole_0 @ X32 @ (k3_xboole_0 @ X32 @ X33))
% 57.46/57.78           = (k4_xboole_0 @ X32 @ X33))),
% 57.46/57.78      inference('cnf', [status(esa)], [t47_xboole_1])).
% 57.46/57.78  thf('46', plain,
% 57.46/57.78      (![X0 : $i, X1 : $i]:
% 57.46/57.78         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 57.46/57.78           = (k4_xboole_0 @ X0 @ X1))),
% 57.46/57.78      inference('sup+', [status(thm)], ['44', '45'])).
% 57.46/57.78  thf('47', plain,
% 57.46/57.78      (![X0 : $i, X1 : $i]:
% 57.46/57.78         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 57.46/57.78           = (k3_xboole_0 @ X1 @ X0))),
% 57.46/57.78      inference('demod', [status(thm)], ['43', '46'])).
% 57.46/57.78  thf('48', plain,
% 57.46/57.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 57.46/57.78         ((k3_xboole_0 @ X2 @ 
% 57.46/57.78           (k4_xboole_0 @ X1 @ (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)))
% 57.46/57.78           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1)))),
% 57.46/57.78      inference('sup+', [status(thm)], ['4', '47'])).
% 57.46/57.78  thf('49', plain,
% 57.46/57.78      (![X36 : $i, X37 : $i, X38 : $i]:
% 57.46/57.78         ((k3_xboole_0 @ X36 @ (k4_xboole_0 @ X37 @ X38))
% 57.46/57.78           = (k4_xboole_0 @ (k3_xboole_0 @ X36 @ X37) @ X38))),
% 57.46/57.78      inference('cnf', [status(esa)], [t49_xboole_1])).
% 57.46/57.78  thf(t50_xboole_1, axiom,
% 57.46/57.78    (![A:$i,B:$i,C:$i]:
% 57.46/57.78     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 57.46/57.78       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 57.46/57.78  thf('50', plain,
% 57.46/57.78      (![X39 : $i, X40 : $i, X41 : $i]:
% 57.46/57.78         ((k3_xboole_0 @ X39 @ (k4_xboole_0 @ X40 @ X41))
% 57.46/57.78           = (k4_xboole_0 @ (k3_xboole_0 @ X39 @ X40) @ 
% 57.46/57.78              (k3_xboole_0 @ X39 @ X41)))),
% 57.46/57.78      inference('cnf', [status(esa)], [t50_xboole_1])).
% 57.46/57.78  thf('51', plain,
% 57.46/57.78      (![X36 : $i, X37 : $i, X38 : $i]:
% 57.46/57.78         ((k3_xboole_0 @ X36 @ (k4_xboole_0 @ X37 @ X38))
% 57.46/57.78           = (k4_xboole_0 @ (k3_xboole_0 @ X36 @ X37) @ X38))),
% 57.46/57.78      inference('cnf', [status(esa)], [t49_xboole_1])).
% 57.46/57.78  thf('52', plain,
% 57.46/57.78      (![X39 : $i, X40 : $i, X41 : $i]:
% 57.46/57.78         ((k3_xboole_0 @ X39 @ (k4_xboole_0 @ X40 @ X41))
% 57.46/57.78           = (k3_xboole_0 @ X39 @ 
% 57.46/57.78              (k4_xboole_0 @ X40 @ (k3_xboole_0 @ X39 @ X41))))),
% 57.46/57.78      inference('demod', [status(thm)], ['50', '51'])).
% 57.46/57.78  thf('53', plain,
% 57.46/57.78      (![X0 : $i, X1 : $i]:
% 57.46/57.78         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 57.46/57.78           = (k3_xboole_0 @ X1 @ X0))),
% 57.46/57.78      inference('demod', [status(thm)], ['43', '46'])).
% 57.46/57.78  thf('54', plain,
% 57.46/57.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 57.46/57.78         ((k3_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1))
% 57.46/57.78           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1)))),
% 57.46/57.78      inference('demod', [status(thm)], ['48', '49', '52', '53'])).
% 57.46/57.78  thf('55', plain,
% 57.46/57.78      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 57.46/57.78      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 57.46/57.78  thf('56', plain,
% 57.46/57.78      (![X44 : $i, X45 : $i, X46 : $i]:
% 57.46/57.78         ((k4_xboole_0 @ X44 @ (k4_xboole_0 @ X45 @ X46))
% 57.46/57.78           = (k2_xboole_0 @ (k4_xboole_0 @ X44 @ X45) @ 
% 57.46/57.78              (k3_xboole_0 @ X44 @ X46)))),
% 57.46/57.78      inference('cnf', [status(esa)], [t52_xboole_1])).
% 57.46/57.78  thf('57', plain,
% 57.46/57.78      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 57.46/57.78      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 57.46/57.78  thf('58', plain,
% 57.46/57.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 57.46/57.78         ((k2_xboole_0 @ (k3_xboole_0 @ X2 @ X0) @ (k4_xboole_0 @ X2 @ X1))
% 57.46/57.78           = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 57.46/57.78      inference('sup+', [status(thm)], ['56', '57'])).
% 57.46/57.78  thf('59', plain,
% 57.46/57.78      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 57.46/57.78      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 57.46/57.78  thf('60', plain,
% 57.46/57.78      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 57.46/57.78      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 57.46/57.78  thf(l98_xboole_1, axiom,
% 57.46/57.78    (![A:$i,B:$i]:
% 57.46/57.78     ( ( k5_xboole_0 @ A @ B ) =
% 57.46/57.78       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 57.46/57.78  thf('61', plain,
% 57.46/57.78      (![X11 : $i, X12 : $i]:
% 57.46/57.78         ((k5_xboole_0 @ X11 @ X12)
% 57.46/57.78           = (k4_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ 
% 57.46/57.78              (k3_xboole_0 @ X11 @ X12)))),
% 57.46/57.78      inference('cnf', [status(esa)], [l98_xboole_1])).
% 57.46/57.78  thf('62', plain,
% 57.46/57.78      (![X0 : $i, X1 : $i]:
% 57.46/57.78         ((k5_xboole_0 @ X0 @ X1)
% 57.46/57.78           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 57.46/57.78      inference('sup+', [status(thm)], ['60', '61'])).
% 57.46/57.78  thf('63', plain,
% 57.46/57.78      (![X0 : $i, X1 : $i]:
% 57.46/57.78         ((k5_xboole_0 @ X0 @ X1)
% 57.46/57.78           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 57.46/57.78      inference('sup+', [status(thm)], ['59', '62'])).
% 57.46/57.78  thf('64', plain,
% 57.46/57.78      (![X4 : $i, X5 : $i]: ((k5_xboole_0 @ X5 @ X4) = (k5_xboole_0 @ X4 @ X5))),
% 57.46/57.78      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 57.46/57.78  thf('65', plain,
% 57.46/57.78      (((k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))
% 57.46/57.78         != (k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 57.46/57.78      inference('demod', [status(thm)], ['3', '54', '55', '58', '63', '64'])).
% 57.46/57.78  thf('66', plain, ($false), inference('simplify', [status(thm)], ['65'])).
% 57.46/57.78  
% 57.46/57.78  % SZS output end Refutation
% 57.46/57.78  
% 57.55/57.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kR7j4JQ0Es

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:12 EST 2020

% Result     : Theorem 0.97s
% Output     : Refutation 0.97s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 203 expanded)
%              Number of leaves         :   22 (  73 expanded)
%              Depth                    :   19
%              Number of atoms          :  702 (1530 expanded)
%              Number of equality atoms :   91 ( 201 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t100_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k4_xboole_0 @ A @ B )
        = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t100_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k3_xboole_0 @ X21 @ X22 ) )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k2_xboole_0 @ X33 @ X34 )
      = ( k5_xboole_0 @ X33 @ ( k4_xboole_0 @ X34 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('17',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k3_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X27 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X25 @ X26 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k3_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X27 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X25 @ X26 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k3_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X27 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X25 @ X26 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('25',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k2_xboole_0 @ X33 @ X34 )
      = ( k5_xboole_0 @ X33 @ ( k4_xboole_0 @ X34 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('28',plain,(
    ! [X28: $i] :
      ( ( k5_xboole_0 @ X28 @ k1_xboole_0 )
      = X28 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['18','29'])).

thf('31',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k2_xboole_0 @ X33 @ X34 )
      = ( k5_xboole_0 @ X33 @ ( k4_xboole_0 @ X34 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('32',plain,(
    ! [X32: $i] :
      ( ( k5_xboole_0 @ X32 @ X32 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('33',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X29 @ X30 ) @ X31 )
      = ( k5_xboole_0 @ X29 @ ( k5_xboole_0 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('35',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('36',plain,(
    ! [X28: $i] :
      ( ( k5_xboole_0 @ X28 @ k1_xboole_0 )
      = X28 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','39'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('41',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('42',plain,(
    ! [X32: $i] :
      ( ( k5_xboole_0 @ X32 @ X32 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('44',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf(t32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = ( k4_xboole_0 @ B @ A ) )
     => ( A = B ) ) )).

thf('45',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X12 = X11 )
      | ( ( k4_xboole_0 @ X12 @ X11 )
       != ( k4_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t32_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != ( k4_xboole_0 @ X1 @ X0 ) )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
       != ( k4_xboole_0 @ X1 @ X0 ) )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['43','48'])).

thf('50',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('51',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k2_xboole_0 @ X33 @ X34 )
      = ( k5_xboole_0 @ X33 @ ( k4_xboole_0 @ X34 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k2_xboole_0 @ X33 @ X34 )
      = ( k5_xboole_0 @ X33 @ ( k4_xboole_0 @ X34 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['49','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('61',plain,(
    ! [X28: $i] :
      ( ( k5_xboole_0 @ X28 @ k1_xboole_0 )
      = X28 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','56','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','67'])).

thf('69',plain,(
    $false ),
    inference(simplify,[status(thm)],['68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kR7j4JQ0Es
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:00:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.97/1.19  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.97/1.19  % Solved by: fo/fo7.sh
% 0.97/1.19  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.97/1.19  % done 1375 iterations in 0.742s
% 0.97/1.19  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.97/1.19  % SZS output start Refutation
% 0.97/1.19  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.97/1.19  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.97/1.19  thf(sk_A_type, type, sk_A: $i).
% 0.97/1.19  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.97/1.19  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.97/1.19  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.97/1.19  thf(sk_B_type, type, sk_B: $i).
% 0.97/1.19  thf(t100_xboole_1, conjecture,
% 0.97/1.19    (![A:$i,B:$i]:
% 0.97/1.19     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.97/1.19  thf(zf_stmt_0, negated_conjecture,
% 0.97/1.19    (~( ![A:$i,B:$i]:
% 0.97/1.19        ( ( k4_xboole_0 @ A @ B ) =
% 0.97/1.19          ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.97/1.19    inference('cnf.neg', [status(esa)], [t100_xboole_1])).
% 0.97/1.19  thf('0', plain,
% 0.97/1.19      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.97/1.19         != (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.97/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.19  thf(commutativity_k3_xboole_0, axiom,
% 0.97/1.19    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.97/1.19  thf('1', plain,
% 0.97/1.19      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.97/1.19      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.97/1.19  thf('2', plain,
% 0.97/1.19      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.97/1.19         != (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.97/1.19      inference('demod', [status(thm)], ['0', '1'])).
% 0.97/1.19  thf('3', plain,
% 0.97/1.19      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.97/1.19      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.97/1.19  thf(t47_xboole_1, axiom,
% 0.97/1.19    (![A:$i,B:$i]:
% 0.97/1.19     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.97/1.19  thf('4', plain,
% 0.97/1.19      (![X21 : $i, X22 : $i]:
% 0.97/1.19         ((k4_xboole_0 @ X21 @ (k3_xboole_0 @ X21 @ X22))
% 0.97/1.19           = (k4_xboole_0 @ X21 @ X22))),
% 0.97/1.19      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.97/1.19  thf('5', plain,
% 0.97/1.19      (![X0 : $i, X1 : $i]:
% 0.97/1.19         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.97/1.19           = (k4_xboole_0 @ X0 @ X1))),
% 0.97/1.19      inference('sup+', [status(thm)], ['3', '4'])).
% 0.97/1.19  thf(t98_xboole_1, axiom,
% 0.97/1.19    (![A:$i,B:$i]:
% 0.97/1.19     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.97/1.19  thf('6', plain,
% 0.97/1.19      (![X33 : $i, X34 : $i]:
% 0.97/1.19         ((k2_xboole_0 @ X33 @ X34)
% 0.97/1.19           = (k5_xboole_0 @ X33 @ (k4_xboole_0 @ X34 @ X33)))),
% 0.97/1.19      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.97/1.19  thf('7', plain,
% 0.97/1.19      (![X0 : $i, X1 : $i]:
% 0.97/1.19         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X1)
% 0.97/1.19           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.97/1.19      inference('sup+', [status(thm)], ['5', '6'])).
% 0.97/1.19  thf(t3_boole, axiom,
% 0.97/1.19    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.97/1.19  thf('8', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.97/1.19      inference('cnf', [status(esa)], [t3_boole])).
% 0.97/1.19  thf(t48_xboole_1, axiom,
% 0.97/1.19    (![A:$i,B:$i]:
% 0.97/1.19     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.97/1.19  thf('9', plain,
% 0.97/1.19      (![X23 : $i, X24 : $i]:
% 0.97/1.19         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 0.97/1.19           = (k3_xboole_0 @ X23 @ X24))),
% 0.97/1.19      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.97/1.19  thf('10', plain,
% 0.97/1.19      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.97/1.19      inference('sup+', [status(thm)], ['8', '9'])).
% 0.97/1.19  thf(t2_boole, axiom,
% 0.97/1.19    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.97/1.19  thf('11', plain,
% 0.97/1.19      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.97/1.19      inference('cnf', [status(esa)], [t2_boole])).
% 0.97/1.19  thf('12', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.97/1.19      inference('demod', [status(thm)], ['10', '11'])).
% 0.97/1.19  thf('13', plain,
% 0.97/1.19      (![X23 : $i, X24 : $i]:
% 0.97/1.19         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 0.97/1.19           = (k3_xboole_0 @ X23 @ X24))),
% 0.97/1.19      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.97/1.19  thf('14', plain,
% 0.97/1.19      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.97/1.19      inference('sup+', [status(thm)], ['12', '13'])).
% 0.97/1.19  thf('15', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.97/1.19      inference('cnf', [status(esa)], [t3_boole])).
% 0.97/1.19  thf('16', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.97/1.19      inference('demod', [status(thm)], ['14', '15'])).
% 0.97/1.19  thf(t49_xboole_1, axiom,
% 0.97/1.19    (![A:$i,B:$i,C:$i]:
% 0.97/1.19     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.97/1.19       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.97/1.19  thf('17', plain,
% 0.97/1.19      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.97/1.19         ((k3_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X27))
% 0.97/1.19           = (k4_xboole_0 @ (k3_xboole_0 @ X25 @ X26) @ X27))),
% 0.97/1.19      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.97/1.19  thf('18', plain,
% 0.97/1.19      (![X0 : $i, X1 : $i]:
% 0.97/1.19         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.97/1.19           = (k4_xboole_0 @ X0 @ X1))),
% 0.97/1.19      inference('sup+', [status(thm)], ['16', '17'])).
% 0.97/1.19  thf('19', plain,
% 0.97/1.19      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.97/1.19         ((k3_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X27))
% 0.97/1.19           = (k4_xboole_0 @ (k3_xboole_0 @ X25 @ X26) @ X27))),
% 0.97/1.19      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.97/1.19  thf('20', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.97/1.19      inference('demod', [status(thm)], ['10', '11'])).
% 0.97/1.19  thf('21', plain,
% 0.97/1.19      (![X0 : $i, X1 : $i]:
% 0.97/1.19         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 0.97/1.19           = (k1_xboole_0))),
% 0.97/1.19      inference('sup+', [status(thm)], ['19', '20'])).
% 0.97/1.19  thf('22', plain,
% 0.97/1.19      (![X0 : $i, X1 : $i]:
% 0.97/1.19         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.97/1.19           = (k4_xboole_0 @ X0 @ X1))),
% 0.97/1.19      inference('sup+', [status(thm)], ['3', '4'])).
% 0.97/1.19  thf('23', plain,
% 0.97/1.19      (![X0 : $i, X1 : $i]:
% 0.97/1.19         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.97/1.19      inference('demod', [status(thm)], ['21', '22'])).
% 0.97/1.19  thf('24', plain,
% 0.97/1.19      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.97/1.19         ((k3_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X27))
% 0.97/1.19           = (k4_xboole_0 @ (k3_xboole_0 @ X25 @ X26) @ X27))),
% 0.97/1.19      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.97/1.19  thf('25', plain,
% 0.97/1.19      (![X33 : $i, X34 : $i]:
% 0.97/1.19         ((k2_xboole_0 @ X33 @ X34)
% 0.97/1.19           = (k5_xboole_0 @ X33 @ (k4_xboole_0 @ X34 @ X33)))),
% 0.97/1.19      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.97/1.19  thf('26', plain,
% 0.97/1.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.19         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 0.97/1.19           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.97/1.19      inference('sup+', [status(thm)], ['24', '25'])).
% 0.97/1.19  thf('27', plain,
% 0.97/1.19      (![X0 : $i, X1 : $i]:
% 0.97/1.19         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.97/1.19           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.97/1.19      inference('sup+', [status(thm)], ['23', '26'])).
% 0.97/1.19  thf(t5_boole, axiom,
% 0.97/1.19    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.97/1.19  thf('28', plain, (![X28 : $i]: ((k5_xboole_0 @ X28 @ k1_xboole_0) = (X28))),
% 0.97/1.19      inference('cnf', [status(esa)], [t5_boole])).
% 0.97/1.19  thf('29', plain,
% 0.97/1.19      (![X0 : $i, X1 : $i]:
% 0.97/1.19         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) = (X0))),
% 0.97/1.19      inference('demod', [status(thm)], ['27', '28'])).
% 0.97/1.19  thf('30', plain,
% 0.97/1.19      (![X0 : $i, X1 : $i]:
% 0.97/1.19         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 0.97/1.19      inference('sup+', [status(thm)], ['18', '29'])).
% 0.97/1.19  thf('31', plain,
% 0.97/1.19      (![X33 : $i, X34 : $i]:
% 0.97/1.19         ((k2_xboole_0 @ X33 @ X34)
% 0.97/1.19           = (k5_xboole_0 @ X33 @ (k4_xboole_0 @ X34 @ X33)))),
% 0.97/1.19      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.97/1.19  thf(t92_xboole_1, axiom,
% 0.97/1.19    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.97/1.19  thf('32', plain, (![X32 : $i]: ((k5_xboole_0 @ X32 @ X32) = (k1_xboole_0))),
% 0.97/1.19      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.97/1.19  thf(t91_xboole_1, axiom,
% 0.97/1.19    (![A:$i,B:$i,C:$i]:
% 0.97/1.19     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.97/1.19       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.97/1.19  thf('33', plain,
% 0.97/1.19      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.97/1.19         ((k5_xboole_0 @ (k5_xboole_0 @ X29 @ X30) @ X31)
% 0.97/1.19           = (k5_xboole_0 @ X29 @ (k5_xboole_0 @ X30 @ X31)))),
% 0.97/1.19      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.97/1.19  thf('34', plain,
% 0.97/1.19      (![X0 : $i, X1 : $i]:
% 0.97/1.19         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.97/1.19           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.97/1.19      inference('sup+', [status(thm)], ['32', '33'])).
% 0.97/1.19  thf(commutativity_k5_xboole_0, axiom,
% 0.97/1.19    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.97/1.19  thf('35', plain,
% 0.97/1.19      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.97/1.19      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.97/1.19  thf('36', plain, (![X28 : $i]: ((k5_xboole_0 @ X28 @ k1_xboole_0) = (X28))),
% 0.97/1.19      inference('cnf', [status(esa)], [t5_boole])).
% 0.97/1.19  thf('37', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.97/1.19      inference('sup+', [status(thm)], ['35', '36'])).
% 0.97/1.19  thf('38', plain,
% 0.97/1.19      (![X0 : $i, X1 : $i]:
% 0.97/1.19         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.97/1.19      inference('demod', [status(thm)], ['34', '37'])).
% 0.97/1.19  thf('39', plain,
% 0.97/1.19      (![X0 : $i, X1 : $i]:
% 0.97/1.19         ((k4_xboole_0 @ X0 @ X1)
% 0.97/1.19           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.97/1.19      inference('sup+', [status(thm)], ['31', '38'])).
% 0.97/1.19  thf('40', plain,
% 0.97/1.19      (![X0 : $i, X1 : $i]:
% 0.97/1.19         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.97/1.19           = (k5_xboole_0 @ X0 @ X0))),
% 0.97/1.19      inference('sup+', [status(thm)], ['30', '39'])).
% 0.97/1.19  thf(t41_xboole_1, axiom,
% 0.97/1.19    (![A:$i,B:$i,C:$i]:
% 0.97/1.19     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.97/1.19       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.97/1.19  thf('41', plain,
% 0.97/1.19      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.97/1.19         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.97/1.19           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.97/1.19      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.97/1.19  thf('42', plain, (![X32 : $i]: ((k5_xboole_0 @ X32 @ X32) = (k1_xboole_0))),
% 0.97/1.19      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.97/1.19  thf('43', plain,
% 0.97/1.19      (![X0 : $i, X1 : $i]:
% 0.97/1.19         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.97/1.19      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.97/1.19  thf(t40_xboole_1, axiom,
% 0.97/1.19    (![A:$i,B:$i]:
% 0.97/1.19     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.97/1.19  thf('44', plain,
% 0.97/1.19      (![X14 : $i, X15 : $i]:
% 0.97/1.19         ((k4_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ X15)
% 0.97/1.19           = (k4_xboole_0 @ X14 @ X15))),
% 0.97/1.19      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.97/1.19  thf(t32_xboole_1, axiom,
% 0.97/1.19    (![A:$i,B:$i]:
% 0.97/1.19     ( ( ( k4_xboole_0 @ A @ B ) = ( k4_xboole_0 @ B @ A ) ) =>
% 0.97/1.19       ( ( A ) = ( B ) ) ))).
% 0.97/1.19  thf('45', plain,
% 0.97/1.19      (![X11 : $i, X12 : $i]:
% 0.97/1.19         (((X12) = (X11))
% 0.97/1.19          | ((k4_xboole_0 @ X12 @ X11) != (k4_xboole_0 @ X11 @ X12)))),
% 0.97/1.19      inference('cnf', [status(esa)], [t32_xboole_1])).
% 0.97/1.19  thf('46', plain,
% 0.97/1.19      (![X0 : $i, X1 : $i]:
% 0.97/1.19         (((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.97/1.19            != (k4_xboole_0 @ X1 @ X0))
% 0.97/1.19          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 0.97/1.19      inference('sup-', [status(thm)], ['44', '45'])).
% 0.97/1.19  thf('47', plain,
% 0.97/1.19      (![X0 : $i, X1 : $i]:
% 0.97/1.19         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.97/1.19      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.97/1.19  thf('48', plain,
% 0.97/1.19      (![X0 : $i, X1 : $i]:
% 0.97/1.19         (((k1_xboole_0) != (k4_xboole_0 @ X1 @ X0))
% 0.97/1.19          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 0.97/1.19      inference('demod', [status(thm)], ['46', '47'])).
% 0.97/1.19  thf('49', plain,
% 0.97/1.19      (![X0 : $i, X1 : $i]:
% 0.97/1.19         (((k1_xboole_0) != (k1_xboole_0))
% 0.97/1.19          | ((k2_xboole_0 @ X1 @ X0)
% 0.97/1.19              = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))))),
% 0.97/1.19      inference('sup-', [status(thm)], ['43', '48'])).
% 0.97/1.19  thf('50', plain,
% 0.97/1.19      (![X14 : $i, X15 : $i]:
% 0.97/1.19         ((k4_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ X15)
% 0.97/1.19           = (k4_xboole_0 @ X14 @ X15))),
% 0.97/1.19      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.97/1.19  thf('51', plain,
% 0.97/1.19      (![X33 : $i, X34 : $i]:
% 0.97/1.19         ((k2_xboole_0 @ X33 @ X34)
% 0.97/1.19           = (k5_xboole_0 @ X33 @ (k4_xboole_0 @ X34 @ X33)))),
% 0.97/1.19      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.97/1.19  thf('52', plain,
% 0.97/1.19      (![X0 : $i, X1 : $i]:
% 0.97/1.19         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.97/1.19           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.97/1.19      inference('sup+', [status(thm)], ['50', '51'])).
% 0.97/1.19  thf('53', plain,
% 0.97/1.19      (![X33 : $i, X34 : $i]:
% 0.97/1.19         ((k2_xboole_0 @ X33 @ X34)
% 0.97/1.19           = (k5_xboole_0 @ X33 @ (k4_xboole_0 @ X34 @ X33)))),
% 0.97/1.19      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.97/1.19  thf('54', plain,
% 0.97/1.19      (![X0 : $i, X1 : $i]:
% 0.97/1.19         ((k2_xboole_0 @ X0 @ X1)
% 0.97/1.19           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.97/1.19      inference('sup+', [status(thm)], ['52', '53'])).
% 0.97/1.19  thf('55', plain,
% 0.97/1.19      (![X0 : $i, X1 : $i]:
% 0.97/1.19         (((k1_xboole_0) != (k1_xboole_0))
% 0.97/1.19          | ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1)))),
% 0.97/1.19      inference('demod', [status(thm)], ['49', '54'])).
% 0.97/1.19  thf('56', plain,
% 0.97/1.19      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.97/1.19      inference('simplify', [status(thm)], ['55'])).
% 0.97/1.19  thf('57', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.97/1.19      inference('demod', [status(thm)], ['10', '11'])).
% 0.97/1.19  thf('58', plain,
% 0.97/1.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.19         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 0.97/1.19           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.97/1.19      inference('sup+', [status(thm)], ['24', '25'])).
% 0.97/1.19  thf('59', plain,
% 0.97/1.19      (![X0 : $i, X1 : $i]:
% 0.97/1.19         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.97/1.19           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ k1_xboole_0)))),
% 0.97/1.19      inference('sup+', [status(thm)], ['57', '58'])).
% 0.97/1.19  thf('60', plain,
% 0.97/1.19      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.97/1.19      inference('cnf', [status(esa)], [t2_boole])).
% 0.97/1.19  thf('61', plain, (![X28 : $i]: ((k5_xboole_0 @ X28 @ k1_xboole_0) = (X28))),
% 0.97/1.19      inference('cnf', [status(esa)], [t5_boole])).
% 0.97/1.19  thf('62', plain,
% 0.97/1.19      (![X0 : $i, X1 : $i]:
% 0.97/1.19         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 0.97/1.19      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.97/1.19  thf('63', plain,
% 0.97/1.19      (![X0 : $i, X1 : $i]:
% 0.97/1.19         ((X1)
% 0.97/1.19           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.97/1.19      inference('demod', [status(thm)], ['7', '56', '62'])).
% 0.97/1.19  thf('64', plain,
% 0.97/1.19      (![X0 : $i, X1 : $i]:
% 0.97/1.19         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.97/1.19      inference('demod', [status(thm)], ['34', '37'])).
% 0.97/1.19  thf('65', plain,
% 0.97/1.19      (![X0 : $i, X1 : $i]:
% 0.97/1.19         ((k4_xboole_0 @ X0 @ X1)
% 0.97/1.19           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.97/1.19      inference('sup+', [status(thm)], ['63', '64'])).
% 0.97/1.19  thf('66', plain,
% 0.97/1.19      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.97/1.19      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.97/1.19  thf('67', plain,
% 0.97/1.19      (![X0 : $i, X1 : $i]:
% 0.97/1.19         ((k4_xboole_0 @ X0 @ X1)
% 0.97/1.19           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.97/1.19      inference('demod', [status(thm)], ['65', '66'])).
% 0.97/1.19  thf('68', plain,
% 0.97/1.19      (((k4_xboole_0 @ sk_A @ sk_B) != (k4_xboole_0 @ sk_A @ sk_B))),
% 0.97/1.19      inference('demod', [status(thm)], ['2', '67'])).
% 0.97/1.19  thf('69', plain, ($false), inference('simplify', [status(thm)], ['68'])).
% 0.97/1.19  
% 0.97/1.19  % SZS output end Refutation
% 0.97/1.19  
% 0.97/1.20  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

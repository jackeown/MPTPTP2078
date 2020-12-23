%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xeo111zYkF

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:02 EST 2020

% Result     : Theorem 4.82s
% Output     : Refutation 4.82s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 174 expanded)
%              Number of leaves         :   30 (  66 expanded)
%              Depth                    :   17
%              Number of atoms          :  900 (1313 expanded)
%              Number of equality atoms :   87 ( 138 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t96_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t96_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) @ ( k5_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('1',plain,(
    ! [X30: $i] :
      ( ( k4_xboole_0 @ X30 @ k1_xboole_0 )
      = X30 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('2',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X26 @ X27 ) @ X26 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X14: $i,X16: $i] :
      ( ( ( k4_xboole_0 @ X14 @ X16 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k4_xboole_0 @ X36 @ ( k4_xboole_0 @ X36 @ X37 ) )
      = ( k3_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X30: $i] :
      ( ( k4_xboole_0 @ X30 @ k1_xboole_0 )
      = X30 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('9',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t23_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('10',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ ( k3_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf(l98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ X17 @ X18 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X17 @ X18 ) @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k3_xboole_0 @ X2 @ X0 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('13',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( k3_xboole_0 @ X38 @ ( k4_xboole_0 @ X39 @ X40 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X38 @ X39 ) @ X40 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k3_xboole_0 @ X2 @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k4_xboole_0 @ X34 @ ( k3_xboole_0 @ X34 @ X35 ) )
      = ( k4_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k2_xboole_0 @ X28 @ ( k4_xboole_0 @ X29 @ X28 ) )
      = ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k4_xboole_0 @ X36 @ ( k4_xboole_0 @ X36 @ X37 ) )
      = ( k3_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('24',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( k3_xboole_0 @ X38 @ ( k4_xboole_0 @ X39 @ X40 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X38 @ X39 ) @ X40 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('26',plain,(
    ! [X62: $i,X63: $i] :
      ( ( k2_xboole_0 @ X62 @ X63 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X62 @ X63 ) @ ( k3_xboole_0 @ X62 @ X63 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('27',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X58 @ X59 ) @ X60 )
      = ( k5_xboole_0 @ X58 @ ( k5_xboole_0 @ X59 @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('28',plain,(
    ! [X62: $i,X63: $i] :
      ( ( k2_xboole_0 @ X62 @ X63 )
      = ( k5_xboole_0 @ X62 @ ( k5_xboole_0 @ X63 @ ( k3_xboole_0 @ X62 @ X63 ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('30',plain,(
    ! [X61: $i] :
      ( ( k5_xboole_0 @ X61 @ X61 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('32',plain,(
    ! [X45: $i] :
      ( ( k5_xboole_0 @ X45 @ k1_xboole_0 )
      = X45 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['22','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['21','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('37',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k4_xboole_0 @ X36 @ ( k4_xboole_0 @ X36 @ X37 ) )
      = ( k3_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('38',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X26 @ X27 ) @ X26 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X14: $i,X16: $i] :
      ( ( ( k4_xboole_0 @ X14 @ X16 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( k3_xboole_0 @ X38 @ ( k4_xboole_0 @ X39 @ X40 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X38 @ X39 ) @ X40 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ X17 @ X18 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X17 @ X18 ) @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k2_xboole_0 @ X28 @ ( k4_xboole_0 @ X29 @ X28 ) )
      = ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('47',plain,(
    ! [X30: $i] :
      ( ( k4_xboole_0 @ X30 @ k1_xboole_0 )
      = X30 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ! [X61: $i] :
      ( ( k5_xboole_0 @ X61 @ X61 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('50',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X58 @ X59 ) @ X60 )
      = ( k5_xboole_0 @ X58 @ ( k5_xboole_0 @ X59 @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('52',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('53',plain,(
    ! [X45: $i] :
      ( ( k5_xboole_0 @ X45 @ k1_xboole_0 )
      = X45 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','57'])).

thf('59',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( k3_xboole_0 @ X38 @ ( k4_xboole_0 @ X39 @ X40 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X38 @ X39 ) @ X40 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('60',plain,(
    ! [X46: $i,X47: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X46 @ X47 ) @ X47 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('61',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('63',plain,(
    ! [X50: $i,X51: $i] :
      ( ( ( k4_xboole_0 @ X50 @ X51 )
        = X50 )
      | ~ ( r1_xboole_0 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['58','59','64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k4_xboole_0 @ X34 @ ( k3_xboole_0 @ X34 @ X35 ) )
      = ( k4_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('70',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k4_xboole_0 @ X36 @ ( k4_xboole_0 @ X36 @ X37 ) )
      = ( k3_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k4_xboole_0 @ X36 @ ( k4_xboole_0 @ X36 @ X37 ) )
      = ( k3_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ X17 @ X18 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X17 @ X18 ) @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['15','16','68','73','74'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('76',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t31_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ ( k2_xboole_0 @ B @ C ) ) )).

thf('77',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X23 @ X24 ) @ ( k3_xboole_0 @ X23 @ X25 ) ) @ ( k2_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t31_xboole_1])).

thf('78',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ ( k3_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('79',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X23 @ ( k2_xboole_0 @ X24 @ X25 ) ) @ ( k2_xboole_0 @ X24 @ X25 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['76','79'])).

thf('81',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['75','82'])).

thf('84',plain,(
    $false ),
    inference(demod,[status(thm)],['0','83'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xeo111zYkF
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:26:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 4.82/5.02  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.82/5.02  % Solved by: fo/fo7.sh
% 4.82/5.02  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.82/5.02  % done 8657 iterations in 4.601s
% 4.82/5.02  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.82/5.02  % SZS output start Refutation
% 4.82/5.02  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 4.82/5.02  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.82/5.02  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.82/5.02  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.82/5.02  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.82/5.02  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.82/5.02  thf(sk_B_1_type, type, sk_B_1: $i).
% 4.82/5.02  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 4.82/5.02  thf(sk_A_type, type, sk_A: $i).
% 4.82/5.02  thf(t96_xboole_1, conjecture,
% 4.82/5.02    (![A:$i,B:$i]:
% 4.82/5.02     ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 4.82/5.02  thf(zf_stmt_0, negated_conjecture,
% 4.82/5.02    (~( ![A:$i,B:$i]:
% 4.82/5.02        ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )),
% 4.82/5.02    inference('cnf.neg', [status(esa)], [t96_xboole_1])).
% 4.82/5.02  thf('0', plain,
% 4.82/5.02      (~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B_1) @ 
% 4.82/5.02          (k5_xboole_0 @ sk_A @ sk_B_1))),
% 4.82/5.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.82/5.02  thf(t3_boole, axiom,
% 4.82/5.02    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 4.82/5.02  thf('1', plain, (![X30 : $i]: ((k4_xboole_0 @ X30 @ k1_xboole_0) = (X30))),
% 4.82/5.02      inference('cnf', [status(esa)], [t3_boole])).
% 4.82/5.02  thf(t36_xboole_1, axiom,
% 4.82/5.02    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 4.82/5.02  thf('2', plain,
% 4.82/5.02      (![X26 : $i, X27 : $i]: (r1_tarski @ (k4_xboole_0 @ X26 @ X27) @ X26)),
% 4.82/5.02      inference('cnf', [status(esa)], [t36_xboole_1])).
% 4.82/5.02  thf('3', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 4.82/5.02      inference('sup+', [status(thm)], ['1', '2'])).
% 4.82/5.02  thf(l32_xboole_1, axiom,
% 4.82/5.02    (![A:$i,B:$i]:
% 4.82/5.02     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 4.82/5.02  thf('4', plain,
% 4.82/5.02      (![X14 : $i, X16 : $i]:
% 4.82/5.02         (((k4_xboole_0 @ X14 @ X16) = (k1_xboole_0))
% 4.82/5.02          | ~ (r1_tarski @ X14 @ X16))),
% 4.82/5.02      inference('cnf', [status(esa)], [l32_xboole_1])).
% 4.82/5.02  thf('5', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 4.82/5.02      inference('sup-', [status(thm)], ['3', '4'])).
% 4.82/5.02  thf(t48_xboole_1, axiom,
% 4.82/5.02    (![A:$i,B:$i]:
% 4.82/5.02     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 4.82/5.02  thf('6', plain,
% 4.82/5.02      (![X36 : $i, X37 : $i]:
% 4.82/5.02         ((k4_xboole_0 @ X36 @ (k4_xboole_0 @ X36 @ X37))
% 4.82/5.02           = (k3_xboole_0 @ X36 @ X37))),
% 4.82/5.02      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.82/5.02  thf('7', plain,
% 4.82/5.02      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 4.82/5.02      inference('sup+', [status(thm)], ['5', '6'])).
% 4.82/5.02  thf('8', plain, (![X30 : $i]: ((k4_xboole_0 @ X30 @ k1_xboole_0) = (X30))),
% 4.82/5.02      inference('cnf', [status(esa)], [t3_boole])).
% 4.82/5.02  thf('9', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 4.82/5.02      inference('demod', [status(thm)], ['7', '8'])).
% 4.82/5.02  thf(t23_xboole_1, axiom,
% 4.82/5.02    (![A:$i,B:$i,C:$i]:
% 4.82/5.02     ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 4.82/5.02       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 4.82/5.02  thf('10', plain,
% 4.82/5.02      (![X19 : $i, X20 : $i, X21 : $i]:
% 4.82/5.02         ((k3_xboole_0 @ X19 @ (k2_xboole_0 @ X20 @ X21))
% 4.82/5.02           = (k2_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ 
% 4.82/5.02              (k3_xboole_0 @ X19 @ X21)))),
% 4.82/5.02      inference('cnf', [status(esa)], [t23_xboole_1])).
% 4.82/5.02  thf(l98_xboole_1, axiom,
% 4.82/5.02    (![A:$i,B:$i]:
% 4.82/5.02     ( ( k5_xboole_0 @ A @ B ) =
% 4.82/5.02       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 4.82/5.02  thf('11', plain,
% 4.82/5.02      (![X17 : $i, X18 : $i]:
% 4.82/5.02         ((k5_xboole_0 @ X17 @ X18)
% 4.82/5.02           = (k4_xboole_0 @ (k2_xboole_0 @ X17 @ X18) @ 
% 4.82/5.02              (k3_xboole_0 @ X17 @ X18)))),
% 4.82/5.02      inference('cnf', [status(esa)], [l98_xboole_1])).
% 4.82/5.02  thf('12', plain,
% 4.82/5.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.82/5.02         ((k5_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ (k3_xboole_0 @ X2 @ X0))
% 4.82/5.02           = (k4_xboole_0 @ (k3_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 4.82/5.02              (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ (k3_xboole_0 @ X2 @ X0))))),
% 4.82/5.02      inference('sup+', [status(thm)], ['10', '11'])).
% 4.82/5.02  thf(t49_xboole_1, axiom,
% 4.82/5.02    (![A:$i,B:$i,C:$i]:
% 4.82/5.02     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 4.82/5.02       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 4.82/5.02  thf('13', plain,
% 4.82/5.02      (![X38 : $i, X39 : $i, X40 : $i]:
% 4.82/5.02         ((k3_xboole_0 @ X38 @ (k4_xboole_0 @ X39 @ X40))
% 4.82/5.02           = (k4_xboole_0 @ (k3_xboole_0 @ X38 @ X39) @ X40))),
% 4.82/5.02      inference('cnf', [status(esa)], [t49_xboole_1])).
% 4.82/5.02  thf('14', plain,
% 4.82/5.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.82/5.02         ((k5_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ (k3_xboole_0 @ X2 @ X0))
% 4.82/5.02           = (k3_xboole_0 @ X2 @ 
% 4.82/5.02              (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 4.82/5.02               (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ (k3_xboole_0 @ X2 @ X0)))))),
% 4.82/5.02      inference('demod', [status(thm)], ['12', '13'])).
% 4.82/5.02  thf('15', plain,
% 4.82/5.02      (![X0 : $i, X1 : $i]:
% 4.82/5.02         ((k5_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 4.82/5.02           = (k3_xboole_0 @ X0 @ 
% 4.82/5.02              (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ 
% 4.82/5.02               (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))))),
% 4.82/5.02      inference('sup+', [status(thm)], ['9', '14'])).
% 4.82/5.02  thf('16', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 4.82/5.02      inference('demod', [status(thm)], ['7', '8'])).
% 4.82/5.02  thf(t47_xboole_1, axiom,
% 4.82/5.02    (![A:$i,B:$i]:
% 4.82/5.02     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 4.82/5.02  thf('17', plain,
% 4.82/5.02      (![X34 : $i, X35 : $i]:
% 4.82/5.02         ((k4_xboole_0 @ X34 @ (k3_xboole_0 @ X34 @ X35))
% 4.82/5.02           = (k4_xboole_0 @ X34 @ X35))),
% 4.82/5.02      inference('cnf', [status(esa)], [t47_xboole_1])).
% 4.82/5.02  thf(t39_xboole_1, axiom,
% 4.82/5.02    (![A:$i,B:$i]:
% 4.82/5.02     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 4.82/5.02  thf('18', plain,
% 4.82/5.02      (![X28 : $i, X29 : $i]:
% 4.82/5.02         ((k2_xboole_0 @ X28 @ (k4_xboole_0 @ X29 @ X28))
% 4.82/5.02           = (k2_xboole_0 @ X28 @ X29))),
% 4.82/5.02      inference('cnf', [status(esa)], [t39_xboole_1])).
% 4.82/5.02  thf('19', plain,
% 4.82/5.02      (![X0 : $i, X1 : $i]:
% 4.82/5.02         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 4.82/5.02           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 4.82/5.02      inference('sup+', [status(thm)], ['17', '18'])).
% 4.82/5.02  thf(commutativity_k2_xboole_0, axiom,
% 4.82/5.02    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 4.82/5.02  thf('20', plain,
% 4.82/5.02      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.82/5.02      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.82/5.02  thf('21', plain,
% 4.82/5.02      (![X0 : $i, X1 : $i]:
% 4.82/5.02         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 4.82/5.02           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 4.82/5.02      inference('demod', [status(thm)], ['19', '20'])).
% 4.82/5.02  thf('22', plain,
% 4.82/5.02      (![X36 : $i, X37 : $i]:
% 4.82/5.02         ((k4_xboole_0 @ X36 @ (k4_xboole_0 @ X36 @ X37))
% 4.82/5.02           = (k3_xboole_0 @ X36 @ X37))),
% 4.82/5.02      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.82/5.02  thf('23', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 4.82/5.02      inference('demod', [status(thm)], ['7', '8'])).
% 4.82/5.02  thf('24', plain,
% 4.82/5.02      (![X38 : $i, X39 : $i, X40 : $i]:
% 4.82/5.02         ((k3_xboole_0 @ X38 @ (k4_xboole_0 @ X39 @ X40))
% 4.82/5.02           = (k4_xboole_0 @ (k3_xboole_0 @ X38 @ X39) @ X40))),
% 4.82/5.02      inference('cnf', [status(esa)], [t49_xboole_1])).
% 4.82/5.02  thf('25', plain,
% 4.82/5.02      (![X0 : $i, X1 : $i]:
% 4.82/5.02         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 4.82/5.02           = (k4_xboole_0 @ X0 @ X1))),
% 4.82/5.02      inference('sup+', [status(thm)], ['23', '24'])).
% 4.82/5.02  thf(t94_xboole_1, axiom,
% 4.82/5.02    (![A:$i,B:$i]:
% 4.82/5.02     ( ( k2_xboole_0 @ A @ B ) =
% 4.82/5.02       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 4.82/5.02  thf('26', plain,
% 4.82/5.02      (![X62 : $i, X63 : $i]:
% 4.82/5.02         ((k2_xboole_0 @ X62 @ X63)
% 4.82/5.02           = (k5_xboole_0 @ (k5_xboole_0 @ X62 @ X63) @ 
% 4.82/5.02              (k3_xboole_0 @ X62 @ X63)))),
% 4.82/5.02      inference('cnf', [status(esa)], [t94_xboole_1])).
% 4.82/5.02  thf(t91_xboole_1, axiom,
% 4.82/5.02    (![A:$i,B:$i,C:$i]:
% 4.82/5.02     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 4.82/5.02       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 4.82/5.02  thf('27', plain,
% 4.82/5.02      (![X58 : $i, X59 : $i, X60 : $i]:
% 4.82/5.02         ((k5_xboole_0 @ (k5_xboole_0 @ X58 @ X59) @ X60)
% 4.82/5.02           = (k5_xboole_0 @ X58 @ (k5_xboole_0 @ X59 @ X60)))),
% 4.82/5.02      inference('cnf', [status(esa)], [t91_xboole_1])).
% 4.82/5.02  thf('28', plain,
% 4.82/5.02      (![X62 : $i, X63 : $i]:
% 4.82/5.02         ((k2_xboole_0 @ X62 @ X63)
% 4.82/5.02           = (k5_xboole_0 @ X62 @ 
% 4.82/5.02              (k5_xboole_0 @ X63 @ (k3_xboole_0 @ X62 @ X63))))),
% 4.82/5.02      inference('demod', [status(thm)], ['26', '27'])).
% 4.82/5.02  thf('29', plain,
% 4.82/5.02      (![X0 : $i, X1 : $i]:
% 4.82/5.02         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 4.82/5.02           = (k5_xboole_0 @ X1 @ 
% 4.82/5.02              (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))))),
% 4.82/5.02      inference('sup+', [status(thm)], ['25', '28'])).
% 4.82/5.02  thf(t92_xboole_1, axiom,
% 4.82/5.02    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 4.82/5.02  thf('30', plain, (![X61 : $i]: ((k5_xboole_0 @ X61 @ X61) = (k1_xboole_0))),
% 4.82/5.02      inference('cnf', [status(esa)], [t92_xboole_1])).
% 4.82/5.02  thf('31', plain,
% 4.82/5.02      (![X0 : $i, X1 : $i]:
% 4.82/5.02         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 4.82/5.02           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 4.82/5.02      inference('demod', [status(thm)], ['29', '30'])).
% 4.82/5.02  thf(t5_boole, axiom,
% 4.82/5.02    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 4.82/5.02  thf('32', plain, (![X45 : $i]: ((k5_xboole_0 @ X45 @ k1_xboole_0) = (X45))),
% 4.82/5.02      inference('cnf', [status(esa)], [t5_boole])).
% 4.82/5.02  thf('33', plain,
% 4.82/5.02      (![X0 : $i, X1 : $i]:
% 4.82/5.02         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 4.82/5.02      inference('demod', [status(thm)], ['31', '32'])).
% 4.82/5.02  thf('34', plain,
% 4.82/5.02      (![X0 : $i, X1 : $i]:
% 4.82/5.02         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 4.82/5.02      inference('sup+', [status(thm)], ['22', '33'])).
% 4.82/5.02  thf('35', plain,
% 4.82/5.02      (![X0 : $i, X1 : $i]:
% 4.82/5.02         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 4.82/5.02           = (X1))),
% 4.82/5.02      inference('demod', [status(thm)], ['21', '34'])).
% 4.82/5.02  thf('36', plain,
% 4.82/5.02      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.82/5.02      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.82/5.02  thf('37', plain,
% 4.82/5.02      (![X36 : $i, X37 : $i]:
% 4.82/5.02         ((k4_xboole_0 @ X36 @ (k4_xboole_0 @ X36 @ X37))
% 4.82/5.02           = (k3_xboole_0 @ X36 @ X37))),
% 4.82/5.02      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.82/5.02  thf('38', plain,
% 4.82/5.02      (![X26 : $i, X27 : $i]: (r1_tarski @ (k4_xboole_0 @ X26 @ X27) @ X26)),
% 4.82/5.02      inference('cnf', [status(esa)], [t36_xboole_1])).
% 4.82/5.02  thf('39', plain,
% 4.82/5.02      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 4.82/5.02      inference('sup+', [status(thm)], ['37', '38'])).
% 4.82/5.02  thf('40', plain,
% 4.82/5.02      (![X14 : $i, X16 : $i]:
% 4.82/5.02         (((k4_xboole_0 @ X14 @ X16) = (k1_xboole_0))
% 4.82/5.02          | ~ (r1_tarski @ X14 @ X16))),
% 4.82/5.02      inference('cnf', [status(esa)], [l32_xboole_1])).
% 4.82/5.02  thf('41', plain,
% 4.82/5.02      (![X0 : $i, X1 : $i]:
% 4.82/5.02         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 4.82/5.02      inference('sup-', [status(thm)], ['39', '40'])).
% 4.82/5.02  thf('42', plain,
% 4.82/5.02      (![X38 : $i, X39 : $i, X40 : $i]:
% 4.82/5.02         ((k3_xboole_0 @ X38 @ (k4_xboole_0 @ X39 @ X40))
% 4.82/5.02           = (k4_xboole_0 @ (k3_xboole_0 @ X38 @ X39) @ X40))),
% 4.82/5.02      inference('cnf', [status(esa)], [t49_xboole_1])).
% 4.82/5.02  thf('43', plain,
% 4.82/5.02      (![X0 : $i, X1 : $i]:
% 4.82/5.02         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 4.82/5.02      inference('demod', [status(thm)], ['41', '42'])).
% 4.82/5.02  thf('44', plain,
% 4.82/5.02      (![X17 : $i, X18 : $i]:
% 4.82/5.02         ((k5_xboole_0 @ X17 @ X18)
% 4.82/5.02           = (k4_xboole_0 @ (k2_xboole_0 @ X17 @ X18) @ 
% 4.82/5.02              (k3_xboole_0 @ X17 @ X18)))),
% 4.82/5.02      inference('cnf', [status(esa)], [l98_xboole_1])).
% 4.82/5.02  thf('45', plain,
% 4.82/5.02      (![X0 : $i, X1 : $i]:
% 4.82/5.02         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 4.82/5.02           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 4.82/5.02              k1_xboole_0))),
% 4.82/5.02      inference('sup+', [status(thm)], ['43', '44'])).
% 4.82/5.02  thf('46', plain,
% 4.82/5.02      (![X28 : $i, X29 : $i]:
% 4.82/5.02         ((k2_xboole_0 @ X28 @ (k4_xboole_0 @ X29 @ X28))
% 4.82/5.02           = (k2_xboole_0 @ X28 @ X29))),
% 4.82/5.02      inference('cnf', [status(esa)], [t39_xboole_1])).
% 4.82/5.02  thf('47', plain, (![X30 : $i]: ((k4_xboole_0 @ X30 @ k1_xboole_0) = (X30))),
% 4.82/5.02      inference('cnf', [status(esa)], [t3_boole])).
% 4.82/5.02  thf('48', plain,
% 4.82/5.02      (![X0 : $i, X1 : $i]:
% 4.82/5.02         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 4.82/5.02           = (k2_xboole_0 @ X0 @ X1))),
% 4.82/5.02      inference('demod', [status(thm)], ['45', '46', '47'])).
% 4.82/5.02  thf('49', plain, (![X61 : $i]: ((k5_xboole_0 @ X61 @ X61) = (k1_xboole_0))),
% 4.82/5.02      inference('cnf', [status(esa)], [t92_xboole_1])).
% 4.82/5.02  thf('50', plain,
% 4.82/5.02      (![X58 : $i, X59 : $i, X60 : $i]:
% 4.82/5.02         ((k5_xboole_0 @ (k5_xboole_0 @ X58 @ X59) @ X60)
% 4.82/5.02           = (k5_xboole_0 @ X58 @ (k5_xboole_0 @ X59 @ X60)))),
% 4.82/5.02      inference('cnf', [status(esa)], [t91_xboole_1])).
% 4.82/5.02  thf('51', plain,
% 4.82/5.02      (![X0 : $i, X1 : $i]:
% 4.82/5.02         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 4.82/5.02           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 4.82/5.02      inference('sup+', [status(thm)], ['49', '50'])).
% 4.82/5.02  thf(commutativity_k5_xboole_0, axiom,
% 4.82/5.02    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 4.82/5.02  thf('52', plain,
% 4.82/5.02      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 4.82/5.02      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 4.82/5.02  thf('53', plain, (![X45 : $i]: ((k5_xboole_0 @ X45 @ k1_xboole_0) = (X45))),
% 4.82/5.02      inference('cnf', [status(esa)], [t5_boole])).
% 4.82/5.02  thf('54', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 4.82/5.02      inference('sup+', [status(thm)], ['52', '53'])).
% 4.82/5.02  thf('55', plain,
% 4.82/5.02      (![X0 : $i, X1 : $i]:
% 4.82/5.02         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 4.82/5.02      inference('demod', [status(thm)], ['51', '54'])).
% 4.82/5.02  thf('56', plain,
% 4.82/5.02      (![X0 : $i, X1 : $i]:
% 4.82/5.02         ((k4_xboole_0 @ X0 @ X1)
% 4.82/5.02           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 4.82/5.02      inference('sup+', [status(thm)], ['48', '55'])).
% 4.82/5.02  thf('57', plain,
% 4.82/5.02      (![X0 : $i, X1 : $i]:
% 4.82/5.02         ((k4_xboole_0 @ X1 @ X0)
% 4.82/5.02           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 4.82/5.02      inference('sup+', [status(thm)], ['36', '56'])).
% 4.82/5.02  thf('58', plain,
% 4.82/5.02      (![X0 : $i, X1 : $i]:
% 4.82/5.02         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X1))
% 4.82/5.02           = (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 4.82/5.02      inference('sup+', [status(thm)], ['35', '57'])).
% 4.82/5.02  thf('59', plain,
% 4.82/5.02      (![X38 : $i, X39 : $i, X40 : $i]:
% 4.82/5.02         ((k3_xboole_0 @ X38 @ (k4_xboole_0 @ X39 @ X40))
% 4.82/5.02           = (k4_xboole_0 @ (k3_xboole_0 @ X38 @ X39) @ X40))),
% 4.82/5.02      inference('cnf', [status(esa)], [t49_xboole_1])).
% 4.82/5.02  thf(t79_xboole_1, axiom,
% 4.82/5.02    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 4.82/5.02  thf('60', plain,
% 4.82/5.02      (![X46 : $i, X47 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X46 @ X47) @ X47)),
% 4.82/5.02      inference('cnf', [status(esa)], [t79_xboole_1])).
% 4.82/5.02  thf(symmetry_r1_xboole_0, axiom,
% 4.82/5.02    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 4.82/5.02  thf('61', plain,
% 4.82/5.02      (![X8 : $i, X9 : $i]:
% 4.82/5.02         ((r1_xboole_0 @ X8 @ X9) | ~ (r1_xboole_0 @ X9 @ X8))),
% 4.82/5.02      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 4.82/5.02  thf('62', plain,
% 4.82/5.02      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 4.82/5.02      inference('sup-', [status(thm)], ['60', '61'])).
% 4.82/5.02  thf(t83_xboole_1, axiom,
% 4.82/5.02    (![A:$i,B:$i]:
% 4.82/5.02     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 4.82/5.02  thf('63', plain,
% 4.82/5.02      (![X50 : $i, X51 : $i]:
% 4.82/5.02         (((k4_xboole_0 @ X50 @ X51) = (X50)) | ~ (r1_xboole_0 @ X50 @ X51))),
% 4.82/5.02      inference('cnf', [status(esa)], [t83_xboole_1])).
% 4.82/5.02  thf('64', plain,
% 4.82/5.02      (![X0 : $i, X1 : $i]:
% 4.82/5.02         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 4.82/5.02      inference('sup-', [status(thm)], ['62', '63'])).
% 4.82/5.02  thf('65', plain,
% 4.82/5.02      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 4.82/5.02      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 4.82/5.02  thf('66', plain,
% 4.82/5.02      (![X0 : $i, X1 : $i]:
% 4.82/5.02         ((k3_xboole_0 @ X0 @ X1)
% 4.82/5.02           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 4.82/5.02      inference('demod', [status(thm)], ['58', '59', '64', '65'])).
% 4.82/5.02  thf('67', plain,
% 4.82/5.02      (![X0 : $i, X1 : $i]:
% 4.82/5.02         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 4.82/5.02      inference('demod', [status(thm)], ['51', '54'])).
% 4.82/5.02  thf('68', plain,
% 4.82/5.02      (![X0 : $i, X1 : $i]:
% 4.82/5.02         ((k4_xboole_0 @ X1 @ X0)
% 4.82/5.02           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 4.82/5.02      inference('sup+', [status(thm)], ['66', '67'])).
% 4.82/5.02  thf('69', plain,
% 4.82/5.02      (![X34 : $i, X35 : $i]:
% 4.82/5.02         ((k4_xboole_0 @ X34 @ (k3_xboole_0 @ X34 @ X35))
% 4.82/5.02           = (k4_xboole_0 @ X34 @ X35))),
% 4.82/5.02      inference('cnf', [status(esa)], [t47_xboole_1])).
% 4.82/5.02  thf('70', plain,
% 4.82/5.02      (![X36 : $i, X37 : $i]:
% 4.82/5.02         ((k4_xboole_0 @ X36 @ (k4_xboole_0 @ X36 @ X37))
% 4.82/5.02           = (k3_xboole_0 @ X36 @ X37))),
% 4.82/5.02      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.82/5.02  thf('71', plain,
% 4.82/5.02      (![X0 : $i, X1 : $i]:
% 4.82/5.02         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 4.82/5.02           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 4.82/5.02      inference('sup+', [status(thm)], ['69', '70'])).
% 4.82/5.02  thf('72', plain,
% 4.82/5.02      (![X36 : $i, X37 : $i]:
% 4.82/5.02         ((k4_xboole_0 @ X36 @ (k4_xboole_0 @ X36 @ X37))
% 4.82/5.02           = (k3_xboole_0 @ X36 @ X37))),
% 4.82/5.02      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.82/5.02  thf('73', plain,
% 4.82/5.02      (![X0 : $i, X1 : $i]:
% 4.82/5.02         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 4.82/5.02           = (k3_xboole_0 @ X1 @ X0))),
% 4.82/5.02      inference('sup+', [status(thm)], ['71', '72'])).
% 4.82/5.02  thf('74', plain,
% 4.82/5.02      (![X17 : $i, X18 : $i]:
% 4.82/5.02         ((k5_xboole_0 @ X17 @ X18)
% 4.82/5.02           = (k4_xboole_0 @ (k2_xboole_0 @ X17 @ X18) @ 
% 4.82/5.02              (k3_xboole_0 @ X17 @ X18)))),
% 4.82/5.02      inference('cnf', [status(esa)], [l98_xboole_1])).
% 4.82/5.02  thf('75', plain,
% 4.82/5.02      (![X0 : $i, X1 : $i]:
% 4.82/5.02         ((k4_xboole_0 @ X0 @ X1)
% 4.82/5.02           = (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 4.82/5.02      inference('demod', [status(thm)], ['15', '16', '68', '73', '74'])).
% 4.82/5.02  thf(idempotence_k2_xboole_0, axiom,
% 4.82/5.02    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 4.82/5.02  thf('76', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ X7) = (X7))),
% 4.82/5.02      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 4.82/5.02  thf(t31_xboole_1, axiom,
% 4.82/5.02    (![A:$i,B:$i,C:$i]:
% 4.82/5.02     ( r1_tarski @
% 4.82/5.02       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ 
% 4.82/5.02       ( k2_xboole_0 @ B @ C ) ))).
% 4.82/5.02  thf('77', plain,
% 4.82/5.02      (![X23 : $i, X24 : $i, X25 : $i]:
% 4.82/5.02         (r1_tarski @ 
% 4.82/5.02          (k2_xboole_0 @ (k3_xboole_0 @ X23 @ X24) @ (k3_xboole_0 @ X23 @ X25)) @ 
% 4.82/5.02          (k2_xboole_0 @ X24 @ X25))),
% 4.82/5.02      inference('cnf', [status(esa)], [t31_xboole_1])).
% 4.82/5.02  thf('78', plain,
% 4.82/5.02      (![X19 : $i, X20 : $i, X21 : $i]:
% 4.82/5.02         ((k3_xboole_0 @ X19 @ (k2_xboole_0 @ X20 @ X21))
% 4.82/5.02           = (k2_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ 
% 4.82/5.02              (k3_xboole_0 @ X19 @ X21)))),
% 4.82/5.02      inference('cnf', [status(esa)], [t23_xboole_1])).
% 4.82/5.02  thf('79', plain,
% 4.82/5.02      (![X23 : $i, X24 : $i, X25 : $i]:
% 4.82/5.02         (r1_tarski @ (k3_xboole_0 @ X23 @ (k2_xboole_0 @ X24 @ X25)) @ 
% 4.82/5.02          (k2_xboole_0 @ X24 @ X25))),
% 4.82/5.02      inference('demod', [status(thm)], ['77', '78'])).
% 4.82/5.02  thf('80', plain,
% 4.82/5.02      (![X0 : $i, X1 : $i]:
% 4.82/5.02         (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X0))),
% 4.82/5.02      inference('sup+', [status(thm)], ['76', '79'])).
% 4.82/5.02  thf('81', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ X7) = (X7))),
% 4.82/5.02      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 4.82/5.02  thf('82', plain,
% 4.82/5.02      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 4.82/5.02      inference('demod', [status(thm)], ['80', '81'])).
% 4.82/5.02  thf('83', plain,
% 4.82/5.02      (![X0 : $i, X1 : $i]:
% 4.82/5.02         (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))),
% 4.82/5.02      inference('sup+', [status(thm)], ['75', '82'])).
% 4.82/5.02  thf('84', plain, ($false), inference('demod', [status(thm)], ['0', '83'])).
% 4.82/5.02  
% 4.82/5.02  % SZS output end Refutation
% 4.82/5.02  
% 4.82/5.03  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gutgEqWDG3

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:14 EST 2020

% Result     : Theorem 11.69s
% Output     : Refutation 11.69s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 262 expanded)
%              Number of leaves         :   27 (  95 expanded)
%              Depth                    :   19
%              Number of atoms          : 1198 (2041 expanded)
%              Number of equality atoms :  136 ( 245 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(t48_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
        = ( k3_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t48_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
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

thf('2',plain,(
    ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k4_xboole_0 @ X34 @ ( k3_xboole_0 @ X34 @ X35 ) )
      = ( k4_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X29 @ X30 ) @ X30 )
      = ( k4_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('7',plain,(
    ! [X28: $i] :
      ( ( k4_xboole_0 @ X28 @ k1_xboole_0 )
      = X28 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('8',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('9',plain,(
    ! [X28: $i] :
      ( ( k4_xboole_0 @ X28 @ o_0_0_xboole_0 )
      = X28 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('10',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X26 @ X27 ) @ X26 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X17: $i,X19: $i] :
      ( ( ( k4_xboole_0 @ X17 @ X19 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('13',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('14',plain,(
    ! [X17: $i,X19: $i] :
      ( ( ( k4_xboole_0 @ X17 @ X19 )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X31 @ X32 ) @ X33 )
      = ( k4_xboole_0 @ X31 @ ( k2_xboole_0 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('17',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X20 @ X21 ) @ X20 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('18',plain,(
    ! [X17: $i,X19: $i] :
      ( ( ( k4_xboole_0 @ X17 @ X19 )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = ( k4_xboole_0 @ B @ A ) )
     => ( A = B ) ) )).

thf('20',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X25 = X24 )
      | ( ( k4_xboole_0 @ X25 @ X24 )
       != ( k4_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t32_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
       != o_0_0_xboole_0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k4_xboole_0 @ X34 @ ( k3_xboole_0 @ X34 @ X35 ) )
      = ( k4_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X1 )
       != o_0_0_xboole_0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != o_0_0_xboole_0 )
      | ( ( k4_xboole_0 @ X2 @ X1 )
        = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
      | ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
        = ( k3_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
        = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('31',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('35',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X31 @ X32 ) @ X33 )
      = ( k4_xboole_0 @ X31 @ ( k2_xboole_0 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('36',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X31 @ X32 ) @ X33 )
      = ( k4_xboole_0 @ X31 @ ( k2_xboole_0 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k2_xboole_0 @ X0 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X31 @ X32 ) @ X33 )
      = ( k4_xboole_0 @ X31 @ ( k2_xboole_0 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('39',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X31 @ X32 ) @ X33 )
      = ( k4_xboole_0 @ X31 @ ( k2_xboole_0 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X3 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X3 ) ) ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X25 = X24 )
      | ( ( k4_xboole_0 @ X25 @ X24 )
       != ( k4_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t32_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) )
       != o_0_0_xboole_0 )
      | ( ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
        = ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X3 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X3 ) ) ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('47',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X31 @ X32 ) @ X33 )
      = ( k4_xboole_0 @ X31 @ ( k2_xboole_0 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X31 @ X32 ) @ X33 )
      = ( k4_xboole_0 @ X31 @ ( k2_xboole_0 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X26 @ X27 ) @ X26 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('52',plain,(
    ! [X17: $i,X19: $i] :
      ( ( ( k4_xboole_0 @ X17 @ X19 )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X31 @ X32 ) @ X33 )
      = ( k4_xboole_0 @ X31 @ ( k2_xboole_0 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
      | ( ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
        = ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['44','45','50','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['34','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['33','58'])).

thf('60',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X31 @ X32 ) @ X33 )
      = ( k4_xboole_0 @ X31 @ ( k2_xboole_0 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X29 @ X30 ) @ X30 )
      = ( k4_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('64',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('65',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X20 @ X21 ) @ X20 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X17: $i,X19: $i] :
      ( ( ( k4_xboole_0 @ X17 @ X19 )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X25 = X24 )
      | ( ( k4_xboole_0 @ X25 @ X24 )
       != ( k4_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t32_xboole_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
       != o_0_0_xboole_0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('72',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k4_xboole_0 @ X34 @ ( k3_xboole_0 @ X34 @ X35 ) )
      = ( k4_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X1 )
       != o_0_0_xboole_0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
       != o_0_0_xboole_0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['63','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X1 )
       != o_0_0_xboole_0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
       != o_0_0_xboole_0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference(demod,[status(thm)],['75','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
      | ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
        = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['62','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['59','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('86',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X29 @ X30 ) @ X30 )
      = ( k4_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('91',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X31 @ X32 ) @ X33 )
      = ( k4_xboole_0 @ X31 @ ( k2_xboole_0 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('94',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C @ X14 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('95',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C @ X14 @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('96',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('97',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['94','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['99'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('101',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('102',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('103',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = o_0_0_xboole_0 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['100','103'])).

thf('105',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k4_xboole_0 @ X34 @ ( k3_xboole_0 @ X34 @ X35 ) )
      = ( k4_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ o_0_0_xboole_0 )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X28: $i] :
      ( ( k4_xboole_0 @ X28 @ o_0_0_xboole_0 )
      = X28 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['93','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['92','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['89','112'])).

thf('114',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('115',plain,(
    ( k3_xboole_0 @ sk_B @ sk_A )
 != ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['2','113','114'])).

thf('116',plain,(
    $false ),
    inference(simplify,[status(thm)],['115'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gutgEqWDG3
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:00:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 11.69/11.93  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 11.69/11.93  % Solved by: fo/fo7.sh
% 11.69/11.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 11.69/11.93  % done 11085 iterations in 11.474s
% 11.69/11.93  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 11.69/11.93  % SZS output start Refutation
% 11.69/11.93  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 11.69/11.93  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 11.69/11.93  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 11.69/11.93  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 11.69/11.93  thf(sk_B_type, type, sk_B: $i).
% 11.69/11.93  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 11.69/11.93  thf(sk_A_type, type, sk_A: $i).
% 11.69/11.93  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 11.69/11.93  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 11.69/11.93  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 11.69/11.93  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 11.69/11.93  thf(t48_xboole_1, conjecture,
% 11.69/11.93    (![A:$i,B:$i]:
% 11.69/11.93     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 11.69/11.93  thf(zf_stmt_0, negated_conjecture,
% 11.69/11.93    (~( ![A:$i,B:$i]:
% 11.69/11.93        ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) =
% 11.69/11.93          ( k3_xboole_0 @ A @ B ) ) )),
% 11.69/11.93    inference('cnf.neg', [status(esa)], [t48_xboole_1])).
% 11.69/11.93  thf('0', plain,
% 11.69/11.93      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 11.69/11.93         != (k3_xboole_0 @ sk_A @ sk_B))),
% 11.69/11.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.69/11.93  thf(commutativity_k3_xboole_0, axiom,
% 11.69/11.93    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 11.69/11.93  thf('1', plain,
% 11.69/11.93      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 11.69/11.93      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 11.69/11.93  thf('2', plain,
% 11.69/11.93      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 11.69/11.93         != (k3_xboole_0 @ sk_B @ sk_A))),
% 11.69/11.93      inference('demod', [status(thm)], ['0', '1'])).
% 11.69/11.93  thf(t47_xboole_1, axiom,
% 11.69/11.93    (![A:$i,B:$i]:
% 11.69/11.93     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 11.69/11.93  thf('3', plain,
% 11.69/11.93      (![X34 : $i, X35 : $i]:
% 11.69/11.93         ((k4_xboole_0 @ X34 @ (k3_xboole_0 @ X34 @ X35))
% 11.69/11.93           = (k4_xboole_0 @ X34 @ X35))),
% 11.69/11.93      inference('cnf', [status(esa)], [t47_xboole_1])).
% 11.69/11.93  thf(commutativity_k2_xboole_0, axiom,
% 11.69/11.93    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 11.69/11.93  thf('4', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 11.69/11.93      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 11.69/11.93  thf(t40_xboole_1, axiom,
% 11.69/11.93    (![A:$i,B:$i]:
% 11.69/11.93     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 11.69/11.93  thf('5', plain,
% 11.69/11.93      (![X29 : $i, X30 : $i]:
% 11.69/11.93         ((k4_xboole_0 @ (k2_xboole_0 @ X29 @ X30) @ X30)
% 11.69/11.93           = (k4_xboole_0 @ X29 @ X30))),
% 11.69/11.93      inference('cnf', [status(esa)], [t40_xboole_1])).
% 11.69/11.93  thf('6', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i]:
% 11.69/11.93         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 11.69/11.93           = (k4_xboole_0 @ X0 @ X1))),
% 11.69/11.93      inference('sup+', [status(thm)], ['4', '5'])).
% 11.69/11.93  thf(t3_boole, axiom,
% 11.69/11.93    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 11.69/11.93  thf('7', plain, (![X28 : $i]: ((k4_xboole_0 @ X28 @ k1_xboole_0) = (X28))),
% 11.69/11.93      inference('cnf', [status(esa)], [t3_boole])).
% 11.69/11.93  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 11.69/11.93  thf('8', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 11.69/11.93      inference('cnf', [status(esa)], [d2_xboole_0])).
% 11.69/11.93  thf('9', plain,
% 11.69/11.93      (![X28 : $i]: ((k4_xboole_0 @ X28 @ o_0_0_xboole_0) = (X28))),
% 11.69/11.93      inference('demod', [status(thm)], ['7', '8'])).
% 11.69/11.93  thf(t36_xboole_1, axiom,
% 11.69/11.93    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 11.69/11.93  thf('10', plain,
% 11.69/11.93      (![X26 : $i, X27 : $i]: (r1_tarski @ (k4_xboole_0 @ X26 @ X27) @ X26)),
% 11.69/11.93      inference('cnf', [status(esa)], [t36_xboole_1])).
% 11.69/11.93  thf('11', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 11.69/11.93      inference('sup+', [status(thm)], ['9', '10'])).
% 11.69/11.93  thf(l32_xboole_1, axiom,
% 11.69/11.93    (![A:$i,B:$i]:
% 11.69/11.93     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 11.69/11.93  thf('12', plain,
% 11.69/11.93      (![X17 : $i, X19 : $i]:
% 11.69/11.93         (((k4_xboole_0 @ X17 @ X19) = (k1_xboole_0))
% 11.69/11.93          | ~ (r1_tarski @ X17 @ X19))),
% 11.69/11.93      inference('cnf', [status(esa)], [l32_xboole_1])).
% 11.69/11.93  thf('13', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 11.69/11.93      inference('cnf', [status(esa)], [d2_xboole_0])).
% 11.69/11.93  thf('14', plain,
% 11.69/11.93      (![X17 : $i, X19 : $i]:
% 11.69/11.93         (((k4_xboole_0 @ X17 @ X19) = (o_0_0_xboole_0))
% 11.69/11.93          | ~ (r1_tarski @ X17 @ X19))),
% 11.69/11.93      inference('demod', [status(thm)], ['12', '13'])).
% 11.69/11.93  thf('15', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (o_0_0_xboole_0))),
% 11.69/11.93      inference('sup-', [status(thm)], ['11', '14'])).
% 11.69/11.93  thf(t41_xboole_1, axiom,
% 11.69/11.93    (![A:$i,B:$i,C:$i]:
% 11.69/11.93     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 11.69/11.93       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 11.69/11.93  thf('16', plain,
% 11.69/11.93      (![X31 : $i, X32 : $i, X33 : $i]:
% 11.69/11.93         ((k4_xboole_0 @ (k4_xboole_0 @ X31 @ X32) @ X33)
% 11.69/11.93           = (k4_xboole_0 @ X31 @ (k2_xboole_0 @ X32 @ X33)))),
% 11.69/11.93      inference('cnf', [status(esa)], [t41_xboole_1])).
% 11.69/11.93  thf(t17_xboole_1, axiom,
% 11.69/11.93    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 11.69/11.93  thf('17', plain,
% 11.69/11.93      (![X20 : $i, X21 : $i]: (r1_tarski @ (k3_xboole_0 @ X20 @ X21) @ X20)),
% 11.69/11.93      inference('cnf', [status(esa)], [t17_xboole_1])).
% 11.69/11.93  thf('18', plain,
% 11.69/11.93      (![X17 : $i, X19 : $i]:
% 11.69/11.93         (((k4_xboole_0 @ X17 @ X19) = (o_0_0_xboole_0))
% 11.69/11.93          | ~ (r1_tarski @ X17 @ X19))),
% 11.69/11.93      inference('demod', [status(thm)], ['12', '13'])).
% 11.69/11.93  thf('19', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i]:
% 11.69/11.93         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (o_0_0_xboole_0))),
% 11.69/11.93      inference('sup-', [status(thm)], ['17', '18'])).
% 11.69/11.93  thf(t32_xboole_1, axiom,
% 11.69/11.93    (![A:$i,B:$i]:
% 11.69/11.93     ( ( ( k4_xboole_0 @ A @ B ) = ( k4_xboole_0 @ B @ A ) ) =>
% 11.69/11.93       ( ( A ) = ( B ) ) ))).
% 11.69/11.93  thf('20', plain,
% 11.69/11.93      (![X24 : $i, X25 : $i]:
% 11.69/11.93         (((X25) = (X24))
% 11.69/11.93          | ((k4_xboole_0 @ X25 @ X24) != (k4_xboole_0 @ X24 @ X25)))),
% 11.69/11.93      inference('cnf', [status(esa)], [t32_xboole_1])).
% 11.69/11.93  thf('21', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i]:
% 11.69/11.93         (((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) != (o_0_0_xboole_0))
% 11.69/11.93          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 11.69/11.93      inference('sup-', [status(thm)], ['19', '20'])).
% 11.69/11.93  thf('22', plain,
% 11.69/11.93      (![X34 : $i, X35 : $i]:
% 11.69/11.93         ((k4_xboole_0 @ X34 @ (k3_xboole_0 @ X34 @ X35))
% 11.69/11.93           = (k4_xboole_0 @ X34 @ X35))),
% 11.69/11.93      inference('cnf', [status(esa)], [t47_xboole_1])).
% 11.69/11.93  thf('23', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i]:
% 11.69/11.93         (((k4_xboole_0 @ X0 @ X1) != (o_0_0_xboole_0))
% 11.69/11.93          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 11.69/11.93      inference('demod', [status(thm)], ['21', '22'])).
% 11.69/11.93  thf('24', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.69/11.93         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) != (o_0_0_xboole_0))
% 11.69/11.93          | ((k4_xboole_0 @ X2 @ X1)
% 11.69/11.93              = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))),
% 11.69/11.93      inference('sup-', [status(thm)], ['16', '23'])).
% 11.69/11.93  thf('25', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i]:
% 11.69/11.93         (((o_0_0_xboole_0) != (o_0_0_xboole_0))
% 11.69/11.93          | ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 11.69/11.93              = (k3_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ 
% 11.69/11.93                 X0)))),
% 11.69/11.93      inference('sup-', [status(thm)], ['15', '24'])).
% 11.69/11.93  thf('26', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i]:
% 11.69/11.93         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 11.69/11.93           = (k4_xboole_0 @ X0 @ X1))),
% 11.69/11.93      inference('sup+', [status(thm)], ['4', '5'])).
% 11.69/11.93  thf('27', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i]:
% 11.69/11.93         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 11.69/11.93           = (k4_xboole_0 @ X0 @ X1))),
% 11.69/11.93      inference('sup+', [status(thm)], ['4', '5'])).
% 11.69/11.93  thf('28', plain,
% 11.69/11.93      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 11.69/11.93      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 11.69/11.93  thf('29', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i]:
% 11.69/11.93         (((o_0_0_xboole_0) != (o_0_0_xboole_0))
% 11.69/11.93          | ((k4_xboole_0 @ X0 @ X1)
% 11.69/11.93              = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))))),
% 11.69/11.93      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 11.69/11.93  thf('30', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i]:
% 11.69/11.93         ((k4_xboole_0 @ X0 @ X1)
% 11.69/11.93           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 11.69/11.93      inference('simplify', [status(thm)], ['29'])).
% 11.69/11.93  thf(t22_xboole_1, axiom,
% 11.69/11.93    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 11.69/11.93  thf('31', plain,
% 11.69/11.93      (![X22 : $i, X23 : $i]:
% 11.69/11.93         ((k2_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23)) = (X22))),
% 11.69/11.93      inference('cnf', [status(esa)], [t22_xboole_1])).
% 11.69/11.93  thf('32', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i]:
% 11.69/11.93         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 11.69/11.93      inference('sup+', [status(thm)], ['30', '31'])).
% 11.69/11.93  thf('33', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i]:
% 11.69/11.93         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 11.69/11.93           = (k2_xboole_0 @ X0 @ X1))),
% 11.69/11.93      inference('sup+', [status(thm)], ['6', '32'])).
% 11.69/11.93  thf('34', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 11.69/11.93      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 11.69/11.93  thf('35', plain,
% 11.69/11.93      (![X31 : $i, X32 : $i, X33 : $i]:
% 11.69/11.93         ((k4_xboole_0 @ (k4_xboole_0 @ X31 @ X32) @ X33)
% 11.69/11.93           = (k4_xboole_0 @ X31 @ (k2_xboole_0 @ X32 @ X33)))),
% 11.69/11.93      inference('cnf', [status(esa)], [t41_xboole_1])).
% 11.69/11.93  thf('36', plain,
% 11.69/11.93      (![X31 : $i, X32 : $i, X33 : $i]:
% 11.69/11.93         ((k4_xboole_0 @ (k4_xboole_0 @ X31 @ X32) @ X33)
% 11.69/11.93           = (k4_xboole_0 @ X31 @ (k2_xboole_0 @ X32 @ X33)))),
% 11.69/11.93      inference('cnf', [status(esa)], [t41_xboole_1])).
% 11.69/11.93  thf('37', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.69/11.93         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3)
% 11.69/11.93           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k2_xboole_0 @ X0 @ X3)))),
% 11.69/11.93      inference('sup+', [status(thm)], ['35', '36'])).
% 11.69/11.93  thf('38', plain,
% 11.69/11.93      (![X31 : $i, X32 : $i, X33 : $i]:
% 11.69/11.93         ((k4_xboole_0 @ (k4_xboole_0 @ X31 @ X32) @ X33)
% 11.69/11.93           = (k4_xboole_0 @ X31 @ (k2_xboole_0 @ X32 @ X33)))),
% 11.69/11.93      inference('cnf', [status(esa)], [t41_xboole_1])).
% 11.69/11.93  thf('39', plain,
% 11.69/11.93      (![X31 : $i, X32 : $i, X33 : $i]:
% 11.69/11.93         ((k4_xboole_0 @ (k4_xboole_0 @ X31 @ X32) @ X33)
% 11.69/11.93           = (k4_xboole_0 @ X31 @ (k2_xboole_0 @ X32 @ X33)))),
% 11.69/11.93      inference('cnf', [status(esa)], [t41_xboole_1])).
% 11.69/11.93  thf('40', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.69/11.93         ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X3))
% 11.69/11.93           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X3))))),
% 11.69/11.93      inference('demod', [status(thm)], ['37', '38', '39'])).
% 11.69/11.93  thf('41', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (o_0_0_xboole_0))),
% 11.69/11.93      inference('sup-', [status(thm)], ['11', '14'])).
% 11.69/11.93  thf('42', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.69/11.93         ((k4_xboole_0 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0) @ 
% 11.69/11.93           (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))) = (o_0_0_xboole_0))),
% 11.69/11.93      inference('sup+', [status(thm)], ['40', '41'])).
% 11.69/11.93  thf('43', plain,
% 11.69/11.93      (![X24 : $i, X25 : $i]:
% 11.69/11.93         (((X25) = (X24))
% 11.69/11.93          | ((k4_xboole_0 @ X25 @ X24) != (k4_xboole_0 @ X24 @ X25)))),
% 11.69/11.93      inference('cnf', [status(esa)], [t32_xboole_1])).
% 11.69/11.93  thf('44', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.69/11.93         (((k4_xboole_0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 11.69/11.93            (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)) != (o_0_0_xboole_0))
% 11.69/11.93          | ((k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 11.69/11.93              = (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)))),
% 11.69/11.93      inference('sup-', [status(thm)], ['42', '43'])).
% 11.69/11.93  thf('45', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.69/11.93         ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X3))
% 11.69/11.93           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X3))))),
% 11.69/11.93      inference('demod', [status(thm)], ['37', '38', '39'])).
% 11.69/11.93  thf('46', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i]:
% 11.69/11.93         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 11.69/11.93           = (k4_xboole_0 @ X0 @ X1))),
% 11.69/11.93      inference('sup+', [status(thm)], ['4', '5'])).
% 11.69/11.93  thf('47', plain,
% 11.69/11.93      (![X31 : $i, X32 : $i, X33 : $i]:
% 11.69/11.93         ((k4_xboole_0 @ (k4_xboole_0 @ X31 @ X32) @ X33)
% 11.69/11.93           = (k4_xboole_0 @ X31 @ (k2_xboole_0 @ X32 @ X33)))),
% 11.69/11.93      inference('cnf', [status(esa)], [t41_xboole_1])).
% 11.69/11.93  thf('48', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.69/11.93         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 11.69/11.93           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X0 @ X2)))),
% 11.69/11.93      inference('sup+', [status(thm)], ['46', '47'])).
% 11.69/11.93  thf('49', plain,
% 11.69/11.93      (![X31 : $i, X32 : $i, X33 : $i]:
% 11.69/11.93         ((k4_xboole_0 @ (k4_xboole_0 @ X31 @ X32) @ X33)
% 11.69/11.93           = (k4_xboole_0 @ X31 @ (k2_xboole_0 @ X32 @ X33)))),
% 11.69/11.93      inference('cnf', [status(esa)], [t41_xboole_1])).
% 11.69/11.93  thf('50', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.69/11.93         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2))
% 11.69/11.93           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X0 @ X2)))),
% 11.69/11.93      inference('demod', [status(thm)], ['48', '49'])).
% 11.69/11.93  thf('51', plain,
% 11.69/11.93      (![X26 : $i, X27 : $i]: (r1_tarski @ (k4_xboole_0 @ X26 @ X27) @ X26)),
% 11.69/11.93      inference('cnf', [status(esa)], [t36_xboole_1])).
% 11.69/11.93  thf('52', plain,
% 11.69/11.93      (![X17 : $i, X19 : $i]:
% 11.69/11.93         (((k4_xboole_0 @ X17 @ X19) = (o_0_0_xboole_0))
% 11.69/11.93          | ~ (r1_tarski @ X17 @ X19))),
% 11.69/11.93      inference('demod', [status(thm)], ['12', '13'])).
% 11.69/11.93  thf('53', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i]:
% 11.69/11.93         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (o_0_0_xboole_0))),
% 11.69/11.93      inference('sup-', [status(thm)], ['51', '52'])).
% 11.69/11.93  thf('54', plain,
% 11.69/11.93      (![X31 : $i, X32 : $i, X33 : $i]:
% 11.69/11.93         ((k4_xboole_0 @ (k4_xboole_0 @ X31 @ X32) @ X33)
% 11.69/11.93           = (k4_xboole_0 @ X31 @ (k2_xboole_0 @ X32 @ X33)))),
% 11.69/11.93      inference('cnf', [status(esa)], [t41_xboole_1])).
% 11.69/11.93  thf('55', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i]:
% 11.69/11.93         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (o_0_0_xboole_0))),
% 11.69/11.93      inference('demod', [status(thm)], ['53', '54'])).
% 11.69/11.93  thf('56', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.69/11.93         (((o_0_0_xboole_0) != (o_0_0_xboole_0))
% 11.69/11.93          | ((k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 11.69/11.93              = (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)))),
% 11.69/11.93      inference('demod', [status(thm)], ['44', '45', '50', '55'])).
% 11.69/11.93  thf('57', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.69/11.93         ((k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 11.69/11.93           = (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 11.69/11.93      inference('simplify', [status(thm)], ['56'])).
% 11.69/11.93  thf('58', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.69/11.93         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2))
% 11.69/11.93           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 11.69/11.93      inference('sup+', [status(thm)], ['34', '57'])).
% 11.69/11.93  thf('59', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i]:
% 11.69/11.93         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 11.69/11.93           = (k2_xboole_0 @ X0 @ X1))),
% 11.69/11.93      inference('demod', [status(thm)], ['33', '58'])).
% 11.69/11.93  thf('60', plain,
% 11.69/11.93      (![X31 : $i, X32 : $i, X33 : $i]:
% 11.69/11.93         ((k4_xboole_0 @ (k4_xboole_0 @ X31 @ X32) @ X33)
% 11.69/11.93           = (k4_xboole_0 @ X31 @ (k2_xboole_0 @ X32 @ X33)))),
% 11.69/11.93      inference('cnf', [status(esa)], [t41_xboole_1])).
% 11.69/11.93  thf('61', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (o_0_0_xboole_0))),
% 11.69/11.93      inference('sup-', [status(thm)], ['11', '14'])).
% 11.69/11.93  thf('62', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i]:
% 11.69/11.93         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 11.69/11.93           = (o_0_0_xboole_0))),
% 11.69/11.93      inference('sup+', [status(thm)], ['60', '61'])).
% 11.69/11.93  thf('63', plain,
% 11.69/11.93      (![X29 : $i, X30 : $i]:
% 11.69/11.93         ((k4_xboole_0 @ (k2_xboole_0 @ X29 @ X30) @ X30)
% 11.69/11.93           = (k4_xboole_0 @ X29 @ X30))),
% 11.69/11.93      inference('cnf', [status(esa)], [t40_xboole_1])).
% 11.69/11.93  thf('64', plain,
% 11.69/11.93      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 11.69/11.93      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 11.69/11.93  thf('65', plain,
% 11.69/11.93      (![X20 : $i, X21 : $i]: (r1_tarski @ (k3_xboole_0 @ X20 @ X21) @ X20)),
% 11.69/11.93      inference('cnf', [status(esa)], [t17_xboole_1])).
% 11.69/11.93  thf('66', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 11.69/11.93      inference('sup+', [status(thm)], ['64', '65'])).
% 11.69/11.93  thf('67', plain,
% 11.69/11.93      (![X17 : $i, X19 : $i]:
% 11.69/11.93         (((k4_xboole_0 @ X17 @ X19) = (o_0_0_xboole_0))
% 11.69/11.93          | ~ (r1_tarski @ X17 @ X19))),
% 11.69/11.93      inference('demod', [status(thm)], ['12', '13'])).
% 11.69/11.93  thf('68', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i]:
% 11.69/11.93         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (o_0_0_xboole_0))),
% 11.69/11.93      inference('sup-', [status(thm)], ['66', '67'])).
% 11.69/11.93  thf('69', plain,
% 11.69/11.93      (![X24 : $i, X25 : $i]:
% 11.69/11.93         (((X25) = (X24))
% 11.69/11.93          | ((k4_xboole_0 @ X25 @ X24) != (k4_xboole_0 @ X24 @ X25)))),
% 11.69/11.93      inference('cnf', [status(esa)], [t32_xboole_1])).
% 11.69/11.93  thf('70', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i]:
% 11.69/11.93         (((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) != (o_0_0_xboole_0))
% 11.69/11.93          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 11.69/11.93      inference('sup-', [status(thm)], ['68', '69'])).
% 11.69/11.93  thf('71', plain,
% 11.69/11.93      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 11.69/11.93      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 11.69/11.93  thf('72', plain,
% 11.69/11.93      (![X34 : $i, X35 : $i]:
% 11.69/11.93         ((k4_xboole_0 @ X34 @ (k3_xboole_0 @ X34 @ X35))
% 11.69/11.93           = (k4_xboole_0 @ X34 @ X35))),
% 11.69/11.93      inference('cnf', [status(esa)], [t47_xboole_1])).
% 11.69/11.93  thf('73', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i]:
% 11.69/11.93         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 11.69/11.93           = (k4_xboole_0 @ X0 @ X1))),
% 11.69/11.93      inference('sup+', [status(thm)], ['71', '72'])).
% 11.69/11.93  thf('74', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i]:
% 11.69/11.93         (((k4_xboole_0 @ X0 @ X1) != (o_0_0_xboole_0))
% 11.69/11.93          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 11.69/11.93      inference('demod', [status(thm)], ['70', '73'])).
% 11.69/11.93  thf('75', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i]:
% 11.69/11.93         (((k4_xboole_0 @ X1 @ X0) != (o_0_0_xboole_0))
% 11.69/11.93          | ((k2_xboole_0 @ X1 @ X0)
% 11.69/11.93              = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))))),
% 11.69/11.93      inference('sup-', [status(thm)], ['63', '74'])).
% 11.69/11.93  thf('76', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i]:
% 11.69/11.93         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (o_0_0_xboole_0))),
% 11.69/11.93      inference('demod', [status(thm)], ['53', '54'])).
% 11.69/11.93  thf('77', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i]:
% 11.69/11.93         (((k4_xboole_0 @ X0 @ X1) != (o_0_0_xboole_0))
% 11.69/11.93          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 11.69/11.93      inference('demod', [status(thm)], ['21', '22'])).
% 11.69/11.93  thf('78', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i]:
% 11.69/11.93         (((o_0_0_xboole_0) != (o_0_0_xboole_0))
% 11.69/11.93          | ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))))),
% 11.69/11.93      inference('sup-', [status(thm)], ['76', '77'])).
% 11.69/11.93  thf('79', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i]:
% 11.69/11.93         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 11.69/11.93      inference('simplify', [status(thm)], ['78'])).
% 11.69/11.93  thf('80', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i]:
% 11.69/11.93         (((k4_xboole_0 @ X1 @ X0) != (o_0_0_xboole_0))
% 11.69/11.93          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 11.69/11.93      inference('demod', [status(thm)], ['75', '79'])).
% 11.69/11.93  thf('81', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i]:
% 11.69/11.93         (((o_0_0_xboole_0) != (o_0_0_xboole_0))
% 11.69/11.93          | ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 11.69/11.93              = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 11.69/11.93      inference('sup-', [status(thm)], ['62', '80'])).
% 11.69/11.93  thf('82', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i]:
% 11.69/11.93         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 11.69/11.93           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 11.69/11.93      inference('simplify', [status(thm)], ['81'])).
% 11.69/11.93  thf('83', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i]:
% 11.69/11.93         ((k2_xboole_0 @ X1 @ X0)
% 11.69/11.93           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 11.69/11.93      inference('sup+', [status(thm)], ['59', '82'])).
% 11.69/11.93  thf('84', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i]:
% 11.69/11.93         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 11.69/11.93           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 11.69/11.93      inference('sup+', [status(thm)], ['3', '83'])).
% 11.69/11.93  thf('85', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 11.69/11.93      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 11.69/11.93  thf('86', plain,
% 11.69/11.93      (![X22 : $i, X23 : $i]:
% 11.69/11.93         ((k2_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23)) = (X22))),
% 11.69/11.93      inference('cnf', [status(esa)], [t22_xboole_1])).
% 11.69/11.93  thf('87', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i]:
% 11.69/11.93         ((X1)
% 11.69/11.93           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 11.69/11.93      inference('demod', [status(thm)], ['84', '85', '86'])).
% 11.69/11.93  thf('88', plain,
% 11.69/11.93      (![X29 : $i, X30 : $i]:
% 11.69/11.93         ((k4_xboole_0 @ (k2_xboole_0 @ X29 @ X30) @ X30)
% 11.69/11.93           = (k4_xboole_0 @ X29 @ X30))),
% 11.69/11.93      inference('cnf', [status(esa)], [t40_xboole_1])).
% 11.69/11.93  thf('89', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i]:
% 11.69/11.93         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 11.69/11.93           = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X1)))),
% 11.69/11.93      inference('sup+', [status(thm)], ['87', '88'])).
% 11.69/11.93  thf('90', plain,
% 11.69/11.93      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 11.69/11.93      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 11.69/11.93  thf('91', plain,
% 11.69/11.93      (![X22 : $i, X23 : $i]:
% 11.69/11.93         ((k2_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23)) = (X22))),
% 11.69/11.93      inference('cnf', [status(esa)], [t22_xboole_1])).
% 11.69/11.93  thf('92', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i]:
% 11.69/11.93         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 11.69/11.93      inference('sup+', [status(thm)], ['90', '91'])).
% 11.69/11.93  thf('93', plain,
% 11.69/11.93      (![X31 : $i, X32 : $i, X33 : $i]:
% 11.69/11.93         ((k4_xboole_0 @ (k4_xboole_0 @ X31 @ X32) @ X33)
% 11.69/11.93           = (k4_xboole_0 @ X31 @ (k2_xboole_0 @ X32 @ X33)))),
% 11.69/11.93      inference('cnf', [status(esa)], [t41_xboole_1])).
% 11.69/11.93  thf(t3_xboole_0, axiom,
% 11.69/11.93    (![A:$i,B:$i]:
% 11.69/11.93     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 11.69/11.93            ( r1_xboole_0 @ A @ B ) ) ) & 
% 11.69/11.93       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 11.69/11.93            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 11.69/11.93  thf('94', plain,
% 11.69/11.93      (![X13 : $i, X14 : $i]:
% 11.69/11.93         ((r1_xboole_0 @ X13 @ X14) | (r2_hidden @ (sk_C @ X14 @ X13) @ X14))),
% 11.69/11.93      inference('cnf', [status(esa)], [t3_xboole_0])).
% 11.69/11.93  thf('95', plain,
% 11.69/11.93      (![X13 : $i, X14 : $i]:
% 11.69/11.93         ((r1_xboole_0 @ X13 @ X14) | (r2_hidden @ (sk_C @ X14 @ X13) @ X13))),
% 11.69/11.93      inference('cnf', [status(esa)], [t3_xboole_0])).
% 11.69/11.93  thf(d5_xboole_0, axiom,
% 11.69/11.93    (![A:$i,B:$i,C:$i]:
% 11.69/11.93     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 11.69/11.93       ( ![D:$i]:
% 11.69/11.93         ( ( r2_hidden @ D @ C ) <=>
% 11.69/11.93           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 11.69/11.93  thf('96', plain,
% 11.69/11.93      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 11.69/11.93         (~ (r2_hidden @ X8 @ X7)
% 11.69/11.93          | ~ (r2_hidden @ X8 @ X6)
% 11.69/11.93          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 11.69/11.93      inference('cnf', [status(esa)], [d5_xboole_0])).
% 11.69/11.93  thf('97', plain,
% 11.69/11.93      (![X5 : $i, X6 : $i, X8 : $i]:
% 11.69/11.93         (~ (r2_hidden @ X8 @ X6)
% 11.69/11.93          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 11.69/11.93      inference('simplify', [status(thm)], ['96'])).
% 11.69/11.93  thf('98', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.69/11.93         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 11.69/11.93          | ~ (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 11.69/11.93      inference('sup-', [status(thm)], ['95', '97'])).
% 11.69/11.93  thf('99', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i]:
% 11.69/11.93         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 11.69/11.93          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 11.69/11.93      inference('sup-', [status(thm)], ['94', '98'])).
% 11.69/11.93  thf('100', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 11.69/11.93      inference('simplify', [status(thm)], ['99'])).
% 11.69/11.93  thf(d7_xboole_0, axiom,
% 11.69/11.93    (![A:$i,B:$i]:
% 11.69/11.93     ( ( r1_xboole_0 @ A @ B ) <=>
% 11.69/11.93       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 11.69/11.93  thf('101', plain,
% 11.69/11.93      (![X10 : $i, X11 : $i]:
% 11.69/11.93         (((k3_xboole_0 @ X10 @ X11) = (k1_xboole_0))
% 11.69/11.93          | ~ (r1_xboole_0 @ X10 @ X11))),
% 11.69/11.93      inference('cnf', [status(esa)], [d7_xboole_0])).
% 11.69/11.93  thf('102', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 11.69/11.93      inference('cnf', [status(esa)], [d2_xboole_0])).
% 11.69/11.93  thf('103', plain,
% 11.69/11.93      (![X10 : $i, X11 : $i]:
% 11.69/11.93         (((k3_xboole_0 @ X10 @ X11) = (o_0_0_xboole_0))
% 11.69/11.93          | ~ (r1_xboole_0 @ X10 @ X11))),
% 11.69/11.93      inference('demod', [status(thm)], ['101', '102'])).
% 11.69/11.93  thf('104', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i]:
% 11.69/11.93         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (o_0_0_xboole_0))),
% 11.69/11.93      inference('sup-', [status(thm)], ['100', '103'])).
% 11.69/11.93  thf('105', plain,
% 11.69/11.93      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 11.69/11.93      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 11.69/11.93  thf('106', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i]:
% 11.69/11.93         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (o_0_0_xboole_0))),
% 11.69/11.93      inference('demod', [status(thm)], ['104', '105'])).
% 11.69/11.93  thf('107', plain,
% 11.69/11.93      (![X34 : $i, X35 : $i]:
% 11.69/11.93         ((k4_xboole_0 @ X34 @ (k3_xboole_0 @ X34 @ X35))
% 11.69/11.93           = (k4_xboole_0 @ X34 @ X35))),
% 11.69/11.93      inference('cnf', [status(esa)], [t47_xboole_1])).
% 11.69/11.93  thf('108', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i]:
% 11.69/11.93         ((k4_xboole_0 @ X0 @ o_0_0_xboole_0)
% 11.69/11.93           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 11.69/11.93      inference('sup+', [status(thm)], ['106', '107'])).
% 11.69/11.93  thf('109', plain,
% 11.69/11.93      (![X28 : $i]: ((k4_xboole_0 @ X28 @ o_0_0_xboole_0) = (X28))),
% 11.69/11.93      inference('demod', [status(thm)], ['7', '8'])).
% 11.69/11.93  thf('110', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i]:
% 11.69/11.93         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 11.69/11.93      inference('demod', [status(thm)], ['108', '109'])).
% 11.69/11.93  thf('111', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.69/11.93         ((X0)
% 11.69/11.93           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 11.69/11.93      inference('sup+', [status(thm)], ['93', '110'])).
% 11.69/11.93  thf('112', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.69/11.93         ((k3_xboole_0 @ X1 @ X0)
% 11.69/11.93           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X2 @ X0)))),
% 11.69/11.93      inference('sup+', [status(thm)], ['92', '111'])).
% 11.69/11.93  thf('113', plain,
% 11.69/11.93      (![X0 : $i, X1 : $i]:
% 11.69/11.93         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 11.69/11.93           = (k3_xboole_0 @ X0 @ X1))),
% 11.69/11.93      inference('demod', [status(thm)], ['89', '112'])).
% 11.69/11.93  thf('114', plain,
% 11.69/11.93      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 11.69/11.93      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 11.69/11.93  thf('115', plain,
% 11.69/11.93      (((k3_xboole_0 @ sk_B @ sk_A) != (k3_xboole_0 @ sk_B @ sk_A))),
% 11.69/11.93      inference('demod', [status(thm)], ['2', '113', '114'])).
% 11.69/11.93  thf('116', plain, ($false), inference('simplify', [status(thm)], ['115'])).
% 11.69/11.93  
% 11.69/11.93  % SZS output end Refutation
% 11.69/11.93  
% 11.69/11.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

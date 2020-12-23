%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SSlzu1D2tG

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:13 EST 2020

% Result     : Theorem 15.99s
% Output     : Refutation 15.99s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 383 expanded)
%              Number of leaves         :   27 ( 137 expanded)
%              Depth                    :   18
%              Number of atoms          : 1207 (3215 expanded)
%              Number of equality atoms :  124 ( 346 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X39: $i,X40: $i] :
      ( ( k4_xboole_0 @ X39 @ ( k3_xboole_0 @ X39 @ X40 ) )
      = ( k4_xboole_0 @ X39 @ X40 ) ) ),
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
    ! [X34: $i,X35: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X34 @ X35 ) @ X35 )
      = ( k4_xboole_0 @ X34 @ X35 ) ) ),
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
    ! [X33: $i] :
      ( ( k4_xboole_0 @ X33 @ k1_xboole_0 )
      = X33 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('8',plain,(
    ! [X31: $i,X32: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X31 @ X32 ) @ X31 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X22: $i,X24: $i] :
      ( ( ( k4_xboole_0 @ X22 @ X24 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X36 @ X37 ) @ X38 )
      = ( k4_xboole_0 @ X36 @ ( k2_xboole_0 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('13',plain,(
    ! [X25: $i,X26: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X25 @ X26 ) @ X25 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('14',plain,(
    ! [X22: $i,X24: $i] :
      ( ( ( k4_xboole_0 @ X22 @ X24 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = ( k4_xboole_0 @ B @ A ) )
     => ( A = B ) ) )).

thf('16',plain,(
    ! [X29: $i,X30: $i] :
      ( ( X30 = X29 )
      | ( ( k4_xboole_0 @ X30 @ X29 )
       != ( k4_xboole_0 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t32_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
       != k1_xboole_0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k4_xboole_0 @ X39 @ ( k3_xboole_0 @ X39 @ X40 ) )
      = ( k4_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( ( k4_xboole_0 @ X2 @ X1 )
        = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
        = ( k3_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
        = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['21','22','23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('27',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ X27 @ ( k3_xboole_0 @ X27 @ X28 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('31',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X36 @ X37 ) @ X38 )
      = ( k4_xboole_0 @ X36 @ ( k2_xboole_0 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('32',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X36 @ X37 ) @ X38 )
      = ( k4_xboole_0 @ X36 @ ( k2_xboole_0 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k2_xboole_0 @ X0 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X36 @ X37 ) @ X38 )
      = ( k4_xboole_0 @ X36 @ ( k2_xboole_0 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('35',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X36 @ X37 ) @ X38 )
      = ( k4_xboole_0 @ X36 @ ( k2_xboole_0 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X3 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X3 ) ) ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X29: $i,X30: $i] :
      ( ( X30 = X29 )
      | ( ( k4_xboole_0 @ X30 @ X29 )
       != ( k4_xboole_0 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t32_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) )
       != k1_xboole_0 )
      | ( ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
        = ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X3 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X3 ) ) ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('43',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X36 @ X37 ) @ X38 )
      = ( k4_xboole_0 @ X36 @ ( k2_xboole_0 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X36 @ X37 ) @ X38 )
      = ( k4_xboole_0 @ X36 @ ( k2_xboole_0 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X31: $i,X32: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X31 @ X32 ) @ X31 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('48',plain,(
    ! [X22: $i,X24: $i] :
      ( ( ( k4_xboole_0 @ X22 @ X24 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X36 @ X37 ) @ X38 )
      = ( k4_xboole_0 @ X36 @ ( k2_xboole_0 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
        = ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['40','41','46','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['30','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['29','54'])).

thf('56',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X36 @ X37 ) @ X38 )
      = ( k4_xboole_0 @ X36 @ ( k2_xboole_0 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('60',plain,(
    ! [X29: $i,X30: $i] :
      ( ( X30 = X29 )
      | ( ( k4_xboole_0 @ X30 @ X29 )
       != ( k4_xboole_0 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t32_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
       != ( k4_xboole_0 @ X1 @ X0 ) )
      | ( X0
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('63',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X36 @ X37 ) @ X38 )
      = ( k4_xboole_0 @ X36 @ ( k2_xboole_0 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('66',plain,(
    ! [X31: $i,X32: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X31 @ X32 ) @ X31 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X22: $i,X24: $i] :
      ( ( ( k4_xboole_0 @ X22 @ X24 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['64','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
       != ( k4_xboole_0 @ X1 @ X0 ) )
      | ( X0
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['61','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
        = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['58','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
        = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('79',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ X27 @ ( k3_xboole_0 @ X27 @ X28 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','75'])).

thf('82',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X34 @ X35 ) @ X35 )
      = ( k4_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

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

thf('84',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ X14 @ X15 )
      | ( r2_hidden @ ( sk_C_1 @ X15 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('85',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ X14 @ X15 )
      | ( r2_hidden @ ( sk_C_1 @ X15 @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('86',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( r2_hidden @ X12 @ X10 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('87',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['89'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('91',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('92',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('93',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ ( k3_xboole_0 @ X18 @ X21 ) )
      | ~ ( r1_xboole_0 @ X18 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['91','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 ) ),
    inference('sup-',[status(thm)],['90','95'])).

thf('97',plain,(
    ! [X22: $i,X24: $i] :
      ( ( ( k4_xboole_0 @ X22 @ X24 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X1 ) ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X33: $i] :
      ( ( k4_xboole_0 @ X33 @ k1_xboole_0 )
      = X33 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k4_xboole_0 @ X39 @ ( k3_xboole_0 @ X39 @ X40 ) )
      = ( k4_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X33: $i] :
      ( ( k4_xboole_0 @ X33 @ k1_xboole_0 )
      = X33 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['83','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['80','105'])).

thf('107',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X36 @ X37 ) @ X38 )
      = ( k4_xboole_0 @ X36 @ ( k2_xboole_0 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('108',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('109',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ X27 @ ( k3_xboole_0 @ X27 @ X28 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['106','107','110'])).

thf('112',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('113',plain,(
    ( k3_xboole_0 @ sk_B @ sk_A )
 != ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['2','111','112'])).

thf('114',plain,(
    $false ),
    inference(simplify,[status(thm)],['113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SSlzu1D2tG
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:31:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 15.99/16.19  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 15.99/16.19  % Solved by: fo/fo7.sh
% 15.99/16.19  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 15.99/16.19  % done 17147 iterations in 15.728s
% 15.99/16.19  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 15.99/16.19  % SZS output start Refutation
% 15.99/16.19  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 15.99/16.19  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 15.99/16.19  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 15.99/16.19  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 15.99/16.19  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 15.99/16.19  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 15.99/16.19  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 15.99/16.19  thf(sk_A_type, type, sk_A: $i).
% 15.99/16.19  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 15.99/16.19  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 15.99/16.19  thf(sk_B_type, type, sk_B: $i).
% 15.99/16.19  thf(t48_xboole_1, conjecture,
% 15.99/16.19    (![A:$i,B:$i]:
% 15.99/16.19     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 15.99/16.19  thf(zf_stmt_0, negated_conjecture,
% 15.99/16.19    (~( ![A:$i,B:$i]:
% 15.99/16.19        ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) =
% 15.99/16.19          ( k3_xboole_0 @ A @ B ) ) )),
% 15.99/16.19    inference('cnf.neg', [status(esa)], [t48_xboole_1])).
% 15.99/16.19  thf('0', plain,
% 15.99/16.19      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 15.99/16.19         != (k3_xboole_0 @ sk_A @ sk_B))),
% 15.99/16.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.99/16.19  thf(commutativity_k3_xboole_0, axiom,
% 15.99/16.19    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 15.99/16.19  thf('1', plain,
% 15.99/16.19      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 15.99/16.19      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 15.99/16.19  thf('2', plain,
% 15.99/16.19      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 15.99/16.19         != (k3_xboole_0 @ sk_B @ sk_A))),
% 15.99/16.19      inference('demod', [status(thm)], ['0', '1'])).
% 15.99/16.19  thf(t47_xboole_1, axiom,
% 15.99/16.19    (![A:$i,B:$i]:
% 15.99/16.19     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 15.99/16.19  thf('3', plain,
% 15.99/16.19      (![X39 : $i, X40 : $i]:
% 15.99/16.19         ((k4_xboole_0 @ X39 @ (k3_xboole_0 @ X39 @ X40))
% 15.99/16.19           = (k4_xboole_0 @ X39 @ X40))),
% 15.99/16.19      inference('cnf', [status(esa)], [t47_xboole_1])).
% 15.99/16.19  thf(commutativity_k2_xboole_0, axiom,
% 15.99/16.19    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 15.99/16.19  thf('4', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 15.99/16.19      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 15.99/16.19  thf(t40_xboole_1, axiom,
% 15.99/16.19    (![A:$i,B:$i]:
% 15.99/16.19     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 15.99/16.19  thf('5', plain,
% 15.99/16.19      (![X34 : $i, X35 : $i]:
% 15.99/16.19         ((k4_xboole_0 @ (k2_xboole_0 @ X34 @ X35) @ X35)
% 15.99/16.19           = (k4_xboole_0 @ X34 @ X35))),
% 15.99/16.19      inference('cnf', [status(esa)], [t40_xboole_1])).
% 15.99/16.19  thf('6', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i]:
% 15.99/16.19         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 15.99/16.19           = (k4_xboole_0 @ X0 @ X1))),
% 15.99/16.19      inference('sup+', [status(thm)], ['4', '5'])).
% 15.99/16.19  thf(t3_boole, axiom,
% 15.99/16.19    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 15.99/16.19  thf('7', plain, (![X33 : $i]: ((k4_xboole_0 @ X33 @ k1_xboole_0) = (X33))),
% 15.99/16.19      inference('cnf', [status(esa)], [t3_boole])).
% 15.99/16.19  thf(t36_xboole_1, axiom,
% 15.99/16.19    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 15.99/16.19  thf('8', plain,
% 15.99/16.19      (![X31 : $i, X32 : $i]: (r1_tarski @ (k4_xboole_0 @ X31 @ X32) @ X31)),
% 15.99/16.19      inference('cnf', [status(esa)], [t36_xboole_1])).
% 15.99/16.19  thf('9', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 15.99/16.19      inference('sup+', [status(thm)], ['7', '8'])).
% 15.99/16.19  thf(l32_xboole_1, axiom,
% 15.99/16.19    (![A:$i,B:$i]:
% 15.99/16.19     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 15.99/16.19  thf('10', plain,
% 15.99/16.19      (![X22 : $i, X24 : $i]:
% 15.99/16.19         (((k4_xboole_0 @ X22 @ X24) = (k1_xboole_0))
% 15.99/16.19          | ~ (r1_tarski @ X22 @ X24))),
% 15.99/16.19      inference('cnf', [status(esa)], [l32_xboole_1])).
% 15.99/16.19  thf('11', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 15.99/16.19      inference('sup-', [status(thm)], ['9', '10'])).
% 15.99/16.19  thf(t41_xboole_1, axiom,
% 15.99/16.19    (![A:$i,B:$i,C:$i]:
% 15.99/16.19     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 15.99/16.19       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 15.99/16.19  thf('12', plain,
% 15.99/16.19      (![X36 : $i, X37 : $i, X38 : $i]:
% 15.99/16.19         ((k4_xboole_0 @ (k4_xboole_0 @ X36 @ X37) @ X38)
% 15.99/16.19           = (k4_xboole_0 @ X36 @ (k2_xboole_0 @ X37 @ X38)))),
% 15.99/16.19      inference('cnf', [status(esa)], [t41_xboole_1])).
% 15.99/16.19  thf(t17_xboole_1, axiom,
% 15.99/16.19    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 15.99/16.19  thf('13', plain,
% 15.99/16.19      (![X25 : $i, X26 : $i]: (r1_tarski @ (k3_xboole_0 @ X25 @ X26) @ X25)),
% 15.99/16.19      inference('cnf', [status(esa)], [t17_xboole_1])).
% 15.99/16.19  thf('14', plain,
% 15.99/16.19      (![X22 : $i, X24 : $i]:
% 15.99/16.19         (((k4_xboole_0 @ X22 @ X24) = (k1_xboole_0))
% 15.99/16.19          | ~ (r1_tarski @ X22 @ X24))),
% 15.99/16.19      inference('cnf', [status(esa)], [l32_xboole_1])).
% 15.99/16.19  thf('15', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i]:
% 15.99/16.19         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 15.99/16.19      inference('sup-', [status(thm)], ['13', '14'])).
% 15.99/16.19  thf(t32_xboole_1, axiom,
% 15.99/16.19    (![A:$i,B:$i]:
% 15.99/16.19     ( ( ( k4_xboole_0 @ A @ B ) = ( k4_xboole_0 @ B @ A ) ) =>
% 15.99/16.19       ( ( A ) = ( B ) ) ))).
% 15.99/16.19  thf('16', plain,
% 15.99/16.19      (![X29 : $i, X30 : $i]:
% 15.99/16.19         (((X30) = (X29))
% 15.99/16.19          | ((k4_xboole_0 @ X30 @ X29) != (k4_xboole_0 @ X29 @ X30)))),
% 15.99/16.19      inference('cnf', [status(esa)], [t32_xboole_1])).
% 15.99/16.19  thf('17', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i]:
% 15.99/16.19         (((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) != (k1_xboole_0))
% 15.99/16.19          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 15.99/16.19      inference('sup-', [status(thm)], ['15', '16'])).
% 15.99/16.19  thf('18', plain,
% 15.99/16.19      (![X39 : $i, X40 : $i]:
% 15.99/16.19         ((k4_xboole_0 @ X39 @ (k3_xboole_0 @ X39 @ X40))
% 15.99/16.19           = (k4_xboole_0 @ X39 @ X40))),
% 15.99/16.19      inference('cnf', [status(esa)], [t47_xboole_1])).
% 15.99/16.19  thf('19', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i]:
% 15.99/16.19         (((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0))
% 15.99/16.19          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 15.99/16.19      inference('demod', [status(thm)], ['17', '18'])).
% 15.99/16.19  thf('20', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.99/16.19         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 15.99/16.19          | ((k4_xboole_0 @ X2 @ X1)
% 15.99/16.19              = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))),
% 15.99/16.19      inference('sup-', [status(thm)], ['12', '19'])).
% 15.99/16.19  thf('21', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i]:
% 15.99/16.19         (((k1_xboole_0) != (k1_xboole_0))
% 15.99/16.19          | ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 15.99/16.19              = (k3_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ 
% 15.99/16.19                 X0)))),
% 15.99/16.19      inference('sup-', [status(thm)], ['11', '20'])).
% 15.99/16.19  thf('22', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i]:
% 15.99/16.19         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 15.99/16.19           = (k4_xboole_0 @ X0 @ X1))),
% 15.99/16.19      inference('sup+', [status(thm)], ['4', '5'])).
% 15.99/16.19  thf('23', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i]:
% 15.99/16.19         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 15.99/16.19           = (k4_xboole_0 @ X0 @ X1))),
% 15.99/16.19      inference('sup+', [status(thm)], ['4', '5'])).
% 15.99/16.19  thf('24', plain,
% 15.99/16.19      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 15.99/16.19      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 15.99/16.19  thf('25', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i]:
% 15.99/16.19         (((k1_xboole_0) != (k1_xboole_0))
% 15.99/16.19          | ((k4_xboole_0 @ X0 @ X1)
% 15.99/16.19              = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))))),
% 15.99/16.19      inference('demod', [status(thm)], ['21', '22', '23', '24'])).
% 15.99/16.19  thf('26', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i]:
% 15.99/16.19         ((k4_xboole_0 @ X0 @ X1)
% 15.99/16.19           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 15.99/16.19      inference('simplify', [status(thm)], ['25'])).
% 15.99/16.19  thf(t22_xboole_1, axiom,
% 15.99/16.19    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 15.99/16.19  thf('27', plain,
% 15.99/16.19      (![X27 : $i, X28 : $i]:
% 15.99/16.19         ((k2_xboole_0 @ X27 @ (k3_xboole_0 @ X27 @ X28)) = (X27))),
% 15.99/16.19      inference('cnf', [status(esa)], [t22_xboole_1])).
% 15.99/16.19  thf('28', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i]:
% 15.99/16.19         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 15.99/16.19      inference('sup+', [status(thm)], ['26', '27'])).
% 15.99/16.19  thf('29', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i]:
% 15.99/16.19         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 15.99/16.19           = (k2_xboole_0 @ X0 @ X1))),
% 15.99/16.19      inference('sup+', [status(thm)], ['6', '28'])).
% 15.99/16.19  thf('30', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 15.99/16.19      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 15.99/16.19  thf('31', plain,
% 15.99/16.19      (![X36 : $i, X37 : $i, X38 : $i]:
% 15.99/16.19         ((k4_xboole_0 @ (k4_xboole_0 @ X36 @ X37) @ X38)
% 15.99/16.19           = (k4_xboole_0 @ X36 @ (k2_xboole_0 @ X37 @ X38)))),
% 15.99/16.19      inference('cnf', [status(esa)], [t41_xboole_1])).
% 15.99/16.19  thf('32', plain,
% 15.99/16.19      (![X36 : $i, X37 : $i, X38 : $i]:
% 15.99/16.19         ((k4_xboole_0 @ (k4_xboole_0 @ X36 @ X37) @ X38)
% 15.99/16.19           = (k4_xboole_0 @ X36 @ (k2_xboole_0 @ X37 @ X38)))),
% 15.99/16.19      inference('cnf', [status(esa)], [t41_xboole_1])).
% 15.99/16.19  thf('33', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 15.99/16.19         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3)
% 15.99/16.19           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k2_xboole_0 @ X0 @ X3)))),
% 15.99/16.19      inference('sup+', [status(thm)], ['31', '32'])).
% 15.99/16.19  thf('34', plain,
% 15.99/16.19      (![X36 : $i, X37 : $i, X38 : $i]:
% 15.99/16.19         ((k4_xboole_0 @ (k4_xboole_0 @ X36 @ X37) @ X38)
% 15.99/16.19           = (k4_xboole_0 @ X36 @ (k2_xboole_0 @ X37 @ X38)))),
% 15.99/16.19      inference('cnf', [status(esa)], [t41_xboole_1])).
% 15.99/16.19  thf('35', plain,
% 15.99/16.19      (![X36 : $i, X37 : $i, X38 : $i]:
% 15.99/16.19         ((k4_xboole_0 @ (k4_xboole_0 @ X36 @ X37) @ X38)
% 15.99/16.19           = (k4_xboole_0 @ X36 @ (k2_xboole_0 @ X37 @ X38)))),
% 15.99/16.19      inference('cnf', [status(esa)], [t41_xboole_1])).
% 15.99/16.19  thf('36', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 15.99/16.19         ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X3))
% 15.99/16.19           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X3))))),
% 15.99/16.19      inference('demod', [status(thm)], ['33', '34', '35'])).
% 15.99/16.19  thf('37', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 15.99/16.19      inference('sup-', [status(thm)], ['9', '10'])).
% 15.99/16.19  thf('38', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.99/16.19         ((k4_xboole_0 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0) @ 
% 15.99/16.19           (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))) = (k1_xboole_0))),
% 15.99/16.19      inference('sup+', [status(thm)], ['36', '37'])).
% 15.99/16.19  thf('39', plain,
% 15.99/16.19      (![X29 : $i, X30 : $i]:
% 15.99/16.19         (((X30) = (X29))
% 15.99/16.19          | ((k4_xboole_0 @ X30 @ X29) != (k4_xboole_0 @ X29 @ X30)))),
% 15.99/16.19      inference('cnf', [status(esa)], [t32_xboole_1])).
% 15.99/16.19  thf('40', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.99/16.19         (((k4_xboole_0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 15.99/16.19            (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)) != (k1_xboole_0))
% 15.99/16.19          | ((k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 15.99/16.19              = (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)))),
% 15.99/16.19      inference('sup-', [status(thm)], ['38', '39'])).
% 15.99/16.19  thf('41', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 15.99/16.19         ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X3))
% 15.99/16.19           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X3))))),
% 15.99/16.19      inference('demod', [status(thm)], ['33', '34', '35'])).
% 15.99/16.19  thf('42', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i]:
% 15.99/16.19         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 15.99/16.19           = (k4_xboole_0 @ X0 @ X1))),
% 15.99/16.19      inference('sup+', [status(thm)], ['4', '5'])).
% 15.99/16.19  thf('43', plain,
% 15.99/16.19      (![X36 : $i, X37 : $i, X38 : $i]:
% 15.99/16.19         ((k4_xboole_0 @ (k4_xboole_0 @ X36 @ X37) @ X38)
% 15.99/16.19           = (k4_xboole_0 @ X36 @ (k2_xboole_0 @ X37 @ X38)))),
% 15.99/16.19      inference('cnf', [status(esa)], [t41_xboole_1])).
% 15.99/16.19  thf('44', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.99/16.19         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 15.99/16.19           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X0 @ X2)))),
% 15.99/16.19      inference('sup+', [status(thm)], ['42', '43'])).
% 15.99/16.19  thf('45', plain,
% 15.99/16.19      (![X36 : $i, X37 : $i, X38 : $i]:
% 15.99/16.19         ((k4_xboole_0 @ (k4_xboole_0 @ X36 @ X37) @ X38)
% 15.99/16.19           = (k4_xboole_0 @ X36 @ (k2_xboole_0 @ X37 @ X38)))),
% 15.99/16.19      inference('cnf', [status(esa)], [t41_xboole_1])).
% 15.99/16.19  thf('46', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.99/16.19         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2))
% 15.99/16.19           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X0 @ X2)))),
% 15.99/16.19      inference('demod', [status(thm)], ['44', '45'])).
% 15.99/16.19  thf('47', plain,
% 15.99/16.19      (![X31 : $i, X32 : $i]: (r1_tarski @ (k4_xboole_0 @ X31 @ X32) @ X31)),
% 15.99/16.19      inference('cnf', [status(esa)], [t36_xboole_1])).
% 15.99/16.19  thf('48', plain,
% 15.99/16.19      (![X22 : $i, X24 : $i]:
% 15.99/16.19         (((k4_xboole_0 @ X22 @ X24) = (k1_xboole_0))
% 15.99/16.19          | ~ (r1_tarski @ X22 @ X24))),
% 15.99/16.19      inference('cnf', [status(esa)], [l32_xboole_1])).
% 15.99/16.19  thf('49', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i]:
% 15.99/16.19         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 15.99/16.19      inference('sup-', [status(thm)], ['47', '48'])).
% 15.99/16.19  thf('50', plain,
% 15.99/16.19      (![X36 : $i, X37 : $i, X38 : $i]:
% 15.99/16.19         ((k4_xboole_0 @ (k4_xboole_0 @ X36 @ X37) @ X38)
% 15.99/16.19           = (k4_xboole_0 @ X36 @ (k2_xboole_0 @ X37 @ X38)))),
% 15.99/16.19      inference('cnf', [status(esa)], [t41_xboole_1])).
% 15.99/16.19  thf('51', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i]:
% 15.99/16.19         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 15.99/16.19      inference('demod', [status(thm)], ['49', '50'])).
% 15.99/16.19  thf('52', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.99/16.19         (((k1_xboole_0) != (k1_xboole_0))
% 15.99/16.19          | ((k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 15.99/16.19              = (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)))),
% 15.99/16.19      inference('demod', [status(thm)], ['40', '41', '46', '51'])).
% 15.99/16.19  thf('53', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.99/16.19         ((k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 15.99/16.19           = (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 15.99/16.19      inference('simplify', [status(thm)], ['52'])).
% 15.99/16.19  thf('54', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.99/16.19         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2))
% 15.99/16.19           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 15.99/16.19      inference('sup+', [status(thm)], ['30', '53'])).
% 15.99/16.19  thf('55', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i]:
% 15.99/16.19         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 15.99/16.19           = (k2_xboole_0 @ X0 @ X1))),
% 15.99/16.19      inference('demod', [status(thm)], ['29', '54'])).
% 15.99/16.19  thf('56', plain,
% 15.99/16.19      (![X36 : $i, X37 : $i, X38 : $i]:
% 15.99/16.19         ((k4_xboole_0 @ (k4_xboole_0 @ X36 @ X37) @ X38)
% 15.99/16.19           = (k4_xboole_0 @ X36 @ (k2_xboole_0 @ X37 @ X38)))),
% 15.99/16.19      inference('cnf', [status(esa)], [t41_xboole_1])).
% 15.99/16.19  thf('57', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 15.99/16.19      inference('sup-', [status(thm)], ['9', '10'])).
% 15.99/16.19  thf('58', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i]:
% 15.99/16.19         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 15.99/16.19           = (k1_xboole_0))),
% 15.99/16.19      inference('sup+', [status(thm)], ['56', '57'])).
% 15.99/16.19  thf('59', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i]:
% 15.99/16.19         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 15.99/16.19           = (k4_xboole_0 @ X0 @ X1))),
% 15.99/16.19      inference('sup+', [status(thm)], ['4', '5'])).
% 15.99/16.19  thf('60', plain,
% 15.99/16.19      (![X29 : $i, X30 : $i]:
% 15.99/16.19         (((X30) = (X29))
% 15.99/16.19          | ((k4_xboole_0 @ X30 @ X29) != (k4_xboole_0 @ X29 @ X30)))),
% 15.99/16.19      inference('cnf', [status(esa)], [t32_xboole_1])).
% 15.99/16.19  thf('61', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i]:
% 15.99/16.19         (((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 15.99/16.19            != (k4_xboole_0 @ X1 @ X0))
% 15.99/16.19          | ((X0) = (k2_xboole_0 @ X0 @ X1)))),
% 15.99/16.19      inference('sup-', [status(thm)], ['59', '60'])).
% 15.99/16.19  thf('62', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 15.99/16.19      inference('sup-', [status(thm)], ['9', '10'])).
% 15.99/16.19  thf('63', plain,
% 15.99/16.19      (![X36 : $i, X37 : $i, X38 : $i]:
% 15.99/16.19         ((k4_xboole_0 @ (k4_xboole_0 @ X36 @ X37) @ X38)
% 15.99/16.19           = (k4_xboole_0 @ X36 @ (k2_xboole_0 @ X37 @ X38)))),
% 15.99/16.19      inference('cnf', [status(esa)], [t41_xboole_1])).
% 15.99/16.19  thf('64', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i]:
% 15.99/16.19         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 15.99/16.19           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 15.99/16.19      inference('sup+', [status(thm)], ['62', '63'])).
% 15.99/16.19  thf('65', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 15.99/16.19      inference('sup-', [status(thm)], ['9', '10'])).
% 15.99/16.19  thf('66', plain,
% 15.99/16.19      (![X31 : $i, X32 : $i]: (r1_tarski @ (k4_xboole_0 @ X31 @ X32) @ X31)),
% 15.99/16.19      inference('cnf', [status(esa)], [t36_xboole_1])).
% 15.99/16.19  thf('67', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 15.99/16.19      inference('sup+', [status(thm)], ['65', '66'])).
% 15.99/16.19  thf('68', plain,
% 15.99/16.19      (![X22 : $i, X24 : $i]:
% 15.99/16.19         (((k4_xboole_0 @ X22 @ X24) = (k1_xboole_0))
% 15.99/16.19          | ~ (r1_tarski @ X22 @ X24))),
% 15.99/16.19      inference('cnf', [status(esa)], [l32_xboole_1])).
% 15.99/16.19  thf('69', plain,
% 15.99/16.19      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 15.99/16.19      inference('sup-', [status(thm)], ['67', '68'])).
% 15.99/16.19  thf('70', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i]:
% 15.99/16.19         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 15.99/16.19      inference('demod', [status(thm)], ['64', '69'])).
% 15.99/16.19  thf('71', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i]:
% 15.99/16.19         (((k1_xboole_0) != (k4_xboole_0 @ X1 @ X0))
% 15.99/16.19          | ((X0) = (k2_xboole_0 @ X0 @ X1)))),
% 15.99/16.19      inference('demod', [status(thm)], ['61', '70'])).
% 15.99/16.19  thf('72', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i]:
% 15.99/16.19         (((k1_xboole_0) != (k1_xboole_0))
% 15.99/16.19          | ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 15.99/16.19              = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 15.99/16.19                 X1)))),
% 15.99/16.19      inference('sup-', [status(thm)], ['58', '71'])).
% 15.99/16.19  thf('73', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 15.99/16.19      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 15.99/16.19  thf('74', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i]:
% 15.99/16.19         (((k1_xboole_0) != (k1_xboole_0))
% 15.99/16.19          | ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 15.99/16.19              = (k2_xboole_0 @ X1 @ 
% 15.99/16.19                 (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))))),
% 15.99/16.19      inference('demod', [status(thm)], ['72', '73'])).
% 15.99/16.19  thf('75', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i]:
% 15.99/16.19         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 15.99/16.19           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 15.99/16.19      inference('simplify', [status(thm)], ['74'])).
% 15.99/16.19  thf('76', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i]:
% 15.99/16.19         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1))
% 15.99/16.19           = (k2_xboole_0 @ X1 @ X0))),
% 15.99/16.19      inference('sup+', [status(thm)], ['55', '75'])).
% 15.99/16.19  thf('77', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i]:
% 15.99/16.19         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 15.99/16.19           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 15.99/16.19      inference('sup+', [status(thm)], ['3', '76'])).
% 15.99/16.19  thf('78', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 15.99/16.19      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 15.99/16.19  thf('79', plain,
% 15.99/16.19      (![X27 : $i, X28 : $i]:
% 15.99/16.19         ((k2_xboole_0 @ X27 @ (k3_xboole_0 @ X27 @ X28)) = (X27))),
% 15.99/16.19      inference('cnf', [status(esa)], [t22_xboole_1])).
% 15.99/16.19  thf('80', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i]:
% 15.99/16.19         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 15.99/16.19           = (X1))),
% 15.99/16.19      inference('demod', [status(thm)], ['77', '78', '79'])).
% 15.99/16.19  thf('81', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i]:
% 15.99/16.19         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1))
% 15.99/16.19           = (k2_xboole_0 @ X1 @ X0))),
% 15.99/16.19      inference('sup+', [status(thm)], ['55', '75'])).
% 15.99/16.19  thf('82', plain,
% 15.99/16.19      (![X34 : $i, X35 : $i]:
% 15.99/16.19         ((k4_xboole_0 @ (k2_xboole_0 @ X34 @ X35) @ X35)
% 15.99/16.19           = (k4_xboole_0 @ X34 @ X35))),
% 15.99/16.19      inference('cnf', [status(esa)], [t40_xboole_1])).
% 15.99/16.19  thf('83', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i]:
% 15.99/16.19         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 15.99/16.19           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 15.99/16.19      inference('sup+', [status(thm)], ['81', '82'])).
% 15.99/16.19  thf(t3_xboole_0, axiom,
% 15.99/16.19    (![A:$i,B:$i]:
% 15.99/16.19     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 15.99/16.19            ( r1_xboole_0 @ A @ B ) ) ) & 
% 15.99/16.19       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 15.99/16.19            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 15.99/16.19  thf('84', plain,
% 15.99/16.19      (![X14 : $i, X15 : $i]:
% 15.99/16.19         ((r1_xboole_0 @ X14 @ X15) | (r2_hidden @ (sk_C_1 @ X15 @ X14) @ X15))),
% 15.99/16.19      inference('cnf', [status(esa)], [t3_xboole_0])).
% 15.99/16.19  thf('85', plain,
% 15.99/16.19      (![X14 : $i, X15 : $i]:
% 15.99/16.19         ((r1_xboole_0 @ X14 @ X15) | (r2_hidden @ (sk_C_1 @ X15 @ X14) @ X14))),
% 15.99/16.19      inference('cnf', [status(esa)], [t3_xboole_0])).
% 15.99/16.19  thf(d5_xboole_0, axiom,
% 15.99/16.19    (![A:$i,B:$i,C:$i]:
% 15.99/16.19     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 15.99/16.19       ( ![D:$i]:
% 15.99/16.19         ( ( r2_hidden @ D @ C ) <=>
% 15.99/16.19           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 15.99/16.19  thf('86', plain,
% 15.99/16.19      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 15.99/16.19         (~ (r2_hidden @ X12 @ X11)
% 15.99/16.19          | ~ (r2_hidden @ X12 @ X10)
% 15.99/16.19          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 15.99/16.19      inference('cnf', [status(esa)], [d5_xboole_0])).
% 15.99/16.19  thf('87', plain,
% 15.99/16.19      (![X9 : $i, X10 : $i, X12 : $i]:
% 15.99/16.19         (~ (r2_hidden @ X12 @ X10)
% 15.99/16.19          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 15.99/16.19      inference('simplify', [status(thm)], ['86'])).
% 15.99/16.19  thf('88', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.99/16.19         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 15.99/16.19          | ~ (r2_hidden @ (sk_C_1 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 15.99/16.19      inference('sup-', [status(thm)], ['85', '87'])).
% 15.99/16.19  thf('89', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i]:
% 15.99/16.19         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 15.99/16.19          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 15.99/16.19      inference('sup-', [status(thm)], ['84', '88'])).
% 15.99/16.19  thf('90', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 15.99/16.19      inference('simplify', [status(thm)], ['89'])).
% 15.99/16.19  thf(d3_tarski, axiom,
% 15.99/16.19    (![A:$i,B:$i]:
% 15.99/16.19     ( ( r1_tarski @ A @ B ) <=>
% 15.99/16.19       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 15.99/16.19  thf('91', plain,
% 15.99/16.19      (![X5 : $i, X7 : $i]:
% 15.99/16.19         ((r1_tarski @ X5 @ X7) | (r2_hidden @ (sk_C @ X7 @ X5) @ X5))),
% 15.99/16.19      inference('cnf', [status(esa)], [d3_tarski])).
% 15.99/16.19  thf('92', plain,
% 15.99/16.19      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 15.99/16.19      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 15.99/16.19  thf(t4_xboole_0, axiom,
% 15.99/16.19    (![A:$i,B:$i]:
% 15.99/16.19     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 15.99/16.19            ( r1_xboole_0 @ A @ B ) ) ) & 
% 15.99/16.19       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 15.99/16.19            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 15.99/16.19  thf('93', plain,
% 15.99/16.19      (![X18 : $i, X20 : $i, X21 : $i]:
% 15.99/16.19         (~ (r2_hidden @ X20 @ (k3_xboole_0 @ X18 @ X21))
% 15.99/16.19          | ~ (r1_xboole_0 @ X18 @ X21))),
% 15.99/16.19      inference('cnf', [status(esa)], [t4_xboole_0])).
% 15.99/16.19  thf('94', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.99/16.19         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 15.99/16.19          | ~ (r1_xboole_0 @ X0 @ X1))),
% 15.99/16.19      inference('sup-', [status(thm)], ['92', '93'])).
% 15.99/16.19  thf('95', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.99/16.19         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 15.99/16.19          | ~ (r1_xboole_0 @ X0 @ X1))),
% 15.99/16.19      inference('sup-', [status(thm)], ['91', '94'])).
% 15.99/16.19  thf('96', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.99/16.19         (r1_tarski @ (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ X2)),
% 15.99/16.19      inference('sup-', [status(thm)], ['90', '95'])).
% 15.99/16.19  thf('97', plain,
% 15.99/16.19      (![X22 : $i, X24 : $i]:
% 15.99/16.19         (((k4_xboole_0 @ X22 @ X24) = (k1_xboole_0))
% 15.99/16.19          | ~ (r1_tarski @ X22 @ X24))),
% 15.99/16.19      inference('cnf', [status(esa)], [l32_xboole_1])).
% 15.99/16.19  thf('98', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.99/16.19         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X1)) @ X0)
% 15.99/16.19           = (k1_xboole_0))),
% 15.99/16.19      inference('sup-', [status(thm)], ['96', '97'])).
% 15.99/16.19  thf('99', plain, (![X33 : $i]: ((k4_xboole_0 @ X33 @ k1_xboole_0) = (X33))),
% 15.99/16.19      inference('cnf', [status(esa)], [t3_boole])).
% 15.99/16.19  thf('100', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i]:
% 15.99/16.19         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 15.99/16.19      inference('sup+', [status(thm)], ['98', '99'])).
% 15.99/16.19  thf('101', plain,
% 15.99/16.19      (![X39 : $i, X40 : $i]:
% 15.99/16.19         ((k4_xboole_0 @ X39 @ (k3_xboole_0 @ X39 @ X40))
% 15.99/16.19           = (k4_xboole_0 @ X39 @ X40))),
% 15.99/16.19      inference('cnf', [status(esa)], [t47_xboole_1])).
% 15.99/16.19  thf('102', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i]:
% 15.99/16.19         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 15.99/16.19           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 15.99/16.19      inference('sup+', [status(thm)], ['100', '101'])).
% 15.99/16.19  thf('103', plain, (![X33 : $i]: ((k4_xboole_0 @ X33 @ k1_xboole_0) = (X33))),
% 15.99/16.19      inference('cnf', [status(esa)], [t3_boole])).
% 15.99/16.19  thf('104', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i]:
% 15.99/16.19         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 15.99/16.19      inference('demod', [status(thm)], ['102', '103'])).
% 15.99/16.19  thf('105', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i]:
% 15.99/16.19         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 15.99/16.19           = (X1))),
% 15.99/16.19      inference('demod', [status(thm)], ['83', '104'])).
% 15.99/16.19  thf('106', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i]:
% 15.99/16.19         ((k4_xboole_0 @ X0 @ 
% 15.99/16.19           (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1)))
% 15.99/16.19           = (k3_xboole_0 @ X0 @ X1))),
% 15.99/16.19      inference('sup+', [status(thm)], ['80', '105'])).
% 15.99/16.19  thf('107', plain,
% 15.99/16.19      (![X36 : $i, X37 : $i, X38 : $i]:
% 15.99/16.19         ((k4_xboole_0 @ (k4_xboole_0 @ X36 @ X37) @ X38)
% 15.99/16.19           = (k4_xboole_0 @ X36 @ (k2_xboole_0 @ X37 @ X38)))),
% 15.99/16.19      inference('cnf', [status(esa)], [t41_xboole_1])).
% 15.99/16.19  thf('108', plain,
% 15.99/16.19      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 15.99/16.19      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 15.99/16.19  thf('109', plain,
% 15.99/16.19      (![X27 : $i, X28 : $i]:
% 15.99/16.19         ((k2_xboole_0 @ X27 @ (k3_xboole_0 @ X27 @ X28)) = (X27))),
% 15.99/16.19      inference('cnf', [status(esa)], [t22_xboole_1])).
% 15.99/16.19  thf('110', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i]:
% 15.99/16.19         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 15.99/16.19      inference('sup+', [status(thm)], ['108', '109'])).
% 15.99/16.19  thf('111', plain,
% 15.99/16.19      (![X0 : $i, X1 : $i]:
% 15.99/16.19         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 15.99/16.19           = (k3_xboole_0 @ X0 @ X1))),
% 15.99/16.19      inference('demod', [status(thm)], ['106', '107', '110'])).
% 15.99/16.19  thf('112', plain,
% 15.99/16.19      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 15.99/16.19      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 15.99/16.19  thf('113', plain,
% 15.99/16.19      (((k3_xboole_0 @ sk_B @ sk_A) != (k3_xboole_0 @ sk_B @ sk_A))),
% 15.99/16.19      inference('demod', [status(thm)], ['2', '111', '112'])).
% 15.99/16.19  thf('114', plain, ($false), inference('simplify', [status(thm)], ['113'])).
% 15.99/16.19  
% 15.99/16.19  % SZS output end Refutation
% 15.99/16.19  
% 16.01/16.20  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

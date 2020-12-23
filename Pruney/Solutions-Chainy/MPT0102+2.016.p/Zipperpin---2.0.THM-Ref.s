%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gnOmVoC3M3

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:59 EST 2020

% Result     : Theorem 8.76s
% Output     : Refutation 8.76s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 233 expanded)
%              Number of leaves         :   27 (  90 expanded)
%              Depth                    :   15
%              Number of atoms          : 1203 (1858 expanded)
%              Number of equality atoms :  132 ( 217 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t95_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k3_xboole_0 @ A @ B )
        = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t95_xboole_1])).

thf('0',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t93_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k2_xboole_0 @ X37 @ X38 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X37 @ X38 ) @ ( k3_xboole_0 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X19 @ X20 ) @ X20 )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('12',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k2_xboole_0 @ X24 @ X25 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X15: $i] :
      ( ( k2_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','11','12','13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','17'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('19',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k3_xboole_0 @ X28 @ ( k4_xboole_0 @ X29 @ X30 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X28 @ X29 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X15: $i] :
      ( ( k2_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(l97_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X6 @ X7 ) @ ( k5_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf(t78_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ A @ C ) ) ) )).

thf('23',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( r1_xboole_0 @ X34 @ X35 )
      | ( ( k3_xboole_0 @ X34 @ ( k2_xboole_0 @ X35 @ X36 ) )
        = ( k3_xboole_0 @ X34 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t78_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('25',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k3_xboole_0 @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('26',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k3_xboole_0 @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 ) ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['21','27'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('29',plain,(
    ! [X18: $i] :
      ( ( k3_xboole_0 @ X18 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('30',plain,(
    ! [X18: $i] :
      ( ( k3_xboole_0 @ X18 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('32',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('33',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k4_xboole_0 @ X26 @ ( k4_xboole_0 @ X26 @ X27 ) )
      = ( k3_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('34',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k4_xboole_0 @ X26 @ ( k4_xboole_0 @ X26 @ X27 ) )
      = ( k3_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X15: $i] :
      ( ( k2_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('37',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k3_xboole_0 @ X28 @ ( k4_xboole_0 @ X29 @ X30 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X28 @ X29 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['32','41'])).

thf('43',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k3_xboole_0 @ X28 @ ( k4_xboole_0 @ X29 @ X30 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X28 @ X29 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('46',plain,(
    ! [X15: $i] :
      ( ( k2_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('47',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k2_xboole_0 @ X24 @ X25 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X18: $i] :
      ( ( k3_xboole_0 @ X18 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45','48','49','50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X1 ) ) @ k1_xboole_0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','52'])).

thf('54',plain,(
    ! [X18: $i] :
      ( ( k3_xboole_0 @ X18 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('55',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k2_xboole_0 @ X37 @ X38 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X37 @ X38 ) @ ( k3_xboole_0 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X15: $i] :
      ( ( k2_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('60',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['56','57','58','59'])).

thf('61',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('62',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k3_xboole_0 @ X28 @ ( k4_xboole_0 @ X29 @ X30 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X28 @ X29 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('66',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['53','60','63','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['35','40'])).

thf('73',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k3_xboole_0 @ X28 @ ( k4_xboole_0 @ X29 @ X30 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X28 @ X29 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('76',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('77',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('82',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k2_xboole_0 @ X24 @ X25 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['80','83'])).

thf('85',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k3_xboole_0 @ X28 @ ( k4_xboole_0 @ X29 @ X30 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X28 @ X29 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['74','75','86','87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['71','89'])).

thf('91',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k4_xboole_0 @ X26 @ ( k4_xboole_0 @ X26 @ X27 ) )
      = ( k3_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('92',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('94',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k4_xboole_0 @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['93','94','95','96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['90','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['20','99'])).

thf('101',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X19 @ X20 ) @ X20 )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('105',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k4_xboole_0 @ X26 @ ( k4_xboole_0 @ X26 @ X27 ) )
      = ( k3_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['103','110'])).

thf('112',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k4_xboole_0 @ X26 @ ( k4_xboole_0 @ X26 @ X27 ) )
      = ( k3_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['100','113'])).

thf('115',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('116',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','114','115'])).

thf('117',plain,(
    $false ),
    inference(simplify,[status(thm)],['116'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gnOmVoC3M3
% 0.16/0.37  % Computer   : n017.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 13:56:01 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 8.76/8.95  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 8.76/8.95  % Solved by: fo/fo7.sh
% 8.76/8.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.76/8.95  % done 7288 iterations in 8.504s
% 8.76/8.95  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 8.76/8.95  % SZS output start Refutation
% 8.76/8.95  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 8.76/8.95  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 8.76/8.95  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 8.76/8.95  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 8.76/8.95  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 8.76/8.95  thf(sk_B_type, type, sk_B: $i).
% 8.76/8.95  thf(sk_A_type, type, sk_A: $i).
% 8.76/8.95  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 8.76/8.95  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 8.76/8.95  thf(t95_xboole_1, conjecture,
% 8.76/8.95    (![A:$i,B:$i]:
% 8.76/8.95     ( ( k3_xboole_0 @ A @ B ) =
% 8.76/8.95       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 8.76/8.95  thf(zf_stmt_0, negated_conjecture,
% 8.76/8.95    (~( ![A:$i,B:$i]:
% 8.76/8.95        ( ( k3_xboole_0 @ A @ B ) =
% 8.76/8.95          ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 8.76/8.95    inference('cnf.neg', [status(esa)], [t95_xboole_1])).
% 8.76/8.95  thf('0', plain,
% 8.76/8.95      (((k3_xboole_0 @ sk_A @ sk_B)
% 8.76/8.95         != (k5_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ 
% 8.76/8.95             (k2_xboole_0 @ sk_A @ sk_B)))),
% 8.76/8.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.76/8.95  thf(t93_xboole_1, axiom,
% 8.76/8.95    (![A:$i,B:$i]:
% 8.76/8.95     ( ( k2_xboole_0 @ A @ B ) =
% 8.76/8.95       ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 8.76/8.95  thf('1', plain,
% 8.76/8.95      (![X37 : $i, X38 : $i]:
% 8.76/8.95         ((k2_xboole_0 @ X37 @ X38)
% 8.76/8.95           = (k2_xboole_0 @ (k5_xboole_0 @ X37 @ X38) @ 
% 8.76/8.95              (k3_xboole_0 @ X37 @ X38)))),
% 8.76/8.95      inference('cnf', [status(esa)], [t93_xboole_1])).
% 8.76/8.95  thf(commutativity_k2_xboole_0, axiom,
% 8.76/8.95    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 8.76/8.95  thf('2', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 8.76/8.95      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 8.76/8.95  thf(t40_xboole_1, axiom,
% 8.76/8.95    (![A:$i,B:$i]:
% 8.76/8.95     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 8.76/8.95  thf('3', plain,
% 8.76/8.95      (![X19 : $i, X20 : $i]:
% 8.76/8.95         ((k4_xboole_0 @ (k2_xboole_0 @ X19 @ X20) @ X20)
% 8.76/8.95           = (k4_xboole_0 @ X19 @ X20))),
% 8.76/8.95      inference('cnf', [status(esa)], [t40_xboole_1])).
% 8.76/8.95  thf('4', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]:
% 8.76/8.95         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 8.76/8.95           = (k4_xboole_0 @ X0 @ X1))),
% 8.76/8.95      inference('sup+', [status(thm)], ['2', '3'])).
% 8.76/8.95  thf(d6_xboole_0, axiom,
% 8.76/8.95    (![A:$i,B:$i]:
% 8.76/8.95     ( ( k5_xboole_0 @ A @ B ) =
% 8.76/8.95       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 8.76/8.95  thf('5', plain,
% 8.76/8.95      (![X4 : $i, X5 : $i]:
% 8.76/8.95         ((k5_xboole_0 @ X4 @ X5)
% 8.76/8.95           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 8.76/8.95      inference('cnf', [status(esa)], [d6_xboole_0])).
% 8.76/8.95  thf('6', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]:
% 8.76/8.95         ((k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 8.76/8.95           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 8.76/8.95              (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))))),
% 8.76/8.95      inference('sup+', [status(thm)], ['4', '5'])).
% 8.76/8.95  thf('7', plain,
% 8.76/8.95      (![X4 : $i, X5 : $i]:
% 8.76/8.95         ((k5_xboole_0 @ X4 @ X5)
% 8.76/8.95           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 8.76/8.95      inference('cnf', [status(esa)], [d6_xboole_0])).
% 8.76/8.95  thf('8', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 8.76/8.95      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 8.76/8.95  thf('9', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]:
% 8.76/8.95         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 8.76/8.95           = (k5_xboole_0 @ X1 @ X0))),
% 8.76/8.95      inference('sup+', [status(thm)], ['7', '8'])).
% 8.76/8.95  thf('10', plain,
% 8.76/8.95      (![X4 : $i, X5 : $i]:
% 8.76/8.95         ((k5_xboole_0 @ X4 @ X5)
% 8.76/8.95           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 8.76/8.95      inference('cnf', [status(esa)], [d6_xboole_0])).
% 8.76/8.95  thf('11', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 8.76/8.95      inference('sup+', [status(thm)], ['9', '10'])).
% 8.76/8.95  thf(t46_xboole_1, axiom,
% 8.76/8.95    (![A:$i,B:$i]:
% 8.76/8.95     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 8.76/8.95  thf('12', plain,
% 8.76/8.95      (![X24 : $i, X25 : $i]:
% 8.76/8.95         ((k4_xboole_0 @ X24 @ (k2_xboole_0 @ X24 @ X25)) = (k1_xboole_0))),
% 8.76/8.95      inference('cnf', [status(esa)], [t46_xboole_1])).
% 8.76/8.95  thf('13', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 8.76/8.95      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 8.76/8.95  thf('14', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 8.76/8.95      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 8.76/8.95  thf(t1_boole, axiom,
% 8.76/8.95    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 8.76/8.95  thf('15', plain, (![X15 : $i]: ((k2_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 8.76/8.95      inference('cnf', [status(esa)], [t1_boole])).
% 8.76/8.95  thf('16', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 8.76/8.95      inference('sup+', [status(thm)], ['14', '15'])).
% 8.76/8.95  thf('17', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]:
% 8.76/8.95         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 8.76/8.95           = (k4_xboole_0 @ X1 @ X0))),
% 8.76/8.95      inference('demod', [status(thm)], ['6', '11', '12', '13', '16'])).
% 8.76/8.95  thf('18', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]:
% 8.76/8.95         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 8.76/8.95           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)))),
% 8.76/8.95      inference('sup+', [status(thm)], ['1', '17'])).
% 8.76/8.95  thf(t49_xboole_1, axiom,
% 8.76/8.95    (![A:$i,B:$i,C:$i]:
% 8.76/8.95     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 8.76/8.95       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 8.76/8.95  thf('19', plain,
% 8.76/8.95      (![X28 : $i, X29 : $i, X30 : $i]:
% 8.76/8.95         ((k3_xboole_0 @ X28 @ (k4_xboole_0 @ X29 @ X30))
% 8.76/8.95           = (k4_xboole_0 @ (k3_xboole_0 @ X28 @ X29) @ X30))),
% 8.76/8.95      inference('cnf', [status(esa)], [t49_xboole_1])).
% 8.76/8.95  thf('20', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]:
% 8.76/8.95         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 8.76/8.95           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 8.76/8.95      inference('demod', [status(thm)], ['18', '19'])).
% 8.76/8.95  thf('21', plain, (![X15 : $i]: ((k2_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 8.76/8.95      inference('cnf', [status(esa)], [t1_boole])).
% 8.76/8.95  thf(l97_xboole_1, axiom,
% 8.76/8.95    (![A:$i,B:$i]:
% 8.76/8.95     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 8.76/8.95  thf('22', plain,
% 8.76/8.95      (![X6 : $i, X7 : $i]:
% 8.76/8.95         (r1_xboole_0 @ (k3_xboole_0 @ X6 @ X7) @ (k5_xboole_0 @ X6 @ X7))),
% 8.76/8.95      inference('cnf', [status(esa)], [l97_xboole_1])).
% 8.76/8.95  thf(t78_xboole_1, axiom,
% 8.76/8.95    (![A:$i,B:$i,C:$i]:
% 8.76/8.95     ( ( r1_xboole_0 @ A @ B ) =>
% 8.76/8.95       ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 8.76/8.95         ( k3_xboole_0 @ A @ C ) ) ))).
% 8.76/8.95  thf('23', plain,
% 8.76/8.95      (![X34 : $i, X35 : $i, X36 : $i]:
% 8.76/8.95         (~ (r1_xboole_0 @ X34 @ X35)
% 8.76/8.95          | ((k3_xboole_0 @ X34 @ (k2_xboole_0 @ X35 @ X36))
% 8.76/8.95              = (k3_xboole_0 @ X34 @ X36)))),
% 8.76/8.95      inference('cnf', [status(esa)], [t78_xboole_1])).
% 8.76/8.95  thf('24', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.76/8.95         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 8.76/8.95           (k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2))
% 8.76/8.95           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 8.76/8.95      inference('sup-', [status(thm)], ['22', '23'])).
% 8.76/8.95  thf(t16_xboole_1, axiom,
% 8.76/8.95    (![A:$i,B:$i,C:$i]:
% 8.76/8.95     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 8.76/8.95       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 8.76/8.95  thf('25', plain,
% 8.76/8.95      (![X10 : $i, X11 : $i, X12 : $i]:
% 8.76/8.95         ((k3_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12)
% 8.76/8.95           = (k3_xboole_0 @ X10 @ (k3_xboole_0 @ X11 @ X12)))),
% 8.76/8.95      inference('cnf', [status(esa)], [t16_xboole_1])).
% 8.76/8.95  thf('26', plain,
% 8.76/8.95      (![X10 : $i, X11 : $i, X12 : $i]:
% 8.76/8.95         ((k3_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12)
% 8.76/8.95           = (k3_xboole_0 @ X10 @ (k3_xboole_0 @ X11 @ X12)))),
% 8.76/8.95      inference('cnf', [status(esa)], [t16_xboole_1])).
% 8.76/8.95  thf('27', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.76/8.95         ((k3_xboole_0 @ X1 @ 
% 8.76/8.95           (k3_xboole_0 @ X0 @ (k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)))
% 8.76/8.95           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X2)))),
% 8.76/8.95      inference('demod', [status(thm)], ['24', '25', '26'])).
% 8.76/8.95  thf('28', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]:
% 8.76/8.95         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 8.76/8.95           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 8.76/8.95      inference('sup+', [status(thm)], ['21', '27'])).
% 8.76/8.95  thf(t2_boole, axiom,
% 8.76/8.95    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 8.76/8.95  thf('29', plain,
% 8.76/8.95      (![X18 : $i]: ((k3_xboole_0 @ X18 @ k1_xboole_0) = (k1_xboole_0))),
% 8.76/8.95      inference('cnf', [status(esa)], [t2_boole])).
% 8.76/8.95  thf('30', plain,
% 8.76/8.95      (![X18 : $i]: ((k3_xboole_0 @ X18 @ k1_xboole_0) = (k1_xboole_0))),
% 8.76/8.95      inference('cnf', [status(esa)], [t2_boole])).
% 8.76/8.95  thf('31', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]:
% 8.76/8.95         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 8.76/8.95           = (k1_xboole_0))),
% 8.76/8.95      inference('demod', [status(thm)], ['28', '29', '30'])).
% 8.76/8.95  thf(commutativity_k3_xboole_0, axiom,
% 8.76/8.95    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 8.76/8.95  thf('32', plain,
% 8.76/8.95      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 8.76/8.95      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 8.76/8.95  thf(t48_xboole_1, axiom,
% 8.76/8.95    (![A:$i,B:$i]:
% 8.76/8.95     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 8.76/8.95  thf('33', plain,
% 8.76/8.95      (![X26 : $i, X27 : $i]:
% 8.76/8.95         ((k4_xboole_0 @ X26 @ (k4_xboole_0 @ X26 @ X27))
% 8.76/8.95           = (k3_xboole_0 @ X26 @ X27))),
% 8.76/8.95      inference('cnf', [status(esa)], [t48_xboole_1])).
% 8.76/8.95  thf('34', plain,
% 8.76/8.95      (![X26 : $i, X27 : $i]:
% 8.76/8.95         ((k4_xboole_0 @ X26 @ (k4_xboole_0 @ X26 @ X27))
% 8.76/8.95           = (k3_xboole_0 @ X26 @ X27))),
% 8.76/8.95      inference('cnf', [status(esa)], [t48_xboole_1])).
% 8.76/8.95  thf('35', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]:
% 8.76/8.95         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 8.76/8.95           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 8.76/8.95      inference('sup+', [status(thm)], ['33', '34'])).
% 8.76/8.95  thf('36', plain, (![X15 : $i]: ((k2_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 8.76/8.95      inference('cnf', [status(esa)], [t1_boole])).
% 8.76/8.95  thf(t21_xboole_1, axiom,
% 8.76/8.95    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 8.76/8.95  thf('37', plain,
% 8.76/8.95      (![X16 : $i, X17 : $i]:
% 8.76/8.95         ((k3_xboole_0 @ X16 @ (k2_xboole_0 @ X16 @ X17)) = (X16))),
% 8.76/8.95      inference('cnf', [status(esa)], [t21_xboole_1])).
% 8.76/8.95  thf('38', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 8.76/8.95      inference('sup+', [status(thm)], ['36', '37'])).
% 8.76/8.95  thf('39', plain,
% 8.76/8.95      (![X28 : $i, X29 : $i, X30 : $i]:
% 8.76/8.95         ((k3_xboole_0 @ X28 @ (k4_xboole_0 @ X29 @ X30))
% 8.76/8.95           = (k4_xboole_0 @ (k3_xboole_0 @ X28 @ X29) @ X30))),
% 8.76/8.95      inference('cnf', [status(esa)], [t49_xboole_1])).
% 8.76/8.95  thf('40', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]:
% 8.76/8.95         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 8.76/8.95           = (k4_xboole_0 @ X0 @ X1))),
% 8.76/8.95      inference('sup+', [status(thm)], ['38', '39'])).
% 8.76/8.95  thf('41', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]:
% 8.76/8.95         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 8.76/8.95           = (k4_xboole_0 @ X1 @ X0))),
% 8.76/8.95      inference('demod', [status(thm)], ['35', '40'])).
% 8.76/8.95  thf('42', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]:
% 8.76/8.95         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 8.76/8.95           = (k4_xboole_0 @ X0 @ X1))),
% 8.76/8.95      inference('sup+', [status(thm)], ['32', '41'])).
% 8.76/8.95  thf('43', plain,
% 8.76/8.95      (![X4 : $i, X5 : $i]:
% 8.76/8.95         ((k5_xboole_0 @ X4 @ X5)
% 8.76/8.95           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 8.76/8.95      inference('cnf', [status(esa)], [d6_xboole_0])).
% 8.76/8.95  thf('44', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]:
% 8.76/8.95         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 8.76/8.95           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 8.76/8.95              (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X1)))),
% 8.76/8.95      inference('sup+', [status(thm)], ['42', '43'])).
% 8.76/8.95  thf('45', plain,
% 8.76/8.95      (![X28 : $i, X29 : $i, X30 : $i]:
% 8.76/8.95         ((k3_xboole_0 @ X28 @ (k4_xboole_0 @ X29 @ X30))
% 8.76/8.95           = (k4_xboole_0 @ (k3_xboole_0 @ X28 @ X29) @ X30))),
% 8.76/8.95      inference('cnf', [status(esa)], [t49_xboole_1])).
% 8.76/8.95  thf('46', plain, (![X15 : $i]: ((k2_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 8.76/8.95      inference('cnf', [status(esa)], [t1_boole])).
% 8.76/8.95  thf('47', plain,
% 8.76/8.95      (![X24 : $i, X25 : $i]:
% 8.76/8.95         ((k4_xboole_0 @ X24 @ (k2_xboole_0 @ X24 @ X25)) = (k1_xboole_0))),
% 8.76/8.95      inference('cnf', [status(esa)], [t46_xboole_1])).
% 8.76/8.95  thf('48', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 8.76/8.95      inference('sup+', [status(thm)], ['46', '47'])).
% 8.76/8.95  thf('49', plain,
% 8.76/8.95      (![X18 : $i]: ((k3_xboole_0 @ X18 @ k1_xboole_0) = (k1_xboole_0))),
% 8.76/8.95      inference('cnf', [status(esa)], [t2_boole])).
% 8.76/8.95  thf('50', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 8.76/8.95      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 8.76/8.95  thf('51', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 8.76/8.95      inference('sup+', [status(thm)], ['14', '15'])).
% 8.76/8.95  thf('52', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]:
% 8.76/8.95         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 8.76/8.95           = (k4_xboole_0 @ X1 @ X0))),
% 8.76/8.95      inference('demod', [status(thm)], ['44', '45', '48', '49', '50', '51'])).
% 8.76/8.95  thf('53', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]:
% 8.76/8.95         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X1)) @ 
% 8.76/8.95           k1_xboole_0)
% 8.76/8.95           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X1)) @ X0))),
% 8.76/8.95      inference('sup+', [status(thm)], ['31', '52'])).
% 8.76/8.95  thf('54', plain,
% 8.76/8.95      (![X18 : $i]: ((k3_xboole_0 @ X18 @ k1_xboole_0) = (k1_xboole_0))),
% 8.76/8.95      inference('cnf', [status(esa)], [t2_boole])).
% 8.76/8.95  thf('55', plain,
% 8.76/8.95      (![X37 : $i, X38 : $i]:
% 8.76/8.95         ((k2_xboole_0 @ X37 @ X38)
% 8.76/8.95           = (k2_xboole_0 @ (k5_xboole_0 @ X37 @ X38) @ 
% 8.76/8.95              (k3_xboole_0 @ X37 @ X38)))),
% 8.76/8.95      inference('cnf', [status(esa)], [t93_xboole_1])).
% 8.76/8.95  thf('56', plain,
% 8.76/8.95      (![X0 : $i]:
% 8.76/8.95         ((k2_xboole_0 @ X0 @ k1_xboole_0)
% 8.76/8.95           = (k2_xboole_0 @ (k5_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 8.76/8.95      inference('sup+', [status(thm)], ['54', '55'])).
% 8.76/8.95  thf('57', plain, (![X15 : $i]: ((k2_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 8.76/8.95      inference('cnf', [status(esa)], [t1_boole])).
% 8.76/8.95  thf('58', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 8.76/8.95      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 8.76/8.95  thf('59', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 8.76/8.95      inference('sup+', [status(thm)], ['14', '15'])).
% 8.76/8.95  thf('60', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 8.76/8.95      inference('demod', [status(thm)], ['56', '57', '58', '59'])).
% 8.76/8.95  thf('61', plain,
% 8.76/8.95      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 8.76/8.95      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 8.76/8.95  thf('62', plain,
% 8.76/8.95      (![X28 : $i, X29 : $i, X30 : $i]:
% 8.76/8.95         ((k3_xboole_0 @ X28 @ (k4_xboole_0 @ X29 @ X30))
% 8.76/8.95           = (k4_xboole_0 @ (k3_xboole_0 @ X28 @ X29) @ X30))),
% 8.76/8.95      inference('cnf', [status(esa)], [t49_xboole_1])).
% 8.76/8.95  thf('63', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.76/8.95         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 8.76/8.95           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 8.76/8.95      inference('sup+', [status(thm)], ['61', '62'])).
% 8.76/8.95  thf('64', plain,
% 8.76/8.95      (![X4 : $i, X5 : $i]:
% 8.76/8.95         ((k5_xboole_0 @ X4 @ X5)
% 8.76/8.95           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 8.76/8.95      inference('cnf', [status(esa)], [d6_xboole_0])).
% 8.76/8.95  thf('65', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 8.76/8.95      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 8.76/8.95  thf('66', plain,
% 8.76/8.95      (![X16 : $i, X17 : $i]:
% 8.76/8.95         ((k3_xboole_0 @ X16 @ (k2_xboole_0 @ X16 @ X17)) = (X16))),
% 8.76/8.95      inference('cnf', [status(esa)], [t21_xboole_1])).
% 8.76/8.95  thf('67', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]:
% 8.76/8.95         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 8.76/8.95      inference('sup+', [status(thm)], ['65', '66'])).
% 8.76/8.95  thf('68', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]:
% 8.76/8.95         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0))
% 8.76/8.95           = (k4_xboole_0 @ X0 @ X1))),
% 8.76/8.95      inference('sup+', [status(thm)], ['64', '67'])).
% 8.76/8.95  thf('69', plain,
% 8.76/8.95      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 8.76/8.95      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 8.76/8.95  thf('70', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]:
% 8.76/8.95         ((k3_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 8.76/8.95           = (k4_xboole_0 @ X0 @ X1))),
% 8.76/8.95      inference('demod', [status(thm)], ['68', '69'])).
% 8.76/8.95  thf('71', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]:
% 8.76/8.95         ((k3_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X1))
% 8.76/8.95           = (k4_xboole_0 @ X1 @ X0))),
% 8.76/8.95      inference('demod', [status(thm)], ['53', '60', '63', '70'])).
% 8.76/8.95  thf('72', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]:
% 8.76/8.95         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 8.76/8.95           = (k4_xboole_0 @ X1 @ X0))),
% 8.76/8.95      inference('demod', [status(thm)], ['35', '40'])).
% 8.76/8.95  thf('73', plain,
% 8.76/8.95      (![X4 : $i, X5 : $i]:
% 8.76/8.95         ((k5_xboole_0 @ X4 @ X5)
% 8.76/8.95           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 8.76/8.95      inference('cnf', [status(esa)], [d6_xboole_0])).
% 8.76/8.95  thf('74', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]:
% 8.76/8.95         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 8.76/8.95           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 8.76/8.95              (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)))),
% 8.76/8.95      inference('sup+', [status(thm)], ['72', '73'])).
% 8.76/8.95  thf('75', plain,
% 8.76/8.95      (![X28 : $i, X29 : $i, X30 : $i]:
% 8.76/8.95         ((k3_xboole_0 @ X28 @ (k4_xboole_0 @ X29 @ X30))
% 8.76/8.95           = (k4_xboole_0 @ (k3_xboole_0 @ X28 @ X29) @ X30))),
% 8.76/8.95      inference('cnf', [status(esa)], [t49_xboole_1])).
% 8.76/8.95  thf(t17_xboole_1, axiom,
% 8.76/8.95    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 8.76/8.95  thf('76', plain,
% 8.76/8.95      (![X13 : $i, X14 : $i]: (r1_tarski @ (k3_xboole_0 @ X13 @ X14) @ X13)),
% 8.76/8.95      inference('cnf', [status(esa)], [t17_xboole_1])).
% 8.76/8.95  thf(t12_xboole_1, axiom,
% 8.76/8.95    (![A:$i,B:$i]:
% 8.76/8.95     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 8.76/8.95  thf('77', plain,
% 8.76/8.95      (![X8 : $i, X9 : $i]:
% 8.76/8.95         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 8.76/8.95      inference('cnf', [status(esa)], [t12_xboole_1])).
% 8.76/8.95  thf('78', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]:
% 8.76/8.95         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 8.76/8.95      inference('sup-', [status(thm)], ['76', '77'])).
% 8.76/8.95  thf('79', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 8.76/8.95      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 8.76/8.95  thf('80', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]:
% 8.76/8.95         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) = (X0))),
% 8.76/8.95      inference('demod', [status(thm)], ['78', '79'])).
% 8.76/8.95  thf('81', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 8.76/8.95      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 8.76/8.95  thf('82', plain,
% 8.76/8.95      (![X24 : $i, X25 : $i]:
% 8.76/8.95         ((k4_xboole_0 @ X24 @ (k2_xboole_0 @ X24 @ X25)) = (k1_xboole_0))),
% 8.76/8.95      inference('cnf', [status(esa)], [t46_xboole_1])).
% 8.76/8.95  thf('83', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]:
% 8.76/8.95         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 8.76/8.95      inference('sup+', [status(thm)], ['81', '82'])).
% 8.76/8.95  thf('84', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]:
% 8.76/8.95         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 8.76/8.95      inference('sup+', [status(thm)], ['80', '83'])).
% 8.76/8.95  thf('85', plain,
% 8.76/8.95      (![X28 : $i, X29 : $i, X30 : $i]:
% 8.76/8.95         ((k3_xboole_0 @ X28 @ (k4_xboole_0 @ X29 @ X30))
% 8.76/8.95           = (k4_xboole_0 @ (k3_xboole_0 @ X28 @ X29) @ X30))),
% 8.76/8.95      inference('cnf', [status(esa)], [t49_xboole_1])).
% 8.76/8.95  thf('86', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]:
% 8.76/8.95         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 8.76/8.95      inference('demod', [status(thm)], ['84', '85'])).
% 8.76/8.95  thf('87', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 8.76/8.95      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 8.76/8.95  thf('88', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 8.76/8.95      inference('sup+', [status(thm)], ['14', '15'])).
% 8.76/8.95  thf('89', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]:
% 8.76/8.95         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 8.76/8.95           = (k4_xboole_0 @ X1 @ X0))),
% 8.76/8.95      inference('demod', [status(thm)], ['74', '75', '86', '87', '88'])).
% 8.76/8.95  thf('90', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]:
% 8.76/8.95         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 8.76/8.95           = (k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X1)))),
% 8.76/8.95      inference('sup+', [status(thm)], ['71', '89'])).
% 8.76/8.95  thf('91', plain,
% 8.76/8.95      (![X26 : $i, X27 : $i]:
% 8.76/8.95         ((k4_xboole_0 @ X26 @ (k4_xboole_0 @ X26 @ X27))
% 8.76/8.95           = (k3_xboole_0 @ X26 @ X27))),
% 8.76/8.95      inference('cnf', [status(esa)], [t48_xboole_1])).
% 8.76/8.95  thf('92', plain,
% 8.76/8.95      (![X4 : $i, X5 : $i]:
% 8.76/8.95         ((k5_xboole_0 @ X4 @ X5)
% 8.76/8.95           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 8.76/8.95      inference('cnf', [status(esa)], [d6_xboole_0])).
% 8.76/8.95  thf('93', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]:
% 8.76/8.95         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 8.76/8.95           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 8.76/8.95              (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)))),
% 8.76/8.95      inference('sup+', [status(thm)], ['91', '92'])).
% 8.76/8.95  thf(t41_xboole_1, axiom,
% 8.76/8.95    (![A:$i,B:$i,C:$i]:
% 8.76/8.95     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 8.76/8.95       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 8.76/8.95  thf('94', plain,
% 8.76/8.95      (![X21 : $i, X22 : $i, X23 : $i]:
% 8.76/8.95         ((k4_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ X23)
% 8.76/8.95           = (k4_xboole_0 @ X21 @ (k2_xboole_0 @ X22 @ X23)))),
% 8.76/8.95      inference('cnf', [status(esa)], [t41_xboole_1])).
% 8.76/8.95  thf('95', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]:
% 8.76/8.95         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 8.76/8.95      inference('sup+', [status(thm)], ['81', '82'])).
% 8.76/8.95  thf('96', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 8.76/8.95      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 8.76/8.95  thf('97', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 8.76/8.95      inference('sup+', [status(thm)], ['14', '15'])).
% 8.76/8.95  thf('98', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]:
% 8.76/8.95         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 8.76/8.95           = (k3_xboole_0 @ X1 @ X0))),
% 8.76/8.95      inference('demod', [status(thm)], ['93', '94', '95', '96', '97'])).
% 8.76/8.95  thf('99', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]:
% 8.76/8.95         ((k3_xboole_0 @ X1 @ X0)
% 8.76/8.95           = (k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X1)))),
% 8.76/8.95      inference('demod', [status(thm)], ['90', '98'])).
% 8.76/8.95  thf('100', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]:
% 8.76/8.95         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 8.76/8.95           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)))),
% 8.76/8.95      inference('demod', [status(thm)], ['20', '99'])).
% 8.76/8.95  thf('101', plain,
% 8.76/8.95      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 8.76/8.95      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 8.76/8.95  thf('102', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]:
% 8.76/8.95         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) = (X0))),
% 8.76/8.95      inference('demod', [status(thm)], ['78', '79'])).
% 8.76/8.95  thf('103', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]:
% 8.76/8.95         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 8.76/8.95      inference('sup+', [status(thm)], ['101', '102'])).
% 8.76/8.95  thf('104', plain,
% 8.76/8.95      (![X19 : $i, X20 : $i]:
% 8.76/8.95         ((k4_xboole_0 @ (k2_xboole_0 @ X19 @ X20) @ X20)
% 8.76/8.95           = (k4_xboole_0 @ X19 @ X20))),
% 8.76/8.95      inference('cnf', [status(esa)], [t40_xboole_1])).
% 8.76/8.95  thf('105', plain,
% 8.76/8.95      (![X26 : $i, X27 : $i]:
% 8.76/8.95         ((k4_xboole_0 @ X26 @ (k4_xboole_0 @ X26 @ X27))
% 8.76/8.95           = (k3_xboole_0 @ X26 @ X27))),
% 8.76/8.95      inference('cnf', [status(esa)], [t48_xboole_1])).
% 8.76/8.95  thf('106', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]:
% 8.76/8.95         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 8.76/8.95           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 8.76/8.95      inference('sup+', [status(thm)], ['104', '105'])).
% 8.76/8.95  thf('107', plain,
% 8.76/8.95      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 8.76/8.95      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 8.76/8.95  thf('108', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]:
% 8.76/8.95         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 8.76/8.95           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 8.76/8.95      inference('demod', [status(thm)], ['106', '107'])).
% 8.76/8.95  thf('109', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]:
% 8.76/8.95         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 8.76/8.95      inference('sup+', [status(thm)], ['65', '66'])).
% 8.76/8.95  thf('110', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]:
% 8.76/8.95         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 8.76/8.95           = (X0))),
% 8.76/8.95      inference('demod', [status(thm)], ['108', '109'])).
% 8.76/8.95  thf('111', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]:
% 8.76/8.95         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 8.76/8.95           = (k3_xboole_0 @ X1 @ X0))),
% 8.76/8.95      inference('sup+', [status(thm)], ['103', '110'])).
% 8.76/8.95  thf('112', plain,
% 8.76/8.95      (![X26 : $i, X27 : $i]:
% 8.76/8.95         ((k4_xboole_0 @ X26 @ (k4_xboole_0 @ X26 @ X27))
% 8.76/8.95           = (k3_xboole_0 @ X26 @ X27))),
% 8.76/8.95      inference('cnf', [status(esa)], [t48_xboole_1])).
% 8.76/8.95  thf('113', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]:
% 8.76/8.95         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 8.76/8.95           = (k3_xboole_0 @ X1 @ X0))),
% 8.76/8.95      inference('demod', [status(thm)], ['111', '112'])).
% 8.76/8.95  thf('114', plain,
% 8.76/8.95      (![X0 : $i, X1 : $i]:
% 8.76/8.95         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 8.76/8.95           = (k3_xboole_0 @ X0 @ X1))),
% 8.76/8.95      inference('demod', [status(thm)], ['100', '113'])).
% 8.76/8.95  thf('115', plain,
% 8.76/8.95      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 8.76/8.95      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 8.76/8.95  thf('116', plain,
% 8.76/8.95      (((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))),
% 8.76/8.95      inference('demod', [status(thm)], ['0', '114', '115'])).
% 8.76/8.95  thf('117', plain, ($false), inference('simplify', [status(thm)], ['116'])).
% 8.76/8.95  
% 8.76/8.95  % SZS output end Refutation
% 8.76/8.95  
% 8.76/8.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

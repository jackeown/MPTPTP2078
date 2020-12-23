%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7h42QZge51

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:08 EST 2020

% Result     : Theorem 35.53s
% Output     : Refutation 35.53s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 181 expanded)
%              Number of leaves         :   21 (  65 expanded)
%              Depth                    :   24
%              Number of atoms          :  835 (1487 expanded)
%              Number of equality atoms :   90 ( 168 expanded)
%              Maximal formula depth    :   10 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t98_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ A @ B )
        = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t98_xboole_1])).

thf('0',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X18: $i,X20: $i] :
      ( ( r1_xboole_0 @ X18 @ X20 )
      | ( ( k4_xboole_0 @ X18 @ X20 )
       != X18 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != ( k4_xboole_0 @ X2 @ X1 ) )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
       != ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t87_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k2_xboole_0 @ ( k4_xboole_0 @ C @ A ) @ B )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ C @ B ) @ A ) ) ) )).

thf('8',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_xboole_0 @ X21 @ X22 )
      | ( ( k2_xboole_0 @ ( k4_xboole_0 @ X23 @ X21 ) @ X22 )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ X23 @ X22 ) @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t87_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','9'])).

thf('11',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != ( k4_xboole_0 @ X2 @ X1 ) )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
       != ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['15','23'])).

thf('25',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k4_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('32',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('37',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf('40',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('41',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('43',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ X27 @ X28 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X27 @ X28 ) @ ( k3_xboole_0 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('44',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ X26 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('45',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ X27 @ X28 )
      = ( k5_xboole_0 @ X27 @ ( k5_xboole_0 @ X28 @ ( k3_xboole_0 @ X27 @ X28 ) ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('47',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) ) @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('57',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X9 @ X10 ) @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','60'])).

thf('62',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('63',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ X26 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) )
      = X2 ) ),
    inference('sup+',[status(thm)],['11','67'])).

thf('69',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) )
      = X2 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) )
      = X2 ) ),
    inference('sup+',[status(thm)],['10','70'])).

thf('72',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = X2 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ X27 @ X28 )
      = ( k5_xboole_0 @ X27 @ ( k5_xboole_0 @ X28 @ ( k3_xboole_0 @ X27 @ X28 ) ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','77'])).

thf('79',plain,(
    $false ),
    inference(simplify,[status(thm)],['78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7h42QZge51
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:39:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 35.53/35.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 35.53/35.71  % Solved by: fo/fo7.sh
% 35.53/35.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 35.53/35.71  % done 23548 iterations in 35.234s
% 35.53/35.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 35.53/35.71  % SZS output start Refutation
% 35.53/35.71  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 35.53/35.71  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 35.53/35.71  thf(sk_B_type, type, sk_B: $i).
% 35.53/35.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 35.53/35.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 35.53/35.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 35.53/35.71  thf(sk_A_type, type, sk_A: $i).
% 35.53/35.71  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 35.53/35.71  thf(t98_xboole_1, conjecture,
% 35.53/35.71    (![A:$i,B:$i]:
% 35.53/35.71     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 35.53/35.71  thf(zf_stmt_0, negated_conjecture,
% 35.53/35.71    (~( ![A:$i,B:$i]:
% 35.53/35.71        ( ( k2_xboole_0 @ A @ B ) =
% 35.53/35.71          ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )),
% 35.53/35.71    inference('cnf.neg', [status(esa)], [t98_xboole_1])).
% 35.53/35.71  thf('0', plain,
% 35.53/35.71      (((k2_xboole_0 @ sk_A @ sk_B)
% 35.53/35.71         != (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_A)))),
% 35.53/35.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.53/35.71  thf(idempotence_k2_xboole_0, axiom,
% 35.53/35.71    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 35.53/35.71  thf('1', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 35.53/35.71      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 35.53/35.71  thf('2', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 35.53/35.71      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 35.53/35.71  thf(t41_xboole_1, axiom,
% 35.53/35.71    (![A:$i,B:$i,C:$i]:
% 35.53/35.71     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 35.53/35.71       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 35.53/35.71  thf('3', plain,
% 35.53/35.71      (![X11 : $i, X12 : $i, X13 : $i]:
% 35.53/35.71         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 35.53/35.71           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 35.53/35.71      inference('cnf', [status(esa)], [t41_xboole_1])).
% 35.53/35.71  thf(t83_xboole_1, axiom,
% 35.53/35.71    (![A:$i,B:$i]:
% 35.53/35.71     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 35.53/35.71  thf('4', plain,
% 35.53/35.71      (![X18 : $i, X20 : $i]:
% 35.53/35.71         ((r1_xboole_0 @ X18 @ X20) | ((k4_xboole_0 @ X18 @ X20) != (X18)))),
% 35.53/35.71      inference('cnf', [status(esa)], [t83_xboole_1])).
% 35.53/35.71  thf('5', plain,
% 35.53/35.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.53/35.71         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 35.53/35.71            != (k4_xboole_0 @ X2 @ X1))
% 35.53/35.71          | (r1_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 35.53/35.71      inference('sup-', [status(thm)], ['3', '4'])).
% 35.53/35.71  thf('6', plain,
% 35.53/35.71      (![X0 : $i, X1 : $i]:
% 35.53/35.71         (((k4_xboole_0 @ X1 @ X0) != (k4_xboole_0 @ X1 @ X0))
% 35.53/35.71          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 35.53/35.71      inference('sup-', [status(thm)], ['2', '5'])).
% 35.53/35.71  thf('7', plain,
% 35.53/35.71      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 35.53/35.71      inference('simplify', [status(thm)], ['6'])).
% 35.53/35.71  thf(t87_xboole_1, axiom,
% 35.53/35.71    (![A:$i,B:$i,C:$i]:
% 35.53/35.71     ( ( r1_xboole_0 @ A @ B ) =>
% 35.53/35.71       ( ( k2_xboole_0 @ ( k4_xboole_0 @ C @ A ) @ B ) =
% 35.53/35.71         ( k4_xboole_0 @ ( k2_xboole_0 @ C @ B ) @ A ) ) ))).
% 35.53/35.71  thf('8', plain,
% 35.53/35.71      (![X21 : $i, X22 : $i, X23 : $i]:
% 35.53/35.71         (~ (r1_xboole_0 @ X21 @ X22)
% 35.53/35.71          | ((k2_xboole_0 @ (k4_xboole_0 @ X23 @ X21) @ X22)
% 35.53/35.71              = (k4_xboole_0 @ (k2_xboole_0 @ X23 @ X22) @ X21)))),
% 35.53/35.71      inference('cnf', [status(esa)], [t87_xboole_1])).
% 35.53/35.71  thf('9', plain,
% 35.53/35.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.53/35.71         ((k2_xboole_0 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0)
% 35.53/35.71           = (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 35.53/35.71      inference('sup-', [status(thm)], ['7', '8'])).
% 35.53/35.71  thf('10', plain,
% 35.53/35.71      (![X0 : $i, X1 : $i]:
% 35.53/35.71         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ X0)
% 35.53/35.71           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 35.53/35.71      inference('sup+', [status(thm)], ['1', '9'])).
% 35.53/35.71  thf('11', plain,
% 35.53/35.71      (![X11 : $i, X12 : $i, X13 : $i]:
% 35.53/35.71         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 35.53/35.71           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 35.53/35.71      inference('cnf', [status(esa)], [t41_xboole_1])).
% 35.53/35.71  thf(t3_boole, axiom,
% 35.53/35.71    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 35.53/35.71  thf('12', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 35.53/35.71      inference('cnf', [status(esa)], [t3_boole])).
% 35.53/35.71  thf(t48_xboole_1, axiom,
% 35.53/35.71    (![A:$i,B:$i]:
% 35.53/35.71     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 35.53/35.71  thf('13', plain,
% 35.53/35.71      (![X14 : $i, X15 : $i]:
% 35.53/35.71         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 35.53/35.71           = (k3_xboole_0 @ X14 @ X15))),
% 35.53/35.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 35.53/35.71  thf('14', plain,
% 35.53/35.71      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 35.53/35.71      inference('sup+', [status(thm)], ['12', '13'])).
% 35.53/35.71  thf('15', plain,
% 35.53/35.71      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 35.53/35.71      inference('sup+', [status(thm)], ['12', '13'])).
% 35.53/35.71  thf('16', plain,
% 35.53/35.71      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 35.53/35.71      inference('sup+', [status(thm)], ['12', '13'])).
% 35.53/35.71  thf(t39_xboole_1, axiom,
% 35.53/35.71    (![A:$i,B:$i]:
% 35.53/35.71     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 35.53/35.71  thf('17', plain,
% 35.53/35.71      (![X6 : $i, X7 : $i]:
% 35.53/35.71         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 35.53/35.71           = (k2_xboole_0 @ X6 @ X7))),
% 35.53/35.71      inference('cnf', [status(esa)], [t39_xboole_1])).
% 35.53/35.71  thf('18', plain,
% 35.53/35.71      (![X0 : $i]:
% 35.53/35.71         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0))
% 35.53/35.71           = (k2_xboole_0 @ X0 @ X0))),
% 35.53/35.71      inference('sup+', [status(thm)], ['16', '17'])).
% 35.53/35.71  thf('19', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 35.53/35.71      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 35.53/35.71  thf('20', plain,
% 35.53/35.71      (![X0 : $i]:
% 35.53/35.71         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 35.53/35.71      inference('demod', [status(thm)], ['18', '19'])).
% 35.53/35.71  thf('21', plain,
% 35.53/35.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.53/35.71         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 35.53/35.71            != (k4_xboole_0 @ X2 @ X1))
% 35.53/35.71          | (r1_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 35.53/35.71      inference('sup-', [status(thm)], ['3', '4'])).
% 35.53/35.71  thf('22', plain,
% 35.53/35.71      (![X0 : $i, X1 : $i]:
% 35.53/35.71         (((k4_xboole_0 @ X1 @ X0) != (k4_xboole_0 @ X1 @ X0))
% 35.53/35.71          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 35.53/35.71             (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 35.53/35.71      inference('sup-', [status(thm)], ['20', '21'])).
% 35.53/35.71  thf('23', plain,
% 35.53/35.71      (![X0 : $i, X1 : $i]:
% 35.53/35.71         (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 35.53/35.71          (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 35.53/35.71      inference('simplify', [status(thm)], ['22'])).
% 35.53/35.71  thf('24', plain,
% 35.53/35.71      (![X0 : $i]:
% 35.53/35.71         (r1_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ 
% 35.53/35.71          (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 35.53/35.71      inference('sup+', [status(thm)], ['15', '23'])).
% 35.53/35.71  thf('25', plain,
% 35.53/35.71      (![X18 : $i, X19 : $i]:
% 35.53/35.71         (((k4_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_xboole_0 @ X18 @ X19))),
% 35.53/35.71      inference('cnf', [status(esa)], [t83_xboole_1])).
% 35.53/35.71  thf('26', plain,
% 35.53/35.71      (![X0 : $i]:
% 35.53/35.71         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ 
% 35.53/35.71           (k3_xboole_0 @ X0 @ k1_xboole_0)) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 35.53/35.71      inference('sup-', [status(thm)], ['24', '25'])).
% 35.53/35.71  thf('27', plain,
% 35.53/35.71      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 35.53/35.71      inference('sup+', [status(thm)], ['12', '13'])).
% 35.53/35.71  thf('28', plain,
% 35.53/35.71      (![X0 : $i]:
% 35.53/35.71         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 35.53/35.71           = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 35.53/35.71      inference('demod', [status(thm)], ['26', '27'])).
% 35.53/35.71  thf('29', plain,
% 35.53/35.71      (![X0 : $i]:
% 35.53/35.71         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ k1_xboole_0)
% 35.53/35.71           = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 35.53/35.71      inference('sup+', [status(thm)], ['14', '28'])).
% 35.53/35.71  thf('30', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 35.53/35.71      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 35.53/35.71  thf('31', plain,
% 35.53/35.71      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 35.53/35.71      inference('sup+', [status(thm)], ['12', '13'])).
% 35.53/35.71  thf('32', plain,
% 35.53/35.71      (![X11 : $i, X12 : $i, X13 : $i]:
% 35.53/35.71         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 35.53/35.71           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 35.53/35.71      inference('cnf', [status(esa)], [t41_xboole_1])).
% 35.53/35.71  thf('33', plain,
% 35.53/35.71      (![X0 : $i, X1 : $i]:
% 35.53/35.71         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X1)
% 35.53/35.71           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 35.53/35.71      inference('sup+', [status(thm)], ['31', '32'])).
% 35.53/35.71  thf('34', plain,
% 35.53/35.71      (![X0 : $i]:
% 35.53/35.71         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X0)
% 35.53/35.71           = (k4_xboole_0 @ X0 @ X0))),
% 35.53/35.71      inference('sup+', [status(thm)], ['30', '33'])).
% 35.53/35.71  thf('35', plain,
% 35.53/35.71      (![X0 : $i]:
% 35.53/35.71         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ 
% 35.53/35.71           (k4_xboole_0 @ X0 @ X0))
% 35.53/35.71           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ (k4_xboole_0 @ X0 @ X0)))),
% 35.53/35.71      inference('sup+', [status(thm)], ['29', '34'])).
% 35.53/35.71  thf('36', plain,
% 35.53/35.71      (![X11 : $i, X12 : $i, X13 : $i]:
% 35.53/35.71         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 35.53/35.71           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 35.53/35.71      inference('cnf', [status(esa)], [t41_xboole_1])).
% 35.53/35.71  thf('37', plain,
% 35.53/35.71      (![X6 : $i, X7 : $i]:
% 35.53/35.71         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 35.53/35.71           = (k2_xboole_0 @ X6 @ X7))),
% 35.53/35.71      inference('cnf', [status(esa)], [t39_xboole_1])).
% 35.53/35.71  thf('38', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 35.53/35.71      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 35.53/35.71  thf('39', plain,
% 35.53/35.71      (![X0 : $i]:
% 35.53/35.71         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ 
% 35.53/35.71           (k4_xboole_0 @ X0 @ X0)) = (k4_xboole_0 @ X0 @ X0))),
% 35.53/35.71      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 35.53/35.71  thf('40', plain,
% 35.53/35.71      (![X14 : $i, X15 : $i]:
% 35.53/35.71         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 35.53/35.71           = (k3_xboole_0 @ X14 @ X15))),
% 35.53/35.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 35.53/35.71  thf(t4_boole, axiom,
% 35.53/35.71    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 35.53/35.71  thf('41', plain,
% 35.53/35.71      (![X16 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X16) = (k1_xboole_0))),
% 35.53/35.71      inference('cnf', [status(esa)], [t4_boole])).
% 35.53/35.71  thf('42', plain,
% 35.53/35.71      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 35.53/35.71      inference('sup+', [status(thm)], ['40', '41'])).
% 35.53/35.71  thf(t94_xboole_1, axiom,
% 35.53/35.71    (![A:$i,B:$i]:
% 35.53/35.71     ( ( k2_xboole_0 @ A @ B ) =
% 35.53/35.71       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 35.53/35.71  thf('43', plain,
% 35.53/35.71      (![X27 : $i, X28 : $i]:
% 35.53/35.71         ((k2_xboole_0 @ X27 @ X28)
% 35.53/35.71           = (k5_xboole_0 @ (k5_xboole_0 @ X27 @ X28) @ 
% 35.53/35.71              (k3_xboole_0 @ X27 @ X28)))),
% 35.53/35.71      inference('cnf', [status(esa)], [t94_xboole_1])).
% 35.53/35.71  thf(t91_xboole_1, axiom,
% 35.53/35.71    (![A:$i,B:$i,C:$i]:
% 35.53/35.71     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 35.53/35.71       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 35.53/35.71  thf('44', plain,
% 35.53/35.71      (![X24 : $i, X25 : $i, X26 : $i]:
% 35.53/35.71         ((k5_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ X26)
% 35.53/35.71           = (k5_xboole_0 @ X24 @ (k5_xboole_0 @ X25 @ X26)))),
% 35.53/35.71      inference('cnf', [status(esa)], [t91_xboole_1])).
% 35.53/35.71  thf('45', plain,
% 35.53/35.71      (![X27 : $i, X28 : $i]:
% 35.53/35.71         ((k2_xboole_0 @ X27 @ X28)
% 35.53/35.71           = (k5_xboole_0 @ X27 @ 
% 35.53/35.71              (k5_xboole_0 @ X28 @ (k3_xboole_0 @ X27 @ X28))))),
% 35.53/35.71      inference('demod', [status(thm)], ['43', '44'])).
% 35.53/35.71  thf('46', plain,
% 35.53/35.71      (![X0 : $i]:
% 35.53/35.71         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 35.53/35.71           = (k5_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)))),
% 35.53/35.71      inference('sup+', [status(thm)], ['42', '45'])).
% 35.53/35.71  thf(t5_boole, axiom,
% 35.53/35.71    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 35.53/35.71  thf('47', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 35.53/35.71      inference('cnf', [status(esa)], [t5_boole])).
% 35.53/35.71  thf('48', plain,
% 35.53/35.71      (![X0 : $i]:
% 35.53/35.71         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 35.53/35.71      inference('demod', [status(thm)], ['46', '47'])).
% 35.53/35.71  thf('49', plain,
% 35.53/35.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.53/35.71         ((k2_xboole_0 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0)
% 35.53/35.71           = (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 35.53/35.71      inference('sup-', [status(thm)], ['7', '8'])).
% 35.53/35.71  thf('50', plain,
% 35.53/35.71      (![X0 : $i, X1 : $i]:
% 35.53/35.71         ((k2_xboole_0 @ 
% 35.53/35.71           (k4_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ X0)) @ X0)
% 35.53/35.71           = (k4_xboole_0 @ (k5_xboole_0 @ k1_xboole_0 @ X0) @ 
% 35.53/35.71              (k4_xboole_0 @ X1 @ X0)))),
% 35.53/35.71      inference('sup+', [status(thm)], ['48', '49'])).
% 35.53/35.71  thf('51', plain,
% 35.53/35.71      (![X16 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X16) = (k1_xboole_0))),
% 35.53/35.71      inference('cnf', [status(esa)], [t4_boole])).
% 35.53/35.71  thf('52', plain,
% 35.53/35.71      (![X0 : $i, X1 : $i]:
% 35.53/35.71         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 35.53/35.71           = (k4_xboole_0 @ (k5_xboole_0 @ k1_xboole_0 @ X0) @ 
% 35.53/35.71              (k4_xboole_0 @ X1 @ X0)))),
% 35.53/35.71      inference('demod', [status(thm)], ['50', '51'])).
% 35.53/35.71  thf('53', plain,
% 35.53/35.71      (![X0 : $i]:
% 35.53/35.71         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 35.53/35.71      inference('demod', [status(thm)], ['46', '47'])).
% 35.53/35.71  thf('54', plain,
% 35.53/35.71      (![X0 : $i, X1 : $i]:
% 35.53/35.71         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 35.53/35.71           = (k4_xboole_0 @ (k5_xboole_0 @ k1_xboole_0 @ X0) @ 
% 35.53/35.71              (k4_xboole_0 @ X1 @ X0)))),
% 35.53/35.71      inference('demod', [status(thm)], ['52', '53'])).
% 35.53/35.71  thf('55', plain,
% 35.53/35.71      (![X0 : $i]:
% 35.53/35.71         ((k5_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ X0))
% 35.53/35.71           = (k4_xboole_0 @ 
% 35.53/35.71              (k5_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ X0)) @ 
% 35.53/35.71              (k4_xboole_0 @ X0 @ X0)))),
% 35.53/35.71      inference('sup+', [status(thm)], ['39', '54'])).
% 35.53/35.71  thf('56', plain,
% 35.53/35.71      (![X0 : $i]:
% 35.53/35.71         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 35.53/35.71      inference('demod', [status(thm)], ['46', '47'])).
% 35.53/35.71  thf(t40_xboole_1, axiom,
% 35.53/35.71    (![A:$i,B:$i]:
% 35.53/35.71     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 35.53/35.71  thf('57', plain,
% 35.53/35.71      (![X9 : $i, X10 : $i]:
% 35.53/35.71         ((k4_xboole_0 @ (k2_xboole_0 @ X9 @ X10) @ X10)
% 35.53/35.71           = (k4_xboole_0 @ X9 @ X10))),
% 35.53/35.71      inference('cnf', [status(esa)], [t40_xboole_1])).
% 35.53/35.71  thf('58', plain,
% 35.53/35.71      (![X0 : $i]:
% 35.53/35.71         ((k4_xboole_0 @ (k5_xboole_0 @ k1_xboole_0 @ X0) @ X0)
% 35.53/35.71           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 35.53/35.71      inference('sup+', [status(thm)], ['56', '57'])).
% 35.53/35.71  thf('59', plain,
% 35.53/35.71      (![X16 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X16) = (k1_xboole_0))),
% 35.53/35.71      inference('cnf', [status(esa)], [t4_boole])).
% 35.53/35.71  thf('60', plain,
% 35.53/35.71      (![X0 : $i]:
% 35.53/35.71         ((k4_xboole_0 @ (k5_xboole_0 @ k1_xboole_0 @ X0) @ X0) = (k1_xboole_0))),
% 35.53/35.71      inference('demod', [status(thm)], ['58', '59'])).
% 35.53/35.71  thf('61', plain,
% 35.53/35.71      (![X0 : $i]:
% 35.53/35.71         ((k5_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 35.53/35.71      inference('demod', [status(thm)], ['55', '60'])).
% 35.53/35.71  thf('62', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 35.53/35.71      inference('cnf', [status(esa)], [t5_boole])).
% 35.53/35.71  thf('63', plain,
% 35.53/35.71      (![X24 : $i, X25 : $i, X26 : $i]:
% 35.53/35.71         ((k5_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ X26)
% 35.53/35.71           = (k5_xboole_0 @ X24 @ (k5_xboole_0 @ X25 @ X26)))),
% 35.53/35.71      inference('cnf', [status(esa)], [t91_xboole_1])).
% 35.53/35.71  thf('64', plain,
% 35.53/35.71      (![X0 : $i, X1 : $i]:
% 35.53/35.71         ((k5_xboole_0 @ X0 @ X1)
% 35.53/35.71           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ X1)))),
% 35.53/35.71      inference('sup+', [status(thm)], ['62', '63'])).
% 35.53/35.71  thf('65', plain,
% 35.53/35.71      (![X0 : $i, X1 : $i]:
% 35.53/35.71         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 35.53/35.71           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 35.53/35.71      inference('sup+', [status(thm)], ['61', '64'])).
% 35.53/35.71  thf('66', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 35.53/35.71      inference('cnf', [status(esa)], [t5_boole])).
% 35.53/35.71  thf('67', plain,
% 35.53/35.71      (![X0 : $i, X1 : $i]:
% 35.53/35.71         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 35.53/35.71      inference('demod', [status(thm)], ['65', '66'])).
% 35.53/35.71  thf('68', plain,
% 35.53/35.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.53/35.71         ((k5_xboole_0 @ X2 @ 
% 35.53/35.71           (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))
% 35.53/35.71           = (X2))),
% 35.53/35.71      inference('sup+', [status(thm)], ['11', '67'])).
% 35.53/35.71  thf('69', plain,
% 35.53/35.71      (![X6 : $i, X7 : $i]:
% 35.53/35.71         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 35.53/35.71           = (k2_xboole_0 @ X6 @ X7))),
% 35.53/35.71      inference('cnf', [status(esa)], [t39_xboole_1])).
% 35.53/35.71  thf('70', plain,
% 35.53/35.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.53/35.71         ((k5_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))
% 35.53/35.71           = (X2))),
% 35.53/35.71      inference('demod', [status(thm)], ['68', '69'])).
% 35.53/35.71  thf('71', plain,
% 35.53/35.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.53/35.71         ((k5_xboole_0 @ X2 @ 
% 35.53/35.71           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))
% 35.53/35.71           = (X2))),
% 35.53/35.71      inference('sup+', [status(thm)], ['10', '70'])).
% 35.53/35.71  thf('72', plain,
% 35.53/35.71      (![X14 : $i, X15 : $i]:
% 35.53/35.71         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 35.53/35.71           = (k3_xboole_0 @ X14 @ X15))),
% 35.53/35.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 35.53/35.71  thf('73', plain,
% 35.53/35.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.53/35.71         ((k5_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 35.53/35.71           = (X2))),
% 35.53/35.71      inference('demod', [status(thm)], ['71', '72'])).
% 35.53/35.71  thf('74', plain,
% 35.53/35.71      (![X27 : $i, X28 : $i]:
% 35.53/35.71         ((k2_xboole_0 @ X27 @ X28)
% 35.53/35.71           = (k5_xboole_0 @ X27 @ 
% 35.53/35.71              (k5_xboole_0 @ X28 @ (k3_xboole_0 @ X27 @ X28))))),
% 35.53/35.71      inference('demod', [status(thm)], ['43', '44'])).
% 35.53/35.71  thf('75', plain,
% 35.53/35.71      (![X0 : $i, X1 : $i]:
% 35.53/35.71         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 35.53/35.71           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 35.53/35.71      inference('sup+', [status(thm)], ['73', '74'])).
% 35.53/35.71  thf('76', plain,
% 35.53/35.71      (![X6 : $i, X7 : $i]:
% 35.53/35.71         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 35.53/35.71           = (k2_xboole_0 @ X6 @ X7))),
% 35.53/35.71      inference('cnf', [status(esa)], [t39_xboole_1])).
% 35.53/35.71  thf('77', plain,
% 35.53/35.71      (![X0 : $i, X1 : $i]:
% 35.53/35.71         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 35.53/35.71           = (k2_xboole_0 @ X0 @ X1))),
% 35.53/35.71      inference('sup+', [status(thm)], ['75', '76'])).
% 35.53/35.71  thf('78', plain,
% 35.53/35.71      (((k2_xboole_0 @ sk_A @ sk_B) != (k2_xboole_0 @ sk_A @ sk_B))),
% 35.53/35.71      inference('demod', [status(thm)], ['0', '77'])).
% 35.53/35.71  thf('79', plain, ($false), inference('simplify', [status(thm)], ['78'])).
% 35.53/35.71  
% 35.53/35.71  % SZS output end Refutation
% 35.53/35.71  
% 35.53/35.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

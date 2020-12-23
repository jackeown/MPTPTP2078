%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hTuaS3cenl

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:13 EST 2020

% Result     : Theorem 9.17s
% Output     : Refutation 9.17s
% Verified   : 
% Statistics : Number of formulae       :  209 (5829 expanded)
%              Number of leaves         :   17 (1933 expanded)
%              Depth                    :   34
%              Number of atoms          : 2081 (59278 expanded)
%              Number of equality atoms :  183 (5366 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('5',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('12',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('17',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('20',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('21',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','23'])).

thf('25',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('29',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('30',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['26','38'])).

thf('40',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('41',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('42',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( r2_hidden @ X3 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(clc,[status(thm)],['39','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ X2 ) ) ),
    inference('sup-',[status(thm)],['7','45'])).

thf('47',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('48',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ ( k4_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf(l98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('50',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ X10 @ X11 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ X2 ) ) ),
    inference('sup-',[status(thm)],['7','45'])).

thf('53',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['53'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('55',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('56',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('57',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ ( k4_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('62',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) )
      = ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['60','65'])).

thf('67',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('68',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['66','71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(clc,[status(thm)],['39','43'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['54','78'])).

thf('80',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('91',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ X10 @ X11 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('94',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('99',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ ( k4_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('102',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('103',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['101','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['100','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['97','106'])).

thf('108',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ ( k4_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X1 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','75'])).

thf('111',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ ( k3_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('118',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ X10 @ X11 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['116','119'])).

thf('121',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['109','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['96','124'])).

thf('126',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ ( k3_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['95','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('130',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','33'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['135','136','137'])).

thf('139',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('140',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ X10 @ X11 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ X10 @ X11 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('144',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ X10 @ X11 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['142','143','144'])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['139','145'])).

thf('147',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('148',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['146','147','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['128','138','149'])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X1 ) ) ),
    inference(demod,[status(thm)],['92','150'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['53'])).

thf('153',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['53'])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ X1 ) ) ),
    inference(demod,[status(thm)],['151','159'])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['89','160'])).

thf('162',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( X3
      = ( k5_xboole_0 @ X3 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['51','162'])).

thf('164',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) @ ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X2 ) @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['46','163'])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X1 ) ) ),
    inference(demod,[status(thm)],['92','150'])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ X0 @ X0 ) ) @ X1 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ ( k4_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('169',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['101','104'])).

thf('171',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['167','168','169','170','171','172'])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','33'])).

thf('175',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['53'])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['123'])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('180',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['175','182'])).

thf('184',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['155','156'])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['123'])).

thf('186',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['164','183','186'])).

thf('188',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','187'])).

thf('189',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','188'])).

thf('190',plain,(
    $false ),
    inference(simplify,[status(thm)],['189'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hTuaS3cenl
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:59:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 9.17/9.39  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 9.17/9.39  % Solved by: fo/fo7.sh
% 9.17/9.39  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.17/9.39  % done 6201 iterations in 8.932s
% 9.17/9.39  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 9.17/9.39  % SZS output start Refutation
% 9.17/9.39  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 9.17/9.39  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 9.17/9.39  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 9.17/9.39  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 9.17/9.39  thf(sk_B_type, type, sk_B: $i).
% 9.17/9.39  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 9.17/9.39  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 9.17/9.39  thf(sk_A_type, type, sk_A: $i).
% 9.17/9.39  thf(t100_xboole_1, conjecture,
% 9.17/9.39    (![A:$i,B:$i]:
% 9.17/9.39     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 9.17/9.39  thf(zf_stmt_0, negated_conjecture,
% 9.17/9.39    (~( ![A:$i,B:$i]:
% 9.17/9.39        ( ( k4_xboole_0 @ A @ B ) =
% 9.17/9.39          ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 9.17/9.39    inference('cnf.neg', [status(esa)], [t100_xboole_1])).
% 9.17/9.39  thf('0', plain,
% 9.17/9.39      (((k4_xboole_0 @ sk_A @ sk_B)
% 9.17/9.39         != (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 9.17/9.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.17/9.39  thf(commutativity_k3_xboole_0, axiom,
% 9.17/9.39    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 9.17/9.39  thf('1', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.17/9.39      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 9.17/9.39  thf('2', plain,
% 9.17/9.39      (((k4_xboole_0 @ sk_A @ sk_B)
% 9.17/9.39         != (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 9.17/9.39      inference('demod', [status(thm)], ['0', '1'])).
% 9.17/9.39  thf('3', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.17/9.39      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 9.17/9.39  thf(d5_xboole_0, axiom,
% 9.17/9.39    (![A:$i,B:$i,C:$i]:
% 9.17/9.39     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 9.17/9.39       ( ![D:$i]:
% 9.17/9.39         ( ( r2_hidden @ D @ C ) <=>
% 9.17/9.39           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 9.17/9.39  thf('4', plain,
% 9.17/9.39      (![X3 : $i, X4 : $i, X7 : $i]:
% 9.17/9.39         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 9.17/9.39          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 9.17/9.39          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 9.17/9.39      inference('cnf', [status(esa)], [d5_xboole_0])).
% 9.17/9.39  thf('5', plain,
% 9.17/9.39      (![X3 : $i, X4 : $i, X7 : $i]:
% 9.17/9.39         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 9.17/9.39          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 9.17/9.39          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 9.17/9.39      inference('cnf', [status(esa)], [d5_xboole_0])).
% 9.17/9.39  thf('6', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 9.17/9.39          | ((X1) = (k4_xboole_0 @ X0 @ X0))
% 9.17/9.39          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 9.17/9.39          | ((X1) = (k4_xboole_0 @ X0 @ X0)))),
% 9.17/9.39      inference('sup-', [status(thm)], ['4', '5'])).
% 9.17/9.39  thf('7', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 9.17/9.39          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 9.17/9.39      inference('simplify', [status(thm)], ['6'])).
% 9.17/9.39  thf(t48_xboole_1, axiom,
% 9.17/9.39    (![A:$i,B:$i]:
% 9.17/9.39     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 9.17/9.39  thf('8', plain,
% 9.17/9.39      (![X17 : $i, X18 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 9.17/9.39           = (k3_xboole_0 @ X17 @ X18))),
% 9.17/9.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.17/9.39  thf(t41_xboole_1, axiom,
% 9.17/9.39    (![A:$i,B:$i,C:$i]:
% 9.17/9.39     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 9.17/9.39       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 9.17/9.39  thf('9', plain,
% 9.17/9.39      (![X12 : $i, X13 : $i, X14 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 9.17/9.39           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 9.17/9.39      inference('cnf', [status(esa)], [t41_xboole_1])).
% 9.17/9.39  thf('10', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 9.17/9.39           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 9.17/9.39      inference('sup+', [status(thm)], ['8', '9'])).
% 9.17/9.39  thf('11', plain,
% 9.17/9.39      (![X17 : $i, X18 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 9.17/9.39           = (k3_xboole_0 @ X17 @ X18))),
% 9.17/9.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.17/9.39  thf('12', plain,
% 9.17/9.39      (![X17 : $i, X18 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 9.17/9.39           = (k3_xboole_0 @ X17 @ X18))),
% 9.17/9.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.17/9.39  thf('13', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 9.17/9.39           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 9.17/9.39      inference('sup+', [status(thm)], ['11', '12'])).
% 9.17/9.39  thf(t47_xboole_1, axiom,
% 9.17/9.39    (![A:$i,B:$i]:
% 9.17/9.39     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 9.17/9.39  thf('14', plain,
% 9.17/9.39      (![X15 : $i, X16 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16))
% 9.17/9.39           = (k4_xboole_0 @ X15 @ X16))),
% 9.17/9.39      inference('cnf', [status(esa)], [t47_xboole_1])).
% 9.17/9.39  thf('15', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 9.17/9.39           = (k4_xboole_0 @ X1 @ X0))),
% 9.17/9.39      inference('sup+', [status(thm)], ['13', '14'])).
% 9.17/9.39  thf('16', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.17/9.39      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 9.17/9.39  thf('17', plain,
% 9.17/9.39      (![X15 : $i, X16 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16))
% 9.17/9.39           = (k4_xboole_0 @ X15 @ X16))),
% 9.17/9.39      inference('cnf', [status(esa)], [t47_xboole_1])).
% 9.17/9.39  thf('18', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 9.17/9.39           = (k4_xboole_0 @ X0 @ X1))),
% 9.17/9.39      inference('sup+', [status(thm)], ['16', '17'])).
% 9.17/9.39  thf('19', plain,
% 9.17/9.39      (![X15 : $i, X16 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16))
% 9.17/9.39           = (k4_xboole_0 @ X15 @ X16))),
% 9.17/9.39      inference('cnf', [status(esa)], [t47_xboole_1])).
% 9.17/9.39  thf('20', plain,
% 9.17/9.39      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 9.17/9.39         (~ (r2_hidden @ X6 @ X5)
% 9.17/9.39          | ~ (r2_hidden @ X6 @ X4)
% 9.17/9.39          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 9.17/9.39      inference('cnf', [status(esa)], [d5_xboole_0])).
% 9.17/9.39  thf('21', plain,
% 9.17/9.39      (![X3 : $i, X4 : $i, X6 : $i]:
% 9.17/9.39         (~ (r2_hidden @ X6 @ X4)
% 9.17/9.39          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 9.17/9.39      inference('simplify', [status(thm)], ['20'])).
% 9.17/9.39  thf('22', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.17/9.39         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 9.17/9.39          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 9.17/9.39      inference('sup-', [status(thm)], ['19', '21'])).
% 9.17/9.39  thf('23', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.17/9.39         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 9.17/9.39          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))))),
% 9.17/9.39      inference('sup-', [status(thm)], ['18', '22'])).
% 9.17/9.39  thf('24', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.17/9.39         (~ (r2_hidden @ X2 @ 
% 9.17/9.39             (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))
% 9.17/9.39          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)))),
% 9.17/9.39      inference('sup-', [status(thm)], ['15', '23'])).
% 9.17/9.39  thf('25', plain,
% 9.17/9.39      (![X12 : $i, X13 : $i, X14 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 9.17/9.39           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 9.17/9.39      inference('cnf', [status(esa)], [t41_xboole_1])).
% 9.17/9.39  thf('26', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.17/9.39         (~ (r2_hidden @ X2 @ 
% 9.17/9.39             (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))
% 9.17/9.39          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1))))),
% 9.17/9.39      inference('demod', [status(thm)], ['24', '25'])).
% 9.17/9.39  thf('27', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 9.17/9.39           = (k4_xboole_0 @ X1 @ X0))),
% 9.17/9.39      inference('sup+', [status(thm)], ['13', '14'])).
% 9.17/9.39  thf('28', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.17/9.39      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 9.17/9.39  thf('29', plain,
% 9.17/9.39      (![X15 : $i, X16 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16))
% 9.17/9.39           = (k4_xboole_0 @ X15 @ X16))),
% 9.17/9.39      inference('cnf', [status(esa)], [t47_xboole_1])).
% 9.17/9.39  thf('30', plain,
% 9.17/9.39      (![X17 : $i, X18 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 9.17/9.39           = (k3_xboole_0 @ X17 @ X18))),
% 9.17/9.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.17/9.39  thf('31', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 9.17/9.39           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 9.17/9.39      inference('sup+', [status(thm)], ['29', '30'])).
% 9.17/9.39  thf('32', plain,
% 9.17/9.39      (![X17 : $i, X18 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 9.17/9.39           = (k3_xboole_0 @ X17 @ X18))),
% 9.17/9.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.17/9.39  thf('33', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 9.17/9.39           = (k3_xboole_0 @ X1 @ X0))),
% 9.17/9.39      inference('sup+', [status(thm)], ['31', '32'])).
% 9.17/9.39  thf('34', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 9.17/9.39           = (k3_xboole_0 @ X0 @ X1))),
% 9.17/9.39      inference('sup+', [status(thm)], ['28', '33'])).
% 9.17/9.39  thf('35', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 9.17/9.39           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 9.17/9.39      inference('sup+', [status(thm)], ['27', '34'])).
% 9.17/9.39  thf('36', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.17/9.39      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 9.17/9.39  thf('37', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 9.17/9.39           = (k4_xboole_0 @ X1 @ X0))),
% 9.17/9.39      inference('sup+', [status(thm)], ['13', '14'])).
% 9.17/9.39  thf('38', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 9.17/9.39           = (k4_xboole_0 @ X1 @ X0))),
% 9.17/9.39      inference('demod', [status(thm)], ['35', '36', '37'])).
% 9.17/9.39  thf('39', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.17/9.39         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 9.17/9.39          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1))))),
% 9.17/9.39      inference('demod', [status(thm)], ['26', '38'])).
% 9.17/9.39  thf('40', plain,
% 9.17/9.39      (![X12 : $i, X13 : $i, X14 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 9.17/9.39           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 9.17/9.39      inference('cnf', [status(esa)], [t41_xboole_1])).
% 9.17/9.39  thf('41', plain,
% 9.17/9.39      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 9.17/9.39         (~ (r2_hidden @ X6 @ X5)
% 9.17/9.39          | (r2_hidden @ X6 @ X3)
% 9.17/9.39          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 9.17/9.39      inference('cnf', [status(esa)], [d5_xboole_0])).
% 9.17/9.39  thf('42', plain,
% 9.17/9.39      (![X3 : $i, X4 : $i, X6 : $i]:
% 9.17/9.39         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 9.17/9.39      inference('simplify', [status(thm)], ['41'])).
% 9.17/9.39  thf('43', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 9.17/9.39         (~ (r2_hidden @ X3 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 9.17/9.39          | (r2_hidden @ X3 @ (k4_xboole_0 @ X2 @ X1)))),
% 9.17/9.39      inference('sup-', [status(thm)], ['40', '42'])).
% 9.17/9.39  thf('44', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.17/9.39         ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 9.17/9.39      inference('clc', [status(thm)], ['39', '43'])).
% 9.17/9.39  thf('45', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.17/9.39         ~ (r2_hidden @ X2 @ (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 9.17/9.39      inference('sup-', [status(thm)], ['10', '44'])).
% 9.17/9.39  thf('46', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 9.17/9.39           = (k4_xboole_0 @ X2 @ X2))),
% 9.17/9.39      inference('sup-', [status(thm)], ['7', '45'])).
% 9.17/9.39  thf('47', plain,
% 9.17/9.39      (![X15 : $i, X16 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16))
% 9.17/9.39           = (k4_xboole_0 @ X15 @ X16))),
% 9.17/9.39      inference('cnf', [status(esa)], [t47_xboole_1])).
% 9.17/9.39  thf(d6_xboole_0, axiom,
% 9.17/9.39    (![A:$i,B:$i]:
% 9.17/9.39     ( ( k5_xboole_0 @ A @ B ) =
% 9.17/9.39       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 9.17/9.39  thf('48', plain,
% 9.17/9.39      (![X8 : $i, X9 : $i]:
% 9.17/9.39         ((k5_xboole_0 @ X8 @ X9)
% 9.17/9.39           = (k2_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ (k4_xboole_0 @ X9 @ X8)))),
% 9.17/9.39      inference('cnf', [status(esa)], [d6_xboole_0])).
% 9.17/9.39  thf('49', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 9.17/9.39           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 9.17/9.39              (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)))),
% 9.17/9.39      inference('sup+', [status(thm)], ['47', '48'])).
% 9.17/9.39  thf(l98_xboole_1, axiom,
% 9.17/9.39    (![A:$i,B:$i]:
% 9.17/9.39     ( ( k5_xboole_0 @ A @ B ) =
% 9.17/9.39       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 9.17/9.39  thf('50', plain,
% 9.17/9.39      (![X10 : $i, X11 : $i]:
% 9.17/9.39         ((k5_xboole_0 @ X10 @ X11)
% 9.17/9.39           = (k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ 
% 9.17/9.39              (k3_xboole_0 @ X10 @ X11)))),
% 9.17/9.39      inference('cnf', [status(esa)], [l98_xboole_1])).
% 9.17/9.39  thf('51', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 9.17/9.39           (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))
% 9.17/9.39           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 9.17/9.39              (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 9.17/9.39               (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))))),
% 9.17/9.39      inference('sup+', [status(thm)], ['49', '50'])).
% 9.17/9.39  thf('52', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 9.17/9.39           = (k4_xboole_0 @ X2 @ X2))),
% 9.17/9.39      inference('sup-', [status(thm)], ['7', '45'])).
% 9.17/9.39  thf('53', plain,
% 9.17/9.39      (![X3 : $i, X4 : $i, X7 : $i]:
% 9.17/9.39         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 9.17/9.39          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 9.17/9.39          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 9.17/9.39      inference('cnf', [status(esa)], [d5_xboole_0])).
% 9.17/9.39  thf('54', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 9.17/9.39          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 9.17/9.39      inference('eq_fact', [status(thm)], ['53'])).
% 9.17/9.39  thf(t98_xboole_1, axiom,
% 9.17/9.39    (![A:$i,B:$i]:
% 9.17/9.39     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 9.17/9.39  thf('55', plain,
% 9.17/9.39      (![X19 : $i, X20 : $i]:
% 9.17/9.39         ((k2_xboole_0 @ X19 @ X20)
% 9.17/9.39           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 9.17/9.39      inference('cnf', [status(esa)], [t98_xboole_1])).
% 9.17/9.39  thf('56', plain,
% 9.17/9.39      (![X17 : $i, X18 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 9.17/9.39           = (k3_xboole_0 @ X17 @ X18))),
% 9.17/9.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.17/9.39  thf('57', plain,
% 9.17/9.39      (![X8 : $i, X9 : $i]:
% 9.17/9.39         ((k5_xboole_0 @ X8 @ X9)
% 9.17/9.39           = (k2_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ (k4_xboole_0 @ X9 @ X8)))),
% 9.17/9.39      inference('cnf', [status(esa)], [d6_xboole_0])).
% 9.17/9.39  thf('58', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 9.17/9.39           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 9.17/9.39              (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)))),
% 9.17/9.39      inference('sup+', [status(thm)], ['56', '57'])).
% 9.17/9.39  thf('59', plain,
% 9.17/9.39      (![X12 : $i, X13 : $i, X14 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 9.17/9.39           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 9.17/9.39      inference('cnf', [status(esa)], [t41_xboole_1])).
% 9.17/9.39  thf('60', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 9.17/9.39           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 9.17/9.39              (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1))))),
% 9.17/9.39      inference('demod', [status(thm)], ['58', '59'])).
% 9.17/9.39  thf('61', plain,
% 9.17/9.39      (![X15 : $i, X16 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16))
% 9.17/9.39           = (k4_xboole_0 @ X15 @ X16))),
% 9.17/9.39      inference('cnf', [status(esa)], [t47_xboole_1])).
% 9.17/9.39  thf('62', plain,
% 9.17/9.39      (![X12 : $i, X13 : $i, X14 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 9.17/9.39           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 9.17/9.39      inference('cnf', [status(esa)], [t41_xboole_1])).
% 9.17/9.39  thf('63', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 9.17/9.39           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 9.17/9.39      inference('sup+', [status(thm)], ['61', '62'])).
% 9.17/9.39  thf('64', plain,
% 9.17/9.39      (![X12 : $i, X13 : $i, X14 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 9.17/9.39           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 9.17/9.39      inference('cnf', [status(esa)], [t41_xboole_1])).
% 9.17/9.39  thf('65', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2))
% 9.17/9.39           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 9.17/9.39      inference('demod', [status(thm)], ['63', '64'])).
% 9.17/9.39  thf('66', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ X1 @ 
% 9.17/9.39           (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1))))
% 9.17/9.39           = (k4_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))))),
% 9.17/9.39      inference('sup+', [status(thm)], ['60', '65'])).
% 9.17/9.39  thf('67', plain,
% 9.17/9.39      (![X17 : $i, X18 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 9.17/9.39           = (k3_xboole_0 @ X17 @ X18))),
% 9.17/9.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.17/9.39  thf('68', plain,
% 9.17/9.39      (![X12 : $i, X13 : $i, X14 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 9.17/9.39           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 9.17/9.39      inference('cnf', [status(esa)], [t41_xboole_1])).
% 9.17/9.39  thf('69', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.17/9.39         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 9.17/9.39           = (k4_xboole_0 @ X2 @ 
% 9.17/9.39              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))))),
% 9.17/9.39      inference('sup+', [status(thm)], ['67', '68'])).
% 9.17/9.39  thf('70', plain,
% 9.17/9.39      (![X12 : $i, X13 : $i, X14 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 9.17/9.39           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 9.17/9.39      inference('cnf', [status(esa)], [t41_xboole_1])).
% 9.17/9.39  thf('71', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.17/9.39         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 9.17/9.39           = (k4_xboole_0 @ X2 @ 
% 9.17/9.39              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 9.17/9.39      inference('demod', [status(thm)], ['69', '70'])).
% 9.17/9.39  thf('72', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.17/9.39      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 9.17/9.39  thf('73', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 9.17/9.39           = (k4_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))))),
% 9.17/9.39      inference('demod', [status(thm)], ['66', '71', '72'])).
% 9.17/9.39  thf('74', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 9.17/9.39           = (k4_xboole_0 @ X1 @ X0))),
% 9.17/9.39      inference('sup+', [status(thm)], ['13', '14'])).
% 9.17/9.39  thf('75', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ X1 @ X0)
% 9.17/9.39           = (k4_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))))),
% 9.17/9.39      inference('demod', [status(thm)], ['73', '74'])).
% 9.17/9.39  thf('76', plain,
% 9.17/9.39      (![X0 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ X0 @ X0)
% 9.17/9.39           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X0)))),
% 9.17/9.39      inference('sup+', [status(thm)], ['55', '75'])).
% 9.17/9.39  thf('77', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.17/9.39         ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 9.17/9.39      inference('clc', [status(thm)], ['39', '43'])).
% 9.17/9.39  thf('78', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 9.17/9.39      inference('sup-', [status(thm)], ['76', '77'])).
% 9.17/9.39  thf('79', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ X0 @ X0)
% 9.17/9.39           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1))),
% 9.17/9.39      inference('sup-', [status(thm)], ['54', '78'])).
% 9.17/9.39  thf('80', plain,
% 9.17/9.39      (![X12 : $i, X13 : $i, X14 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 9.17/9.39           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 9.17/9.39      inference('cnf', [status(esa)], [t41_xboole_1])).
% 9.17/9.39  thf('81', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ X0 @ X0)
% 9.17/9.39           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 9.17/9.39      inference('demod', [status(thm)], ['79', '80'])).
% 9.17/9.39  thf('82', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.17/9.39         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 9.17/9.39           = (k4_xboole_0 @ X2 @ 
% 9.17/9.39              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 9.17/9.39      inference('demod', [status(thm)], ['69', '70'])).
% 9.17/9.39  thf('83', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 9.17/9.39           = (k4_xboole_0 @ X0 @ X0))),
% 9.17/9.39      inference('sup+', [status(thm)], ['81', '82'])).
% 9.17/9.39  thf('84', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.17/9.39      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 9.17/9.39  thf('85', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 9.17/9.39           = (k4_xboole_0 @ X0 @ X0))),
% 9.17/9.39      inference('sup+', [status(thm)], ['83', '84'])).
% 9.17/9.39  thf('86', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 9.17/9.39           = (k4_xboole_0 @ X0 @ X0))),
% 9.17/9.39      inference('sup+', [status(thm)], ['81', '82'])).
% 9.17/9.39  thf('87', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X1 @ X1))),
% 9.17/9.39      inference('sup+', [status(thm)], ['85', '86'])).
% 9.17/9.39  thf('88', plain,
% 9.17/9.39      (![X19 : $i, X20 : $i]:
% 9.17/9.39         ((k2_xboole_0 @ X19 @ X20)
% 9.17/9.39           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 9.17/9.39      inference('cnf', [status(esa)], [t98_xboole_1])).
% 9.17/9.39  thf('89', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k2_xboole_0 @ X1 @ X1)
% 9.17/9.39           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 9.17/9.39      inference('sup+', [status(thm)], ['87', '88'])).
% 9.17/9.39  thf('90', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X1 @ X1))),
% 9.17/9.39      inference('sup+', [status(thm)], ['85', '86'])).
% 9.17/9.39  thf('91', plain,
% 9.17/9.39      (![X17 : $i, X18 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 9.17/9.39           = (k3_xboole_0 @ X17 @ X18))),
% 9.17/9.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.17/9.39  thf('92', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 9.17/9.39           = (k3_xboole_0 @ X1 @ X1))),
% 9.17/9.39      inference('sup+', [status(thm)], ['90', '91'])).
% 9.17/9.39  thf('93', plain,
% 9.17/9.39      (![X10 : $i, X11 : $i]:
% 9.17/9.39         ((k5_xboole_0 @ X10 @ X11)
% 9.17/9.39           = (k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ 
% 9.17/9.39              (k3_xboole_0 @ X10 @ X11)))),
% 9.17/9.39      inference('cnf', [status(esa)], [l98_xboole_1])).
% 9.17/9.39  thf('94', plain,
% 9.17/9.39      (![X17 : $i, X18 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 9.17/9.39           = (k3_xboole_0 @ X17 @ X18))),
% 9.17/9.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.17/9.39  thf('95', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 9.17/9.39           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 9.17/9.39      inference('sup+', [status(thm)], ['93', '94'])).
% 9.17/9.39  thf('96', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 9.17/9.39          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 9.17/9.39      inference('simplify', [status(thm)], ['6'])).
% 9.17/9.39  thf('97', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k2_xboole_0 @ X1 @ X1)
% 9.17/9.39           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 9.17/9.39      inference('sup+', [status(thm)], ['87', '88'])).
% 9.17/9.39  thf('98', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X1 @ X1))),
% 9.17/9.39      inference('sup+', [status(thm)], ['85', '86'])).
% 9.17/9.39  thf('99', plain,
% 9.17/9.39      (![X8 : $i, X9 : $i]:
% 9.17/9.39         ((k5_xboole_0 @ X8 @ X9)
% 9.17/9.39           = (k2_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ (k4_xboole_0 @ X9 @ X8)))),
% 9.17/9.39      inference('cnf', [status(esa)], [d6_xboole_0])).
% 9.17/9.39  thf('100', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k5_xboole_0 @ X1 @ X1)
% 9.17/9.39           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ (k4_xboole_0 @ X1 @ X1)))),
% 9.17/9.39      inference('sup+', [status(thm)], ['98', '99'])).
% 9.17/9.39  thf('101', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ X0 @ X0)
% 9.17/9.39           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 9.17/9.39      inference('demod', [status(thm)], ['79', '80'])).
% 9.17/9.39  thf('102', plain,
% 9.17/9.39      (![X12 : $i, X13 : $i, X14 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 9.17/9.39           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 9.17/9.39      inference('cnf', [status(esa)], [t41_xboole_1])).
% 9.17/9.39  thf('103', plain,
% 9.17/9.39      (![X19 : $i, X20 : $i]:
% 9.17/9.39         ((k2_xboole_0 @ X19 @ X20)
% 9.17/9.39           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 9.17/9.39      inference('cnf', [status(esa)], [t98_xboole_1])).
% 9.17/9.39  thf('104', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.17/9.39         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))
% 9.17/9.39           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 9.17/9.39      inference('sup+', [status(thm)], ['102', '103'])).
% 9.17/9.39  thf('105', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 9.17/9.39           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 9.17/9.39      inference('sup+', [status(thm)], ['101', '104'])).
% 9.17/9.39  thf('106', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k5_xboole_0 @ X1 @ X1)
% 9.17/9.39           = (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ (k4_xboole_0 @ X1 @ X1)))),
% 9.17/9.39      inference('demod', [status(thm)], ['100', '105'])).
% 9.17/9.39  thf('107', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k5_xboole_0 @ X1 @ X1)
% 9.17/9.39           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ (k4_xboole_0 @ X0 @ X0)))),
% 9.17/9.39      inference('sup+', [status(thm)], ['97', '106'])).
% 9.17/9.39  thf('108', plain,
% 9.17/9.39      (![X8 : $i, X9 : $i]:
% 9.17/9.39         ((k5_xboole_0 @ X8 @ X9)
% 9.17/9.39           = (k2_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ (k4_xboole_0 @ X9 @ X8)))),
% 9.17/9.39      inference('cnf', [status(esa)], [d6_xboole_0])).
% 9.17/9.39  thf('109', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X1) = (k5_xboole_0 @ X0 @ X0))),
% 9.17/9.39      inference('demod', [status(thm)], ['107', '108'])).
% 9.17/9.39  thf('110', plain,
% 9.17/9.39      (![X0 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ X0 @ X0)
% 9.17/9.39           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X0)))),
% 9.17/9.39      inference('sup+', [status(thm)], ['55', '75'])).
% 9.17/9.39  thf('111', plain,
% 9.17/9.39      (![X17 : $i, X18 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 9.17/9.39           = (k3_xboole_0 @ X17 @ X18))),
% 9.17/9.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.17/9.39  thf('112', plain,
% 9.17/9.39      (![X0 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0))
% 9.17/9.39           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X0)))),
% 9.17/9.39      inference('sup+', [status(thm)], ['110', '111'])).
% 9.17/9.39  thf('113', plain,
% 9.17/9.39      (![X17 : $i, X18 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 9.17/9.39           = (k3_xboole_0 @ X17 @ X18))),
% 9.17/9.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.17/9.39  thf('114', plain,
% 9.17/9.39      (![X0 : $i]:
% 9.17/9.39         ((k3_xboole_0 @ X0 @ X0)
% 9.17/9.39           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X0)))),
% 9.17/9.39      inference('demod', [status(thm)], ['112', '113'])).
% 9.17/9.39  thf('115', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 9.17/9.39           = (k4_xboole_0 @ X0 @ X1))),
% 9.17/9.39      inference('sup+', [status(thm)], ['16', '17'])).
% 9.17/9.39  thf('116', plain,
% 9.17/9.39      (![X0 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ (k3_xboole_0 @ X0 @ X0))
% 9.17/9.39           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ X0))),
% 9.17/9.39      inference('sup+', [status(thm)], ['114', '115'])).
% 9.17/9.39  thf('117', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.17/9.39      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 9.17/9.39  thf('118', plain,
% 9.17/9.39      (![X10 : $i, X11 : $i]:
% 9.17/9.39         ((k5_xboole_0 @ X10 @ X11)
% 9.17/9.39           = (k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ 
% 9.17/9.39              (k3_xboole_0 @ X10 @ X11)))),
% 9.17/9.39      inference('cnf', [status(esa)], [l98_xboole_1])).
% 9.17/9.39  thf('119', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k5_xboole_0 @ X0 @ X1)
% 9.17/9.39           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 9.17/9.39      inference('sup+', [status(thm)], ['117', '118'])).
% 9.17/9.39  thf('120', plain,
% 9.17/9.39      (![X0 : $i]:
% 9.17/9.39         ((k5_xboole_0 @ X0 @ X0)
% 9.17/9.39           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ X0))),
% 9.17/9.39      inference('demod', [status(thm)], ['116', '119'])).
% 9.17/9.39  thf('121', plain,
% 9.17/9.39      (![X3 : $i, X4 : $i, X6 : $i]:
% 9.17/9.39         (~ (r2_hidden @ X6 @ X4)
% 9.17/9.39          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 9.17/9.39      inference('simplify', [status(thm)], ['20'])).
% 9.17/9.39  thf('122', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 9.17/9.39          | ~ (r2_hidden @ X1 @ X0))),
% 9.17/9.39      inference('sup-', [status(thm)], ['120', '121'])).
% 9.17/9.39  thf('123', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.17/9.39         (~ (r2_hidden @ X2 @ (k5_xboole_0 @ X0 @ X0))
% 9.17/9.39          | ~ (r2_hidden @ X2 @ X1))),
% 9.17/9.39      inference('sup-', [status(thm)], ['109', '122'])).
% 9.17/9.39  thf('124', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 9.17/9.39      inference('condensation', [status(thm)], ['123'])).
% 9.17/9.39  thf('125', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X1 @ X1))),
% 9.17/9.39      inference('sup-', [status(thm)], ['96', '124'])).
% 9.17/9.39  thf('126', plain,
% 9.17/9.39      (![X17 : $i, X18 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 9.17/9.39           = (k3_xboole_0 @ X17 @ X18))),
% 9.17/9.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.17/9.39  thf('127', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 9.17/9.39           = (k3_xboole_0 @ X1 @ X1))),
% 9.17/9.39      inference('sup+', [status(thm)], ['125', '126'])).
% 9.17/9.39  thf('128', plain,
% 9.17/9.39      (![X0 : $i]:
% 9.17/9.39         ((k3_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ (k3_xboole_0 @ X0 @ X0))
% 9.17/9.39           = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ (k2_xboole_0 @ X0 @ X0)))),
% 9.17/9.39      inference('sup+', [status(thm)], ['95', '127'])).
% 9.17/9.39  thf('129', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ X0 @ X0)
% 9.17/9.39           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 9.17/9.39      inference('demod', [status(thm)], ['79', '80'])).
% 9.17/9.39  thf('130', plain,
% 9.17/9.39      (![X17 : $i, X18 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 9.17/9.39           = (k3_xboole_0 @ X17 @ X18))),
% 9.17/9.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.17/9.39  thf('131', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0))
% 9.17/9.39           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 9.17/9.39      inference('sup+', [status(thm)], ['129', '130'])).
% 9.17/9.39  thf('132', plain,
% 9.17/9.39      (![X17 : $i, X18 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 9.17/9.39           = (k3_xboole_0 @ X17 @ X18))),
% 9.17/9.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.17/9.39  thf('133', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k3_xboole_0 @ X0 @ X0)
% 9.17/9.39           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 9.17/9.39      inference('demod', [status(thm)], ['131', '132'])).
% 9.17/9.39  thf('134', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 9.17/9.39           = (k3_xboole_0 @ X0 @ X1))),
% 9.17/9.39      inference('sup+', [status(thm)], ['28', '33'])).
% 9.17/9.39  thf('135', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X0))
% 9.17/9.39           = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 9.17/9.39      inference('sup+', [status(thm)], ['133', '134'])).
% 9.17/9.39  thf('136', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.17/9.39      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 9.17/9.39  thf('137', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k3_xboole_0 @ X0 @ X0)
% 9.17/9.39           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 9.17/9.39      inference('demod', [status(thm)], ['131', '132'])).
% 9.17/9.39  thf('138', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X0))
% 9.17/9.39           = (k3_xboole_0 @ X0 @ X0))),
% 9.17/9.39      inference('demod', [status(thm)], ['135', '136', '137'])).
% 9.17/9.39  thf('139', plain,
% 9.17/9.39      (![X19 : $i, X20 : $i]:
% 9.17/9.39         ((k2_xboole_0 @ X19 @ X20)
% 9.17/9.39           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 9.17/9.39      inference('cnf', [status(esa)], [t98_xboole_1])).
% 9.17/9.39  thf('140', plain,
% 9.17/9.39      (![X10 : $i, X11 : $i]:
% 9.17/9.39         ((k5_xboole_0 @ X10 @ X11)
% 9.17/9.39           = (k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ 
% 9.17/9.39              (k3_xboole_0 @ X10 @ X11)))),
% 9.17/9.39      inference('cnf', [status(esa)], [l98_xboole_1])).
% 9.17/9.39  thf('141', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 9.17/9.39           = (k4_xboole_0 @ X1 @ X0))),
% 9.17/9.39      inference('demod', [status(thm)], ['35', '36', '37'])).
% 9.17/9.39  thf('142', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k3_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ 
% 9.17/9.39           (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))
% 9.17/9.39           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 9.17/9.39      inference('sup+', [status(thm)], ['140', '141'])).
% 9.17/9.39  thf('143', plain,
% 9.17/9.39      (![X10 : $i, X11 : $i]:
% 9.17/9.39         ((k5_xboole_0 @ X10 @ X11)
% 9.17/9.39           = (k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ 
% 9.17/9.39              (k3_xboole_0 @ X10 @ X11)))),
% 9.17/9.39      inference('cnf', [status(esa)], [l98_xboole_1])).
% 9.17/9.39  thf('144', plain,
% 9.17/9.39      (![X10 : $i, X11 : $i]:
% 9.17/9.39         ((k5_xboole_0 @ X10 @ X11)
% 9.17/9.39           = (k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ 
% 9.17/9.39              (k3_xboole_0 @ X10 @ X11)))),
% 9.17/9.39      inference('cnf', [status(esa)], [l98_xboole_1])).
% 9.17/9.39  thf('145', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k3_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 9.17/9.39           = (k5_xboole_0 @ X1 @ X0))),
% 9.17/9.39      inference('demod', [status(thm)], ['142', '143', '144'])).
% 9.17/9.39  thf('146', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 9.17/9.39           (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))
% 9.17/9.39           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 9.17/9.39      inference('sup+', [status(thm)], ['139', '145'])).
% 9.17/9.39  thf('147', plain,
% 9.17/9.39      (![X19 : $i, X20 : $i]:
% 9.17/9.39         ((k2_xboole_0 @ X19 @ X20)
% 9.17/9.39           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 9.17/9.39      inference('cnf', [status(esa)], [t98_xboole_1])).
% 9.17/9.39  thf('148', plain,
% 9.17/9.39      (![X19 : $i, X20 : $i]:
% 9.17/9.39         ((k2_xboole_0 @ X19 @ X20)
% 9.17/9.39           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 9.17/9.39      inference('cnf', [status(esa)], [t98_xboole_1])).
% 9.17/9.39  thf('149', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 9.17/9.39           = (k2_xboole_0 @ X1 @ X0))),
% 9.17/9.39      inference('demod', [status(thm)], ['146', '147', '148'])).
% 9.17/9.39  thf('150', plain,
% 9.17/9.39      (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (k2_xboole_0 @ X0 @ X0))),
% 9.17/9.39      inference('demod', [status(thm)], ['128', '138', '149'])).
% 9.17/9.39  thf('151', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 9.17/9.39           = (k2_xboole_0 @ X1 @ X1))),
% 9.17/9.39      inference('demod', [status(thm)], ['92', '150'])).
% 9.17/9.39  thf('152', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 9.17/9.39          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 9.17/9.39      inference('eq_fact', [status(thm)], ['53'])).
% 9.17/9.39  thf('153', plain,
% 9.17/9.39      (![X3 : $i, X4 : $i, X7 : $i]:
% 9.17/9.39         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 9.17/9.39          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 9.17/9.39          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 9.17/9.39          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 9.17/9.39      inference('cnf', [status(esa)], [d5_xboole_0])).
% 9.17/9.39  thf('154', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 9.17/9.39          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 9.17/9.39          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 9.17/9.39          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 9.17/9.39      inference('sup-', [status(thm)], ['152', '153'])).
% 9.17/9.39  thf('155', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 9.17/9.39          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 9.17/9.39          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 9.17/9.39      inference('simplify', [status(thm)], ['154'])).
% 9.17/9.39  thf('156', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 9.17/9.39          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 9.17/9.39      inference('eq_fact', [status(thm)], ['53'])).
% 9.17/9.39  thf('157', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 9.17/9.39          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 9.17/9.39      inference('clc', [status(thm)], ['155', '156'])).
% 9.17/9.39  thf('158', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 9.17/9.39      inference('sup-', [status(thm)], ['76', '77'])).
% 9.17/9.39  thf('159', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((X1) = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 9.17/9.39      inference('sup-', [status(thm)], ['157', '158'])).
% 9.17/9.39  thf('160', plain, (![X1 : $i]: ((X1) = (k2_xboole_0 @ X1 @ X1))),
% 9.17/9.39      inference('demod', [status(thm)], ['151', '159'])).
% 9.17/9.39  thf('161', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((X1) = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 9.17/9.39      inference('demod', [status(thm)], ['89', '160'])).
% 9.17/9.39  thf('162', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i, X3 : $i]:
% 9.17/9.39         ((X3)
% 9.17/9.39           = (k5_xboole_0 @ X3 @ (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)))),
% 9.17/9.39      inference('sup+', [status(thm)], ['52', '161'])).
% 9.17/9.39  thf('163', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ X1 @ X0)
% 9.17/9.39           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 9.17/9.39              (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 9.17/9.39               (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))))),
% 9.17/9.39      inference('demod', [status(thm)], ['51', '162'])).
% 9.17/9.39  thf('164', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ X1 @ X2)
% 9.17/9.39           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)) @ 
% 9.17/9.39              (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X2) @ (k4_xboole_0 @ X0 @ X0))))),
% 9.17/9.39      inference('sup+', [status(thm)], ['46', '163'])).
% 9.17/9.39  thf('165', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 9.17/9.39           = (k2_xboole_0 @ X1 @ X1))),
% 9.17/9.39      inference('demod', [status(thm)], ['92', '150'])).
% 9.17/9.39  thf('166', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 9.17/9.39           = (k4_xboole_0 @ X0 @ X0))),
% 9.17/9.39      inference('sup+', [status(thm)], ['81', '82'])).
% 9.17/9.39  thf('167', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k3_xboole_0 @ 
% 9.17/9.39           (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ (k4_xboole_0 @ X0 @ X0)) @ 
% 9.17/9.39           X1)
% 9.17/9.39           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ (k4_xboole_0 @ X0 @ X0)))),
% 9.17/9.39      inference('sup+', [status(thm)], ['165', '166'])).
% 9.17/9.39  thf('168', plain,
% 9.17/9.39      (![X8 : $i, X9 : $i]:
% 9.17/9.39         ((k5_xboole_0 @ X8 @ X9)
% 9.17/9.39           = (k2_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ (k4_xboole_0 @ X9 @ X8)))),
% 9.17/9.39      inference('cnf', [status(esa)], [d6_xboole_0])).
% 9.17/9.39  thf('169', plain,
% 9.17/9.39      (![X12 : $i, X13 : $i, X14 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 9.17/9.39           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 9.17/9.39      inference('cnf', [status(esa)], [t41_xboole_1])).
% 9.17/9.39  thf('170', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 9.17/9.39           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 9.17/9.39      inference('sup+', [status(thm)], ['101', '104'])).
% 9.17/9.39  thf('171', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k2_xboole_0 @ X1 @ X1)
% 9.17/9.39           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 9.17/9.39      inference('sup+', [status(thm)], ['87', '88'])).
% 9.17/9.39  thf('172', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ X0 @ X0)
% 9.17/9.39           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 9.17/9.39      inference('demod', [status(thm)], ['79', '80'])).
% 9.17/9.39  thf('173', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k3_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1)
% 9.17/9.39           = (k4_xboole_0 @ X0 @ X0))),
% 9.17/9.39      inference('demod', [status(thm)],
% 9.17/9.39                ['167', '168', '169', '170', '171', '172'])).
% 9.17/9.39  thf('174', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 9.17/9.39           = (k3_xboole_0 @ X0 @ X1))),
% 9.17/9.39      inference('sup+', [status(thm)], ['28', '33'])).
% 9.17/9.39  thf('175', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 9.17/9.39           = (k3_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)))),
% 9.17/9.39      inference('sup+', [status(thm)], ['173', '174'])).
% 9.17/9.39  thf('176', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 9.17/9.39          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 9.17/9.39      inference('eq_fact', [status(thm)], ['53'])).
% 9.17/9.39  thf('177', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 9.17/9.39      inference('condensation', [status(thm)], ['123'])).
% 9.17/9.39  thf('178', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k5_xboole_0 @ X0 @ X0)
% 9.17/9.39           = (k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1))),
% 9.17/9.39      inference('sup-', [status(thm)], ['176', '177'])).
% 9.17/9.39  thf('179', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 9.17/9.39           = (k4_xboole_0 @ X0 @ X0))),
% 9.17/9.39      inference('sup+', [status(thm)], ['83', '84'])).
% 9.17/9.39  thf('180', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k3_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 9.17/9.39           = (k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ (k5_xboole_0 @ X0 @ X0)))),
% 9.17/9.39      inference('sup+', [status(thm)], ['178', '179'])).
% 9.17/9.39  thf('181', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k5_xboole_0 @ X0 @ X0)
% 9.17/9.39           = (k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1))),
% 9.17/9.39      inference('sup-', [status(thm)], ['176', '177'])).
% 9.17/9.39  thf('182', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k3_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 9.17/9.39           = (k5_xboole_0 @ X0 @ X0))),
% 9.17/9.39      inference('demod', [status(thm)], ['180', '181'])).
% 9.17/9.39  thf('183', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 9.17/9.39           = (k5_xboole_0 @ X0 @ X0))),
% 9.17/9.39      inference('demod', [status(thm)], ['175', '182'])).
% 9.17/9.39  thf('184', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 9.17/9.39          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 9.17/9.39      inference('clc', [status(thm)], ['155', '156'])).
% 9.17/9.39  thf('185', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 9.17/9.39      inference('condensation', [status(thm)], ['123'])).
% 9.17/9.39  thf('186', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((X1) = (k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)))),
% 9.17/9.39      inference('sup-', [status(thm)], ['184', '185'])).
% 9.17/9.39  thf('187', plain,
% 9.17/9.39      (![X1 : $i, X2 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ X1 @ X2)
% 9.17/9.39           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 9.17/9.39      inference('demod', [status(thm)], ['164', '183', '186'])).
% 9.17/9.39  thf('188', plain,
% 9.17/9.39      (![X0 : $i, X1 : $i]:
% 9.17/9.39         ((k4_xboole_0 @ X0 @ X1)
% 9.17/9.39           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 9.17/9.39      inference('sup+', [status(thm)], ['3', '187'])).
% 9.17/9.39  thf('189', plain,
% 9.17/9.39      (((k4_xboole_0 @ sk_A @ sk_B) != (k4_xboole_0 @ sk_A @ sk_B))),
% 9.17/9.39      inference('demod', [status(thm)], ['2', '188'])).
% 9.17/9.39  thf('190', plain, ($false), inference('simplify', [status(thm)], ['189'])).
% 9.17/9.39  
% 9.17/9.39  % SZS output end Refutation
% 9.17/9.39  
% 9.17/9.40  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

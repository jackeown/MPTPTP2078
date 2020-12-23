%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NN0Lo4IzAd

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 106 expanded)
%              Number of leaves         :   28 (  42 expanded)
%              Depth                    :   18
%              Number of atoms          :  622 ( 768 expanded)
%              Number of equality atoms :   60 (  76 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t70_enumset1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k1_enumset1 @ A @ A @ B )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t70_enumset1])).

thf('0',plain,(
    ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('1',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k2_tarski @ X32 @ X33 )
      = ( k2_xboole_0 @ ( k1_tarski @ X32 ) @ ( k1_tarski @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k2_xboole_0 @ X25 @ X26 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X7 )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['4'])).

thf('6',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X8 )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X7 )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X8 )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['8','10'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('13',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('16',plain,(
    ! [X18: $i] :
      ( ( k2_xboole_0 @ X18 @ X18 )
      = X18 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('17',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k2_xboole_0 @ X25 @ X26 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X27 @ X28 ) @ X29 )
      = ( k5_xboole_0 @ X27 @ ( k5_xboole_0 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('22',plain,(
    ! [X24: $i] :
      ( ( k4_xboole_0 @ X24 @ k1_xboole_0 )
      = X24 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k2_xboole_0 @ X30 @ X31 )
      = ( k5_xboole_0 @ X30 @ ( k4_xboole_0 @ X31 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('25',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('27',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ~ ( r2_hidden @ X16 @ X14 )
      | ( X15
       != ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('28',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('32',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_xboole_0 @ X22 @ X21 )
        = X21 )
      | ~ ( r1_tarski @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['24','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['2','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('39',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k2_xboole_0 @ X30 @ X31 )
      = ( k5_xboole_0 @ X30 @ ( k4_xboole_0 @ X31 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X18: $i] :
      ( ( k2_xboole_0 @ X18 @ X18 )
      = X18 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['37','42'])).

thf('44',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('45',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('46',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['43','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','51'])).

thf('53',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_xboole_0 @ X22 @ X21 )
        = X21 )
      | ~ ( r1_tarski @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('55',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k1_enumset1 @ X34 @ X35 @ X36 )
      = ( k2_xboole_0 @ ( k1_tarski @ X34 ) @ ( k2_tarski @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','56'])).

thf('58',plain,(
    $false ),
    inference(simplify,[status(thm)],['57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NN0Lo4IzAd
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:47:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.57  % Solved by: fo/fo7.sh
% 0.21/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.57  % done 374 iterations in 0.119s
% 0.21/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.57  % SZS output start Refutation
% 0.21/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.57  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.57  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.57  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.57  thf(t70_enumset1, conjecture,
% 0.21/0.57    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.57    (~( ![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ) )),
% 0.21/0.57    inference('cnf.neg', [status(esa)], [t70_enumset1])).
% 0.21/0.57  thf('0', plain,
% 0.21/0.57      (((k1_enumset1 @ sk_A @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(t41_enumset1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( k2_tarski @ A @ B ) =
% 0.21/0.57       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.21/0.57  thf('1', plain,
% 0.21/0.57      (![X32 : $i, X33 : $i]:
% 0.21/0.57         ((k2_tarski @ X32 @ X33)
% 0.21/0.57           = (k2_xboole_0 @ (k1_tarski @ X32) @ (k1_tarski @ X33)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.21/0.57  thf(t46_xboole_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.21/0.57  thf('2', plain,
% 0.21/0.57      (![X25 : $i, X26 : $i]:
% 0.21/0.57         ((k4_xboole_0 @ X25 @ (k2_xboole_0 @ X25 @ X26)) = (k1_xboole_0))),
% 0.21/0.57      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.21/0.57  thf(t100_xboole_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.57  thf('3', plain,
% 0.21/0.57      (![X19 : $i, X20 : $i]:
% 0.21/0.57         ((k4_xboole_0 @ X19 @ X20)
% 0.21/0.57           = (k5_xboole_0 @ X19 @ (k3_xboole_0 @ X19 @ X20)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.57  thf(d4_xboole_0, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.21/0.57       ( ![D:$i]:
% 0.21/0.57         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.57           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.21/0.57  thf('4', plain,
% 0.21/0.57      (![X7 : $i, X8 : $i, X11 : $i]:
% 0.21/0.57         (((X11) = (k3_xboole_0 @ X7 @ X8))
% 0.21/0.57          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X7)
% 0.21/0.57          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 0.21/0.57      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.21/0.57  thf('5', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.21/0.57          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.21/0.57      inference('eq_fact', [status(thm)], ['4'])).
% 0.21/0.57  thf('6', plain,
% 0.21/0.57      (![X7 : $i, X8 : $i, X11 : $i]:
% 0.21/0.57         (((X11) = (k3_xboole_0 @ X7 @ X8))
% 0.21/0.57          | ~ (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X8)
% 0.21/0.57          | ~ (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X7)
% 0.21/0.57          | ~ (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 0.21/0.57      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.21/0.57  thf('7', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((X0) = (k3_xboole_0 @ X0 @ X0))
% 0.21/0.57          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 0.21/0.57          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 0.21/0.57          | ((X0) = (k3_xboole_0 @ X0 @ X0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.57  thf('8', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 0.21/0.57          | ((X0) = (k3_xboole_0 @ X0 @ X0)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.57  thf('9', plain,
% 0.21/0.57      (![X7 : $i, X8 : $i, X11 : $i]:
% 0.21/0.57         (((X11) = (k3_xboole_0 @ X7 @ X8))
% 0.21/0.57          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X8)
% 0.21/0.57          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 0.21/0.57      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.21/0.57  thf('10', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.21/0.57          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.57      inference('eq_fact', [status(thm)], ['9'])).
% 0.21/0.57  thf('11', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.21/0.57      inference('clc', [status(thm)], ['8', '10'])).
% 0.21/0.57  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.57    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.57  thf('12', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.57  thf('13', plain,
% 0.21/0.57      (![X19 : $i, X20 : $i]:
% 0.21/0.57         ((k4_xboole_0 @ X19 @ X20)
% 0.21/0.57           = (k5_xboole_0 @ X19 @ (k3_xboole_0 @ X19 @ X20)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.57  thf('14', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((k4_xboole_0 @ X0 @ X1)
% 0.21/0.57           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.57      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.57  thf('15', plain,
% 0.21/0.57      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['11', '14'])).
% 0.21/0.57  thf(idempotence_k2_xboole_0, axiom,
% 0.21/0.57    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.21/0.57  thf('16', plain, (![X18 : $i]: ((k2_xboole_0 @ X18 @ X18) = (X18))),
% 0.21/0.57      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.21/0.57  thf('17', plain,
% 0.21/0.57      (![X25 : $i, X26 : $i]:
% 0.21/0.57         ((k4_xboole_0 @ X25 @ (k2_xboole_0 @ X25 @ X26)) = (k1_xboole_0))),
% 0.21/0.57      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.21/0.57  thf('18', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['16', '17'])).
% 0.21/0.57  thf('19', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['15', '18'])).
% 0.21/0.57  thf(t91_xboole_1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.21/0.57       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.21/0.57  thf('20', plain,
% 0.21/0.57      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.21/0.57         ((k5_xboole_0 @ (k5_xboole_0 @ X27 @ X28) @ X29)
% 0.21/0.57           = (k5_xboole_0 @ X27 @ (k5_xboole_0 @ X28 @ X29)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.21/0.57  thf('21', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.21/0.57           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.21/0.57      inference('sup+', [status(thm)], ['19', '20'])).
% 0.21/0.57  thf(t3_boole, axiom,
% 0.21/0.57    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.57  thf('22', plain, (![X24 : $i]: ((k4_xboole_0 @ X24 @ k1_xboole_0) = (X24))),
% 0.21/0.57      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.57  thf(t98_xboole_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.21/0.57  thf('23', plain,
% 0.21/0.57      (![X30 : $i, X31 : $i]:
% 0.21/0.57         ((k2_xboole_0 @ X30 @ X31)
% 0.21/0.57           = (k5_xboole_0 @ X30 @ (k4_xboole_0 @ X31 @ X30)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.21/0.57  thf('24', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['22', '23'])).
% 0.21/0.57  thf(d3_tarski, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.57  thf('25', plain,
% 0.21/0.57      (![X3 : $i, X5 : $i]:
% 0.21/0.57         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.57  thf('26', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['16', '17'])).
% 0.21/0.57  thf(d5_xboole_0, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.21/0.57       ( ![D:$i]:
% 0.21/0.57         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.57           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.21/0.57  thf('27', plain,
% 0.21/0.57      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X16 @ X15)
% 0.21/0.57          | ~ (r2_hidden @ X16 @ X14)
% 0.21/0.57          | ((X15) != (k4_xboole_0 @ X13 @ X14)))),
% 0.21/0.57      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.57  thf('28', plain,
% 0.21/0.57      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X16 @ X14)
% 0.21/0.57          | ~ (r2_hidden @ X16 @ (k4_xboole_0 @ X13 @ X14)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['27'])).
% 0.21/0.57  thf('29', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['26', '28'])).
% 0.21/0.57  thf('30', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.57      inference('condensation', [status(thm)], ['29'])).
% 0.21/0.57  thf('31', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.57      inference('sup-', [status(thm)], ['25', '30'])).
% 0.21/0.57  thf(t12_xboole_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.21/0.57  thf('32', plain,
% 0.21/0.57      (![X21 : $i, X22 : $i]:
% 0.21/0.57         (((k2_xboole_0 @ X22 @ X21) = (X21)) | ~ (r1_tarski @ X22 @ X21))),
% 0.21/0.57      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.57  thf('33', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.57  thf('34', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['24', '33'])).
% 0.21/0.57  thf('35', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.21/0.57      inference('demod', [status(thm)], ['21', '34'])).
% 0.21/0.57  thf('36', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((k3_xboole_0 @ X1 @ X0)
% 0.21/0.57           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.21/0.57      inference('sup+', [status(thm)], ['3', '35'])).
% 0.21/0.57  thf('37', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 0.21/0.57           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['2', '36'])).
% 0.21/0.57  thf('38', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['16', '17'])).
% 0.21/0.57  thf('39', plain,
% 0.21/0.57      (![X30 : $i, X31 : $i]:
% 0.21/0.57         ((k2_xboole_0 @ X30 @ X31)
% 0.21/0.57           = (k5_xboole_0 @ X30 @ (k4_xboole_0 @ X31 @ X30)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.21/0.57  thf('40', plain,
% 0.21/0.57      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['38', '39'])).
% 0.21/0.57  thf('41', plain, (![X18 : $i]: ((k2_xboole_0 @ X18 @ X18) = (X18))),
% 0.21/0.57      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.21/0.57  thf('42', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.57      inference('demod', [status(thm)], ['40', '41'])).
% 0.21/0.57  thf('43', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.21/0.57      inference('demod', [status(thm)], ['37', '42'])).
% 0.21/0.57  thf('44', plain,
% 0.21/0.57      (![X3 : $i, X5 : $i]:
% 0.21/0.57         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.57  thf('45', plain,
% 0.21/0.57      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X10 @ X9)
% 0.21/0.57          | (r2_hidden @ X10 @ X8)
% 0.21/0.57          | ((X9) != (k3_xboole_0 @ X7 @ X8)))),
% 0.21/0.57      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.21/0.57  thf('46', plain,
% 0.21/0.57      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.21/0.57         ((r2_hidden @ X10 @ X8)
% 0.21/0.57          | ~ (r2_hidden @ X10 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['45'])).
% 0.21/0.57  thf('47', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.21/0.57          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['44', '46'])).
% 0.21/0.57  thf('48', plain,
% 0.21/0.57      (![X3 : $i, X5 : $i]:
% 0.21/0.57         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.57  thf('49', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.21/0.57          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.57  thf('50', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.21/0.57      inference('simplify', [status(thm)], ['49'])).
% 0.21/0.57  thf('51', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.57      inference('sup+', [status(thm)], ['43', '50'])).
% 0.21/0.57  thf('52', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         (r1_tarski @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['1', '51'])).
% 0.21/0.57  thf('53', plain,
% 0.21/0.57      (![X21 : $i, X22 : $i]:
% 0.21/0.57         (((k2_xboole_0 @ X22 @ X21) = (X21)) | ~ (r1_tarski @ X22 @ X21))),
% 0.21/0.57      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.57  thf('54', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.21/0.57           = (k2_tarski @ X1 @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.57  thf(t42_enumset1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.21/0.57       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.21/0.57  thf('55', plain,
% 0.21/0.57      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.21/0.57         ((k1_enumset1 @ X34 @ X35 @ X36)
% 0.21/0.57           = (k2_xboole_0 @ (k1_tarski @ X34) @ (k2_tarski @ X35 @ X36)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.21/0.57  thf('56', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((k1_enumset1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.21/0.57      inference('demod', [status(thm)], ['54', '55'])).
% 0.21/0.57  thf('57', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['0', '56'])).
% 0.21/0.57  thf('58', plain, ($false), inference('simplify', [status(thm)], ['57'])).
% 0.21/0.57  
% 0.21/0.57  % SZS output end Refutation
% 0.21/0.57  
% 0.21/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

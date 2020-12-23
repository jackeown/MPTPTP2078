%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lyCqZCUgQf

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:32 EST 2020

% Result     : Theorem 1.15s
% Output     : Refutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :  163 (1516 expanded)
%              Number of leaves         :   21 ( 492 expanded)
%              Depth                    :   34
%              Number of atoms          : 1467 (13899 expanded)
%              Number of equality atoms :  151 (1461 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('8',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X15: $i,X17: $i] :
      ( ( r1_xboole_0 @ X15 @ X17 )
      | ( ( k4_xboole_0 @ X15 @ X17 )
       != X15 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != X1 )
      | ( r1_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != X0 )
      | ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('14',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('17',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) @ k1_xboole_0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','20'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','20'])).

thf('33',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','20'])).

thf('35',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('37',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','39'])).

thf('41',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('44',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ X10 )
      | ( ( k3_xboole_0 @ X8 @ X10 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k4_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('51',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ( X21 = X18 )
      | ( X20
       != ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('52',plain,(
    ! [X18: $i,X21: $i] :
      ( ( X21 = X18 )
      | ~ ( r2_hidden @ X21 @ ( k1_tarski @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('55',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['53','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X15: $i,X17: $i] :
      ( ( r1_xboole_0 @ X15 @ X17 )
      | ( ( k4_xboole_0 @ X15 @ X17 )
       != X15 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf(t58_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
      | ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
        | ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t58_zfmisc_1])).

thf('65',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('68',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['66','68'])).

thf('70',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('71',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( X19 != X18 )
      | ( r2_hidden @ X19 @ X20 )
      | ( X20
       != ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('72',plain,(
    ! [X18: $i] :
      ( r2_hidden @ X18 @ ( k1_tarski @ X18 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      | ( r2_hidden @ X1 @ ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['70','74'])).

thf('76',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['69','77'])).

thf('79',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(l44_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('80',plain,(
    ! [X29: $i,X30: $i] :
      ( ( X29 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X30 @ X29 ) @ X29 )
      | ( X29
        = ( k1_tarski @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf('81',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('82',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('83',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['81','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['80','84'])).

thf('86',plain,(
    ! [X18: $i,X21: $i] :
      ( ( X21 = X18 )
      | ~ ( r2_hidden @ X21 @ ( k1_tarski @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C_1 @ X2 @ ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X29: $i,X30: $i] :
      ( ( X29 = k1_xboole_0 )
      | ( ( sk_C_1 @ X30 @ X29 )
       != X30 )
      | ( X29
        = ( k1_tarski @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 != X1 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X2 )
        = ( k1_tarski @ X1 ) )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X2 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X2 )
        = ( k1_tarski @ X1 ) )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X2 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X2 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X2 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('92',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('93',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('97',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['98','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['95','102'])).

thf('104',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 @ X2 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['91','105'])).

thf('107',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 @ X2 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( k1_tarski @ X0 ) @ X2 @ X2 ) @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['90','108'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('110',plain,(
    ! [X23: $i] :
      ( ( k2_tarski @ X23 @ X23 )
      = ( k1_tarski @ X23 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['95','102'])).

thf('112',plain,(
    ! [X23: $i] :
      ( ( k2_tarski @ X23 @ X23 )
      = ( k1_tarski @ X23 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('113',plain,(
    ! [X18: $i,X21: $i] :
      ( ( X21 = X18 )
      | ~ ( r2_hidden @ X21 @ ( k1_tarski @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_tarski @ X0 @ X0 )
        = k1_xboole_0 )
      | ( ( sk_D @ ( k2_tarski @ X0 @ X0 ) @ X1 @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['111','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 )
        = X0 )
      | ( ( k2_tarski @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['110','115'])).

thf('117',plain,(
    ! [X23: $i] :
      ( ( k2_tarski @ X23 @ X23 )
      = ( k1_tarski @ X23 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('118',plain,(
    ! [X18: $i] :
      ( r2_hidden @ X18 @ ( k1_tarski @ X18 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('119',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 )
        = X0 ) ) ),
    inference('sup+',[status(thm)],['116','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 )
      = X0 ) ),
    inference(clc,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['109','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['79','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['78','127'])).

thf('129',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['49','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('131',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('133',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('136',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['133','134','135'])).

thf('137',plain,(
    ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('139',plain,(
    ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['136','139'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lyCqZCUgQf
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:22:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.15/1.35  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.15/1.35  % Solved by: fo/fo7.sh
% 1.15/1.35  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.15/1.35  % done 1771 iterations in 0.891s
% 1.15/1.35  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.15/1.35  % SZS output start Refutation
% 1.15/1.35  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.15/1.35  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.15/1.35  thf(sk_A_type, type, sk_A: $i).
% 1.15/1.35  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.15/1.35  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.15/1.35  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.15/1.35  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.15/1.35  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.15/1.35  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.15/1.35  thf(sk_B_type, type, sk_B: $i).
% 1.15/1.35  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.15/1.35  thf(d5_xboole_0, axiom,
% 1.15/1.35    (![A:$i,B:$i,C:$i]:
% 1.15/1.35     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.15/1.35       ( ![D:$i]:
% 1.15/1.35         ( ( r2_hidden @ D @ C ) <=>
% 1.15/1.35           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.15/1.35  thf('0', plain,
% 1.15/1.35      (![X3 : $i, X4 : $i, X7 : $i]:
% 1.15/1.35         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 1.15/1.35          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 1.15/1.35          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 1.15/1.35      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.15/1.35  thf('1', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.15/1.35          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.15/1.35      inference('eq_fact', [status(thm)], ['0'])).
% 1.15/1.35  thf(t47_xboole_1, axiom,
% 1.15/1.35    (![A:$i,B:$i]:
% 1.15/1.35     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.15/1.35  thf('2', plain,
% 1.15/1.35      (![X11 : $i, X12 : $i]:
% 1.15/1.35         ((k4_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12))
% 1.15/1.35           = (k4_xboole_0 @ X11 @ X12))),
% 1.15/1.35      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.15/1.35  thf(t48_xboole_1, axiom,
% 1.15/1.35    (![A:$i,B:$i]:
% 1.15/1.35     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.15/1.35  thf('3', plain,
% 1.15/1.35      (![X13 : $i, X14 : $i]:
% 1.15/1.35         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.15/1.35           = (k3_xboole_0 @ X13 @ X14))),
% 1.15/1.35      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.15/1.35  thf('4', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 1.15/1.35           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.15/1.35      inference('sup+', [status(thm)], ['2', '3'])).
% 1.15/1.35  thf('5', plain,
% 1.15/1.35      (![X13 : $i, X14 : $i]:
% 1.15/1.35         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.15/1.35           = (k3_xboole_0 @ X13 @ X14))),
% 1.15/1.35      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.15/1.35  thf('6', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.15/1.35           = (k3_xboole_0 @ X1 @ X0))),
% 1.15/1.35      inference('sup+', [status(thm)], ['4', '5'])).
% 1.15/1.35  thf(commutativity_k3_xboole_0, axiom,
% 1.15/1.35    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.15/1.35  thf('7', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.15/1.35      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.15/1.35  thf('8', plain,
% 1.15/1.35      (![X13 : $i, X14 : $i]:
% 1.15/1.35         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.15/1.35           = (k3_xboole_0 @ X13 @ X14))),
% 1.15/1.35      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.15/1.35  thf(t83_xboole_1, axiom,
% 1.15/1.35    (![A:$i,B:$i]:
% 1.15/1.35     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.15/1.35  thf('9', plain,
% 1.15/1.35      (![X15 : $i, X17 : $i]:
% 1.15/1.35         ((r1_xboole_0 @ X15 @ X17) | ((k4_xboole_0 @ X15 @ X17) != (X15)))),
% 1.15/1.35      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.15/1.35  thf('10', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         (((k3_xboole_0 @ X1 @ X0) != (X1))
% 1.15/1.35          | (r1_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.15/1.35      inference('sup-', [status(thm)], ['8', '9'])).
% 1.15/1.35  thf('11', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         (((k3_xboole_0 @ X1 @ X0) != (X0))
% 1.15/1.35          | (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 1.15/1.35      inference('sup-', [status(thm)], ['7', '10'])).
% 1.15/1.35  thf('12', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         (((k3_xboole_0 @ X1 @ X0) != (k3_xboole_0 @ X1 @ X0))
% 1.15/1.35          | (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 1.15/1.35             (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)))),
% 1.15/1.35      inference('sup-', [status(thm)], ['6', '11'])).
% 1.15/1.35  thf('13', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 1.15/1.35          (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 1.15/1.35      inference('simplify', [status(thm)], ['12'])).
% 1.15/1.35  thf(d7_xboole_0, axiom,
% 1.15/1.35    (![A:$i,B:$i]:
% 1.15/1.35     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.15/1.35       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.15/1.35  thf('14', plain,
% 1.15/1.35      (![X8 : $i, X9 : $i]:
% 1.15/1.35         (((k3_xboole_0 @ X8 @ X9) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 1.15/1.35      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.15/1.35  thf('15', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ 
% 1.15/1.35           (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)) = (k1_xboole_0))),
% 1.15/1.35      inference('sup-', [status(thm)], ['13', '14'])).
% 1.15/1.35  thf('16', plain,
% 1.15/1.35      (![X13 : $i, X14 : $i]:
% 1.15/1.35         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.15/1.35           = (k3_xboole_0 @ X13 @ X14))),
% 1.15/1.35      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.15/1.35  thf('17', plain,
% 1.15/1.35      (![X13 : $i, X14 : $i]:
% 1.15/1.35         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.15/1.35           = (k3_xboole_0 @ X13 @ X14))),
% 1.15/1.35      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.15/1.35  thf('18', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.15/1.35           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.15/1.35      inference('sup+', [status(thm)], ['16', '17'])).
% 1.15/1.35  thf('19', plain,
% 1.15/1.35      (![X11 : $i, X12 : $i]:
% 1.15/1.35         ((k4_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12))
% 1.15/1.35           = (k4_xboole_0 @ X11 @ X12))),
% 1.15/1.35      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.15/1.35  thf('20', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 1.15/1.35           = (k4_xboole_0 @ X1 @ X0))),
% 1.15/1.35      inference('sup+', [status(thm)], ['18', '19'])).
% 1.15/1.35  thf('21', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 1.15/1.35      inference('demod', [status(thm)], ['15', '20'])).
% 1.15/1.35  thf('22', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 1.15/1.35           = (k4_xboole_0 @ X1 @ X0))),
% 1.15/1.35      inference('sup+', [status(thm)], ['18', '19'])).
% 1.15/1.35  thf('23', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.15/1.35      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.15/1.35  thf('24', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.15/1.35           = (k3_xboole_0 @ X1 @ X0))),
% 1.15/1.35      inference('sup+', [status(thm)], ['4', '5'])).
% 1.15/1.35  thf('25', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.15/1.35           = (k3_xboole_0 @ X0 @ X1))),
% 1.15/1.35      inference('sup+', [status(thm)], ['23', '24'])).
% 1.15/1.35  thf('26', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.15/1.35           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 1.15/1.35      inference('sup+', [status(thm)], ['22', '25'])).
% 1.15/1.35  thf('27', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.15/1.35      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.15/1.35  thf('28', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 1.15/1.35           = (k4_xboole_0 @ X1 @ X0))),
% 1.15/1.35      inference('sup+', [status(thm)], ['18', '19'])).
% 1.15/1.35  thf('29', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.15/1.35           = (k4_xboole_0 @ X1 @ X0))),
% 1.15/1.35      inference('demod', [status(thm)], ['26', '27', '28'])).
% 1.15/1.35  thf('30', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((k3_xboole_0 @ (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) @ 
% 1.15/1.35           k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 1.15/1.35      inference('sup+', [status(thm)], ['21', '29'])).
% 1.15/1.35  thf('31', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 1.15/1.35      inference('demod', [status(thm)], ['15', '20'])).
% 1.15/1.35  thf('32', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 1.15/1.35      inference('demod', [status(thm)], ['15', '20'])).
% 1.15/1.35  thf('33', plain,
% 1.15/1.35      (((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.15/1.35      inference('demod', [status(thm)], ['30', '31', '32'])).
% 1.15/1.35  thf('34', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 1.15/1.35      inference('demod', [status(thm)], ['15', '20'])).
% 1.15/1.35  thf('35', plain,
% 1.15/1.35      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.15/1.35      inference('sup+', [status(thm)], ['33', '34'])).
% 1.15/1.35  thf('36', plain,
% 1.15/1.35      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.15/1.35         (~ (r2_hidden @ X6 @ X5)
% 1.15/1.35          | ~ (r2_hidden @ X6 @ X4)
% 1.15/1.35          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 1.15/1.35      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.15/1.35  thf('37', plain,
% 1.15/1.35      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.15/1.35         (~ (r2_hidden @ X6 @ X4)
% 1.15/1.35          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 1.15/1.35      inference('simplify', [status(thm)], ['36'])).
% 1.15/1.35  thf('38', plain,
% 1.15/1.35      (![X0 : $i]:
% 1.15/1.35         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 1.15/1.35      inference('sup-', [status(thm)], ['35', '37'])).
% 1.15/1.35  thf('39', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.15/1.35      inference('simplify', [status(thm)], ['38'])).
% 1.15/1.35  thf('40', plain,
% 1.15/1.35      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.15/1.35      inference('sup-', [status(thm)], ['1', '39'])).
% 1.15/1.35  thf('41', plain,
% 1.15/1.35      (![X13 : $i, X14 : $i]:
% 1.15/1.35         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.15/1.35           = (k3_xboole_0 @ X13 @ X14))),
% 1.15/1.35      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.15/1.35  thf('42', plain,
% 1.15/1.35      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 1.15/1.35      inference('sup+', [status(thm)], ['40', '41'])).
% 1.15/1.35  thf('43', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.15/1.35      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.15/1.35  thf('44', plain,
% 1.15/1.35      (![X8 : $i, X10 : $i]:
% 1.15/1.35         ((r1_xboole_0 @ X8 @ X10)
% 1.15/1.35          | ((k3_xboole_0 @ X8 @ X10) != (k1_xboole_0)))),
% 1.15/1.35      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.15/1.35  thf('45', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 1.15/1.35      inference('sup-', [status(thm)], ['43', '44'])).
% 1.15/1.35  thf('46', plain,
% 1.15/1.35      (![X0 : $i]:
% 1.15/1.35         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 1.15/1.35      inference('sup-', [status(thm)], ['42', '45'])).
% 1.15/1.35  thf('47', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.15/1.35      inference('simplify', [status(thm)], ['46'])).
% 1.15/1.35  thf('48', plain,
% 1.15/1.35      (![X15 : $i, X16 : $i]:
% 1.15/1.35         (((k4_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_xboole_0 @ X15 @ X16))),
% 1.15/1.35      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.15/1.35  thf('49', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.15/1.35      inference('sup-', [status(thm)], ['47', '48'])).
% 1.15/1.35  thf('50', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.15/1.35          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.15/1.35      inference('eq_fact', [status(thm)], ['0'])).
% 1.15/1.35  thf(d1_tarski, axiom,
% 1.15/1.35    (![A:$i,B:$i]:
% 1.15/1.35     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.15/1.35       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.15/1.35  thf('51', plain,
% 1.15/1.35      (![X18 : $i, X20 : $i, X21 : $i]:
% 1.15/1.35         (~ (r2_hidden @ X21 @ X20)
% 1.15/1.35          | ((X21) = (X18))
% 1.15/1.35          | ((X20) != (k1_tarski @ X18)))),
% 1.15/1.35      inference('cnf', [status(esa)], [d1_tarski])).
% 1.15/1.35  thf('52', plain,
% 1.15/1.35      (![X18 : $i, X21 : $i]:
% 1.15/1.35         (((X21) = (X18)) | ~ (r2_hidden @ X21 @ (k1_tarski @ X18)))),
% 1.15/1.35      inference('simplify', [status(thm)], ['51'])).
% 1.15/1.35  thf('53', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         (((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 1.15/1.35          | ((sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 1.15/1.35      inference('sup-', [status(thm)], ['50', '52'])).
% 1.15/1.35  thf('54', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.15/1.35          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.15/1.35      inference('eq_fact', [status(thm)], ['0'])).
% 1.15/1.35  thf('55', plain,
% 1.15/1.35      (![X3 : $i, X4 : $i, X7 : $i]:
% 1.15/1.35         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 1.15/1.35          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 1.15/1.35          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 1.15/1.35          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 1.15/1.35      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.15/1.35  thf('56', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 1.15/1.35          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.15/1.35          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 1.15/1.35          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.15/1.35      inference('sup-', [status(thm)], ['54', '55'])).
% 1.15/1.35  thf('57', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 1.15/1.35          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.15/1.35          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.15/1.35      inference('simplify', [status(thm)], ['56'])).
% 1.15/1.35  thf('58', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.15/1.35          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.15/1.35      inference('eq_fact', [status(thm)], ['0'])).
% 1.15/1.35  thf('59', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 1.15/1.35          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 1.15/1.35      inference('clc', [status(thm)], ['57', '58'])).
% 1.15/1.35  thf('60', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((r2_hidden @ X0 @ X1)
% 1.15/1.35          | ((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 1.15/1.35          | ((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 1.15/1.35      inference('sup+', [status(thm)], ['53', '59'])).
% 1.15/1.35  thf('61', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         (((k1_tarski @ X0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 1.15/1.35          | (r2_hidden @ X0 @ X1))),
% 1.15/1.35      inference('simplify', [status(thm)], ['60'])).
% 1.15/1.35  thf('62', plain,
% 1.15/1.35      (![X15 : $i, X17 : $i]:
% 1.15/1.35         ((r1_xboole_0 @ X15 @ X17) | ((k4_xboole_0 @ X15 @ X17) != (X15)))),
% 1.15/1.35      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.15/1.35  thf('63', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 1.15/1.35          | (r2_hidden @ X0 @ X1)
% 1.15/1.35          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 1.15/1.35      inference('sup-', [status(thm)], ['61', '62'])).
% 1.15/1.35  thf('64', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 1.15/1.35      inference('simplify', [status(thm)], ['63'])).
% 1.15/1.35  thf(t58_zfmisc_1, conjecture,
% 1.15/1.35    (![A:$i,B:$i]:
% 1.15/1.35     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 1.15/1.35       ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 1.15/1.35  thf(zf_stmt_0, negated_conjecture,
% 1.15/1.35    (~( ![A:$i,B:$i]:
% 1.15/1.35        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 1.15/1.35          ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )),
% 1.15/1.35    inference('cnf.neg', [status(esa)], [t58_zfmisc_1])).
% 1.15/1.35  thf('65', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('66', plain, ((r2_hidden @ sk_A @ sk_B)),
% 1.15/1.35      inference('sup-', [status(thm)], ['64', '65'])).
% 1.15/1.35  thf('67', plain,
% 1.15/1.35      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.15/1.35         (~ (r2_hidden @ X2 @ X3)
% 1.15/1.35          | (r2_hidden @ X2 @ X4)
% 1.15/1.35          | (r2_hidden @ X2 @ X5)
% 1.15/1.35          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 1.15/1.35      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.15/1.35  thf('68', plain,
% 1.15/1.35      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.15/1.35         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 1.15/1.35          | (r2_hidden @ X2 @ X4)
% 1.15/1.35          | ~ (r2_hidden @ X2 @ X3))),
% 1.15/1.35      inference('simplify', [status(thm)], ['67'])).
% 1.15/1.35  thf('69', plain,
% 1.15/1.35      (![X0 : $i]:
% 1.15/1.35         ((r2_hidden @ sk_A @ X0)
% 1.15/1.35          | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ X0)))),
% 1.15/1.35      inference('sup-', [status(thm)], ['66', '68'])).
% 1.15/1.35  thf('70', plain,
% 1.15/1.35      (![X11 : $i, X12 : $i]:
% 1.15/1.35         ((k4_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12))
% 1.15/1.35           = (k4_xboole_0 @ X11 @ X12))),
% 1.15/1.35      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.15/1.35  thf('71', plain,
% 1.15/1.35      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.15/1.35         (((X19) != (X18))
% 1.15/1.35          | (r2_hidden @ X19 @ X20)
% 1.15/1.35          | ((X20) != (k1_tarski @ X18)))),
% 1.15/1.35      inference('cnf', [status(esa)], [d1_tarski])).
% 1.15/1.35  thf('72', plain, (![X18 : $i]: (r2_hidden @ X18 @ (k1_tarski @ X18))),
% 1.15/1.35      inference('simplify', [status(thm)], ['71'])).
% 1.15/1.35  thf('73', plain,
% 1.15/1.35      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.15/1.35         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 1.15/1.35          | (r2_hidden @ X2 @ X4)
% 1.15/1.35          | ~ (r2_hidden @ X2 @ X3))),
% 1.15/1.35      inference('simplify', [status(thm)], ['67'])).
% 1.15/1.35  thf('74', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((r2_hidden @ X0 @ X1)
% 1.15/1.35          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 1.15/1.35      inference('sup-', [status(thm)], ['72', '73'])).
% 1.15/1.35  thf('75', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((r2_hidden @ X1 @ (k4_xboole_0 @ (k1_tarski @ X1) @ X0))
% 1.15/1.35          | (r2_hidden @ X1 @ (k3_xboole_0 @ (k1_tarski @ X1) @ X0)))),
% 1.15/1.35      inference('sup+', [status(thm)], ['70', '74'])).
% 1.15/1.35  thf('76', plain,
% 1.15/1.35      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.15/1.35         (~ (r2_hidden @ X6 @ X4)
% 1.15/1.35          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 1.15/1.35      inference('simplify', [status(thm)], ['36'])).
% 1.15/1.35  thf('77', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]:
% 1.15/1.35         ((r2_hidden @ X1 @ (k3_xboole_0 @ (k1_tarski @ X1) @ X0))
% 1.15/1.35          | ~ (r2_hidden @ X1 @ X0))),
% 1.15/1.35      inference('sup-', [status(thm)], ['75', '76'])).
% 1.15/1.35  thf('78', plain,
% 1.15/1.35      (![X0 : $i]:
% 1.15/1.35         ((r2_hidden @ sk_A @ X0)
% 1.15/1.35          | (r2_hidden @ sk_A @ 
% 1.15/1.35             (k3_xboole_0 @ (k1_tarski @ sk_A) @ (k4_xboole_0 @ sk_B @ X0))))),
% 1.15/1.35      inference('sup-', [status(thm)], ['69', '77'])).
% 1.15/1.35  thf('79', plain,
% 1.15/1.35      (![X13 : $i, X14 : $i]:
% 1.15/1.35         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.15/1.35           = (k3_xboole_0 @ X13 @ X14))),
% 1.15/1.35      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.15/1.35  thf(l44_zfmisc_1, axiom,
% 1.15/1.35    (![A:$i,B:$i]:
% 1.15/1.35     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.15/1.35          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 1.15/1.35  thf('80', plain,
% 1.15/1.35      (![X29 : $i, X30 : $i]:
% 1.15/1.35         (((X29) = (k1_xboole_0))
% 1.15/1.35          | (r2_hidden @ (sk_C_1 @ X30 @ X29) @ X29)
% 1.15/1.35          | ((X29) = (k1_tarski @ X30)))),
% 1.15/1.35      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 1.15/1.35  thf('81', plain,
% 1.15/1.35      (![X13 : $i, X14 : $i]:
% 1.15/1.35         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.15/1.35           = (k3_xboole_0 @ X13 @ X14))),
% 1.15/1.35      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.15/1.35  thf('82', plain,
% 1.15/1.35      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.15/1.35         (~ (r2_hidden @ X6 @ X5)
% 1.15/1.35          | (r2_hidden @ X6 @ X3)
% 1.15/1.35          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 1.15/1.35      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.15/1.35  thf('83', plain,
% 1.15/1.35      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.15/1.35         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 1.15/1.36      inference('simplify', [status(thm)], ['82'])).
% 1.15/1.36  thf('84', plain,
% 1.15/1.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.36         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 1.15/1.36      inference('sup-', [status(thm)], ['81', '83'])).
% 1.15/1.36  thf('85', plain,
% 1.15/1.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.36         (((k3_xboole_0 @ X1 @ X0) = (k1_tarski @ X2))
% 1.15/1.36          | ((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 1.15/1.36          | (r2_hidden @ (sk_C_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X1))),
% 1.15/1.36      inference('sup-', [status(thm)], ['80', '84'])).
% 1.15/1.36  thf('86', plain,
% 1.15/1.36      (![X18 : $i, X21 : $i]:
% 1.15/1.36         (((X21) = (X18)) | ~ (r2_hidden @ X21 @ (k1_tarski @ X18)))),
% 1.15/1.36      inference('simplify', [status(thm)], ['51'])).
% 1.15/1.36  thf('87', plain,
% 1.15/1.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.36         (((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 1.15/1.36          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X2))
% 1.15/1.36          | ((sk_C_1 @ X2 @ (k3_xboole_0 @ (k1_tarski @ X0) @ X1)) = (X0)))),
% 1.15/1.36      inference('sup-', [status(thm)], ['85', '86'])).
% 1.15/1.36  thf('88', plain,
% 1.15/1.36      (![X29 : $i, X30 : $i]:
% 1.15/1.36         (((X29) = (k1_xboole_0))
% 1.15/1.36          | ((sk_C_1 @ X30 @ X29) != (X30))
% 1.15/1.36          | ((X29) = (k1_tarski @ X30)))),
% 1.15/1.36      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 1.15/1.36  thf('89', plain,
% 1.15/1.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.36         (((X0) != (X1))
% 1.15/1.36          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X2) = (k1_tarski @ X1))
% 1.15/1.36          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X2) = (k1_xboole_0))
% 1.15/1.36          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X2) = (k1_tarski @ X1))
% 1.15/1.36          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X2) = (k1_xboole_0)))),
% 1.15/1.36      inference('sup-', [status(thm)], ['87', '88'])).
% 1.15/1.36  thf('90', plain,
% 1.15/1.36      (![X1 : $i, X2 : $i]:
% 1.15/1.36         (((k3_xboole_0 @ (k1_tarski @ X1) @ X2) = (k1_xboole_0))
% 1.15/1.36          | ((k3_xboole_0 @ (k1_tarski @ X1) @ X2) = (k1_tarski @ X1)))),
% 1.15/1.36      inference('simplify', [status(thm)], ['89'])).
% 1.15/1.36  thf('91', plain,
% 1.15/1.36      (![X13 : $i, X14 : $i]:
% 1.15/1.36         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.15/1.36           = (k3_xboole_0 @ X13 @ X14))),
% 1.15/1.36      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.15/1.36  thf('92', plain,
% 1.15/1.36      (![X3 : $i, X4 : $i, X7 : $i]:
% 1.15/1.36         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 1.15/1.36          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 1.15/1.36          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 1.15/1.36      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.15/1.36  thf('93', plain,
% 1.15/1.36      (![X3 : $i, X4 : $i, X7 : $i]:
% 1.15/1.36         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 1.15/1.36          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 1.15/1.36          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 1.15/1.36      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.15/1.36  thf('94', plain,
% 1.15/1.36      (![X0 : $i, X1 : $i]:
% 1.15/1.36         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 1.15/1.36          | ((X1) = (k4_xboole_0 @ X0 @ X0))
% 1.15/1.36          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 1.15/1.36          | ((X1) = (k4_xboole_0 @ X0 @ X0)))),
% 1.15/1.36      inference('sup-', [status(thm)], ['92', '93'])).
% 1.15/1.36  thf('95', plain,
% 1.15/1.36      (![X0 : $i, X1 : $i]:
% 1.15/1.36         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 1.15/1.36          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 1.15/1.36      inference('simplify', [status(thm)], ['94'])).
% 1.15/1.36  thf('96', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.15/1.36      inference('sup-', [status(thm)], ['47', '48'])).
% 1.15/1.36  thf('97', plain,
% 1.15/1.36      (![X13 : $i, X14 : $i]:
% 1.15/1.36         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.15/1.36           = (k3_xboole_0 @ X13 @ X14))),
% 1.15/1.36      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.15/1.36  thf('98', plain,
% 1.15/1.36      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.15/1.36      inference('sup+', [status(thm)], ['96', '97'])).
% 1.15/1.36  thf('99', plain,
% 1.15/1.36      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 1.15/1.36      inference('sup+', [status(thm)], ['40', '41'])).
% 1.15/1.36  thf('100', plain,
% 1.15/1.36      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.15/1.36      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.15/1.36  thf('101', plain,
% 1.15/1.36      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.15/1.36      inference('sup+', [status(thm)], ['99', '100'])).
% 1.15/1.36  thf('102', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.15/1.36      inference('demod', [status(thm)], ['98', '101'])).
% 1.15/1.36  thf('103', plain,
% 1.15/1.36      (![X0 : $i, X1 : $i]:
% 1.15/1.36         (((X1) = (k1_xboole_0)) | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 1.15/1.36      inference('demod', [status(thm)], ['95', '102'])).
% 1.15/1.36  thf('104', plain,
% 1.15/1.36      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.15/1.36         (~ (r2_hidden @ X6 @ X4)
% 1.15/1.36          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 1.15/1.36      inference('simplify', [status(thm)], ['36'])).
% 1.15/1.36  thf('105', plain,
% 1.15/1.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.36         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 1.15/1.36          | ~ (r2_hidden @ (sk_D @ (k4_xboole_0 @ X1 @ X0) @ X2 @ X2) @ X0))),
% 1.15/1.36      inference('sup-', [status(thm)], ['103', '104'])).
% 1.15/1.36  thf('106', plain,
% 1.15/1.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.36         (~ (r2_hidden @ (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X2 @ X2) @ 
% 1.15/1.36             (k4_xboole_0 @ X1 @ X0))
% 1.15/1.36          | ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0)))),
% 1.15/1.36      inference('sup-', [status(thm)], ['91', '105'])).
% 1.15/1.36  thf('107', plain,
% 1.15/1.36      (![X13 : $i, X14 : $i]:
% 1.15/1.36         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.15/1.36           = (k3_xboole_0 @ X13 @ X14))),
% 1.15/1.36      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.15/1.36  thf('108', plain,
% 1.15/1.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.36         (~ (r2_hidden @ (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X2 @ X2) @ 
% 1.15/1.36             (k4_xboole_0 @ X1 @ X0))
% 1.15/1.36          | ((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)))),
% 1.15/1.36      inference('demod', [status(thm)], ['106', '107'])).
% 1.15/1.36  thf('109', plain,
% 1.15/1.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.36         (~ (r2_hidden @ (sk_D @ (k1_tarski @ X0) @ X2 @ X2) @ 
% 1.15/1.36             (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 1.15/1.36          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 1.15/1.36          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0)))),
% 1.15/1.36      inference('sup-', [status(thm)], ['90', '108'])).
% 1.15/1.36  thf(t69_enumset1, axiom,
% 1.15/1.36    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.15/1.36  thf('110', plain,
% 1.15/1.36      (![X23 : $i]: ((k2_tarski @ X23 @ X23) = (k1_tarski @ X23))),
% 1.15/1.36      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.15/1.36  thf('111', plain,
% 1.15/1.36      (![X0 : $i, X1 : $i]:
% 1.15/1.36         (((X1) = (k1_xboole_0)) | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 1.15/1.36      inference('demod', [status(thm)], ['95', '102'])).
% 1.15/1.36  thf('112', plain,
% 1.15/1.36      (![X23 : $i]: ((k2_tarski @ X23 @ X23) = (k1_tarski @ X23))),
% 1.15/1.36      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.15/1.36  thf('113', plain,
% 1.15/1.36      (![X18 : $i, X21 : $i]:
% 1.15/1.36         (((X21) = (X18)) | ~ (r2_hidden @ X21 @ (k1_tarski @ X18)))),
% 1.15/1.36      inference('simplify', [status(thm)], ['51'])).
% 1.15/1.36  thf('114', plain,
% 1.15/1.36      (![X0 : $i, X1 : $i]:
% 1.15/1.36         (~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0)) | ((X1) = (X0)))),
% 1.15/1.36      inference('sup-', [status(thm)], ['112', '113'])).
% 1.15/1.36  thf('115', plain,
% 1.15/1.36      (![X0 : $i, X1 : $i]:
% 1.15/1.36         (((k2_tarski @ X0 @ X0) = (k1_xboole_0))
% 1.15/1.36          | ((sk_D @ (k2_tarski @ X0 @ X0) @ X1 @ X1) = (X0)))),
% 1.15/1.36      inference('sup-', [status(thm)], ['111', '114'])).
% 1.15/1.36  thf('116', plain,
% 1.15/1.36      (![X0 : $i, X1 : $i]:
% 1.15/1.36         (((sk_D @ (k1_tarski @ X0) @ X1 @ X1) = (X0))
% 1.15/1.36          | ((k2_tarski @ X0 @ X0) = (k1_xboole_0)))),
% 1.15/1.36      inference('sup+', [status(thm)], ['110', '115'])).
% 1.15/1.36  thf('117', plain,
% 1.15/1.36      (![X23 : $i]: ((k2_tarski @ X23 @ X23) = (k1_tarski @ X23))),
% 1.15/1.36      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.15/1.36  thf('118', plain, (![X18 : $i]: (r2_hidden @ X18 @ (k1_tarski @ X18))),
% 1.15/1.36      inference('simplify', [status(thm)], ['71'])).
% 1.15/1.36  thf('119', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X0))),
% 1.15/1.36      inference('sup+', [status(thm)], ['117', '118'])).
% 1.15/1.36  thf('120', plain,
% 1.15/1.36      (![X0 : $i, X1 : $i]:
% 1.15/1.36         ((r2_hidden @ X0 @ k1_xboole_0)
% 1.15/1.36          | ((sk_D @ (k1_tarski @ X0) @ X1 @ X1) = (X0)))),
% 1.15/1.36      inference('sup+', [status(thm)], ['116', '119'])).
% 1.15/1.36  thf('121', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.15/1.36      inference('simplify', [status(thm)], ['38'])).
% 1.15/1.36  thf('122', plain,
% 1.15/1.36      (![X0 : $i, X1 : $i]: ((sk_D @ (k1_tarski @ X0) @ X1 @ X1) = (X0))),
% 1.15/1.36      inference('clc', [status(thm)], ['120', '121'])).
% 1.15/1.36  thf('123', plain,
% 1.15/1.36      (![X0 : $i, X1 : $i]:
% 1.15/1.36         (~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 1.15/1.36          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 1.15/1.36          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0)))),
% 1.15/1.36      inference('demod', [status(thm)], ['109', '122'])).
% 1.15/1.36  thf('124', plain,
% 1.15/1.36      (![X0 : $i, X1 : $i]:
% 1.15/1.36         (((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 1.15/1.36          | ~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 1.15/1.36      inference('simplify', [status(thm)], ['123'])).
% 1.15/1.36  thf('125', plain,
% 1.15/1.36      (![X0 : $i, X1 : $i]:
% 1.15/1.36         (~ (r2_hidden @ X1 @ (k3_xboole_0 @ (k1_tarski @ X1) @ X0))
% 1.15/1.36          | ((k3_xboole_0 @ (k1_tarski @ X1) @ 
% 1.15/1.36              (k4_xboole_0 @ (k1_tarski @ X1) @ X0)) = (k1_xboole_0)))),
% 1.15/1.36      inference('sup-', [status(thm)], ['79', '124'])).
% 1.15/1.36  thf('126', plain,
% 1.15/1.36      (![X0 : $i, X1 : $i]:
% 1.15/1.36         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 1.15/1.36           = (k4_xboole_0 @ X1 @ X0))),
% 1.15/1.36      inference('sup+', [status(thm)], ['18', '19'])).
% 1.15/1.36  thf('127', plain,
% 1.15/1.36      (![X0 : $i, X1 : $i]:
% 1.15/1.36         (~ (r2_hidden @ X1 @ (k3_xboole_0 @ (k1_tarski @ X1) @ X0))
% 1.15/1.36          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0)))),
% 1.15/1.36      inference('demod', [status(thm)], ['125', '126'])).
% 1.15/1.36  thf('128', plain,
% 1.15/1.36      (![X0 : $i]:
% 1.15/1.36         ((r2_hidden @ sk_A @ X0)
% 1.15/1.36          | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k4_xboole_0 @ sk_B @ X0))
% 1.15/1.36              = (k1_xboole_0)))),
% 1.15/1.36      inference('sup-', [status(thm)], ['78', '127'])).
% 1.15/1.36  thf('129', plain,
% 1.15/1.36      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))
% 1.15/1.36        | (r2_hidden @ sk_A @ k1_xboole_0))),
% 1.15/1.36      inference('sup+', [status(thm)], ['49', '128'])).
% 1.15/1.36  thf('130', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.15/1.36      inference('simplify', [status(thm)], ['38'])).
% 1.15/1.36  thf('131', plain,
% 1.15/1.36      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 1.15/1.36      inference('clc', [status(thm)], ['129', '130'])).
% 1.15/1.36  thf('132', plain,
% 1.15/1.36      (![X13 : $i, X14 : $i]:
% 1.15/1.36         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.15/1.36           = (k3_xboole_0 @ X13 @ X14))),
% 1.15/1.36      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.15/1.36  thf('133', plain,
% 1.15/1.36      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0)
% 1.15/1.36         = (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 1.15/1.36      inference('sup+', [status(thm)], ['131', '132'])).
% 1.15/1.36  thf('134', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.15/1.36      inference('sup-', [status(thm)], ['47', '48'])).
% 1.15/1.36  thf('135', plain,
% 1.15/1.36      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.15/1.36      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.15/1.36  thf('136', plain,
% 1.15/1.36      (((k1_tarski @ sk_A) = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 1.15/1.36      inference('demod', [status(thm)], ['133', '134', '135'])).
% 1.15/1.36  thf('137', plain,
% 1.15/1.36      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 1.15/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.36  thf('138', plain,
% 1.15/1.36      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.15/1.36      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.15/1.36  thf('139', plain,
% 1.15/1.36      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (k1_tarski @ sk_A))),
% 1.15/1.36      inference('demod', [status(thm)], ['137', '138'])).
% 1.15/1.36  thf('140', plain, ($false),
% 1.15/1.36      inference('simplify_reflect-', [status(thm)], ['136', '139'])).
% 1.15/1.36  
% 1.15/1.36  % SZS output end Refutation
% 1.15/1.36  
% 1.15/1.36  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

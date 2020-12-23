%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.b5pK2dpap7

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:48 EST 2020

% Result     : Theorem 0.62s
% Output     : Refutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 741 expanded)
%              Number of leaves         :   27 ( 221 expanded)
%              Depth                    :   24
%              Number of atoms          :  877 (6997 expanded)
%              Number of equality atoms :   93 ( 738 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('0',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X17 != X16 )
      | ( r2_hidden @ X17 @ X18 )
      | ( X18
       != ( k2_tarski @ X19 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('1',plain,(
    ! [X16: $i,X19: $i] :
      ( r2_hidden @ X16 @ ( k2_tarski @ X19 @ X16 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('2',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k2_enumset1 @ X34 @ X34 @ X35 @ X36 )
      = ( k1_enumset1 @ X34 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_enumset1 @ X32 @ X32 @ X33 )
      = ( k2_tarski @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_enumset1 @ X32 @ X32 @ X33 )
      = ( k2_tarski @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('6',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( k2_enumset1 @ X22 @ X23 @ X24 @ X25 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X22 @ X23 @ X24 ) @ ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('9',plain,(
    ! [X31: $i] :
      ( ( k2_tarski @ X31 @ X31 )
      = ( k1_tarski @ X31 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('11',plain,(
    ! [X43: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf(t10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) )
         != ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) )).

thf('12',plain,(
    ! [X41: $i,X42: $i] :
      ( ( X41 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( k2_xboole_0 @ X41 @ X42 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X41 ) @ ( k1_setfam_1 @ X42 ) ) )
      | ( X42 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t10_setfam_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X1 ) @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ ( k1_tarski @ X1 ) ) @ X0 ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X43: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t12_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
        = ( k3_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_setfam_1])).

thf('17',plain,(
    ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
     != ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X31: $i] :
      ( ( k2_tarski @ X31 @ X31 )
      = ( k1_tarski @ X31 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('21',plain,(
    ! [X16: $i,X19: $i] :
      ( r2_hidden @ X16 @ ( k2_tarski @ X19 @ X16 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

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

thf('23',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('27',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('28',plain,(
    ! [X31: $i] :
      ( ( k2_tarski @ X31 @ X31 )
      = ( k1_tarski @ X31 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('29',plain,(
    ! [X16: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X20 @ X18 )
      | ( X20 = X19 )
      | ( X20 = X16 )
      | ( X18
       != ( k2_tarski @ X19 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('30',plain,(
    ! [X16: $i,X19: $i,X20: $i] :
      ( ( X20 = X16 )
      | ( X20 = X19 )
      | ~ ( r2_hidden @ X20 @ ( k2_tarski @ X19 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('40',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('45',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k3_xboole_0 @ X7 @ X10 ) )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ k1_xboole_0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
      | ~ ( r2_hidden @ X2 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X2 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X1 = X2 ) ) ),
    inference('sup-',[status(thm)],['26','49'])).

thf('51',plain,(
    ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
       != ( k3_xboole_0 @ sk_A @ sk_B ) )
      | ( r1_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X1 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['25','53'])).

thf('55',plain,(
    ! [X16: $i,X19: $i] :
      ( r2_hidden @ X16 @ ( k2_tarski @ X19 @ X16 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('56',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('57',plain,(
    ! [X43: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('58',plain,
    ( ( ( k1_setfam_1 @ k1_xboole_0 )
      = sk_B )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( ( k1_setfam_1 @ k1_xboole_0 )
        = sk_B )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X1 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( ( k1_setfam_1 @ k1_xboole_0 )
        = sk_B )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k1_setfam_1 @ k1_xboole_0 )
    = sk_B ),
    inference('sup-',[status(thm)],['55','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( k1_setfam_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['54','63'])).

thf('65',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('67',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X1 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('68',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('69',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('70',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','73'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('75',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('77',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','73'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['78','81'])).

thf('83',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('86',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k3_xboole_0 @ X7 @ X10 ) )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','88'])).

thf('90',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','89'])).

thf('91',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','64'])).

thf('92',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X1 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('93',plain,(
    $false ),
    inference(demod,[status(thm)],['90','91','92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.b5pK2dpap7
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:27:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.62/0.81  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.62/0.81  % Solved by: fo/fo7.sh
% 0.62/0.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.62/0.81  % done 610 iterations in 0.350s
% 0.62/0.81  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.62/0.81  % SZS output start Refutation
% 0.62/0.81  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.62/0.81  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.62/0.81  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.62/0.81  thf(sk_B_type, type, sk_B: $i).
% 0.62/0.81  thf(sk_A_type, type, sk_A: $i).
% 0.62/0.81  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.62/0.81  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.62/0.81  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.62/0.81  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.62/0.81  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.62/0.81  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.62/0.81  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.62/0.81  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.62/0.81  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.62/0.81  thf(d2_tarski, axiom,
% 0.62/0.81    (![A:$i,B:$i,C:$i]:
% 0.62/0.81     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.62/0.81       ( ![D:$i]:
% 0.62/0.81         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.62/0.81  thf('0', plain,
% 0.62/0.81      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.62/0.81         (((X17) != (X16))
% 0.62/0.81          | (r2_hidden @ X17 @ X18)
% 0.62/0.81          | ((X18) != (k2_tarski @ X19 @ X16)))),
% 0.62/0.81      inference('cnf', [status(esa)], [d2_tarski])).
% 0.62/0.81  thf('1', plain,
% 0.62/0.81      (![X16 : $i, X19 : $i]: (r2_hidden @ X16 @ (k2_tarski @ X19 @ X16))),
% 0.62/0.81      inference('simplify', [status(thm)], ['0'])).
% 0.62/0.81  thf(t71_enumset1, axiom,
% 0.62/0.81    (![A:$i,B:$i,C:$i]:
% 0.62/0.81     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.62/0.81  thf('2', plain,
% 0.62/0.81      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.62/0.81         ((k2_enumset1 @ X34 @ X34 @ X35 @ X36)
% 0.62/0.81           = (k1_enumset1 @ X34 @ X35 @ X36))),
% 0.62/0.81      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.62/0.81  thf(t70_enumset1, axiom,
% 0.62/0.81    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.62/0.81  thf('3', plain,
% 0.62/0.81      (![X32 : $i, X33 : $i]:
% 0.62/0.81         ((k1_enumset1 @ X32 @ X32 @ X33) = (k2_tarski @ X32 @ X33))),
% 0.62/0.81      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.62/0.81  thf('4', plain,
% 0.62/0.81      (![X0 : $i, X1 : $i]:
% 0.62/0.81         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.62/0.81      inference('sup+', [status(thm)], ['2', '3'])).
% 0.62/0.81  thf('5', plain,
% 0.62/0.81      (![X32 : $i, X33 : $i]:
% 0.62/0.81         ((k1_enumset1 @ X32 @ X32 @ X33) = (k2_tarski @ X32 @ X33))),
% 0.62/0.81      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.62/0.81  thf(t46_enumset1, axiom,
% 0.62/0.81    (![A:$i,B:$i,C:$i,D:$i]:
% 0.62/0.81     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.62/0.81       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.62/0.81  thf('6', plain,
% 0.62/0.81      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.62/0.81         ((k2_enumset1 @ X22 @ X23 @ X24 @ X25)
% 0.62/0.81           = (k2_xboole_0 @ (k1_enumset1 @ X22 @ X23 @ X24) @ (k1_tarski @ X25)))),
% 0.62/0.81      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.62/0.81  thf('7', plain,
% 0.62/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.81         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.62/0.81           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.62/0.81      inference('sup+', [status(thm)], ['5', '6'])).
% 0.62/0.81  thf('8', plain,
% 0.62/0.81      (![X0 : $i, X1 : $i]:
% 0.62/0.81         ((k2_tarski @ X1 @ X0)
% 0.62/0.81           = (k2_xboole_0 @ (k2_tarski @ X1 @ X1) @ (k1_tarski @ X0)))),
% 0.62/0.81      inference('sup+', [status(thm)], ['4', '7'])).
% 0.62/0.81  thf(t69_enumset1, axiom,
% 0.62/0.81    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.62/0.81  thf('9', plain, (![X31 : $i]: ((k2_tarski @ X31 @ X31) = (k1_tarski @ X31))),
% 0.62/0.81      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.62/0.81  thf('10', plain,
% 0.62/0.81      (![X0 : $i, X1 : $i]:
% 0.62/0.81         ((k2_tarski @ X1 @ X0)
% 0.62/0.81           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.62/0.81      inference('demod', [status(thm)], ['8', '9'])).
% 0.62/0.81  thf(t11_setfam_1, axiom,
% 0.62/0.81    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.62/0.81  thf('11', plain, (![X43 : $i]: ((k1_setfam_1 @ (k1_tarski @ X43)) = (X43))),
% 0.62/0.81      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.62/0.81  thf(t10_setfam_1, axiom,
% 0.62/0.81    (![A:$i,B:$i]:
% 0.62/0.81     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.62/0.81          ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) ) !=
% 0.62/0.81            ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) ))).
% 0.62/0.81  thf('12', plain,
% 0.62/0.81      (![X41 : $i, X42 : $i]:
% 0.62/0.81         (((X41) = (k1_xboole_0))
% 0.62/0.81          | ((k1_setfam_1 @ (k2_xboole_0 @ X41 @ X42))
% 0.62/0.81              = (k3_xboole_0 @ (k1_setfam_1 @ X41) @ (k1_setfam_1 @ X42)))
% 0.62/0.81          | ((X42) = (k1_xboole_0)))),
% 0.62/0.81      inference('cnf', [status(esa)], [t10_setfam_1])).
% 0.62/0.81  thf('13', plain,
% 0.62/0.81      (![X0 : $i, X1 : $i]:
% 0.62/0.81         (((k1_setfam_1 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.62/0.81            = (k3_xboole_0 @ (k1_setfam_1 @ X1) @ X0))
% 0.62/0.81          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.62/0.81          | ((X1) = (k1_xboole_0)))),
% 0.62/0.81      inference('sup+', [status(thm)], ['11', '12'])).
% 0.62/0.81  thf('14', plain,
% 0.62/0.81      (![X0 : $i, X1 : $i]:
% 0.62/0.81         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.62/0.81            = (k3_xboole_0 @ (k1_setfam_1 @ (k1_tarski @ X1)) @ X0))
% 0.62/0.81          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.62/0.81          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.62/0.81      inference('sup+', [status(thm)], ['10', '13'])).
% 0.62/0.81  thf('15', plain, (![X43 : $i]: ((k1_setfam_1 @ (k1_tarski @ X43)) = (X43))),
% 0.62/0.81      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.62/0.81  thf('16', plain,
% 0.62/0.81      (![X0 : $i, X1 : $i]:
% 0.62/0.81         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))
% 0.62/0.81          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.62/0.81          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.62/0.81      inference('demod', [status(thm)], ['14', '15'])).
% 0.62/0.81  thf(t12_setfam_1, conjecture,
% 0.62/0.81    (![A:$i,B:$i]:
% 0.62/0.81     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.62/0.81  thf(zf_stmt_0, negated_conjecture,
% 0.62/0.81    (~( ![A:$i,B:$i]:
% 0.62/0.81        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ) )),
% 0.62/0.81    inference('cnf.neg', [status(esa)], [t12_setfam_1])).
% 0.62/0.81  thf('17', plain,
% 0.62/0.81      (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.62/0.81         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.62/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.81  thf('18', plain,
% 0.62/0.81      ((((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))
% 0.62/0.81        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.62/0.81        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.62/0.81      inference('sup-', [status(thm)], ['16', '17'])).
% 0.62/0.81  thf('19', plain,
% 0.62/0.81      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.62/0.81        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.62/0.81      inference('simplify', [status(thm)], ['18'])).
% 0.62/0.81  thf('20', plain,
% 0.62/0.81      (![X31 : $i]: ((k2_tarski @ X31 @ X31) = (k1_tarski @ X31))),
% 0.62/0.81      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.62/0.81  thf('21', plain,
% 0.62/0.81      (![X16 : $i, X19 : $i]: (r2_hidden @ X16 @ (k2_tarski @ X19 @ X16))),
% 0.62/0.81      inference('simplify', [status(thm)], ['0'])).
% 0.62/0.81  thf('22', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.62/0.81      inference('sup+', [status(thm)], ['20', '21'])).
% 0.62/0.81  thf(t3_xboole_0, axiom,
% 0.62/0.81    (![A:$i,B:$i]:
% 0.62/0.81     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.62/0.81            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.62/0.81       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.62/0.81            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.62/0.81  thf('23', plain,
% 0.62/0.81      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.62/0.81         (~ (r2_hidden @ X5 @ X3)
% 0.62/0.81          | ~ (r2_hidden @ X5 @ X6)
% 0.62/0.81          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.62/0.81      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.62/0.81  thf('24', plain,
% 0.62/0.81      (![X0 : $i, X1 : $i]:
% 0.62/0.81         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.62/0.81      inference('sup-', [status(thm)], ['22', '23'])).
% 0.62/0.81  thf('25', plain,
% 0.62/0.81      (![X0 : $i]:
% 0.62/0.81         (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.62/0.81          | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.62/0.81          | ~ (r2_hidden @ sk_B @ X0))),
% 0.62/0.81      inference('sup-', [status(thm)], ['19', '24'])).
% 0.62/0.81  thf('26', plain,
% 0.62/0.81      (![X3 : $i, X4 : $i]:
% 0.62/0.81         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.62/0.81      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.62/0.81  thf('27', plain,
% 0.62/0.81      (![X3 : $i, X4 : $i]:
% 0.62/0.81         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.62/0.81      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.62/0.81  thf('28', plain,
% 0.62/0.81      (![X31 : $i]: ((k2_tarski @ X31 @ X31) = (k1_tarski @ X31))),
% 0.62/0.81      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.62/0.81  thf('29', plain,
% 0.62/0.81      (![X16 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.62/0.81         (~ (r2_hidden @ X20 @ X18)
% 0.62/0.81          | ((X20) = (X19))
% 0.62/0.81          | ((X20) = (X16))
% 0.62/0.81          | ((X18) != (k2_tarski @ X19 @ X16)))),
% 0.62/0.81      inference('cnf', [status(esa)], [d2_tarski])).
% 0.62/0.81  thf('30', plain,
% 0.62/0.81      (![X16 : $i, X19 : $i, X20 : $i]:
% 0.62/0.81         (((X20) = (X16))
% 0.62/0.81          | ((X20) = (X19))
% 0.62/0.81          | ~ (r2_hidden @ X20 @ (k2_tarski @ X19 @ X16)))),
% 0.62/0.81      inference('simplify', [status(thm)], ['29'])).
% 0.62/0.81  thf('31', plain,
% 0.62/0.81      (![X0 : $i, X1 : $i]:
% 0.62/0.81         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.62/0.81      inference('sup-', [status(thm)], ['28', '30'])).
% 0.62/0.81  thf('32', plain,
% 0.62/0.81      (![X0 : $i, X1 : $i]:
% 0.62/0.81         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.62/0.81      inference('simplify', [status(thm)], ['31'])).
% 0.62/0.81  thf('33', plain,
% 0.62/0.81      (![X0 : $i, X1 : $i]:
% 0.62/0.81         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.62/0.81          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.62/0.81      inference('sup-', [status(thm)], ['27', '32'])).
% 0.62/0.81  thf('34', plain,
% 0.62/0.81      (![X3 : $i, X4 : $i]:
% 0.62/0.81         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 0.62/0.81      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.62/0.81  thf('35', plain,
% 0.62/0.81      (![X0 : $i, X1 : $i]:
% 0.62/0.81         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.62/0.81      inference('simplify', [status(thm)], ['31'])).
% 0.62/0.81  thf('36', plain,
% 0.62/0.81      (![X0 : $i, X1 : $i]:
% 0.62/0.81         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.62/0.81          | ((sk_C @ (k1_tarski @ X0) @ X1) = (X0)))),
% 0.62/0.81      inference('sup-', [status(thm)], ['34', '35'])).
% 0.62/0.81  thf('37', plain,
% 0.62/0.81      (![X0 : $i, X1 : $i]:
% 0.62/0.81         (((X0) = (X1))
% 0.62/0.81          | (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.62/0.81          | (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.62/0.81      inference('sup+', [status(thm)], ['33', '36'])).
% 0.62/0.81  thf('38', plain,
% 0.62/0.81      (![X0 : $i, X1 : $i]:
% 0.62/0.81         ((r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)) | ((X0) = (X1)))),
% 0.62/0.81      inference('simplify', [status(thm)], ['37'])).
% 0.62/0.81  thf('39', plain,
% 0.62/0.81      (![X0 : $i, X1 : $i]:
% 0.62/0.81         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.62/0.81          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.62/0.81      inference('sup-', [status(thm)], ['27', '32'])).
% 0.62/0.81  thf('40', plain,
% 0.62/0.81      (![X3 : $i, X4 : $i]:
% 0.62/0.81         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 0.62/0.81      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.62/0.81  thf('41', plain,
% 0.62/0.81      (![X0 : $i, X1 : $i]:
% 0.62/0.81         ((r2_hidden @ X0 @ X1)
% 0.62/0.81          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.62/0.81          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.62/0.81      inference('sup+', [status(thm)], ['39', '40'])).
% 0.62/0.81  thf('42', plain,
% 0.62/0.81      (![X0 : $i, X1 : $i]:
% 0.62/0.81         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.62/0.81      inference('simplify', [status(thm)], ['41'])).
% 0.62/0.81  thf(d7_xboole_0, axiom,
% 0.62/0.81    (![A:$i,B:$i]:
% 0.62/0.81     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.62/0.81       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.62/0.81  thf('43', plain,
% 0.62/0.81      (![X0 : $i, X1 : $i]:
% 0.62/0.81         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.62/0.81      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.62/0.81  thf('44', plain,
% 0.62/0.81      (![X0 : $i, X1 : $i]:
% 0.62/0.81         ((r2_hidden @ X1 @ X0)
% 0.62/0.81          | ((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0)))),
% 0.62/0.81      inference('sup-', [status(thm)], ['42', '43'])).
% 0.62/0.81  thf(t4_xboole_0, axiom,
% 0.62/0.81    (![A:$i,B:$i]:
% 0.62/0.81     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.62/0.81            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.62/0.81       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.62/0.81            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.62/0.81  thf('45', plain,
% 0.62/0.81      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.62/0.81         (~ (r2_hidden @ X9 @ (k3_xboole_0 @ X7 @ X10))
% 0.62/0.81          | ~ (r1_xboole_0 @ X7 @ X10))),
% 0.62/0.81      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.62/0.81  thf('46', plain,
% 0.62/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.81         (~ (r2_hidden @ X2 @ k1_xboole_0)
% 0.62/0.81          | (r2_hidden @ X1 @ X0)
% 0.62/0.81          | ~ (r1_xboole_0 @ (k1_tarski @ X1) @ X0))),
% 0.62/0.81      inference('sup-', [status(thm)], ['44', '45'])).
% 0.62/0.81  thf('47', plain,
% 0.62/0.81      (![X0 : $i, X1 : $i]:
% 0.62/0.81         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.62/0.81      inference('sup-', [status(thm)], ['22', '23'])).
% 0.62/0.81  thf('48', plain,
% 0.62/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.81         (~ (r1_xboole_0 @ (k1_tarski @ X1) @ X0)
% 0.62/0.81          | ~ (r2_hidden @ X2 @ k1_xboole_0))),
% 0.62/0.81      inference('clc', [status(thm)], ['46', '47'])).
% 0.62/0.81  thf('49', plain,
% 0.62/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.81         (((X1) = (X0)) | ~ (r2_hidden @ X2 @ k1_xboole_0))),
% 0.62/0.81      inference('sup-', [status(thm)], ['38', '48'])).
% 0.62/0.81  thf('50', plain,
% 0.62/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.81         ((r1_xboole_0 @ k1_xboole_0 @ X0) | ((X1) = (X2)))),
% 0.62/0.81      inference('sup-', [status(thm)], ['26', '49'])).
% 0.62/0.81  thf('51', plain,
% 0.62/0.81      (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.62/0.81         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.62/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.81  thf('52', plain,
% 0.62/0.81      (![X0 : $i, X1 : $i]:
% 0.62/0.81         (((X0) != (k3_xboole_0 @ sk_A @ sk_B))
% 0.62/0.81          | (r1_xboole_0 @ k1_xboole_0 @ X1))),
% 0.62/0.81      inference('sup-', [status(thm)], ['50', '51'])).
% 0.62/0.81  thf('53', plain, (![X1 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X1)),
% 0.62/0.81      inference('simplify', [status(thm)], ['52'])).
% 0.62/0.81  thf('54', plain,
% 0.62/0.81      (![X0 : $i]:
% 0.62/0.81         (((k1_tarski @ sk_A) = (k1_xboole_0)) | ~ (r2_hidden @ sk_B @ X0))),
% 0.62/0.81      inference('demod', [status(thm)], ['25', '53'])).
% 0.62/0.81  thf('55', plain,
% 0.62/0.81      (![X16 : $i, X19 : $i]: (r2_hidden @ X16 @ (k2_tarski @ X19 @ X16))),
% 0.62/0.81      inference('simplify', [status(thm)], ['0'])).
% 0.62/0.81  thf('56', plain,
% 0.62/0.81      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.62/0.81        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.62/0.81      inference('simplify', [status(thm)], ['18'])).
% 0.62/0.81  thf('57', plain, (![X43 : $i]: ((k1_setfam_1 @ (k1_tarski @ X43)) = (X43))),
% 0.62/0.81      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.62/0.81  thf('58', plain,
% 0.62/0.81      ((((k1_setfam_1 @ k1_xboole_0) = (sk_B))
% 0.62/0.81        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.62/0.81      inference('sup+', [status(thm)], ['56', '57'])).
% 0.62/0.81  thf('59', plain,
% 0.62/0.81      (![X0 : $i, X1 : $i]:
% 0.62/0.81         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.62/0.81      inference('sup-', [status(thm)], ['22', '23'])).
% 0.62/0.81  thf('60', plain,
% 0.62/0.81      (![X0 : $i]:
% 0.62/0.81         (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.62/0.81          | ((k1_setfam_1 @ k1_xboole_0) = (sk_B))
% 0.62/0.81          | ~ (r2_hidden @ sk_A @ X0))),
% 0.62/0.81      inference('sup-', [status(thm)], ['58', '59'])).
% 0.62/0.81  thf('61', plain, (![X1 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X1)),
% 0.62/0.81      inference('simplify', [status(thm)], ['52'])).
% 0.62/0.81  thf('62', plain,
% 0.62/0.81      (![X0 : $i]:
% 0.62/0.81         (((k1_setfam_1 @ k1_xboole_0) = (sk_B)) | ~ (r2_hidden @ sk_A @ X0))),
% 0.62/0.81      inference('demod', [status(thm)], ['60', '61'])).
% 0.62/0.81  thf('63', plain, (((k1_setfam_1 @ k1_xboole_0) = (sk_B))),
% 0.62/0.81      inference('sup-', [status(thm)], ['55', '62'])).
% 0.62/0.81  thf('64', plain,
% 0.62/0.81      (![X0 : $i]:
% 0.62/0.81         (((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.62/0.81          | ~ (r2_hidden @ (k1_setfam_1 @ k1_xboole_0) @ X0))),
% 0.62/0.81      inference('demod', [status(thm)], ['54', '63'])).
% 0.62/0.81  thf('65', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.62/0.81      inference('sup-', [status(thm)], ['1', '64'])).
% 0.62/0.81  thf('66', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.62/0.81      inference('sup+', [status(thm)], ['20', '21'])).
% 0.62/0.81  thf('67', plain, (![X1 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X1)),
% 0.62/0.81      inference('simplify', [status(thm)], ['52'])).
% 0.62/0.81  thf('68', plain,
% 0.62/0.81      (![X3 : $i, X4 : $i]:
% 0.62/0.81         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.62/0.81      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.62/0.81  thf('69', plain,
% 0.62/0.81      (![X3 : $i, X4 : $i]:
% 0.62/0.81         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 0.62/0.81      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.62/0.81  thf('70', plain,
% 0.62/0.81      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.62/0.81         (~ (r2_hidden @ X5 @ X3)
% 0.62/0.81          | ~ (r2_hidden @ X5 @ X6)
% 0.62/0.81          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.62/0.81      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.62/0.81  thf('71', plain,
% 0.62/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.81         ((r1_xboole_0 @ X1 @ X0)
% 0.62/0.81          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.62/0.81          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.62/0.81      inference('sup-', [status(thm)], ['69', '70'])).
% 0.62/0.81  thf('72', plain,
% 0.62/0.81      (![X0 : $i, X1 : $i]:
% 0.62/0.81         ((r1_xboole_0 @ X0 @ X1)
% 0.62/0.81          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.62/0.81          | (r1_xboole_0 @ X0 @ X1))),
% 0.62/0.81      inference('sup-', [status(thm)], ['68', '71'])).
% 0.62/0.81  thf('73', plain,
% 0.62/0.81      (![X0 : $i, X1 : $i]:
% 0.62/0.81         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.62/0.81      inference('simplify', [status(thm)], ['72'])).
% 0.62/0.81  thf('74', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.62/0.81      inference('sup-', [status(thm)], ['67', '73'])).
% 0.62/0.81  thf(t83_xboole_1, axiom,
% 0.62/0.81    (![A:$i,B:$i]:
% 0.62/0.81     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.62/0.81  thf('75', plain,
% 0.62/0.81      (![X13 : $i, X14 : $i]:
% 0.62/0.81         (((k4_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_xboole_0 @ X13 @ X14))),
% 0.62/0.81      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.62/0.81  thf('76', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.62/0.81      inference('sup-', [status(thm)], ['74', '75'])).
% 0.62/0.81  thf(t48_xboole_1, axiom,
% 0.62/0.81    (![A:$i,B:$i]:
% 0.62/0.81     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.62/0.81  thf('77', plain,
% 0.62/0.81      (![X11 : $i, X12 : $i]:
% 0.62/0.81         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.62/0.81           = (k3_xboole_0 @ X11 @ X12))),
% 0.62/0.81      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.62/0.81  thf('78', plain,
% 0.62/0.81      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.62/0.81      inference('sup+', [status(thm)], ['76', '77'])).
% 0.62/0.81  thf('79', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.62/0.81      inference('sup-', [status(thm)], ['67', '73'])).
% 0.62/0.81  thf('80', plain,
% 0.62/0.81      (![X0 : $i, X1 : $i]:
% 0.62/0.81         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.62/0.81      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.62/0.81  thf('81', plain,
% 0.62/0.81      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.62/0.81      inference('sup-', [status(thm)], ['79', '80'])).
% 0.62/0.81  thf('82', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.62/0.81      inference('demod', [status(thm)], ['78', '81'])).
% 0.62/0.81  thf('83', plain,
% 0.62/0.81      (![X11 : $i, X12 : $i]:
% 0.62/0.81         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.62/0.81           = (k3_xboole_0 @ X11 @ X12))),
% 0.62/0.81      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.62/0.81  thf('84', plain,
% 0.62/0.81      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.62/0.81      inference('sup+', [status(thm)], ['82', '83'])).
% 0.62/0.81  thf('85', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.62/0.81      inference('sup-', [status(thm)], ['74', '75'])).
% 0.62/0.81  thf('86', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.62/0.81      inference('demod', [status(thm)], ['84', '85'])).
% 0.62/0.81  thf('87', plain,
% 0.62/0.81      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.62/0.81         (~ (r2_hidden @ X9 @ (k3_xboole_0 @ X7 @ X10))
% 0.62/0.81          | ~ (r1_xboole_0 @ X7 @ X10))),
% 0.62/0.81      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.62/0.81  thf('88', plain,
% 0.62/0.81      (![X0 : $i, X1 : $i]:
% 0.62/0.81         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.62/0.81      inference('sup-', [status(thm)], ['86', '87'])).
% 0.62/0.81  thf('89', plain,
% 0.62/0.81      (![X0 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.62/0.81      inference('sup-', [status(thm)], ['66', '88'])).
% 0.62/0.81  thf('90', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0)),
% 0.62/0.81      inference('sup-', [status(thm)], ['65', '89'])).
% 0.62/0.81  thf('91', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.62/0.81      inference('sup-', [status(thm)], ['1', '64'])).
% 0.62/0.81  thf('92', plain, (![X1 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X1)),
% 0.62/0.81      inference('simplify', [status(thm)], ['52'])).
% 0.62/0.81  thf('93', plain, ($false),
% 0.62/0.81      inference('demod', [status(thm)], ['90', '91', '92'])).
% 0.62/0.81  
% 0.62/0.81  % SZS output end Refutation
% 0.62/0.81  
% 0.62/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

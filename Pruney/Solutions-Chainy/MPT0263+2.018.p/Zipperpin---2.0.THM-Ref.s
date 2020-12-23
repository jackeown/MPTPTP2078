%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mRv1hbHDoA

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:33 EST 2020

% Result     : Theorem 7.69s
% Output     : Refutation 7.69s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 165 expanded)
%              Number of leaves         :   19 (  55 expanded)
%              Depth                    :   24
%              Number of atoms          :  926 (1506 expanded)
%              Number of equality atoms :  102 ( 154 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('2',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('3',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ X1 @ X0 ) @ X3 @ X2 ) @ X2 )
      | ( ( k4_xboole_0 @ X1 @ X0 )
        = ( k4_xboole_0 @ X2 @ X3 ) )
      | ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ X1 @ X0 ) @ X3 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('5',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('6',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('7',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 @ k1_xboole_0 ) @ X2 )
      | ( ( k4_xboole_0 @ X2 @ X1 )
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('12',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['8'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['8'])).

thf('15',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 @ k1_xboole_0 ) @ X2 )
      | ( ( k4_xboole_0 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('17',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('18',plain,(
    ! [X14: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X16 )
      | ( X18 = X17 )
      | ( X18 = X14 )
      | ( X16
       != ( k2_tarski @ X17 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('19',plain,(
    ! [X14: $i,X17: $i,X18: $i] :
      ( ( X18 = X14 )
      | ( X18 = X17 )
      | ~ ( r2_hidden @ X18 @ ( k2_tarski @ X17 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X2 )
        = k1_xboole_0 )
      | ( ( sk_D @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) @ X1 @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(l35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('24',plain,(
    ! [X26: $i,X28: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X26 ) @ X28 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ ( sk_D @ X2 @ X1 @ X0 ) ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X26: $i,X28: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X26 ) @ X28 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ ( sk_D @ X0 @ X2 @ X1 ) ) @ X1 )
        = k1_xboole_0 )
      | ( X0
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ ( sk_D @ X0 @ X2 @ X1 ) ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k4_xboole_0 @ k1_xboole_0 @ X2 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ ( sk_D @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) @ X2 @ k1_xboole_0 ) ) @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['22','27'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('31',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ ( sk_D @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) @ X2 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['28','29','30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_tarski @ ( sk_D @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) @ X2 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('35',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r2_hidden @ X26 @ X27 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X26 ) @ X27 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != k1_xboole_0 )
      | ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['8'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['33','38'])).

thf('40',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ k1_xboole_0 )
        = ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X1 )
        = ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ X0 ) )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('50',plain,(
    ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('54',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('55',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['53','56'])).

thf('58',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['52','57'])).

thf('59',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('60',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('62',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_D @ X3 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X3 )
      | ( X3
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X3 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ X2 )
      | ( X2
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ X2 )
      | ( X2
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['8'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,
    ( ( k1_tarski @ sk_A )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['60','73'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('75',plain,(
    ! [X11: $i,X13: $i] :
      ( ( r1_xboole_0 @ X11 @ X13 )
      | ( ( k4_xboole_0 @ X11 @ X13 )
       != X11 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('76',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    $false ),
    inference(demod,[status(thm)],['0','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mRv1hbHDoA
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:56:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 7.69/7.91  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 7.69/7.91  % Solved by: fo/fo7.sh
% 7.69/7.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.69/7.91  % done 4429 iterations in 7.461s
% 7.69/7.91  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 7.69/7.91  % SZS output start Refutation
% 7.69/7.91  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 7.69/7.91  thf(sk_A_type, type, sk_A: $i).
% 7.69/7.91  thf(sk_B_type, type, sk_B: $i).
% 7.69/7.91  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 7.69/7.91  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 7.69/7.91  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 7.69/7.91  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 7.69/7.91  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 7.69/7.91  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 7.69/7.91  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 7.69/7.91  thf(t58_zfmisc_1, conjecture,
% 7.69/7.91    (![A:$i,B:$i]:
% 7.69/7.91     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 7.69/7.91       ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 7.69/7.91  thf(zf_stmt_0, negated_conjecture,
% 7.69/7.91    (~( ![A:$i,B:$i]:
% 7.69/7.91        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 7.69/7.91          ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )),
% 7.69/7.91    inference('cnf.neg', [status(esa)], [t58_zfmisc_1])).
% 7.69/7.91  thf('0', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)),
% 7.69/7.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.69/7.91  thf(d5_xboole_0, axiom,
% 7.69/7.91    (![A:$i,B:$i,C:$i]:
% 7.69/7.91     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 7.69/7.91       ( ![D:$i]:
% 7.69/7.91         ( ( r2_hidden @ D @ C ) <=>
% 7.69/7.91           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 7.69/7.91  thf('1', plain,
% 7.69/7.91      (![X3 : $i, X4 : $i, X7 : $i]:
% 7.69/7.91         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 7.69/7.91          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 7.69/7.91          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 7.69/7.91      inference('cnf', [status(esa)], [d5_xboole_0])).
% 7.69/7.91  thf('2', plain,
% 7.69/7.91      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 7.69/7.91         (~ (r2_hidden @ X6 @ X5)
% 7.69/7.91          | (r2_hidden @ X6 @ X3)
% 7.69/7.91          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 7.69/7.91      inference('cnf', [status(esa)], [d5_xboole_0])).
% 7.69/7.91  thf('3', plain,
% 7.69/7.91      (![X3 : $i, X4 : $i, X6 : $i]:
% 7.69/7.91         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 7.69/7.91      inference('simplify', [status(thm)], ['2'])).
% 7.69/7.91  thf('4', plain,
% 7.69/7.91      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.69/7.91         ((r2_hidden @ (sk_D @ (k4_xboole_0 @ X1 @ X0) @ X3 @ X2) @ X2)
% 7.69/7.91          | ((k4_xboole_0 @ X1 @ X0) = (k4_xboole_0 @ X2 @ X3))
% 7.69/7.91          | (r2_hidden @ (sk_D @ (k4_xboole_0 @ X1 @ X0) @ X3 @ X2) @ X1))),
% 7.69/7.91      inference('sup-', [status(thm)], ['1', '3'])).
% 7.69/7.91  thf(t3_boole, axiom,
% 7.69/7.91    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 7.69/7.91  thf('5', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 7.69/7.91      inference('cnf', [status(esa)], [t3_boole])).
% 7.69/7.91  thf('6', plain,
% 7.69/7.91      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 7.69/7.91         (~ (r2_hidden @ X6 @ X5)
% 7.69/7.91          | ~ (r2_hidden @ X6 @ X4)
% 7.69/7.91          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 7.69/7.91      inference('cnf', [status(esa)], [d5_xboole_0])).
% 7.69/7.91  thf('7', plain,
% 7.69/7.91      (![X3 : $i, X4 : $i, X6 : $i]:
% 7.69/7.91         (~ (r2_hidden @ X6 @ X4)
% 7.69/7.91          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 7.69/7.91      inference('simplify', [status(thm)], ['6'])).
% 7.69/7.91  thf('8', plain,
% 7.69/7.91      (![X0 : $i, X1 : $i]:
% 7.69/7.91         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 7.69/7.91      inference('sup-', [status(thm)], ['5', '7'])).
% 7.69/7.91  thf('9', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 7.69/7.91      inference('condensation', [status(thm)], ['8'])).
% 7.69/7.91  thf('10', plain,
% 7.69/7.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.69/7.91         ((r2_hidden @ (sk_D @ (k4_xboole_0 @ X2 @ X1) @ X0 @ k1_xboole_0) @ X2)
% 7.69/7.91          | ((k4_xboole_0 @ X2 @ X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 7.69/7.91      inference('sup-', [status(thm)], ['4', '9'])).
% 7.69/7.91  thf('11', plain,
% 7.69/7.91      (![X3 : $i, X4 : $i, X7 : $i]:
% 7.69/7.91         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 7.69/7.91          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 7.69/7.91          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 7.69/7.91      inference('cnf', [status(esa)], [d5_xboole_0])).
% 7.69/7.91  thf('12', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 7.69/7.91      inference('condensation', [status(thm)], ['8'])).
% 7.69/7.91  thf('13', plain,
% 7.69/7.91      (![X0 : $i, X1 : $i]:
% 7.69/7.91         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 7.69/7.91          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 7.69/7.91      inference('sup-', [status(thm)], ['11', '12'])).
% 7.69/7.91  thf('14', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 7.69/7.91      inference('condensation', [status(thm)], ['8'])).
% 7.69/7.91  thf('15', plain,
% 7.69/7.91      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 7.69/7.91      inference('sup-', [status(thm)], ['13', '14'])).
% 7.69/7.91  thf('16', plain,
% 7.69/7.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.69/7.91         ((r2_hidden @ (sk_D @ (k4_xboole_0 @ X2 @ X1) @ X0 @ k1_xboole_0) @ X2)
% 7.69/7.91          | ((k4_xboole_0 @ X2 @ X1) = (k1_xboole_0)))),
% 7.69/7.91      inference('demod', [status(thm)], ['10', '15'])).
% 7.69/7.91  thf(t69_enumset1, axiom,
% 7.69/7.91    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 7.69/7.91  thf('17', plain,
% 7.69/7.91      (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 7.69/7.91      inference('cnf', [status(esa)], [t69_enumset1])).
% 7.69/7.91  thf(d2_tarski, axiom,
% 7.69/7.91    (![A:$i,B:$i,C:$i]:
% 7.69/7.91     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 7.69/7.91       ( ![D:$i]:
% 7.69/7.91         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 7.69/7.91  thf('18', plain,
% 7.69/7.91      (![X14 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 7.69/7.91         (~ (r2_hidden @ X18 @ X16)
% 7.69/7.91          | ((X18) = (X17))
% 7.69/7.91          | ((X18) = (X14))
% 7.69/7.91          | ((X16) != (k2_tarski @ X17 @ X14)))),
% 7.69/7.91      inference('cnf', [status(esa)], [d2_tarski])).
% 7.69/7.91  thf('19', plain,
% 7.69/7.91      (![X14 : $i, X17 : $i, X18 : $i]:
% 7.69/7.91         (((X18) = (X14))
% 7.69/7.91          | ((X18) = (X17))
% 7.69/7.91          | ~ (r2_hidden @ X18 @ (k2_tarski @ X17 @ X14)))),
% 7.69/7.91      inference('simplify', [status(thm)], ['18'])).
% 7.69/7.91  thf('20', plain,
% 7.69/7.91      (![X0 : $i, X1 : $i]:
% 7.69/7.91         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 7.69/7.91      inference('sup-', [status(thm)], ['17', '19'])).
% 7.69/7.91  thf('21', plain,
% 7.69/7.91      (![X0 : $i, X1 : $i]:
% 7.69/7.91         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 7.69/7.91      inference('simplify', [status(thm)], ['20'])).
% 7.69/7.91  thf('22', plain,
% 7.69/7.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.69/7.91         (((k4_xboole_0 @ (k1_tarski @ X0) @ X2) = (k1_xboole_0))
% 7.69/7.91          | ((sk_D @ (k4_xboole_0 @ (k1_tarski @ X0) @ X2) @ X1 @ k1_xboole_0)
% 7.69/7.91              = (X0)))),
% 7.69/7.91      inference('sup-', [status(thm)], ['16', '21'])).
% 7.69/7.91  thf('23', plain,
% 7.69/7.91      (![X3 : $i, X4 : $i, X7 : $i]:
% 7.69/7.91         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 7.69/7.91          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 7.69/7.91          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 7.69/7.91      inference('cnf', [status(esa)], [d5_xboole_0])).
% 7.69/7.91  thf(l35_zfmisc_1, axiom,
% 7.69/7.91    (![A:$i,B:$i]:
% 7.69/7.91     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 7.69/7.91       ( r2_hidden @ A @ B ) ))).
% 7.69/7.91  thf('24', plain,
% 7.69/7.91      (![X26 : $i, X28 : $i]:
% 7.69/7.91         (((k4_xboole_0 @ (k1_tarski @ X26) @ X28) = (k1_xboole_0))
% 7.69/7.91          | ~ (r2_hidden @ X26 @ X28))),
% 7.69/7.91      inference('cnf', [status(esa)], [l35_zfmisc_1])).
% 7.69/7.91  thf('25', plain,
% 7.69/7.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.69/7.91         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 7.69/7.91          | ((X2) = (k4_xboole_0 @ X0 @ X1))
% 7.69/7.91          | ((k4_xboole_0 @ (k1_tarski @ (sk_D @ X2 @ X1 @ X0)) @ X0)
% 7.69/7.91              = (k1_xboole_0)))),
% 7.69/7.91      inference('sup-', [status(thm)], ['23', '24'])).
% 7.69/7.91  thf('26', plain,
% 7.69/7.91      (![X26 : $i, X28 : $i]:
% 7.69/7.91         (((k4_xboole_0 @ (k1_tarski @ X26) @ X28) = (k1_xboole_0))
% 7.69/7.91          | ~ (r2_hidden @ X26 @ X28))),
% 7.69/7.91      inference('cnf', [status(esa)], [l35_zfmisc_1])).
% 7.69/7.91  thf('27', plain,
% 7.69/7.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.69/7.91         (((k4_xboole_0 @ (k1_tarski @ (sk_D @ X0 @ X2 @ X1)) @ X1)
% 7.69/7.91            = (k1_xboole_0))
% 7.69/7.91          | ((X0) = (k4_xboole_0 @ X1 @ X2))
% 7.69/7.91          | ((k4_xboole_0 @ (k1_tarski @ (sk_D @ X0 @ X2 @ X1)) @ X0)
% 7.69/7.91              = (k1_xboole_0)))),
% 7.69/7.91      inference('sup-', [status(thm)], ['25', '26'])).
% 7.69/7.91  thf('28', plain,
% 7.69/7.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.69/7.91         (((k4_xboole_0 @ (k1_tarski @ X0) @ 
% 7.69/7.91            (k4_xboole_0 @ (k1_tarski @ X0) @ X1)) = (k1_xboole_0))
% 7.69/7.91          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 7.69/7.91          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1)
% 7.69/7.91              = (k4_xboole_0 @ k1_xboole_0 @ X2))
% 7.69/7.91          | ((k4_xboole_0 @ 
% 7.69/7.91              (k1_tarski @ 
% 7.69/7.91               (sk_D @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1) @ X2 @ k1_xboole_0)) @ 
% 7.69/7.91              k1_xboole_0) = (k1_xboole_0)))),
% 7.69/7.91      inference('sup+', [status(thm)], ['22', '27'])).
% 7.69/7.91  thf(t48_xboole_1, axiom,
% 7.69/7.91    (![A:$i,B:$i]:
% 7.69/7.91     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 7.69/7.91  thf('29', plain,
% 7.69/7.91      (![X9 : $i, X10 : $i]:
% 7.69/7.91         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 7.69/7.91           = (k3_xboole_0 @ X9 @ X10))),
% 7.69/7.91      inference('cnf', [status(esa)], [t48_xboole_1])).
% 7.69/7.91  thf('30', plain,
% 7.69/7.91      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 7.69/7.91      inference('sup-', [status(thm)], ['13', '14'])).
% 7.69/7.91  thf('31', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 7.69/7.91      inference('cnf', [status(esa)], [t3_boole])).
% 7.69/7.91  thf('32', plain,
% 7.69/7.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.69/7.91         (((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 7.69/7.91          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 7.69/7.91          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 7.69/7.91          | ((k1_tarski @ 
% 7.69/7.91              (sk_D @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1) @ X2 @ k1_xboole_0))
% 7.69/7.91              = (k1_xboole_0)))),
% 7.69/7.91      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 7.69/7.91  thf('33', plain,
% 7.69/7.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.69/7.91         (((k1_tarski @ 
% 7.69/7.91            (sk_D @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1) @ X2 @ k1_xboole_0))
% 7.69/7.91            = (k1_xboole_0))
% 7.69/7.91          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 7.69/7.91          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0)))),
% 7.69/7.91      inference('simplify', [status(thm)], ['32'])).
% 7.69/7.91  thf('34', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 7.69/7.91      inference('cnf', [status(esa)], [t3_boole])).
% 7.69/7.91  thf('35', plain,
% 7.69/7.91      (![X26 : $i, X27 : $i]:
% 7.69/7.91         ((r2_hidden @ X26 @ X27)
% 7.69/7.91          | ((k4_xboole_0 @ (k1_tarski @ X26) @ X27) != (k1_xboole_0)))),
% 7.69/7.91      inference('cnf', [status(esa)], [l35_zfmisc_1])).
% 7.69/7.91  thf('36', plain,
% 7.69/7.91      (![X0 : $i]:
% 7.69/7.91         (((k1_tarski @ X0) != (k1_xboole_0)) | (r2_hidden @ X0 @ k1_xboole_0))),
% 7.69/7.91      inference('sup-', [status(thm)], ['34', '35'])).
% 7.69/7.91  thf('37', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 7.69/7.91      inference('condensation', [status(thm)], ['8'])).
% 7.69/7.91  thf('38', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 7.69/7.91      inference('clc', [status(thm)], ['36', '37'])).
% 7.69/7.91  thf('39', plain,
% 7.69/7.91      (![X0 : $i, X1 : $i]:
% 7.69/7.91         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 7.69/7.91          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0)))),
% 7.69/7.91      inference('simplify_reflect-', [status(thm)], ['33', '38'])).
% 7.69/7.91  thf('40', plain,
% 7.69/7.91      (![X9 : $i, X10 : $i]:
% 7.69/7.91         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 7.69/7.91           = (k3_xboole_0 @ X9 @ X10))),
% 7.69/7.91      inference('cnf', [status(esa)], [t48_xboole_1])).
% 7.69/7.91  thf('41', plain,
% 7.69/7.91      (![X0 : $i, X1 : $i]:
% 7.69/7.91         (((k4_xboole_0 @ (k1_tarski @ X1) @ k1_xboole_0)
% 7.69/7.91            = (k3_xboole_0 @ (k1_tarski @ X1) @ X0))
% 7.69/7.91          | ((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0)))),
% 7.69/7.91      inference('sup+', [status(thm)], ['39', '40'])).
% 7.69/7.91  thf('42', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 7.69/7.91      inference('cnf', [status(esa)], [t3_boole])).
% 7.69/7.91  thf('43', plain,
% 7.69/7.91      (![X0 : $i, X1 : $i]:
% 7.69/7.91         (((k1_tarski @ X1) = (k3_xboole_0 @ (k1_tarski @ X1) @ X0))
% 7.69/7.91          | ((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0)))),
% 7.69/7.91      inference('demod', [status(thm)], ['41', '42'])).
% 7.69/7.91  thf(commutativity_k3_xboole_0, axiom,
% 7.69/7.91    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 7.69/7.91  thf('44', plain,
% 7.69/7.91      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 7.69/7.91      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 7.69/7.91  thf('45', plain,
% 7.69/7.91      (![X0 : $i, X1 : $i]:
% 7.69/7.91         (((k3_xboole_0 @ X1 @ (k1_tarski @ X0)) = (k1_tarski @ X0))
% 7.69/7.91          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0)))),
% 7.69/7.91      inference('sup+', [status(thm)], ['43', '44'])).
% 7.69/7.91  thf('46', plain,
% 7.69/7.91      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 7.69/7.91      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 7.69/7.91  thf('47', plain,
% 7.69/7.91      (![X0 : $i, X1 : $i]:
% 7.69/7.91         (((k3_xboole_0 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0))
% 7.69/7.91          | ((k3_xboole_0 @ X1 @ (k1_tarski @ X0)) = (k1_tarski @ X0)))),
% 7.69/7.91      inference('sup+', [status(thm)], ['45', '46'])).
% 7.69/7.91  thf('48', plain,
% 7.69/7.91      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 7.69/7.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.69/7.91  thf('49', plain,
% 7.69/7.91      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 7.69/7.91      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 7.69/7.91  thf('50', plain,
% 7.69/7.91      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (k1_tarski @ sk_A))),
% 7.69/7.91      inference('demod', [status(thm)], ['48', '49'])).
% 7.69/7.91  thf('51', plain,
% 7.69/7.91      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 7.69/7.91        | ((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))),
% 7.69/7.91      inference('sup-', [status(thm)], ['47', '50'])).
% 7.69/7.91  thf('52', plain,
% 7.69/7.91      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 7.69/7.91      inference('simplify', [status(thm)], ['51'])).
% 7.69/7.91  thf('53', plain,
% 7.69/7.91      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 7.69/7.91      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 7.69/7.91  thf('54', plain,
% 7.69/7.91      (![X9 : $i, X10 : $i]:
% 7.69/7.91         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 7.69/7.91           = (k3_xboole_0 @ X9 @ X10))),
% 7.69/7.91      inference('cnf', [status(esa)], [t48_xboole_1])).
% 7.69/7.91  thf('55', plain,
% 7.69/7.91      (![X9 : $i, X10 : $i]:
% 7.69/7.91         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 7.69/7.91           = (k3_xboole_0 @ X9 @ X10))),
% 7.69/7.91      inference('cnf', [status(esa)], [t48_xboole_1])).
% 7.69/7.91  thf('56', plain,
% 7.69/7.91      (![X0 : $i, X1 : $i]:
% 7.69/7.91         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 7.69/7.91           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 7.69/7.91      inference('sup+', [status(thm)], ['54', '55'])).
% 7.69/7.91  thf('57', plain,
% 7.69/7.91      (![X0 : $i, X1 : $i]:
% 7.69/7.91         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 7.69/7.91           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 7.69/7.91      inference('sup+', [status(thm)], ['53', '56'])).
% 7.69/7.91  thf('58', plain,
% 7.69/7.91      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0)
% 7.69/7.91         = (k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 7.69/7.91            (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 7.69/7.91      inference('sup+', [status(thm)], ['52', '57'])).
% 7.69/7.91  thf('59', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 7.69/7.91      inference('cnf', [status(esa)], [t3_boole])).
% 7.69/7.91  thf('60', plain,
% 7.69/7.91      (((k1_tarski @ sk_A)
% 7.69/7.91         = (k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 7.69/7.91            (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 7.69/7.91      inference('demod', [status(thm)], ['58', '59'])).
% 7.69/7.91  thf('61', plain,
% 7.69/7.91      (![X3 : $i, X4 : $i, X7 : $i]:
% 7.69/7.91         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 7.69/7.91          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 7.69/7.91          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 7.69/7.91      inference('cnf', [status(esa)], [d5_xboole_0])).
% 7.69/7.91  thf('62', plain,
% 7.69/7.91      (![X3 : $i, X4 : $i, X6 : $i]:
% 7.69/7.91         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 7.69/7.91      inference('simplify', [status(thm)], ['2'])).
% 7.69/7.91  thf('63', plain,
% 7.69/7.91      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.69/7.91         ((r2_hidden @ (sk_D @ X3 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X3)
% 7.69/7.91          | ((X3) = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))
% 7.69/7.91          | (r2_hidden @ (sk_D @ X3 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 7.69/7.91      inference('sup-', [status(thm)], ['61', '62'])).
% 7.69/7.91  thf('64', plain,
% 7.69/7.91      (![X3 : $i, X4 : $i, X7 : $i]:
% 7.69/7.91         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 7.69/7.91          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 7.69/7.91          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 7.69/7.91      inference('cnf', [status(esa)], [d5_xboole_0])).
% 7.69/7.91  thf('65', plain,
% 7.69/7.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.69/7.91         (((X2) = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))
% 7.69/7.91          | (r2_hidden @ (sk_D @ X2 @ X0 @ (k4_xboole_0 @ X0 @ X1)) @ X2)
% 7.69/7.91          | (r2_hidden @ (sk_D @ X2 @ X0 @ (k4_xboole_0 @ X0 @ X1)) @ X2)
% 7.69/7.91          | ((X2) = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)))),
% 7.69/7.91      inference('sup-', [status(thm)], ['63', '64'])).
% 7.69/7.91  thf('66', plain,
% 7.69/7.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.69/7.91         ((r2_hidden @ (sk_D @ X2 @ X0 @ (k4_xboole_0 @ X0 @ X1)) @ X2)
% 7.69/7.91          | ((X2) = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)))),
% 7.69/7.91      inference('simplify', [status(thm)], ['65'])).
% 7.69/7.91  thf('67', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 7.69/7.91      inference('condensation', [status(thm)], ['8'])).
% 7.69/7.91  thf('68', plain,
% 7.69/7.91      (![X0 : $i, X1 : $i]:
% 7.69/7.91         ((k1_xboole_0) = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 7.69/7.91      inference('sup-', [status(thm)], ['66', '67'])).
% 7.69/7.91  thf('69', plain,
% 7.69/7.91      (![X9 : $i, X10 : $i]:
% 7.69/7.91         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 7.69/7.91           = (k3_xboole_0 @ X9 @ X10))),
% 7.69/7.91      inference('cnf', [status(esa)], [t48_xboole_1])).
% 7.69/7.91  thf('70', plain,
% 7.69/7.91      (![X0 : $i, X1 : $i]:
% 7.69/7.91         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 7.69/7.91           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 7.69/7.91      inference('sup+', [status(thm)], ['68', '69'])).
% 7.69/7.91  thf('71', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 7.69/7.91      inference('cnf', [status(esa)], [t3_boole])).
% 7.69/7.91  thf('72', plain,
% 7.69/7.91      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 7.69/7.91      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 7.69/7.91  thf('73', plain,
% 7.69/7.91      (![X0 : $i, X1 : $i]:
% 7.69/7.91         ((k4_xboole_0 @ X0 @ X1)
% 7.69/7.91           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 7.69/7.91      inference('demod', [status(thm)], ['70', '71', '72'])).
% 7.69/7.91  thf('74', plain,
% 7.69/7.91      (((k1_tarski @ sk_A) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 7.69/7.91      inference('demod', [status(thm)], ['60', '73'])).
% 7.69/7.91  thf(t83_xboole_1, axiom,
% 7.69/7.91    (![A:$i,B:$i]:
% 7.69/7.91     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 7.69/7.91  thf('75', plain,
% 7.69/7.91      (![X11 : $i, X13 : $i]:
% 7.69/7.91         ((r1_xboole_0 @ X11 @ X13) | ((k4_xboole_0 @ X11 @ X13) != (X11)))),
% 7.69/7.91      inference('cnf', [status(esa)], [t83_xboole_1])).
% 7.69/7.91  thf('76', plain,
% 7.69/7.91      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 7.69/7.91        | (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 7.69/7.91      inference('sup-', [status(thm)], ['74', '75'])).
% 7.69/7.91  thf('77', plain, ((r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)),
% 7.69/7.91      inference('simplify', [status(thm)], ['76'])).
% 7.69/7.91  thf('78', plain, ($false), inference('demod', [status(thm)], ['0', '77'])).
% 7.69/7.91  
% 7.69/7.91  % SZS output end Refutation
% 7.69/7.91  
% 7.69/7.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

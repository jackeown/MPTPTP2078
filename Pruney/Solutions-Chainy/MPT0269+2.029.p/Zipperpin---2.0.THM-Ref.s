%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.g6ooZ4d1Ei

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:06 EST 2020

% Result     : Theorem 1.74s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 213 expanded)
%              Number of leaves         :   22 (  68 expanded)
%              Depth                    :   19
%              Number of atoms          :  694 (1751 expanded)
%              Number of equality atoms :   80 ( 212 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t66_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
          = k1_xboole_0 )
        & ( A != k1_xboole_0 )
        & ( A
         != ( k1_tarski @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
            = k1_xboole_0 )
          & ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_zfmisc_1])).

thf('0',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( ( k4_xboole_0 @ X9 @ X10 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('2',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(simplify,[status(thm)],['2'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('9',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('11',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('15',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('19',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ k1_xboole_0 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ k1_xboole_0 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_A @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ sk_A @ X0 @ k1_xboole_0 ) @ ( k1_tarski @ sk_B ) )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','23'])).

thf('25',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_A @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ sk_A @ X0 @ k1_xboole_0 ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['16'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_D @ sk_A @ X0 @ k1_xboole_0 ) @ ( k1_tarski @ sk_B ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('29',plain,(
    ! [X27: $i] :
      ( ( k2_tarski @ X27 @ X27 )
      = ( k1_tarski @ X27 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('30',plain,(
    ! [X21: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X25 @ X23 )
      | ( X25 = X24 )
      | ( X25 = X21 )
      | ( X23
       != ( k2_tarski @ X24 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('31',plain,(
    ! [X21: $i,X24: $i,X25: $i] :
      ( ( X25 = X21 )
      | ( X25 = X24 )
      | ~ ( r2_hidden @ X25 @ ( k2_tarski @ X24 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( sk_D @ sk_A @ X0 @ k1_xboole_0 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('36',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('39',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('41',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('42',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('43',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( sk_A
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['34','47'])).

thf('49',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('50',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('53',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('56',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['51','56'])).

thf('58',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','57'])).

thf('59',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('62',plain,(
    ! [X37: $i,X39: $i,X40: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X37 @ X39 ) @ X40 )
      | ~ ( r2_hidden @ X39 @ X40 )
      | ~ ( r2_hidden @ X37 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X0 )
      | ( r1_tarski @ ( k2_tarski @ X2 @ ( sk_D @ X0 @ X1 @ k1_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_tarski @ sk_B @ ( sk_D @ sk_A @ X0 @ k1_xboole_0 ) ) @ sk_A )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( sk_D @ sk_A @ X0 @ k1_xboole_0 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('66',plain,(
    ! [X27: $i] :
      ( ( k2_tarski @ X27 @ X27 )
      = ( k1_tarski @ X27 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('67',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['67','68'])).

thf('70',plain,(
    $false ),
    inference(demod,[status(thm)],['7','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.g6ooZ4d1Ei
% 0.16/0.37  % Computer   : n010.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 14:45:59 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 1.74/1.97  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.74/1.97  % Solved by: fo/fo7.sh
% 1.74/1.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.74/1.97  % done 2102 iterations in 1.494s
% 1.74/1.97  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.74/1.97  % SZS output start Refutation
% 1.74/1.97  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.74/1.97  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.74/1.97  thf(sk_B_type, type, sk_B: $i).
% 1.74/1.97  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.74/1.97  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.74/1.97  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.74/1.97  thf(sk_A_type, type, sk_A: $i).
% 1.74/1.97  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.74/1.97  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.74/1.97  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.74/1.97  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.74/1.97  thf(t66_zfmisc_1, conjecture,
% 1.74/1.97    (![A:$i,B:$i]:
% 1.74/1.97     ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 1.74/1.97          ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ))).
% 1.74/1.98  thf(zf_stmt_0, negated_conjecture,
% 1.74/1.98    (~( ![A:$i,B:$i]:
% 1.74/1.98        ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 1.74/1.98             ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ) )),
% 1.74/1.98    inference('cnf.neg', [status(esa)], [t66_zfmisc_1])).
% 1.74/1.98  thf('0', plain,
% 1.74/1.98      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf(l32_xboole_1, axiom,
% 1.74/1.98    (![A:$i,B:$i]:
% 1.74/1.98     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.74/1.98  thf('1', plain,
% 1.74/1.98      (![X9 : $i, X10 : $i]:
% 1.74/1.98         ((r1_tarski @ X9 @ X10) | ((k4_xboole_0 @ X9 @ X10) != (k1_xboole_0)))),
% 1.74/1.98      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.74/1.98  thf('2', plain,
% 1.74/1.98      ((((k1_xboole_0) != (k1_xboole_0))
% 1.74/1.98        | (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['0', '1'])).
% 1.74/1.98  thf('3', plain, ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))),
% 1.74/1.98      inference('simplify', [status(thm)], ['2'])).
% 1.74/1.98  thf(d10_xboole_0, axiom,
% 1.74/1.98    (![A:$i,B:$i]:
% 1.74/1.98     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.74/1.98  thf('4', plain,
% 1.74/1.98      (![X6 : $i, X8 : $i]:
% 1.74/1.98         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 1.74/1.98      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.74/1.98  thf('5', plain,
% 1.74/1.98      ((~ (r1_tarski @ (k1_tarski @ sk_B) @ sk_A)
% 1.74/1.98        | ((k1_tarski @ sk_B) = (sk_A)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['3', '4'])).
% 1.74/1.98  thf('6', plain, (((sk_A) != (k1_tarski @ sk_B))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('7', plain, (~ (r1_tarski @ (k1_tarski @ sk_B) @ sk_A)),
% 1.74/1.98      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 1.74/1.98  thf('8', plain,
% 1.74/1.98      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf(d5_xboole_0, axiom,
% 1.74/1.98    (![A:$i,B:$i,C:$i]:
% 1.74/1.98     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.74/1.98       ( ![D:$i]:
% 1.74/1.98         ( ( r2_hidden @ D @ C ) <=>
% 1.74/1.98           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.74/1.98  thf('9', plain,
% 1.74/1.98      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.74/1.98         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 1.74/1.98          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 1.74/1.98          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.74/1.98      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.74/1.98  thf('10', plain,
% 1.74/1.98      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 1.74/1.98      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.74/1.98  thf('11', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 1.74/1.98      inference('simplify', [status(thm)], ['10'])).
% 1.74/1.98  thf('12', plain,
% 1.74/1.98      (![X9 : $i, X11 : $i]:
% 1.74/1.98         (((k4_xboole_0 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 1.74/1.98      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.74/1.98  thf('13', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.74/1.98      inference('sup-', [status(thm)], ['11', '12'])).
% 1.74/1.98  thf('14', plain,
% 1.74/1.98      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.74/1.98         (~ (r2_hidden @ X4 @ X3)
% 1.74/1.98          | ~ (r2_hidden @ X4 @ X2)
% 1.74/1.98          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 1.74/1.98      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.74/1.98  thf('15', plain,
% 1.74/1.98      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.74/1.98         (~ (r2_hidden @ X4 @ X2)
% 1.74/1.98          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 1.74/1.98      inference('simplify', [status(thm)], ['14'])).
% 1.74/1.98  thf('16', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i]:
% 1.74/1.98         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 1.74/1.98      inference('sup-', [status(thm)], ['13', '15'])).
% 1.74/1.98  thf('17', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.74/1.98      inference('condensation', [status(thm)], ['16'])).
% 1.74/1.98  thf('18', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i]:
% 1.74/1.98         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 1.74/1.98          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['9', '17'])).
% 1.74/1.98  thf(t4_boole, axiom,
% 1.74/1.98    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 1.74/1.98  thf('19', plain,
% 1.74/1.98      (![X18 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X18) = (k1_xboole_0))),
% 1.74/1.98      inference('cnf', [status(esa)], [t4_boole])).
% 1.74/1.98  thf('20', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i]:
% 1.74/1.98         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 1.74/1.98          | ((X1) = (k1_xboole_0)))),
% 1.74/1.98      inference('demod', [status(thm)], ['18', '19'])).
% 1.74/1.98  thf('21', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.74/1.98         (~ (r2_hidden @ X0 @ X1)
% 1.74/1.98          | (r2_hidden @ X0 @ X2)
% 1.74/1.98          | (r2_hidden @ X0 @ X3)
% 1.74/1.98          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 1.74/1.98      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.74/1.98  thf('22', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.74/1.98         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 1.74/1.98          | (r2_hidden @ X0 @ X2)
% 1.74/1.98          | ~ (r2_hidden @ X0 @ X1))),
% 1.74/1.98      inference('simplify', [status(thm)], ['21'])).
% 1.74/1.98  thf('23', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.74/1.98         (((X0) = (k1_xboole_0))
% 1.74/1.98          | (r2_hidden @ (sk_D @ X0 @ X1 @ k1_xboole_0) @ X2)
% 1.74/1.98          | (r2_hidden @ (sk_D @ X0 @ X1 @ k1_xboole_0) @ 
% 1.74/1.98             (k4_xboole_0 @ X0 @ X2)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['20', '22'])).
% 1.74/1.98  thf('24', plain,
% 1.74/1.98      (![X0 : $i]:
% 1.74/1.98         ((r2_hidden @ (sk_D @ sk_A @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 1.74/1.98          | (r2_hidden @ (sk_D @ sk_A @ X0 @ k1_xboole_0) @ (k1_tarski @ sk_B))
% 1.74/1.98          | ((sk_A) = (k1_xboole_0)))),
% 1.74/1.98      inference('sup+', [status(thm)], ['8', '23'])).
% 1.74/1.98  thf('25', plain, (((sk_A) != (k1_xboole_0))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('26', plain,
% 1.74/1.98      (![X0 : $i]:
% 1.74/1.98         ((r2_hidden @ (sk_D @ sk_A @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 1.74/1.98          | (r2_hidden @ (sk_D @ sk_A @ X0 @ k1_xboole_0) @ (k1_tarski @ sk_B)))),
% 1.74/1.98      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 1.74/1.98  thf('27', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.74/1.98      inference('condensation', [status(thm)], ['16'])).
% 1.74/1.98  thf('28', plain,
% 1.74/1.98      (![X0 : $i]:
% 1.74/1.98         (r2_hidden @ (sk_D @ sk_A @ X0 @ k1_xboole_0) @ (k1_tarski @ sk_B))),
% 1.74/1.98      inference('clc', [status(thm)], ['26', '27'])).
% 1.74/1.98  thf(t69_enumset1, axiom,
% 1.74/1.98    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.74/1.98  thf('29', plain,
% 1.74/1.98      (![X27 : $i]: ((k2_tarski @ X27 @ X27) = (k1_tarski @ X27))),
% 1.74/1.98      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.74/1.98  thf(d2_tarski, axiom,
% 1.74/1.98    (![A:$i,B:$i,C:$i]:
% 1.74/1.98     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 1.74/1.98       ( ![D:$i]:
% 1.74/1.98         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 1.74/1.98  thf('30', plain,
% 1.74/1.98      (![X21 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 1.74/1.98         (~ (r2_hidden @ X25 @ X23)
% 1.74/1.98          | ((X25) = (X24))
% 1.74/1.98          | ((X25) = (X21))
% 1.74/1.98          | ((X23) != (k2_tarski @ X24 @ X21)))),
% 1.74/1.98      inference('cnf', [status(esa)], [d2_tarski])).
% 1.74/1.98  thf('31', plain,
% 1.74/1.98      (![X21 : $i, X24 : $i, X25 : $i]:
% 1.74/1.98         (((X25) = (X21))
% 1.74/1.98          | ((X25) = (X24))
% 1.74/1.98          | ~ (r2_hidden @ X25 @ (k2_tarski @ X24 @ X21)))),
% 1.74/1.98      inference('simplify', [status(thm)], ['30'])).
% 1.74/1.98  thf('32', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i]:
% 1.74/1.98         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['29', '31'])).
% 1.74/1.98  thf('33', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i]:
% 1.74/1.98         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 1.74/1.98      inference('simplify', [status(thm)], ['32'])).
% 1.74/1.98  thf('34', plain, (![X0 : $i]: ((sk_D @ sk_A @ X0 @ k1_xboole_0) = (sk_B))),
% 1.74/1.98      inference('sup-', [status(thm)], ['28', '33'])).
% 1.74/1.98  thf('35', plain,
% 1.74/1.98      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.74/1.98         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 1.74/1.98          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 1.74/1.98          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.74/1.98      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.74/1.98  thf('36', plain,
% 1.74/1.98      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.74/1.98         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 1.74/1.98          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 1.74/1.98          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.74/1.98      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.74/1.98  thf('37', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i]:
% 1.74/1.98         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 1.74/1.98          | ((X1) = (k4_xboole_0 @ X0 @ X0))
% 1.74/1.98          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 1.74/1.98          | ((X1) = (k4_xboole_0 @ X0 @ X0)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['35', '36'])).
% 1.74/1.98  thf('38', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.74/1.98      inference('sup-', [status(thm)], ['11', '12'])).
% 1.74/1.98  thf(t48_xboole_1, axiom,
% 1.74/1.98    (![A:$i,B:$i]:
% 1.74/1.98     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.74/1.98  thf('39', plain,
% 1.74/1.98      (![X16 : $i, X17 : $i]:
% 1.74/1.98         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.74/1.98           = (k3_xboole_0 @ X16 @ X17))),
% 1.74/1.98      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.74/1.98  thf('40', plain,
% 1.74/1.98      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 1.74/1.98      inference('sup+', [status(thm)], ['38', '39'])).
% 1.74/1.98  thf(t3_boole, axiom,
% 1.74/1.98    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.74/1.98  thf('41', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 1.74/1.98      inference('cnf', [status(esa)], [t3_boole])).
% 1.74/1.98  thf('42', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 1.74/1.98      inference('demod', [status(thm)], ['40', '41'])).
% 1.74/1.98  thf(t100_xboole_1, axiom,
% 1.74/1.98    (![A:$i,B:$i]:
% 1.74/1.98     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.74/1.98  thf('43', plain,
% 1.74/1.98      (![X12 : $i, X13 : $i]:
% 1.74/1.98         ((k4_xboole_0 @ X12 @ X13)
% 1.74/1.98           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 1.74/1.98      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.74/1.98  thf('44', plain,
% 1.74/1.98      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.74/1.98      inference('sup+', [status(thm)], ['42', '43'])).
% 1.74/1.98  thf('45', plain,
% 1.74/1.98      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.74/1.98      inference('sup+', [status(thm)], ['42', '43'])).
% 1.74/1.98  thf('46', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i]:
% 1.74/1.98         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 1.74/1.98          | ((X1) = (k5_xboole_0 @ X0 @ X0))
% 1.74/1.98          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 1.74/1.98          | ((X1) = (k5_xboole_0 @ X0 @ X0)))),
% 1.74/1.98      inference('demod', [status(thm)], ['37', '44', '45'])).
% 1.74/1.98  thf('47', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i]:
% 1.74/1.98         (((X1) = (k5_xboole_0 @ X0 @ X0))
% 1.74/1.98          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 1.74/1.98      inference('simplify', [status(thm)], ['46'])).
% 1.74/1.98  thf('48', plain,
% 1.74/1.98      (((r2_hidden @ sk_B @ sk_A)
% 1.74/1.98        | ((sk_A) = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0)))),
% 1.74/1.98      inference('sup+', [status(thm)], ['34', '47'])).
% 1.74/1.98  thf('49', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 1.74/1.98      inference('cnf', [status(esa)], [t3_boole])).
% 1.74/1.98  thf('50', plain,
% 1.74/1.98      (![X12 : $i, X13 : $i]:
% 1.74/1.98         ((k4_xboole_0 @ X12 @ X13)
% 1.74/1.98           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 1.74/1.98      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.74/1.98  thf('51', plain,
% 1.74/1.98      (![X0 : $i]:
% 1.74/1.98         ((X0) = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 1.74/1.98      inference('sup+', [status(thm)], ['49', '50'])).
% 1.74/1.98  thf('52', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 1.74/1.98      inference('cnf', [status(esa)], [t3_boole])).
% 1.74/1.98  thf('53', plain,
% 1.74/1.98      (![X16 : $i, X17 : $i]:
% 1.74/1.98         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.74/1.98           = (k3_xboole_0 @ X16 @ X17))),
% 1.74/1.98      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.74/1.98  thf('54', plain,
% 1.74/1.98      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.74/1.98      inference('sup+', [status(thm)], ['52', '53'])).
% 1.74/1.98  thf('55', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.74/1.98      inference('sup-', [status(thm)], ['11', '12'])).
% 1.74/1.98  thf('56', plain,
% 1.74/1.98      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.74/1.98      inference('demod', [status(thm)], ['54', '55'])).
% 1.74/1.98  thf('57', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.74/1.98      inference('demod', [status(thm)], ['51', '56'])).
% 1.74/1.98  thf('58', plain, (((r2_hidden @ sk_B @ sk_A) | ((sk_A) = (k1_xboole_0)))),
% 1.74/1.98      inference('demod', [status(thm)], ['48', '57'])).
% 1.74/1.98  thf('59', plain, (((sk_A) != (k1_xboole_0))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('60', plain, ((r2_hidden @ sk_B @ sk_A)),
% 1.74/1.98      inference('simplify_reflect-', [status(thm)], ['58', '59'])).
% 1.74/1.98  thf('61', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i]:
% 1.74/1.98         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 1.74/1.98          | ((X1) = (k1_xboole_0)))),
% 1.74/1.98      inference('demod', [status(thm)], ['18', '19'])).
% 1.74/1.98  thf(t38_zfmisc_1, axiom,
% 1.74/1.98    (![A:$i,B:$i,C:$i]:
% 1.74/1.98     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 1.74/1.98       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 1.74/1.98  thf('62', plain,
% 1.74/1.98      (![X37 : $i, X39 : $i, X40 : $i]:
% 1.74/1.98         ((r1_tarski @ (k2_tarski @ X37 @ X39) @ X40)
% 1.74/1.98          | ~ (r2_hidden @ X39 @ X40)
% 1.74/1.98          | ~ (r2_hidden @ X37 @ X40))),
% 1.74/1.98      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 1.74/1.98  thf('63', plain,
% 1.74/1.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.74/1.98         (((X0) = (k1_xboole_0))
% 1.74/1.98          | ~ (r2_hidden @ X2 @ X0)
% 1.74/1.98          | (r1_tarski @ (k2_tarski @ X2 @ (sk_D @ X0 @ X1 @ k1_xboole_0)) @ X0))),
% 1.74/1.98      inference('sup-', [status(thm)], ['61', '62'])).
% 1.74/1.98  thf('64', plain,
% 1.74/1.98      (![X0 : $i]:
% 1.74/1.98         ((r1_tarski @ (k2_tarski @ sk_B @ (sk_D @ sk_A @ X0 @ k1_xboole_0)) @ 
% 1.74/1.98           sk_A)
% 1.74/1.98          | ((sk_A) = (k1_xboole_0)))),
% 1.74/1.98      inference('sup-', [status(thm)], ['60', '63'])).
% 1.74/1.98  thf('65', plain, (![X0 : $i]: ((sk_D @ sk_A @ X0 @ k1_xboole_0) = (sk_B))),
% 1.74/1.98      inference('sup-', [status(thm)], ['28', '33'])).
% 1.74/1.98  thf('66', plain,
% 1.74/1.98      (![X27 : $i]: ((k2_tarski @ X27 @ X27) = (k1_tarski @ X27))),
% 1.74/1.98      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.74/1.98  thf('67', plain,
% 1.74/1.98      (((r1_tarski @ (k1_tarski @ sk_B) @ sk_A) | ((sk_A) = (k1_xboole_0)))),
% 1.74/1.98      inference('demod', [status(thm)], ['64', '65', '66'])).
% 1.74/1.98  thf('68', plain, (((sk_A) != (k1_xboole_0))),
% 1.74/1.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.98  thf('69', plain, ((r1_tarski @ (k1_tarski @ sk_B) @ sk_A)),
% 1.74/1.98      inference('simplify_reflect-', [status(thm)], ['67', '68'])).
% 1.74/1.98  thf('70', plain, ($false), inference('demod', [status(thm)], ['7', '69'])).
% 1.74/1.98  
% 1.74/1.98  % SZS output end Refutation
% 1.74/1.98  
% 1.82/1.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qqF70Ip52S

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  147 (1233 expanded)
%              Number of leaves         :   28 ( 369 expanded)
%              Depth                    :   31
%              Number of atoms          : 1338 (12734 expanded)
%              Number of equality atoms :  190 (1739 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t28_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
        & ( A != C )
        & ( A != D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
          & ( A != C )
          & ( A != D ) ) ),
    inference('cnf.neg',[status(esa)],[t28_zfmisc_1])).

thf('0',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_enumset1 @ X20 @ X20 @ X21 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('2',plain,(
    r1_tarski @ ( k1_enumset1 @ sk_A @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    r1_tarski @ ( k1_enumset1 @ sk_A @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('4',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( X28
        = ( k2_tarski @ X26 @ X27 ) )
      | ( X28
        = ( k1_tarski @ X27 ) )
      | ( X28
        = ( k1_tarski @ X26 ) )
      | ( X28 = k1_xboole_0 )
      | ~ ( r1_tarski @ X28 @ ( k2_tarski @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('5',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D_1 ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k2_tarski @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X26: $i,X28: $i,X29: $i] :
      ( ( r1_tarski @ X28 @ ( k2_tarski @ X26 @ X29 ) )
      | ( X28
       != ( k1_tarski @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('7',plain,(
    ! [X26: $i,X29: $i] :
      ( r1_tarski @ ( k1_tarski @ X29 ) @ ( k2_tarski @ X26 @ X29 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_D_1 ) @ ( k1_enumset1 @ sk_A @ sk_A @ sk_B ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D_1 ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_enumset1 @ X20 @ X20 @ X21 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t25_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        & ( A != B )
        & ( A != C ) ) )).

thf('10',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X33 = X32 )
      | ( X33 = X34 )
      | ~ ( r1_tarski @ ( k1_tarski @ X33 ) @ ( k2_tarski @ X32 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t25_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X2 ) @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
      | ( X2 = X0 )
      | ( X2 = X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D_1 ) )
    | ( sk_D_1 = sk_A )
    | ( sk_D_1 = sk_B ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    sk_A != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D_1 ) )
    | ( sk_D_1 = sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_enumset1 @ X20 @ X20 @ X21 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('16',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X15 != X17 )
      | ( r2_hidden @ X15 @ X16 )
      | ( X16
       != ( k2_tarski @ X17 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('17',plain,(
    ! [X14: $i,X17: $i] :
      ( r2_hidden @ X17 @ ( k2_tarski @ X17 @ X14 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','17'])).

thf('19',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_D_1 ) )
    | ( sk_D_1 = sk_B )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','18'])).

thf(t94_enumset1,axiom,(
    ! [A: $i] :
      ( ( k5_enumset1 @ A @ A @ A @ A @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('20',plain,(
    ! [X25: $i] :
      ( ( k5_enumset1 @ X25 @ X25 @ X25 @ X25 @ X25 @ X25 @ X25 )
      = ( k1_tarski @ X25 ) ) ),
    inference(cnf,[status(esa)],[t94_enumset1])).

thf(t89_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_enumset1 @ A @ A @ A @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('21',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k5_enumset1 @ X22 @ X22 @ X22 @ X22 @ X22 @ X23 @ X24 )
      = ( k1_enumset1 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t89_enumset1])).

thf('22',plain,(
    ! [X25: $i] :
      ( ( k1_enumset1 @ X25 @ X25 @ X25 )
      = ( k1_tarski @ X25 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_enumset1 @ X20 @ X20 @ X21 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('24',plain,(
    ! [X14: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X16 )
      | ( X18 = X17 )
      | ( X18 = X14 )
      | ( X16
       != ( k2_tarski @ X17 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('25',plain,(
    ! [X14: $i,X17: $i,X18: $i] :
      ( ( X18 = X14 )
      | ( X18 = X17 )
      | ~ ( r2_hidden @ X18 @ ( k2_tarski @ X17 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
      | ( X2 = X1 )
      | ( X2 = X0 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['22','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( sk_D_1 = sk_B )
    | ( sk_A = sk_D_1 ) ),
    inference('sup-',[status(thm)],['19','28'])).

thf('30',plain,(
    sk_A != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( sk_D_1 = sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','17'])).

thf('33',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C ) )
    | ( sk_D_1 = sk_B )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('35',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_D_1 = sk_B )
    | ( sk_A = sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_D_1 = sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_enumset1 @ X20 @ X20 @ X21 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('39',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X15 != X14 )
      | ( r2_hidden @ X15 @ X16 )
      | ( X16
       != ( k2_tarski @ X17 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('40',plain,(
    ! [X14: $i,X17: $i] :
      ( r2_hidden @ X14 @ ( k2_tarski @ X17 @ X14 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','40'])).

thf('42',plain,
    ( ( r2_hidden @ sk_B @ k1_xboole_0 )
    | ( sk_D_1 = sk_B ) ),
    inference('sup+',[status(thm)],['37','41'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('43',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('44',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t89_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) )).

thf('50',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t89_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf(t74_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ B ) ) )).

thf('52',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_xboole_0 @ X9 @ X10 )
      | ( r1_xboole_0 @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t74_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k3_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('54',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X8 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['48','55'])).

thf('57',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    sk_D_1 = sk_B ),
    inference(clc,[status(thm)],['42','57'])).

thf('59',plain,(
    r1_tarski @ ( k1_enumset1 @ sk_A @ sk_A @ sk_D_1 ) @ ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['2','58'])).

thf('60',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( sk_D_1 = sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','40'])).

thf('62',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_C ) )
    | ( sk_D_1 = sk_B )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('64',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_D_1 = sk_B )
    | ( sk_B = sk_C ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','40'])).

thf('66',plain,
    ( ( r2_hidden @ sk_B @ k1_xboole_0 )
    | ( sk_B = sk_C )
    | ( sk_D_1 = sk_B ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('68',plain,
    ( ( sk_D_1 = sk_B )
    | ( sk_B = sk_C ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D_1 ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k2_tarski @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('70',plain,(
    ! [X14: $i,X17: $i] :
      ( r2_hidden @ X17 @ ( k2_tarski @ X17 @ X14 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('71',plain,
    ( ( r2_hidden @ sk_C @ ( k1_enumset1 @ sk_A @ sk_A @ sk_B ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D_1 ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
      | ( X2 = X1 )
      | ( X2 = X0 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('73',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D_1 ) )
    | ( sk_C = sk_B )
    | ( sk_C = sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D_1 ) )
    | ( sk_C = sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_D_1 )
      = ( k1_tarski @ sk_D_1 ) )
    | ( sk_B = sk_C )
    | ( sk_C = sk_B )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['68','75'])).

thf('77',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( sk_B = sk_C )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_D_1 )
      = ( k1_tarski @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    sk_D_1 = sk_B ),
    inference(clc,[status(thm)],['42','57'])).

thf('79',plain,(
    sk_D_1 = sk_B ),
    inference(clc,[status(thm)],['42','57'])).

thf('80',plain,(
    sk_D_1 = sk_B ),
    inference(clc,[status(thm)],['42','57'])).

thf('81',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_D_1 )
      = k1_xboole_0 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_D_1 )
      = ( k1_tarski @ sk_C ) )
    | ( sk_D_1 = sk_C )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_D_1 )
      = ( k1_tarski @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['77','78','79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','17'])).

thf('83',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_D_1 ) )
    | ( sk_D_1 = sk_C )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_D_1 )
      = ( k1_tarski @ sk_C ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('85',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_D_1 )
      = k1_xboole_0 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_D_1 )
      = ( k1_tarski @ sk_C ) )
    | ( sk_D_1 = sk_C )
    | ( sk_A = sk_D_1 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    sk_A != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_D_1 )
      = k1_xboole_0 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_D_1 )
      = ( k1_tarski @ sk_C ) )
    | ( sk_D_1 = sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','40'])).

thf('89',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k1_tarski @ sk_C ) )
    | ( sk_D_1 = sk_C )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('91',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_D_1 )
      = k1_xboole_0 )
    | ( sk_D_1 = sk_C ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','40'])).

thf('93',plain,
    ( ( r2_hidden @ sk_D_1 @ k1_xboole_0 )
    | ( sk_D_1 = sk_C ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('95',plain,(
    sk_D_1 = sk_C ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,(
    sk_D_1 = sk_C ),
    inference(clc,[status(thm)],['93','94'])).

thf('97',plain,(
    ! [X25: $i] :
      ( ( k1_enumset1 @ X25 @ X25 @ X25 )
      = ( k1_tarski @ X25 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('98',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_enumset1 @ X20 @ X20 @ X21 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
      = ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    r1_tarski @ ( k1_enumset1 @ sk_A @ sk_A @ sk_C ) @ ( k1_tarski @ sk_C ) ),
    inference(demod,[status(thm)],['59','95','96','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
      = ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('102',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( X28
        = ( k2_tarski @ X26 @ X27 ) )
      | ( X28
        = ( k1_tarski @ X27 ) )
      | ( X28
        = ( k1_tarski @ X26 ) )
      | ( X28 = k1_xboole_0 )
      | ~ ( r1_tarski @ X28 @ ( k2_tarski @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
      = ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_C )
      = ( k1_tarski @ sk_C ) ) ),
    inference('sup-',[status(thm)],['100','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','17'])).

thf('109',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('111',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( sk_A = sk_C ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( k1_enumset1 @ sk_A @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','40'])).

thf('115',plain,(
    r2_hidden @ sk_C @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('117',plain,(
    $false ),
    inference('sup-',[status(thm)],['115','116'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qqF70Ip52S
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:39:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 199 iterations in 0.084s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.20/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.53  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.53  thf(t28_zfmisc_1, conjecture,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.53     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.20/0.53          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.53        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.20/0.53             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D_1))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t70_enumset1, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      (![X20 : $i, X21 : $i]:
% 0.20/0.53         ((k1_enumset1 @ X20 @ X20 @ X21) = (k2_tarski @ X20 @ X21))),
% 0.20/0.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      ((r1_tarski @ (k1_enumset1 @ sk_A @ sk_A @ sk_B) @ 
% 0.20/0.53        (k2_tarski @ sk_C @ sk_D_1))),
% 0.20/0.53      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      ((r1_tarski @ (k1_enumset1 @ sk_A @ sk_A @ sk_B) @ 
% 0.20/0.53        (k2_tarski @ sk_C @ sk_D_1))),
% 0.20/0.53      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.53  thf(l45_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.20/0.53       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.20/0.53            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.20/0.53         (((X28) = (k2_tarski @ X26 @ X27))
% 0.20/0.53          | ((X28) = (k1_tarski @ X27))
% 0.20/0.53          | ((X28) = (k1_tarski @ X26))
% 0.20/0.53          | ((X28) = (k1_xboole_0))
% 0.20/0.53          | ~ (r1_tarski @ X28 @ (k2_tarski @ X26 @ X27)))),
% 0.20/0.53      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      ((((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0))
% 0.20/0.53        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.20/0.53        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_D_1))
% 0.20/0.53        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k2_tarski @ sk_C @ sk_D_1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (![X26 : $i, X28 : $i, X29 : $i]:
% 0.20/0.53         ((r1_tarski @ X28 @ (k2_tarski @ X26 @ X29))
% 0.20/0.53          | ((X28) != (k1_tarski @ X29)))),
% 0.20/0.53      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X26 : $i, X29 : $i]:
% 0.20/0.53         (r1_tarski @ (k1_tarski @ X29) @ (k2_tarski @ X26 @ X29))),
% 0.20/0.53      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (((r1_tarski @ (k1_tarski @ sk_D_1) @ (k1_enumset1 @ sk_A @ sk_A @ sk_B))
% 0.20/0.53        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_D_1))
% 0.20/0.53        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.20/0.53        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['5', '7'])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (![X20 : $i, X21 : $i]:
% 0.20/0.53         ((k1_enumset1 @ X20 @ X20 @ X21) = (k2_tarski @ X20 @ X21))),
% 0.20/0.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.53  thf(t25_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.20/0.53          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.20/0.53         (((X33) = (X32))
% 0.20/0.53          | ((X33) = (X34))
% 0.20/0.53          | ~ (r1_tarski @ (k1_tarski @ X33) @ (k2_tarski @ X32 @ X34)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t25_zfmisc_1])).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         (~ (r1_tarski @ (k1_tarski @ X2) @ (k1_enumset1 @ X1 @ X1 @ X0))
% 0.20/0.53          | ((X2) = (X0))
% 0.20/0.53          | ((X2) = (X1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      ((((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0))
% 0.20/0.53        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.20/0.53        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_D_1))
% 0.20/0.53        | ((sk_D_1) = (sk_A))
% 0.20/0.53        | ((sk_D_1) = (sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['8', '11'])).
% 0.20/0.53  thf('13', plain, (((sk_A) != (sk_D_1))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      ((((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0))
% 0.20/0.53        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.20/0.53        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_D_1))
% 0.20/0.53        | ((sk_D_1) = (sk_B)))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (![X20 : $i, X21 : $i]:
% 0.20/0.53         ((k1_enumset1 @ X20 @ X20 @ X21) = (k2_tarski @ X20 @ X21))),
% 0.20/0.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.53  thf(d2_tarski, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.20/0.53       ( ![D:$i]:
% 0.20/0.53         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.53         (((X15) != (X17))
% 0.20/0.53          | (r2_hidden @ X15 @ X16)
% 0.20/0.53          | ((X16) != (k2_tarski @ X17 @ X14)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (![X14 : $i, X17 : $i]: (r2_hidden @ X17 @ (k2_tarski @ X17 @ X14))),
% 0.20/0.53      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['15', '17'])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (((r2_hidden @ sk_A @ (k1_tarski @ sk_D_1))
% 0.20/0.53        | ((sk_D_1) = (sk_B))
% 0.20/0.53        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.20/0.53        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['14', '18'])).
% 0.20/0.53  thf(t94_enumset1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( k5_enumset1 @ A @ A @ A @ A @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (![X25 : $i]:
% 0.20/0.53         ((k5_enumset1 @ X25 @ X25 @ X25 @ X25 @ X25 @ X25 @ X25)
% 0.20/0.53           = (k1_tarski @ X25))),
% 0.20/0.53      inference('cnf', [status(esa)], [t94_enumset1])).
% 0.20/0.53  thf(t89_enumset1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( k5_enumset1 @ A @ A @ A @ A @ A @ B @ C ) =
% 0.20/0.53       ( k1_enumset1 @ A @ B @ C ) ))).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.53         ((k5_enumset1 @ X22 @ X22 @ X22 @ X22 @ X22 @ X23 @ X24)
% 0.20/0.53           = (k1_enumset1 @ X22 @ X23 @ X24))),
% 0.20/0.53      inference('cnf', [status(esa)], [t89_enumset1])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      (![X25 : $i]: ((k1_enumset1 @ X25 @ X25 @ X25) = (k1_tarski @ X25))),
% 0.20/0.53      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      (![X20 : $i, X21 : $i]:
% 0.20/0.53         ((k1_enumset1 @ X20 @ X20 @ X21) = (k2_tarski @ X20 @ X21))),
% 0.20/0.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      (![X14 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X18 @ X16)
% 0.20/0.53          | ((X18) = (X17))
% 0.20/0.53          | ((X18) = (X14))
% 0.20/0.53          | ((X16) != (k2_tarski @ X17 @ X14)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (![X14 : $i, X17 : $i, X18 : $i]:
% 0.20/0.53         (((X18) = (X14))
% 0.20/0.53          | ((X18) = (X17))
% 0.20/0.53          | ~ (r2_hidden @ X18 @ (k2_tarski @ X17 @ X14)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X2 @ (k1_enumset1 @ X1 @ X1 @ X0))
% 0.20/0.53          | ((X2) = (X1))
% 0.20/0.53          | ((X2) = (X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['23', '25'])).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['22', '26'])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['27'])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      ((((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0))
% 0.20/0.53        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.20/0.53        | ((sk_D_1) = (sk_B))
% 0.20/0.53        | ((sk_A) = (sk_D_1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['19', '28'])).
% 0.20/0.53  thf('30', plain, (((sk_A) != (sk_D_1))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      ((((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0))
% 0.20/0.53        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.20/0.53        | ((sk_D_1) = (sk_B)))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['15', '17'])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      (((r2_hidden @ sk_A @ (k1_tarski @ sk_C))
% 0.20/0.53        | ((sk_D_1) = (sk_B))
% 0.20/0.53        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['31', '32'])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['27'])).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      ((((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0))
% 0.20/0.53        | ((sk_D_1) = (sk_B))
% 0.20/0.53        | ((sk_A) = (sk_C)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.53  thf('36', plain, (((sk_A) != (sk_C))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      ((((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0))
% 0.20/0.53        | ((sk_D_1) = (sk_B)))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['35', '36'])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      (![X20 : $i, X21 : $i]:
% 0.20/0.53         ((k1_enumset1 @ X20 @ X20 @ X21) = (k2_tarski @ X20 @ X21))),
% 0.20/0.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.53  thf('39', plain,
% 0.20/0.53      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.53         (((X15) != (X14))
% 0.20/0.53          | (r2_hidden @ X15 @ X16)
% 0.20/0.53          | ((X16) != (k2_tarski @ X17 @ X14)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      (![X14 : $i, X17 : $i]: (r2_hidden @ X14 @ (k2_tarski @ X17 @ X14))),
% 0.20/0.53      inference('simplify', [status(thm)], ['39'])).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['38', '40'])).
% 0.20/0.53  thf('42', plain, (((r2_hidden @ sk_B @ k1_xboole_0) | ((sk_D_1) = (sk_B)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['37', '41'])).
% 0.20/0.53  thf(t4_boole, axiom,
% 0.20/0.53    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      (![X6 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [t4_boole])).
% 0.20/0.53  thf(t100_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.53  thf('44', plain,
% 0.20/0.53      (![X4 : $i, X5 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ X4 @ X5)
% 0.20/0.53           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.53  thf(t1_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.20/0.53       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.53          | ~ (r2_hidden @ X0 @ X2)
% 0.20/0.53          | ~ (r2_hidden @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.20/0.53  thf('46', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.20/0.53          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.20/0.53          | ~ (r2_hidden @ X2 @ X1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.53  thf('47', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 0.20/0.53          | ~ (r2_hidden @ X1 @ k1_xboole_0)
% 0.20/0.53          | ~ (r2_hidden @ X1 @ (k3_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['43', '46'])).
% 0.20/0.53  thf('48', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X1 @ (k3_xboole_0 @ k1_xboole_0 @ X0))
% 0.20/0.53          | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.20/0.53      inference('simplify', [status(thm)], ['47'])).
% 0.20/0.53  thf('49', plain,
% 0.20/0.53      (![X6 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [t4_boole])).
% 0.20/0.53  thf(t89_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ))).
% 0.20/0.53  thf('50', plain,
% 0.20/0.53      (![X12 : $i, X13 : $i]:
% 0.20/0.53         (r1_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ (k4_xboole_0 @ X12 @ X13))),
% 0.20/0.53      inference('cnf', [status(esa)], [t89_xboole_1])).
% 0.20/0.53  thf('51', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (r1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0)),
% 0.20/0.53      inference('sup+', [status(thm)], ['49', '50'])).
% 0.20/0.53  thf(t74_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ~( ( ~( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) & 
% 0.20/0.53          ( r1_xboole_0 @ A @ B ) ) ))).
% 0.20/0.53  thf('52', plain,
% 0.20/0.53      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.53         (~ (r1_xboole_0 @ X9 @ X10)
% 0.20/0.53          | (r1_xboole_0 @ X9 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t74_xboole_1])).
% 0.20/0.53  thf('53', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (r1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0) @ 
% 0.20/0.53          (k3_xboole_0 @ k1_xboole_0 @ X1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.53  thf(t66_xboole_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.20/0.53       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.20/0.53  thf('54', plain,
% 0.20/0.53      (![X8 : $i]: (((X8) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X8 @ X8))),
% 0.20/0.53      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.20/0.53  thf('55', plain,
% 0.20/0.53      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.53  thf('56', plain,
% 0.20/0.53      (![X1 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['48', '55'])).
% 0.20/0.53  thf('57', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.20/0.53      inference('simplify', [status(thm)], ['56'])).
% 0.20/0.53  thf('58', plain, (((sk_D_1) = (sk_B))),
% 0.20/0.53      inference('clc', [status(thm)], ['42', '57'])).
% 0.20/0.53  thf('59', plain,
% 0.20/0.53      ((r1_tarski @ (k1_enumset1 @ sk_A @ sk_A @ sk_D_1) @ 
% 0.20/0.53        (k2_tarski @ sk_C @ sk_D_1))),
% 0.20/0.53      inference('demod', [status(thm)], ['2', '58'])).
% 0.20/0.53  thf('60', plain,
% 0.20/0.53      ((((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0))
% 0.20/0.53        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.20/0.53        | ((sk_D_1) = (sk_B)))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 0.20/0.53  thf('61', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['38', '40'])).
% 0.20/0.53  thf('62', plain,
% 0.20/0.53      (((r2_hidden @ sk_B @ (k1_tarski @ sk_C))
% 0.20/0.53        | ((sk_D_1) = (sk_B))
% 0.20/0.53        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['60', '61'])).
% 0.20/0.53  thf('63', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['27'])).
% 0.20/0.53  thf('64', plain,
% 0.20/0.53      ((((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0))
% 0.20/0.53        | ((sk_D_1) = (sk_B))
% 0.20/0.53        | ((sk_B) = (sk_C)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['62', '63'])).
% 0.20/0.53  thf('65', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['38', '40'])).
% 0.20/0.53  thf('66', plain,
% 0.20/0.53      (((r2_hidden @ sk_B @ k1_xboole_0)
% 0.20/0.53        | ((sk_B) = (sk_C))
% 0.20/0.53        | ((sk_D_1) = (sk_B)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['64', '65'])).
% 0.20/0.53  thf('67', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.20/0.53      inference('simplify', [status(thm)], ['56'])).
% 0.20/0.53  thf('68', plain, ((((sk_D_1) = (sk_B)) | ((sk_B) = (sk_C)))),
% 0.20/0.53      inference('clc', [status(thm)], ['66', '67'])).
% 0.20/0.53  thf('69', plain,
% 0.20/0.53      ((((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0))
% 0.20/0.53        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.20/0.53        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_D_1))
% 0.20/0.53        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k2_tarski @ sk_C @ sk_D_1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.53  thf('70', plain,
% 0.20/0.53      (![X14 : $i, X17 : $i]: (r2_hidden @ X17 @ (k2_tarski @ X17 @ X14))),
% 0.20/0.53      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.53  thf('71', plain,
% 0.20/0.53      (((r2_hidden @ sk_C @ (k1_enumset1 @ sk_A @ sk_A @ sk_B))
% 0.20/0.53        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_D_1))
% 0.20/0.53        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.20/0.53        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['69', '70'])).
% 0.20/0.53  thf('72', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X2 @ (k1_enumset1 @ X1 @ X1 @ X0))
% 0.20/0.53          | ((X2) = (X1))
% 0.20/0.53          | ((X2) = (X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['23', '25'])).
% 0.20/0.53  thf('73', plain,
% 0.20/0.53      ((((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0))
% 0.20/0.53        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.20/0.53        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_D_1))
% 0.20/0.53        | ((sk_C) = (sk_B))
% 0.20/0.53        | ((sk_C) = (sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['71', '72'])).
% 0.20/0.53  thf('74', plain, (((sk_A) != (sk_C))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('75', plain,
% 0.20/0.53      ((((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0))
% 0.20/0.53        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.20/0.53        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_D_1))
% 0.20/0.53        | ((sk_C) = (sk_B)))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['73', '74'])).
% 0.20/0.53  thf('76', plain,
% 0.20/0.53      ((((k1_enumset1 @ sk_A @ sk_A @ sk_D_1) = (k1_tarski @ sk_D_1))
% 0.20/0.53        | ((sk_B) = (sk_C))
% 0.20/0.53        | ((sk_C) = (sk_B))
% 0.20/0.53        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.20/0.53        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['68', '75'])).
% 0.20/0.53  thf('77', plain,
% 0.20/0.53      ((((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0))
% 0.20/0.53        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.20/0.53        | ((sk_B) = (sk_C))
% 0.20/0.53        | ((k1_enumset1 @ sk_A @ sk_A @ sk_D_1) = (k1_tarski @ sk_D_1)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['76'])).
% 0.20/0.53  thf('78', plain, (((sk_D_1) = (sk_B))),
% 0.20/0.53      inference('clc', [status(thm)], ['42', '57'])).
% 0.20/0.53  thf('79', plain, (((sk_D_1) = (sk_B))),
% 0.20/0.53      inference('clc', [status(thm)], ['42', '57'])).
% 0.20/0.53  thf('80', plain, (((sk_D_1) = (sk_B))),
% 0.20/0.53      inference('clc', [status(thm)], ['42', '57'])).
% 0.20/0.53  thf('81', plain,
% 0.20/0.53      ((((k1_enumset1 @ sk_A @ sk_A @ sk_D_1) = (k1_xboole_0))
% 0.20/0.53        | ((k1_enumset1 @ sk_A @ sk_A @ sk_D_1) = (k1_tarski @ sk_C))
% 0.20/0.53        | ((sk_D_1) = (sk_C))
% 0.20/0.53        | ((k1_enumset1 @ sk_A @ sk_A @ sk_D_1) = (k1_tarski @ sk_D_1)))),
% 0.20/0.53      inference('demod', [status(thm)], ['77', '78', '79', '80'])).
% 0.20/0.53  thf('82', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['15', '17'])).
% 0.20/0.53  thf('83', plain,
% 0.20/0.53      (((r2_hidden @ sk_A @ (k1_tarski @ sk_D_1))
% 0.20/0.53        | ((sk_D_1) = (sk_C))
% 0.20/0.53        | ((k1_enumset1 @ sk_A @ sk_A @ sk_D_1) = (k1_tarski @ sk_C))
% 0.20/0.53        | ((k1_enumset1 @ sk_A @ sk_A @ sk_D_1) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['81', '82'])).
% 0.20/0.53  thf('84', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['27'])).
% 0.20/0.53  thf('85', plain,
% 0.20/0.53      ((((k1_enumset1 @ sk_A @ sk_A @ sk_D_1) = (k1_xboole_0))
% 0.20/0.53        | ((k1_enumset1 @ sk_A @ sk_A @ sk_D_1) = (k1_tarski @ sk_C))
% 0.20/0.53        | ((sk_D_1) = (sk_C))
% 0.20/0.53        | ((sk_A) = (sk_D_1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['83', '84'])).
% 0.20/0.53  thf('86', plain, (((sk_A) != (sk_D_1))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('87', plain,
% 0.20/0.53      ((((k1_enumset1 @ sk_A @ sk_A @ sk_D_1) = (k1_xboole_0))
% 0.20/0.53        | ((k1_enumset1 @ sk_A @ sk_A @ sk_D_1) = (k1_tarski @ sk_C))
% 0.20/0.53        | ((sk_D_1) = (sk_C)))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['85', '86'])).
% 0.20/0.53  thf('88', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['38', '40'])).
% 0.20/0.53  thf('89', plain,
% 0.20/0.53      (((r2_hidden @ sk_D_1 @ (k1_tarski @ sk_C))
% 0.20/0.53        | ((sk_D_1) = (sk_C))
% 0.20/0.53        | ((k1_enumset1 @ sk_A @ sk_A @ sk_D_1) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['87', '88'])).
% 0.20/0.53  thf('90', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['27'])).
% 0.20/0.53  thf('91', plain,
% 0.20/0.53      ((((k1_enumset1 @ sk_A @ sk_A @ sk_D_1) = (k1_xboole_0))
% 0.20/0.53        | ((sk_D_1) = (sk_C)))),
% 0.20/0.53      inference('clc', [status(thm)], ['89', '90'])).
% 0.20/0.53  thf('92', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['38', '40'])).
% 0.20/0.53  thf('93', plain,
% 0.20/0.53      (((r2_hidden @ sk_D_1 @ k1_xboole_0) | ((sk_D_1) = (sk_C)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['91', '92'])).
% 0.20/0.53  thf('94', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.20/0.53      inference('simplify', [status(thm)], ['56'])).
% 0.20/0.53  thf('95', plain, (((sk_D_1) = (sk_C))),
% 0.20/0.53      inference('clc', [status(thm)], ['93', '94'])).
% 0.20/0.53  thf('96', plain, (((sk_D_1) = (sk_C))),
% 0.20/0.53      inference('clc', [status(thm)], ['93', '94'])).
% 0.20/0.53  thf('97', plain,
% 0.20/0.53      (![X25 : $i]: ((k1_enumset1 @ X25 @ X25 @ X25) = (k1_tarski @ X25))),
% 0.20/0.53      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.53  thf('98', plain,
% 0.20/0.53      (![X20 : $i, X21 : $i]:
% 0.20/0.53         ((k1_enumset1 @ X20 @ X20 @ X21) = (k2_tarski @ X20 @ X21))),
% 0.20/0.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.53  thf('99', plain, (![X0 : $i]: ((k1_tarski @ X0) = (k2_tarski @ X0 @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['97', '98'])).
% 0.20/0.53  thf('100', plain,
% 0.20/0.53      ((r1_tarski @ (k1_enumset1 @ sk_A @ sk_A @ sk_C) @ (k1_tarski @ sk_C))),
% 0.20/0.53      inference('demod', [status(thm)], ['59', '95', '96', '99'])).
% 0.20/0.53  thf('101', plain, (![X0 : $i]: ((k1_tarski @ X0) = (k2_tarski @ X0 @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['97', '98'])).
% 0.20/0.53  thf('102', plain,
% 0.20/0.53      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.20/0.53         (((X28) = (k2_tarski @ X26 @ X27))
% 0.20/0.53          | ((X28) = (k1_tarski @ X27))
% 0.20/0.53          | ((X28) = (k1_tarski @ X26))
% 0.20/0.53          | ((X28) = (k1_xboole_0))
% 0.20/0.53          | ~ (r1_tarski @ X28 @ (k2_tarski @ X26 @ X27)))),
% 0.20/0.53      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.20/0.53  thf('103', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.20/0.53          | ((X1) = (k1_xboole_0))
% 0.20/0.53          | ((X1) = (k1_tarski @ X0))
% 0.20/0.53          | ((X1) = (k1_tarski @ X0))
% 0.20/0.53          | ((X1) = (k2_tarski @ X0 @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['101', '102'])).
% 0.20/0.53  thf('104', plain, (![X0 : $i]: ((k1_tarski @ X0) = (k2_tarski @ X0 @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['97', '98'])).
% 0.20/0.53  thf('105', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.20/0.53          | ((X1) = (k1_xboole_0))
% 0.20/0.53          | ((X1) = (k1_tarski @ X0))
% 0.20/0.53          | ((X1) = (k1_tarski @ X0))
% 0.20/0.53          | ((X1) = (k1_tarski @ X0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['103', '104'])).
% 0.20/0.53  thf('106', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((X1) = (k1_tarski @ X0))
% 0.20/0.53          | ((X1) = (k1_xboole_0))
% 0.20/0.53          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['105'])).
% 0.20/0.53  thf('107', plain,
% 0.20/0.53      ((((k1_enumset1 @ sk_A @ sk_A @ sk_C) = (k1_xboole_0))
% 0.20/0.53        | ((k1_enumset1 @ sk_A @ sk_A @ sk_C) = (k1_tarski @ sk_C)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['100', '106'])).
% 0.20/0.53  thf('108', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['15', '17'])).
% 0.20/0.53  thf('109', plain,
% 0.20/0.53      (((r2_hidden @ sk_A @ (k1_tarski @ sk_C))
% 0.20/0.53        | ((k1_enumset1 @ sk_A @ sk_A @ sk_C) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['107', '108'])).
% 0.20/0.53  thf('110', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['27'])).
% 0.20/0.53  thf('111', plain,
% 0.20/0.53      ((((k1_enumset1 @ sk_A @ sk_A @ sk_C) = (k1_xboole_0))
% 0.20/0.53        | ((sk_A) = (sk_C)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['109', '110'])).
% 0.20/0.53  thf('112', plain, (((sk_A) != (sk_C))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('113', plain, (((k1_enumset1 @ sk_A @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['111', '112'])).
% 0.20/0.53  thf('114', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['38', '40'])).
% 0.20/0.53  thf('115', plain, ((r2_hidden @ sk_C @ k1_xboole_0)),
% 0.20/0.53      inference('sup+', [status(thm)], ['113', '114'])).
% 0.20/0.53  thf('116', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.20/0.53      inference('simplify', [status(thm)], ['56'])).
% 0.20/0.53  thf('117', plain, ($false), inference('sup-', [status(thm)], ['115', '116'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

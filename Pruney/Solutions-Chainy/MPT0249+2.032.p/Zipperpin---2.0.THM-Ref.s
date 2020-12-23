%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ww07XLIJ2D

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:43 EST 2020

% Result     : Theorem 0.57s
% Output     : Refutation 0.57s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 531 expanded)
%              Number of leaves         :   27 ( 172 expanded)
%              Depth                    :   23
%              Number of atoms          :  792 (4259 expanded)
%              Number of equality atoms :  109 ( 673 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t44_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ( B != C )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ( B != C )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t44_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('3',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_1 )
    = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['0','3'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('6',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','12'])).

thf('14',plain,
    ( ( k5_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B_1 @ ( k3_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['4','13'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('16',plain,
    ( ( k5_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) )
    = ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('17',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('18',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('20',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('26',plain,(
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

thf('27',plain,(
    ! [X21: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X25 @ X23 )
      | ( X25 = X24 )
      | ( X25 = X21 )
      | ( X23
       != ( k2_tarski @ X24 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('28',plain,(
    ! [X21: $i,X24: $i,X25: $i] :
      ( ( X25 = X21 )
      | ( X25 = X24 )
      | ~ ( r2_hidden @ X25 @ ( k2_tarski @ X24 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( sk_B @ sk_B_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('33',plain,(
    ! [X55: $i,X57: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X55 ) @ X57 )
      | ~ ( r2_hidden @ X55 @ X57 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('35',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    | ( sk_B_1
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('39',plain,
    ( ( sk_B @ sk_B_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['25','30'])).

thf('40',plain,
    ( ( sk_B_1
      = ( k1_tarski @ sk_A ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k5_xboole_0 @ sk_C_1 @ sk_B_1 )
    = ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['16','42'])).

thf('44',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('45',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k5_xboole_0 @ sk_C_1 @ ( k5_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','12'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k5_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','12'])).

thf('53',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_1 )
    = ( k5_xboole_0 @ sk_C_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('55',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('57',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B_1 @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k4_xboole_0 @ sk_B_1 @ X0 ) )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B_1 @ X0 ) )
      | ( ( k4_xboole_0 @ sk_B_1 @ X0 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ sk_B_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ ( k4_xboole_0 @ sk_B_1 @ X0 ) )
      | ( ( k4_xboole_0 @ sk_B_1 @ X0 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ sk_B_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B_1 @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ sk_B_1 @ ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('71',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B_1 @ X0 )
        = k1_xboole_0 )
      | ( sk_B_1
        = ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B_1 @ X0 )
        = ( k5_xboole_0 @ sk_B_1 @ k1_xboole_0 ) )
      | ( sk_B_1
        = ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B_1 @ X0 )
        = sk_B_1 )
      | ( sk_B_1
        = ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( sk_C_1 = sk_B_1 )
    | ( sk_B_1
      = ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['55','77'])).

thf('79',plain,(
    sk_B_1 != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( sk_B_1
    = ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('82',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_1 )
    = ( k5_xboole_0 @ sk_B_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['53','54'])).

thf('84',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('85',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['85','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ww07XLIJ2D
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:33:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.57/0.79  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.57/0.79  % Solved by: fo/fo7.sh
% 0.57/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.57/0.79  % done 464 iterations in 0.323s
% 0.57/0.79  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.57/0.79  % SZS output start Refutation
% 0.57/0.79  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.57/0.79  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.57/0.79  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.57/0.79  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.57/0.79  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.57/0.79  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.57/0.79  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.57/0.79  thf(sk_B_type, type, sk_B: $i > $i).
% 0.57/0.79  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.57/0.79  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.57/0.79  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.57/0.79  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.57/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.57/0.79  thf(t44_zfmisc_1, conjecture,
% 0.57/0.79    (![A:$i,B:$i,C:$i]:
% 0.57/0.79     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.57/0.79          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.57/0.79          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.57/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.57/0.79    (~( ![A:$i,B:$i,C:$i]:
% 0.57/0.79        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.57/0.79             ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.57/0.79             ( ( C ) != ( k1_xboole_0 ) ) ) ) )),
% 0.57/0.79    inference('cnf.neg', [status(esa)], [t44_zfmisc_1])).
% 0.57/0.79  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf(t95_xboole_1, axiom,
% 0.57/0.79    (![A:$i,B:$i]:
% 0.57/0.79     ( ( k3_xboole_0 @ A @ B ) =
% 0.57/0.79       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.57/0.79  thf('1', plain,
% 0.57/0.79      (![X19 : $i, X20 : $i]:
% 0.57/0.79         ((k3_xboole_0 @ X19 @ X20)
% 0.57/0.79           = (k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ 
% 0.57/0.79              (k2_xboole_0 @ X19 @ X20)))),
% 0.57/0.79      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.57/0.79  thf(t91_xboole_1, axiom,
% 0.57/0.79    (![A:$i,B:$i,C:$i]:
% 0.57/0.79     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.57/0.79       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.57/0.79  thf('2', plain,
% 0.57/0.79      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.57/0.79         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 0.57/0.79           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 0.57/0.79      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.57/0.79  thf('3', plain,
% 0.57/0.79      (![X19 : $i, X20 : $i]:
% 0.57/0.79         ((k3_xboole_0 @ X19 @ X20)
% 0.57/0.79           = (k5_xboole_0 @ X19 @ 
% 0.57/0.79              (k5_xboole_0 @ X20 @ (k2_xboole_0 @ X19 @ X20))))),
% 0.57/0.79      inference('demod', [status(thm)], ['1', '2'])).
% 0.57/0.79  thf('4', plain,
% 0.57/0.79      (((k3_xboole_0 @ sk_B_1 @ sk_C_1)
% 0.57/0.79         = (k5_xboole_0 @ sk_B_1 @ (k5_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A))))),
% 0.57/0.79      inference('sup+', [status(thm)], ['0', '3'])).
% 0.57/0.79  thf(t92_xboole_1, axiom,
% 0.57/0.79    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.57/0.79  thf('5', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ X18) = (k1_xboole_0))),
% 0.57/0.79      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.57/0.79  thf('6', plain,
% 0.57/0.79      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.57/0.79         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 0.57/0.79           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 0.57/0.79      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.57/0.79  thf('7', plain,
% 0.57/0.79      (![X0 : $i, X1 : $i]:
% 0.57/0.79         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.57/0.79           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.57/0.79      inference('sup+', [status(thm)], ['5', '6'])).
% 0.57/0.79  thf('8', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ X18) = (k1_xboole_0))),
% 0.57/0.79      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.57/0.79  thf('9', plain,
% 0.57/0.79      (![X0 : $i, X1 : $i]:
% 0.57/0.79         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.57/0.79           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.57/0.79      inference('sup+', [status(thm)], ['5', '6'])).
% 0.57/0.79  thf('10', plain,
% 0.57/0.79      (![X0 : $i]:
% 0.57/0.79         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.57/0.79      inference('sup+', [status(thm)], ['8', '9'])).
% 0.57/0.79  thf(t5_boole, axiom,
% 0.57/0.79    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.57/0.79  thf('11', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.57/0.79      inference('cnf', [status(esa)], [t5_boole])).
% 0.57/0.79  thf('12', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.57/0.79      inference('demod', [status(thm)], ['10', '11'])).
% 0.57/0.79  thf('13', plain,
% 0.57/0.79      (![X0 : $i, X1 : $i]:
% 0.57/0.79         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.57/0.79      inference('demod', [status(thm)], ['7', '12'])).
% 0.57/0.79  thf('14', plain,
% 0.57/0.79      (((k5_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A))
% 0.57/0.79         = (k5_xboole_0 @ sk_B_1 @ (k3_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 0.57/0.79      inference('sup+', [status(thm)], ['4', '13'])).
% 0.57/0.79  thf(t100_xboole_1, axiom,
% 0.57/0.79    (![A:$i,B:$i]:
% 0.57/0.79     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.57/0.79  thf('15', plain,
% 0.57/0.79      (![X8 : $i, X9 : $i]:
% 0.57/0.79         ((k4_xboole_0 @ X8 @ X9)
% 0.57/0.79           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.57/0.79      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.57/0.79  thf('16', plain,
% 0.57/0.79      (((k5_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A))
% 0.57/0.79         = (k4_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.57/0.79      inference('demod', [status(thm)], ['14', '15'])).
% 0.57/0.79  thf(t7_xboole_0, axiom,
% 0.57/0.79    (![A:$i]:
% 0.57/0.79     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.57/0.79          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.57/0.79  thf('17', plain,
% 0.57/0.79      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.57/0.79      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.57/0.79  thf('18', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf(t7_xboole_1, axiom,
% 0.57/0.79    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.57/0.79  thf('19', plain,
% 0.57/0.79      (![X13 : $i, X14 : $i]: (r1_tarski @ X13 @ (k2_xboole_0 @ X13 @ X14))),
% 0.57/0.79      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.57/0.79  thf('20', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.57/0.79      inference('sup+', [status(thm)], ['18', '19'])).
% 0.57/0.79  thf(d3_tarski, axiom,
% 0.57/0.79    (![A:$i,B:$i]:
% 0.57/0.79     ( ( r1_tarski @ A @ B ) <=>
% 0.57/0.79       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.57/0.79  thf('21', plain,
% 0.57/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.79         (~ (r2_hidden @ X0 @ X1)
% 0.57/0.79          | (r2_hidden @ X0 @ X2)
% 0.57/0.79          | ~ (r1_tarski @ X1 @ X2))),
% 0.57/0.79      inference('cnf', [status(esa)], [d3_tarski])).
% 0.57/0.79  thf('22', plain,
% 0.57/0.79      (![X0 : $i]:
% 0.57/0.79         ((r2_hidden @ X0 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.57/0.79      inference('sup-', [status(thm)], ['20', '21'])).
% 0.57/0.79  thf('23', plain,
% 0.57/0.79      ((((sk_B_1) = (k1_xboole_0))
% 0.57/0.79        | (r2_hidden @ (sk_B @ sk_B_1) @ (k1_tarski @ sk_A)))),
% 0.57/0.79      inference('sup-', [status(thm)], ['17', '22'])).
% 0.57/0.79  thf('24', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('25', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (k1_tarski @ sk_A))),
% 0.57/0.79      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.57/0.79  thf(t69_enumset1, axiom,
% 0.57/0.79    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.57/0.79  thf('26', plain,
% 0.57/0.79      (![X27 : $i]: ((k2_tarski @ X27 @ X27) = (k1_tarski @ X27))),
% 0.57/0.79      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.57/0.79  thf(d2_tarski, axiom,
% 0.57/0.79    (![A:$i,B:$i,C:$i]:
% 0.57/0.79     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.57/0.79       ( ![D:$i]:
% 0.57/0.79         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.57/0.79  thf('27', plain,
% 0.57/0.79      (![X21 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.57/0.79         (~ (r2_hidden @ X25 @ X23)
% 0.57/0.79          | ((X25) = (X24))
% 0.57/0.79          | ((X25) = (X21))
% 0.57/0.79          | ((X23) != (k2_tarski @ X24 @ X21)))),
% 0.57/0.79      inference('cnf', [status(esa)], [d2_tarski])).
% 0.57/0.79  thf('28', plain,
% 0.57/0.79      (![X21 : $i, X24 : $i, X25 : $i]:
% 0.57/0.79         (((X25) = (X21))
% 0.57/0.79          | ((X25) = (X24))
% 0.57/0.79          | ~ (r2_hidden @ X25 @ (k2_tarski @ X24 @ X21)))),
% 0.57/0.79      inference('simplify', [status(thm)], ['27'])).
% 0.57/0.79  thf('29', plain,
% 0.57/0.79      (![X0 : $i, X1 : $i]:
% 0.57/0.79         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.57/0.79      inference('sup-', [status(thm)], ['26', '28'])).
% 0.57/0.79  thf('30', plain,
% 0.57/0.79      (![X0 : $i, X1 : $i]:
% 0.57/0.79         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.57/0.79      inference('simplify', [status(thm)], ['29'])).
% 0.57/0.79  thf('31', plain, (((sk_B @ sk_B_1) = (sk_A))),
% 0.57/0.79      inference('sup-', [status(thm)], ['25', '30'])).
% 0.57/0.79  thf('32', plain,
% 0.57/0.79      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.57/0.79      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.57/0.79  thf(l1_zfmisc_1, axiom,
% 0.57/0.79    (![A:$i,B:$i]:
% 0.57/0.79     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.57/0.79  thf('33', plain,
% 0.57/0.79      (![X55 : $i, X57 : $i]:
% 0.57/0.79         ((r1_tarski @ (k1_tarski @ X55) @ X57) | ~ (r2_hidden @ X55 @ X57))),
% 0.57/0.79      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.57/0.79  thf('34', plain,
% 0.57/0.79      (![X0 : $i]:
% 0.57/0.79         (((X0) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.57/0.79      inference('sup-', [status(thm)], ['32', '33'])).
% 0.57/0.79  thf(d10_xboole_0, axiom,
% 0.57/0.79    (![A:$i,B:$i]:
% 0.57/0.79     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.57/0.79  thf('35', plain,
% 0.57/0.79      (![X5 : $i, X7 : $i]:
% 0.57/0.79         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 0.57/0.79      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.57/0.79  thf('36', plain,
% 0.57/0.79      (![X0 : $i]:
% 0.57/0.79         (((X0) = (k1_xboole_0))
% 0.57/0.79          | ~ (r1_tarski @ X0 @ (k1_tarski @ (sk_B @ X0)))
% 0.57/0.79          | ((X0) = (k1_tarski @ (sk_B @ X0))))),
% 0.57/0.79      inference('sup-', [status(thm)], ['34', '35'])).
% 0.57/0.79  thf('37', plain,
% 0.57/0.79      ((~ (r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.57/0.79        | ((sk_B_1) = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.57/0.79        | ((sk_B_1) = (k1_xboole_0)))),
% 0.57/0.79      inference('sup-', [status(thm)], ['31', '36'])).
% 0.57/0.79  thf('38', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.57/0.79      inference('sup+', [status(thm)], ['18', '19'])).
% 0.57/0.79  thf('39', plain, (((sk_B @ sk_B_1) = (sk_A))),
% 0.57/0.79      inference('sup-', [status(thm)], ['25', '30'])).
% 0.57/0.79  thf('40', plain,
% 0.57/0.79      ((((sk_B_1) = (k1_tarski @ sk_A)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.57/0.79      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.57/0.79  thf('41', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('42', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 0.57/0.79      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 0.57/0.79  thf('43', plain,
% 0.57/0.79      (((k5_xboole_0 @ sk_C_1 @ sk_B_1) = (k4_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.57/0.79      inference('demod', [status(thm)], ['16', '42'])).
% 0.57/0.79  thf('44', plain,
% 0.57/0.79      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.57/0.79         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 0.57/0.79           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 0.57/0.79      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.57/0.79  thf('45', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ X18) = (k1_xboole_0))),
% 0.57/0.79      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.57/0.79  thf('46', plain,
% 0.57/0.79      (![X0 : $i, X1 : $i]:
% 0.57/0.79         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 0.57/0.79           = (k1_xboole_0))),
% 0.57/0.79      inference('sup+', [status(thm)], ['44', '45'])).
% 0.57/0.79  thf('47', plain,
% 0.57/0.79      (((k5_xboole_0 @ sk_C_1 @ 
% 0.57/0.79         (k5_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ sk_B_1 @ sk_C_1)))
% 0.57/0.79         = (k1_xboole_0))),
% 0.57/0.79      inference('sup+', [status(thm)], ['43', '46'])).
% 0.57/0.79  thf('48', plain,
% 0.57/0.79      (![X8 : $i, X9 : $i]:
% 0.57/0.79         ((k4_xboole_0 @ X8 @ X9)
% 0.57/0.79           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.57/0.79      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.57/0.79  thf('49', plain,
% 0.57/0.79      (![X0 : $i, X1 : $i]:
% 0.57/0.79         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.57/0.79      inference('demod', [status(thm)], ['7', '12'])).
% 0.57/0.79  thf('50', plain,
% 0.57/0.79      (![X0 : $i, X1 : $i]:
% 0.57/0.79         ((k3_xboole_0 @ X1 @ X0)
% 0.57/0.79           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.57/0.79      inference('sup+', [status(thm)], ['48', '49'])).
% 0.57/0.79  thf('51', plain,
% 0.57/0.79      (((k5_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ sk_B_1 @ sk_C_1))
% 0.57/0.79         = (k1_xboole_0))),
% 0.57/0.79      inference('demod', [status(thm)], ['47', '50'])).
% 0.57/0.79  thf('52', plain,
% 0.57/0.79      (![X0 : $i, X1 : $i]:
% 0.57/0.79         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.57/0.79      inference('demod', [status(thm)], ['7', '12'])).
% 0.57/0.79  thf('53', plain,
% 0.57/0.79      (((k3_xboole_0 @ sk_B_1 @ sk_C_1) = (k5_xboole_0 @ sk_C_1 @ k1_xboole_0))),
% 0.57/0.79      inference('sup+', [status(thm)], ['51', '52'])).
% 0.57/0.79  thf('54', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.57/0.79      inference('cnf', [status(esa)], [t5_boole])).
% 0.57/0.79  thf('55', plain, (((k3_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_C_1))),
% 0.57/0.79      inference('demod', [status(thm)], ['53', '54'])).
% 0.57/0.79  thf('56', plain,
% 0.57/0.79      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.57/0.79      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.57/0.79  thf(t36_xboole_1, axiom,
% 0.57/0.79    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.57/0.79  thf('57', plain,
% 0.57/0.79      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 0.57/0.79      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.57/0.79  thf('58', plain,
% 0.57/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.79         (~ (r2_hidden @ X0 @ X1)
% 0.57/0.79          | (r2_hidden @ X0 @ X2)
% 0.57/0.79          | ~ (r1_tarski @ X1 @ X2))),
% 0.57/0.79      inference('cnf', [status(esa)], [d3_tarski])).
% 0.57/0.79  thf('59', plain,
% 0.57/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.79         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.57/0.79      inference('sup-', [status(thm)], ['57', '58'])).
% 0.57/0.79  thf('60', plain,
% 0.57/0.79      (![X0 : $i, X1 : $i]:
% 0.57/0.79         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.57/0.79          | (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.57/0.79      inference('sup-', [status(thm)], ['56', '59'])).
% 0.57/0.79  thf('61', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 0.57/0.79      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 0.57/0.79  thf('62', plain,
% 0.57/0.79      (![X0 : $i, X1 : $i]:
% 0.57/0.79         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.57/0.79      inference('simplify', [status(thm)], ['29'])).
% 0.57/0.79  thf('63', plain,
% 0.57/0.79      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_B_1) | ((X0) = (sk_A)))),
% 0.57/0.79      inference('sup-', [status(thm)], ['61', '62'])).
% 0.57/0.79  thf('64', plain,
% 0.57/0.79      (![X0 : $i]:
% 0.57/0.79         (((k4_xboole_0 @ sk_B_1 @ X0) = (k1_xboole_0))
% 0.57/0.79          | ((sk_B @ (k4_xboole_0 @ sk_B_1 @ X0)) = (sk_A)))),
% 0.57/0.79      inference('sup-', [status(thm)], ['60', '63'])).
% 0.57/0.79  thf('65', plain,
% 0.57/0.79      (![X0 : $i]:
% 0.57/0.79         (((X0) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.57/0.79      inference('sup-', [status(thm)], ['32', '33'])).
% 0.57/0.79  thf('66', plain,
% 0.57/0.79      (![X0 : $i]:
% 0.57/0.79         ((r1_tarski @ (k1_tarski @ sk_A) @ (k4_xboole_0 @ sk_B_1 @ X0))
% 0.57/0.79          | ((k4_xboole_0 @ sk_B_1 @ X0) = (k1_xboole_0))
% 0.57/0.79          | ((k4_xboole_0 @ sk_B_1 @ X0) = (k1_xboole_0)))),
% 0.57/0.79      inference('sup+', [status(thm)], ['64', '65'])).
% 0.57/0.79  thf('67', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 0.57/0.79      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 0.57/0.79  thf('68', plain,
% 0.57/0.79      (![X0 : $i]:
% 0.57/0.79         ((r1_tarski @ sk_B_1 @ (k4_xboole_0 @ sk_B_1 @ X0))
% 0.57/0.79          | ((k4_xboole_0 @ sk_B_1 @ X0) = (k1_xboole_0))
% 0.57/0.79          | ((k4_xboole_0 @ sk_B_1 @ X0) = (k1_xboole_0)))),
% 0.57/0.79      inference('demod', [status(thm)], ['66', '67'])).
% 0.57/0.79  thf('69', plain,
% 0.57/0.79      (![X0 : $i]:
% 0.57/0.79         (((k4_xboole_0 @ sk_B_1 @ X0) = (k1_xboole_0))
% 0.57/0.79          | (r1_tarski @ sk_B_1 @ (k4_xboole_0 @ sk_B_1 @ X0)))),
% 0.57/0.79      inference('simplify', [status(thm)], ['68'])).
% 0.57/0.79  thf('70', plain,
% 0.57/0.79      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 0.57/0.79      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.57/0.79  thf('71', plain,
% 0.57/0.79      (![X5 : $i, X7 : $i]:
% 0.57/0.79         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 0.57/0.79      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.57/0.79  thf('72', plain,
% 0.57/0.79      (![X0 : $i, X1 : $i]:
% 0.57/0.79         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.57/0.79          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.57/0.79      inference('sup-', [status(thm)], ['70', '71'])).
% 0.57/0.79  thf('73', plain,
% 0.57/0.79      (![X0 : $i]:
% 0.57/0.79         (((k4_xboole_0 @ sk_B_1 @ X0) = (k1_xboole_0))
% 0.57/0.79          | ((sk_B_1) = (k4_xboole_0 @ sk_B_1 @ X0)))),
% 0.57/0.79      inference('sup-', [status(thm)], ['69', '72'])).
% 0.57/0.79  thf('74', plain,
% 0.57/0.79      (![X0 : $i, X1 : $i]:
% 0.57/0.79         ((k3_xboole_0 @ X1 @ X0)
% 0.57/0.79           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.57/0.79      inference('sup+', [status(thm)], ['48', '49'])).
% 0.57/0.79  thf('75', plain,
% 0.57/0.79      (![X0 : $i]:
% 0.57/0.79         (((k3_xboole_0 @ sk_B_1 @ X0) = (k5_xboole_0 @ sk_B_1 @ k1_xboole_0))
% 0.57/0.79          | ((sk_B_1) = (k4_xboole_0 @ sk_B_1 @ X0)))),
% 0.57/0.79      inference('sup+', [status(thm)], ['73', '74'])).
% 0.57/0.79  thf('76', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.57/0.79      inference('cnf', [status(esa)], [t5_boole])).
% 0.57/0.79  thf('77', plain,
% 0.57/0.79      (![X0 : $i]:
% 0.57/0.79         (((k3_xboole_0 @ sk_B_1 @ X0) = (sk_B_1))
% 0.57/0.79          | ((sk_B_1) = (k4_xboole_0 @ sk_B_1 @ X0)))),
% 0.57/0.79      inference('demod', [status(thm)], ['75', '76'])).
% 0.57/0.79  thf('78', plain,
% 0.57/0.79      ((((sk_C_1) = (sk_B_1)) | ((sk_B_1) = (k4_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 0.57/0.79      inference('sup+', [status(thm)], ['55', '77'])).
% 0.57/0.79  thf('79', plain, (((sk_B_1) != (sk_C_1))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('80', plain, (((sk_B_1) = (k4_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.57/0.79      inference('simplify_reflect-', [status(thm)], ['78', '79'])).
% 0.57/0.79  thf('81', plain,
% 0.57/0.79      (![X0 : $i, X1 : $i]:
% 0.57/0.79         ((k3_xboole_0 @ X1 @ X0)
% 0.57/0.79           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.57/0.79      inference('sup+', [status(thm)], ['48', '49'])).
% 0.57/0.79  thf('82', plain,
% 0.57/0.79      (((k3_xboole_0 @ sk_B_1 @ sk_C_1) = (k5_xboole_0 @ sk_B_1 @ sk_B_1))),
% 0.57/0.79      inference('sup+', [status(thm)], ['80', '81'])).
% 0.57/0.79  thf('83', plain, (((k3_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_C_1))),
% 0.57/0.79      inference('demod', [status(thm)], ['53', '54'])).
% 0.57/0.79  thf('84', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ X18) = (k1_xboole_0))),
% 0.57/0.79      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.57/0.79  thf('85', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.57/0.79      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.57/0.79  thf('86', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('87', plain, ($false),
% 0.57/0.79      inference('simplify_reflect-', [status(thm)], ['85', '86'])).
% 0.57/0.79  
% 0.57/0.79  % SZS output end Refutation
% 0.57/0.79  
% 0.57/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

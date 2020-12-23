%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vnNC1jVjeo

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:53 EST 2020

% Result     : Theorem 5.43s
% Output     : Refutation 5.43s
% Verified   : 
% Statistics : Number of formulae       :  231 (4512 expanded)
%              Number of leaves         :   29 (1354 expanded)
%              Depth                    :   40
%              Number of atoms          : 1965 (44489 expanded)
%              Number of equality atoms :  265 (6405 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    ! [X92: $i,X93: $i] :
      ( ( k1_enumset1 @ X92 @ X92 @ X93 )
      = ( k2_tarski @ X92 @ X93 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('2',plain,(
    r1_tarski @ ( k1_enumset1 @ sk_A @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('4',plain,
    ( ( k2_xboole_0 @ ( k1_enumset1 @ sk_A @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D_1 ) )
    = ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X92: $i,X93: $i] :
      ( ( k1_enumset1 @ X92 @ X92 @ X93 )
      = ( k2_tarski @ X92 @ X93 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t45_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('6',plain,(
    ! [X71: $i,X72: $i,X73: $i,X74: $i] :
      ( ( k2_enumset1 @ X71 @ X72 @ X73 @ X74 )
      = ( k2_xboole_0 @ ( k2_tarski @ X71 @ X72 ) @ ( k2_tarski @ X73 @ X74 ) ) ) ),
    inference(cnf,[status(esa)],[t45_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t104_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ C @ B @ D ) ) )).

thf('8',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( k2_enumset1 @ X40 @ X42 @ X41 @ X43 )
      = ( k2_enumset1 @ X40 @ X41 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t104_enumset1])).

thf('9',plain,
    ( ( k2_enumset1 @ sk_A @ sk_C @ sk_B @ sk_D_1 )
    = ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['4','7','8'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('10',plain,(
    ! [X94: $i,X95: $i,X96: $i] :
      ( ( k2_enumset1 @ X94 @ X94 @ X95 @ X96 )
      = ( k1_enumset1 @ X94 @ X95 @ X96 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('11',plain,(
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

thf('12',plain,(
    ! [X119: $i,X120: $i,X121: $i] :
      ( ( X121
        = ( k2_tarski @ X119 @ X120 ) )
      | ( X121
        = ( k1_tarski @ X120 ) )
      | ( X121
        = ( k1_tarski @ X119 ) )
      | ( X121 = k1_xboole_0 )
      | ~ ( r1_tarski @ X121 @ ( k2_tarski @ X119 @ X120 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('13',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D_1 ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k2_tarski @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('14',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X11 != X10 )
      | ( r2_hidden @ X11 @ X12 )
      | ( X12
       != ( k2_tarski @ X13 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('15',plain,(
    ! [X10: $i,X13: $i] :
      ( r2_hidden @ X10 @ ( k2_tarski @ X13 @ X10 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k1_enumset1 @ sk_A @ sk_A @ sk_B ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D_1 ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X92: $i,X93: $i] :
      ( ( k1_enumset1 @ X92 @ X92 @ X93 )
      = ( k2_tarski @ X92 @ X93 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('18',plain,(
    ! [X10: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X12 )
      | ( X14 = X13 )
      | ( X14 = X10 )
      | ( X12
       != ( k2_tarski @ X13 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('19',plain,(
    ! [X10: $i,X13: $i,X14: $i] :
      ( ( X14 = X10 )
      | ( X14 = X13 )
      | ~ ( r2_hidden @ X14 @ ( k2_tarski @ X13 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
      | ( X2 = X1 )
      | ( X2 = X0 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D_1 ) )
    | ( sk_D_1 = sk_B )
    | ( sk_D_1 = sk_A ) ),
    inference('sup-',[status(thm)],['16','20'])).

thf('22',plain,(
    sk_A != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D_1 ) )
    | ( sk_D_1 = sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X92: $i,X93: $i] :
      ( ( k1_enumset1 @ X92 @ X92 @ X93 )
      = ( k2_tarski @ X92 @ X93 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('25',plain,(
    ! [X10: $i,X13: $i] :
      ( r2_hidden @ X10 @ ( k2_tarski @ X13 @ X10 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_D_1 ) )
    | ( sk_D_1 = sk_B )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('28',plain,(
    ! [X91: $i] :
      ( ( k2_tarski @ X91 @ X91 )
      = ( k1_tarski @ X91 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('29',plain,(
    ! [X10: $i,X13: $i,X14: $i] :
      ( ( X14 = X10 )
      | ( X14 = X13 )
      | ~ ( r2_hidden @ X14 @ ( k2_tarski @ X13 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( sk_D_1 = sk_B )
    | ( sk_B = sk_D_1 ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf('33',plain,
    ( ( sk_D_1 = sk_B )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X92: $i,X93: $i] :
      ( ( k1_enumset1 @ X92 @ X92 @ X93 )
      = ( k2_tarski @ X92 @ X93 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('35',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X11 != X13 )
      | ( r2_hidden @ X11 @ X12 )
      | ( X12
       != ( k2_tarski @ X13 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('36',plain,(
    ! [X10: $i,X13: $i] :
      ( r2_hidden @ X13 @ ( k2_tarski @ X13 @ X10 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','36'])).

thf('38',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_D_1 = sk_B ) ),
    inference('sup+',[status(thm)],['33','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('40',plain,
    ( ( sk_D_1 = sk_B )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_A = sk_C ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( sk_D_1 = sk_B )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X92: $i,X93: $i] :
      ( ( k1_enumset1 @ X92 @ X92 @ X93 )
      = ( k2_tarski @ X92 @ X93 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('44',plain,(
    ! [X119: $i,X121: $i,X122: $i] :
      ( ( r1_tarski @ X121 @ ( k2_tarski @ X119 @ X122 ) )
      | ( X121
       != ( k1_tarski @ X122 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('45',plain,(
    ! [X119: $i,X122: $i] :
      ( r1_tarski @ ( k1_tarski @ X122 ) @ ( k2_tarski @ X119 @ X122 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','45'])).

thf('47',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
    | ( sk_D_1 = sk_B ) ),
    inference('sup+',[status(thm)],['42','46'])).

thf('48',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('49',plain,
    ( ( sk_D_1 = sk_B )
    | ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X91: $i] :
      ( ( k2_tarski @ X91 @ X91 )
      = ( k1_tarski @ X91 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('51',plain,(
    ! [X119: $i,X121: $i,X122: $i] :
      ( ( r1_tarski @ X121 @ ( k2_tarski @ X119 @ X122 ) )
      | ( X121 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('52',plain,(
    ! [X119: $i,X122: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k2_tarski @ X119 @ X122 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','52'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('54',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('58',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('60',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
      = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( sk_D_1 = sk_B )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','63'])).

thf('65',plain,(
    ! [X91: $i] :
      ( ( k2_tarski @ X91 @ X91 )
      = ( k1_tarski @ X91 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('66',plain,(
    ! [X71: $i,X72: $i,X73: $i,X74: $i] :
      ( ( k2_enumset1 @ X71 @ X72 @ X73 @ X74 )
      = ( k2_xboole_0 @ ( k2_tarski @ X71 @ X72 ) @ ( k2_tarski @ X73 @ X74 ) ) ) ),
    inference(cnf,[status(esa)],[t45_enumset1])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_enumset1 @ X1 @ X0 @ sk_B @ sk_B )
        = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ k1_xboole_0 ) )
      | ( sk_D_1 = sk_B ) ) ),
    inference('sup+',[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X119: $i,X122: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k2_tarski @ X119 @ X122 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('70',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k5_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_enumset1 @ X1 @ X0 @ sk_B @ sk_B )
        = ( k2_tarski @ X1 @ X0 ) )
      | ( sk_D_1 = sk_B ) ) ),
    inference(demod,[status(thm)],['68','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( ( k1_enumset1 @ X0 @ sk_B @ sk_B )
        = ( k2_tarski @ X0 @ X0 ) )
      | ( sk_D_1 = sk_B ) ) ),
    inference('sup+',[status(thm)],['10','80'])).

thf('82',plain,(
    ! [X119: $i,X121: $i,X122: $i] :
      ( ( r1_tarski @ X121 @ ( k2_tarski @ X119 @ X122 ) )
      | ( X121
       != ( k1_tarski @ X119 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('83',plain,(
    ! [X119: $i,X122: $i] :
      ( r1_tarski @ ( k1_tarski @ X119 ) @ ( k2_tarski @ X119 @ X122 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_tarski @ X1 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('88',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k5_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X1 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( k2_enumset1 @ X40 @ X42 @ X41 @ X43 )
      = ( k2_enumset1 @ X40 @ X41 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t104_enumset1])).

thf('97',plain,(
    ! [X94: $i,X95: $i,X96: $i] :
      ( ( k2_enumset1 @ X94 @ X94 @ X95 @ X96 )
      = ( k1_enumset1 @ X94 @ X95 @ X96 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['95','98'])).

thf('100',plain,(
    ! [X119: $i,X122: $i] :
      ( r1_tarski @ ( k1_tarski @ X122 ) @ ( k2_tarski @ X119 @ X122 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('101',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X91: $i] :
      ( ( k2_tarski @ X91 @ X91 )
      = ( k1_tarski @ X91 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('104',plain,(
    ! [X71: $i,X72: $i,X73: $i,X74: $i] :
      ( ( k2_enumset1 @ X71 @ X72 @ X73 @ X74 )
      = ( k2_xboole_0 @ ( k2_tarski @ X71 @ X72 ) @ ( k2_tarski @ X73 @ X74 ) ) ) ),
    inference(cnf,[status(esa)],[t45_enumset1])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X94: $i,X95: $i,X96: $i] :
      ( ( k2_enumset1 @ X94 @ X94 @ X95 @ X96 )
      = ( k1_enumset1 @ X94 @ X95 @ X96 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['102','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['99','108'])).

thf('110',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( k2_enumset1 @ X40 @ X42 @ X41 @ X43 )
      = ( k2_enumset1 @ X40 @ X41 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t104_enumset1])).

thf('111',plain,(
    ! [X119: $i,X121: $i,X122: $i] :
      ( ( r1_tarski @ X121 @ ( k2_tarski @ X119 @ X122 ) )
      | ( X121
       != ( k2_tarski @ X119 @ X122 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('112',plain,(
    ! [X119: $i,X122: $i] :
      ( r1_tarski @ ( k2_tarski @ X119 @ X122 ) @ ( k2_tarski @ X119 @ X122 ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X71: $i,X72: $i,X73: $i,X74: $i] :
      ( ( k2_enumset1 @ X71 @ X72 @ X73 @ X74 )
      = ( k2_xboole_0 @ ( k2_tarski @ X71 @ X72 ) @ ( k2_tarski @ X73 @ X74 ) ) ) ),
    inference(cnf,[status(esa)],[t45_enumset1])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['110','116'])).

thf('118',plain,(
    ! [X94: $i,X95: $i,X96: $i] :
      ( ( k2_enumset1 @ X94 @ X94 @ X95 @ X96 )
      = ( k1_enumset1 @ X94 @ X95 @ X96 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['109','119'])).

thf('121',plain,(
    ! [X91: $i] :
      ( ( k2_tarski @ X91 @ X91 )
      = ( k1_tarski @ X91 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ sk_B @ X0 )
        = ( k1_tarski @ X0 ) )
      | ( sk_D_1 = sk_B ) ) ),
    inference(demod,[status(thm)],['81','120','121'])).

thf('123',plain,(
    ! [X10: $i,X13: $i] :
      ( r2_hidden @ X13 @ ( k2_tarski @ X13 @ X10 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ ( k1_tarski @ X0 ) )
      | ( sk_D_1 = sk_B ) ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( sk_D_1 = sk_B )
      | ( sk_B = X0 ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    sk_D_1 = sk_B ),
    inference(condensation,[status(thm)],['126'])).

thf('128',plain,
    ( ( k2_enumset1 @ sk_A @ sk_C @ sk_D_1 @ sk_D_1 )
    = ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['9','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','36'])).

thf('130',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D_1 ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k2_tarski @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('131',plain,(
    ! [X10: $i,X13: $i,X14: $i] :
      ( ( X14 = X10 )
      | ( X14 = X13 )
      | ~ ( r2_hidden @ X14 @ ( k2_tarski @ X13 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_enumset1 @ sk_A @ sk_A @ sk_B ) )
      | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
        = ( k1_tarski @ sk_D_1 ) )
      | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
        = ( k1_tarski @ sk_C ) )
      | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( X0 = sk_C )
      | ( X0 = sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,
    ( ( sk_A = sk_D_1 )
    | ( sk_A = sk_C )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['129','132'])).

thf('134',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    sk_A != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['133','134','135'])).

thf('137',plain,(
    sk_D_1 = sk_B ),
    inference(condensation,[status(thm)],['126'])).

thf('138',plain,(
    sk_D_1 = sk_B ),
    inference(condensation,[status(thm)],['126'])).

thf('139',plain,(
    sk_D_1 = sk_B ),
    inference(condensation,[status(thm)],['126'])).

thf('140',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_D_1 )
      = k1_xboole_0 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_D_1 )
      = ( k1_tarski @ sk_C ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_D_1 )
      = ( k1_tarski @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['136','137','138','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','36'])).

thf('142',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_D_1 ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_D_1 )
      = ( k1_tarski @ sk_C ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('144',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_D_1 )
      = k1_xboole_0 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_D_1 )
      = ( k1_tarski @ sk_C ) )
    | ( sk_A = sk_D_1 ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    sk_A != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_D_1 )
      = k1_xboole_0 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_D_1 )
      = ( k1_tarski @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('148',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k1_tarski @ sk_C ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('150',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_D_1 )
      = k1_xboole_0 )
    | ( sk_D_1 = sk_C ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('152',plain,
    ( ( r2_hidden @ sk_D_1 @ k1_xboole_0 )
    | ( sk_D_1 = sk_C ) ),
    inference('sup+',[status(thm)],['150','151'])).

thf('153',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_D_1 )
      = k1_xboole_0 )
    | ( sk_D_1 = sk_C ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('154',plain,(
    ! [X92: $i,X93: $i] :
      ( ( k1_enumset1 @ X92 @ X92 @ X93 )
      = ( k2_tarski @ X92 @ X93 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('155',plain,(
    ! [X119: $i,X122: $i] :
      ( r1_tarski @ ( k1_tarski @ X119 ) @ ( k2_tarski @ X119 @ X122 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['154','155'])).

thf('157',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
    | ( sk_D_1 = sk_C ) ),
    inference('sup+',[status(thm)],['153','156'])).

thf('158',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('159',plain,
    ( ( sk_D_1 = sk_C )
    | ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('161',plain,
    ( ( sk_D_1 = sk_C )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( sk_D_1 = sk_C )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,
    ( ( sk_D_1 = sk_C )
    | ( sk_D_1 = sk_A )
    | ( sk_D_1 = sk_C ) ),
    inference('sup-',[status(thm)],['152','163'])).

thf('165',plain,
    ( ( sk_D_1 = sk_A )
    | ( sk_D_1 = sk_C ) ),
    inference(simplify,[status(thm)],['164'])).

thf('166',plain,(
    sk_A != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    sk_D_1 = sk_C ),
    inference('simplify_reflect-',[status(thm)],['165','166'])).

thf('168',plain,(
    sk_D_1 = sk_C ),
    inference('simplify_reflect-',[status(thm)],['165','166'])).

thf('169',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('170',plain,(
    ! [X119: $i,X122: $i] :
      ( r1_tarski @ ( k1_tarski @ X122 ) @ ( k2_tarski @ X119 @ X122 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('171',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k5_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('180',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['169','180'])).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_enumset1 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['181','182'])).

thf('184',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['109','119'])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('186',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X1 )
      = ( k1_enumset1 @ X1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['99','108'])).

thf('188',plain,(
    ! [X92: $i,X93: $i] :
      ( ( k1_enumset1 @ X92 @ X92 @ X93 )
      = ( k2_tarski @ X92 @ X93 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('189',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['187','188'])).

thf('190',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('191',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X1 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['189','190'])).

thf('192',plain,(
    sk_D_1 = sk_C ),
    inference('simplify_reflect-',[status(thm)],['165','166'])).

thf('193',plain,(
    ! [X91: $i] :
      ( ( k2_tarski @ X91 @ X91 )
      = ( k1_tarski @ X91 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('194',plain,
    ( ( k1_enumset1 @ sk_A @ sk_A @ sk_C )
    = ( k1_tarski @ sk_C ) ),
    inference(demod,[status(thm)],['128','167','168','183','186','191','192','193'])).

thf('195',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','36'])).

thf('196',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_C ) ),
    inference('sup+',[status(thm)],['194','195'])).

thf('197',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('198',plain,(
    sk_A = sk_C ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['198','199'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vnNC1jVjeo
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:47:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 5.43/5.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.43/5.60  % Solved by: fo/fo7.sh
% 5.43/5.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.43/5.60  % done 6903 iterations in 5.146s
% 5.43/5.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.43/5.60  % SZS output start Refutation
% 5.43/5.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 5.43/5.60  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 5.43/5.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.43/5.60  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 5.43/5.60  thf(sk_B_type, type, sk_B: $i).
% 5.43/5.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.43/5.60  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 5.43/5.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.43/5.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 5.43/5.60  thf(sk_D_1_type, type, sk_D_1: $i).
% 5.43/5.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 5.43/5.60  thf(sk_C_type, type, sk_C: $i).
% 5.43/5.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 5.43/5.60  thf(sk_A_type, type, sk_A: $i).
% 5.43/5.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 5.43/5.60  thf(t28_zfmisc_1, conjecture,
% 5.43/5.60    (![A:$i,B:$i,C:$i,D:$i]:
% 5.43/5.60     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 5.43/5.60          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 5.43/5.60  thf(zf_stmt_0, negated_conjecture,
% 5.43/5.60    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 5.43/5.60        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 5.43/5.60             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 5.43/5.60    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 5.43/5.60  thf('0', plain,
% 5.43/5.60      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D_1))),
% 5.43/5.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.43/5.60  thf(t70_enumset1, axiom,
% 5.43/5.60    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 5.43/5.60  thf('1', plain,
% 5.43/5.60      (![X92 : $i, X93 : $i]:
% 5.43/5.60         ((k1_enumset1 @ X92 @ X92 @ X93) = (k2_tarski @ X92 @ X93))),
% 5.43/5.60      inference('cnf', [status(esa)], [t70_enumset1])).
% 5.43/5.60  thf('2', plain,
% 5.43/5.60      ((r1_tarski @ (k1_enumset1 @ sk_A @ sk_A @ sk_B) @ 
% 5.43/5.60        (k2_tarski @ sk_C @ sk_D_1))),
% 5.43/5.60      inference('demod', [status(thm)], ['0', '1'])).
% 5.43/5.60  thf(t12_xboole_1, axiom,
% 5.43/5.60    (![A:$i,B:$i]:
% 5.43/5.60     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 5.43/5.60  thf('3', plain,
% 5.43/5.60      (![X2 : $i, X3 : $i]:
% 5.43/5.60         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 5.43/5.60      inference('cnf', [status(esa)], [t12_xboole_1])).
% 5.43/5.60  thf('4', plain,
% 5.43/5.60      (((k2_xboole_0 @ (k1_enumset1 @ sk_A @ sk_A @ sk_B) @ 
% 5.43/5.60         (k2_tarski @ sk_C @ sk_D_1)) = (k2_tarski @ sk_C @ sk_D_1))),
% 5.43/5.60      inference('sup-', [status(thm)], ['2', '3'])).
% 5.43/5.60  thf('5', plain,
% 5.43/5.60      (![X92 : $i, X93 : $i]:
% 5.43/5.60         ((k1_enumset1 @ X92 @ X92 @ X93) = (k2_tarski @ X92 @ X93))),
% 5.43/5.60      inference('cnf', [status(esa)], [t70_enumset1])).
% 5.43/5.60  thf(t45_enumset1, axiom,
% 5.43/5.60    (![A:$i,B:$i,C:$i,D:$i]:
% 5.43/5.60     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 5.43/5.60       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 5.43/5.60  thf('6', plain,
% 5.43/5.60      (![X71 : $i, X72 : $i, X73 : $i, X74 : $i]:
% 5.43/5.60         ((k2_enumset1 @ X71 @ X72 @ X73 @ X74)
% 5.43/5.60           = (k2_xboole_0 @ (k2_tarski @ X71 @ X72) @ (k2_tarski @ X73 @ X74)))),
% 5.43/5.60      inference('cnf', [status(esa)], [t45_enumset1])).
% 5.43/5.60  thf('7', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.43/5.60         ((k2_enumset1 @ X1 @ X0 @ X3 @ X2)
% 5.43/5.60           = (k2_xboole_0 @ (k1_enumset1 @ X1 @ X1 @ X0) @ 
% 5.43/5.60              (k2_tarski @ X3 @ X2)))),
% 5.43/5.60      inference('sup+', [status(thm)], ['5', '6'])).
% 5.43/5.60  thf(t104_enumset1, axiom,
% 5.43/5.60    (![A:$i,B:$i,C:$i,D:$i]:
% 5.43/5.60     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ B @ D ) ))).
% 5.43/5.60  thf('8', plain,
% 5.43/5.60      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 5.43/5.60         ((k2_enumset1 @ X40 @ X42 @ X41 @ X43)
% 5.43/5.60           = (k2_enumset1 @ X40 @ X41 @ X42 @ X43))),
% 5.43/5.60      inference('cnf', [status(esa)], [t104_enumset1])).
% 5.43/5.60  thf('9', plain,
% 5.43/5.60      (((k2_enumset1 @ sk_A @ sk_C @ sk_B @ sk_D_1)
% 5.43/5.60         = (k2_tarski @ sk_C @ sk_D_1))),
% 5.43/5.60      inference('demod', [status(thm)], ['4', '7', '8'])).
% 5.43/5.60  thf(t71_enumset1, axiom,
% 5.43/5.60    (![A:$i,B:$i,C:$i]:
% 5.43/5.60     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 5.43/5.60  thf('10', plain,
% 5.43/5.60      (![X94 : $i, X95 : $i, X96 : $i]:
% 5.43/5.60         ((k2_enumset1 @ X94 @ X94 @ X95 @ X96)
% 5.43/5.60           = (k1_enumset1 @ X94 @ X95 @ X96))),
% 5.43/5.60      inference('cnf', [status(esa)], [t71_enumset1])).
% 5.43/5.60  thf('11', plain,
% 5.43/5.60      ((r1_tarski @ (k1_enumset1 @ sk_A @ sk_A @ sk_B) @ 
% 5.43/5.60        (k2_tarski @ sk_C @ sk_D_1))),
% 5.43/5.60      inference('demod', [status(thm)], ['0', '1'])).
% 5.43/5.60  thf(l45_zfmisc_1, axiom,
% 5.43/5.60    (![A:$i,B:$i,C:$i]:
% 5.43/5.60     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 5.43/5.60       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 5.43/5.60            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 5.43/5.60  thf('12', plain,
% 5.43/5.60      (![X119 : $i, X120 : $i, X121 : $i]:
% 5.43/5.60         (((X121) = (k2_tarski @ X119 @ X120))
% 5.43/5.60          | ((X121) = (k1_tarski @ X120))
% 5.43/5.60          | ((X121) = (k1_tarski @ X119))
% 5.43/5.60          | ((X121) = (k1_xboole_0))
% 5.43/5.60          | ~ (r1_tarski @ X121 @ (k2_tarski @ X119 @ X120)))),
% 5.43/5.60      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 5.43/5.60  thf('13', plain,
% 5.43/5.60      ((((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0))
% 5.43/5.60        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 5.43/5.60        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_D_1))
% 5.43/5.60        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k2_tarski @ sk_C @ sk_D_1)))),
% 5.43/5.60      inference('sup-', [status(thm)], ['11', '12'])).
% 5.43/5.60  thf(d2_tarski, axiom,
% 5.43/5.60    (![A:$i,B:$i,C:$i]:
% 5.43/5.60     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 5.43/5.60       ( ![D:$i]:
% 5.43/5.60         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 5.43/5.60  thf('14', plain,
% 5.43/5.60      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 5.43/5.60         (((X11) != (X10))
% 5.43/5.60          | (r2_hidden @ X11 @ X12)
% 5.43/5.60          | ((X12) != (k2_tarski @ X13 @ X10)))),
% 5.43/5.60      inference('cnf', [status(esa)], [d2_tarski])).
% 5.43/5.60  thf('15', plain,
% 5.43/5.60      (![X10 : $i, X13 : $i]: (r2_hidden @ X10 @ (k2_tarski @ X13 @ X10))),
% 5.43/5.60      inference('simplify', [status(thm)], ['14'])).
% 5.43/5.60  thf('16', plain,
% 5.43/5.60      (((r2_hidden @ sk_D_1 @ (k1_enumset1 @ sk_A @ sk_A @ sk_B))
% 5.43/5.60        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_D_1))
% 5.43/5.60        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 5.43/5.60        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0)))),
% 5.43/5.60      inference('sup+', [status(thm)], ['13', '15'])).
% 5.43/5.60  thf('17', plain,
% 5.43/5.60      (![X92 : $i, X93 : $i]:
% 5.43/5.60         ((k1_enumset1 @ X92 @ X92 @ X93) = (k2_tarski @ X92 @ X93))),
% 5.43/5.60      inference('cnf', [status(esa)], [t70_enumset1])).
% 5.43/5.60  thf('18', plain,
% 5.43/5.60      (![X10 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 5.43/5.60         (~ (r2_hidden @ X14 @ X12)
% 5.43/5.60          | ((X14) = (X13))
% 5.43/5.60          | ((X14) = (X10))
% 5.43/5.60          | ((X12) != (k2_tarski @ X13 @ X10)))),
% 5.43/5.60      inference('cnf', [status(esa)], [d2_tarski])).
% 5.43/5.60  thf('19', plain,
% 5.43/5.60      (![X10 : $i, X13 : $i, X14 : $i]:
% 5.43/5.60         (((X14) = (X10))
% 5.43/5.60          | ((X14) = (X13))
% 5.43/5.60          | ~ (r2_hidden @ X14 @ (k2_tarski @ X13 @ X10)))),
% 5.43/5.60      inference('simplify', [status(thm)], ['18'])).
% 5.43/5.60  thf('20', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.43/5.60         (~ (r2_hidden @ X2 @ (k1_enumset1 @ X1 @ X1 @ X0))
% 5.43/5.60          | ((X2) = (X1))
% 5.43/5.60          | ((X2) = (X0)))),
% 5.43/5.60      inference('sup-', [status(thm)], ['17', '19'])).
% 5.43/5.60  thf('21', plain,
% 5.43/5.60      ((((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0))
% 5.43/5.60        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 5.43/5.60        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_D_1))
% 5.43/5.60        | ((sk_D_1) = (sk_B))
% 5.43/5.60        | ((sk_D_1) = (sk_A)))),
% 5.43/5.60      inference('sup-', [status(thm)], ['16', '20'])).
% 5.43/5.60  thf('22', plain, (((sk_A) != (sk_D_1))),
% 5.43/5.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.43/5.60  thf('23', plain,
% 5.43/5.60      ((((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0))
% 5.43/5.60        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 5.43/5.60        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_D_1))
% 5.43/5.60        | ((sk_D_1) = (sk_B)))),
% 5.43/5.60      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 5.43/5.60  thf('24', plain,
% 5.43/5.60      (![X92 : $i, X93 : $i]:
% 5.43/5.60         ((k1_enumset1 @ X92 @ X92 @ X93) = (k2_tarski @ X92 @ X93))),
% 5.43/5.60      inference('cnf', [status(esa)], [t70_enumset1])).
% 5.43/5.60  thf('25', plain,
% 5.43/5.60      (![X10 : $i, X13 : $i]: (r2_hidden @ X10 @ (k2_tarski @ X13 @ X10))),
% 5.43/5.60      inference('simplify', [status(thm)], ['14'])).
% 5.43/5.60  thf('26', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 5.43/5.60      inference('sup+', [status(thm)], ['24', '25'])).
% 5.43/5.60  thf('27', plain,
% 5.43/5.60      (((r2_hidden @ sk_B @ (k1_tarski @ sk_D_1))
% 5.43/5.60        | ((sk_D_1) = (sk_B))
% 5.43/5.60        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 5.43/5.60        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0)))),
% 5.43/5.60      inference('sup+', [status(thm)], ['23', '26'])).
% 5.43/5.60  thf(t69_enumset1, axiom,
% 5.43/5.60    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 5.43/5.60  thf('28', plain,
% 5.43/5.60      (![X91 : $i]: ((k2_tarski @ X91 @ X91) = (k1_tarski @ X91))),
% 5.43/5.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 5.43/5.60  thf('29', plain,
% 5.43/5.60      (![X10 : $i, X13 : $i, X14 : $i]:
% 5.43/5.60         (((X14) = (X10))
% 5.43/5.60          | ((X14) = (X13))
% 5.43/5.60          | ~ (r2_hidden @ X14 @ (k2_tarski @ X13 @ X10)))),
% 5.43/5.60      inference('simplify', [status(thm)], ['18'])).
% 5.43/5.60  thf('30', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i]:
% 5.43/5.60         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 5.43/5.60      inference('sup-', [status(thm)], ['28', '29'])).
% 5.43/5.60  thf('31', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i]:
% 5.43/5.60         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 5.43/5.60      inference('simplify', [status(thm)], ['30'])).
% 5.43/5.60  thf('32', plain,
% 5.43/5.60      ((((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0))
% 5.43/5.60        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 5.43/5.60        | ((sk_D_1) = (sk_B))
% 5.43/5.60        | ((sk_B) = (sk_D_1)))),
% 5.43/5.60      inference('sup-', [status(thm)], ['27', '31'])).
% 5.43/5.60  thf('33', plain,
% 5.43/5.60      ((((sk_D_1) = (sk_B))
% 5.43/5.60        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 5.43/5.60        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0)))),
% 5.43/5.60      inference('simplify', [status(thm)], ['32'])).
% 5.43/5.60  thf('34', plain,
% 5.43/5.60      (![X92 : $i, X93 : $i]:
% 5.43/5.60         ((k1_enumset1 @ X92 @ X92 @ X93) = (k2_tarski @ X92 @ X93))),
% 5.43/5.60      inference('cnf', [status(esa)], [t70_enumset1])).
% 5.43/5.60  thf('35', plain,
% 5.43/5.60      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 5.43/5.60         (((X11) != (X13))
% 5.43/5.60          | (r2_hidden @ X11 @ X12)
% 5.43/5.60          | ((X12) != (k2_tarski @ X13 @ X10)))),
% 5.43/5.60      inference('cnf', [status(esa)], [d2_tarski])).
% 5.43/5.60  thf('36', plain,
% 5.43/5.60      (![X10 : $i, X13 : $i]: (r2_hidden @ X13 @ (k2_tarski @ X13 @ X10))),
% 5.43/5.60      inference('simplify', [status(thm)], ['35'])).
% 5.43/5.60  thf('37', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 5.43/5.60      inference('sup+', [status(thm)], ['34', '36'])).
% 5.43/5.60  thf('38', plain,
% 5.43/5.60      (((r2_hidden @ sk_A @ (k1_tarski @ sk_C))
% 5.43/5.60        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0))
% 5.43/5.60        | ((sk_D_1) = (sk_B)))),
% 5.43/5.60      inference('sup+', [status(thm)], ['33', '37'])).
% 5.43/5.60  thf('39', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i]:
% 5.43/5.60         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 5.43/5.60      inference('simplify', [status(thm)], ['30'])).
% 5.43/5.60  thf('40', plain,
% 5.43/5.60      ((((sk_D_1) = (sk_B))
% 5.43/5.60        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0))
% 5.43/5.60        | ((sk_A) = (sk_C)))),
% 5.43/5.60      inference('sup-', [status(thm)], ['38', '39'])).
% 5.43/5.60  thf('41', plain, (((sk_A) != (sk_C))),
% 5.43/5.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.43/5.60  thf('42', plain,
% 5.43/5.60      ((((sk_D_1) = (sk_B))
% 5.43/5.60        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0)))),
% 5.43/5.60      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 5.43/5.60  thf('43', plain,
% 5.43/5.60      (![X92 : $i, X93 : $i]:
% 5.43/5.60         ((k1_enumset1 @ X92 @ X92 @ X93) = (k2_tarski @ X92 @ X93))),
% 5.43/5.60      inference('cnf', [status(esa)], [t70_enumset1])).
% 5.43/5.60  thf('44', plain,
% 5.43/5.60      (![X119 : $i, X121 : $i, X122 : $i]:
% 5.43/5.60         ((r1_tarski @ X121 @ (k2_tarski @ X119 @ X122))
% 5.43/5.60          | ((X121) != (k1_tarski @ X122)))),
% 5.43/5.60      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 5.43/5.60  thf('45', plain,
% 5.43/5.60      (![X119 : $i, X122 : $i]:
% 5.43/5.60         (r1_tarski @ (k1_tarski @ X122) @ (k2_tarski @ X119 @ X122))),
% 5.43/5.60      inference('simplify', [status(thm)], ['44'])).
% 5.43/5.60  thf('46', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i]:
% 5.43/5.60         (r1_tarski @ (k1_tarski @ X0) @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 5.43/5.60      inference('sup+', [status(thm)], ['43', '45'])).
% 5.43/5.60  thf('47', plain,
% 5.43/5.60      (((r1_tarski @ (k1_tarski @ sk_B) @ k1_xboole_0) | ((sk_D_1) = (sk_B)))),
% 5.43/5.60      inference('sup+', [status(thm)], ['42', '46'])).
% 5.43/5.60  thf('48', plain,
% 5.43/5.60      (![X2 : $i, X3 : $i]:
% 5.43/5.60         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 5.43/5.60      inference('cnf', [status(esa)], [t12_xboole_1])).
% 5.43/5.60  thf('49', plain,
% 5.43/5.60      ((((sk_D_1) = (sk_B))
% 5.43/5.60        | ((k2_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0) = (k1_xboole_0)))),
% 5.43/5.60      inference('sup-', [status(thm)], ['47', '48'])).
% 5.43/5.60  thf('50', plain,
% 5.43/5.60      (![X91 : $i]: ((k2_tarski @ X91 @ X91) = (k1_tarski @ X91))),
% 5.43/5.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 5.43/5.60  thf('51', plain,
% 5.43/5.60      (![X119 : $i, X121 : $i, X122 : $i]:
% 5.43/5.60         ((r1_tarski @ X121 @ (k2_tarski @ X119 @ X122))
% 5.43/5.60          | ((X121) != (k1_xboole_0)))),
% 5.43/5.60      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 5.43/5.60  thf('52', plain,
% 5.43/5.60      (![X119 : $i, X122 : $i]:
% 5.43/5.60         (r1_tarski @ k1_xboole_0 @ (k2_tarski @ X119 @ X122))),
% 5.43/5.60      inference('simplify', [status(thm)], ['51'])).
% 5.43/5.60  thf('53', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0))),
% 5.43/5.60      inference('sup+', [status(thm)], ['50', '52'])).
% 5.43/5.60  thf(t28_xboole_1, axiom,
% 5.43/5.60    (![A:$i,B:$i]:
% 5.43/5.60     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 5.43/5.60  thf('54', plain,
% 5.43/5.60      (![X4 : $i, X5 : $i]:
% 5.43/5.60         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 5.43/5.60      inference('cnf', [status(esa)], [t28_xboole_1])).
% 5.43/5.60  thf('55', plain,
% 5.43/5.60      (![X0 : $i]:
% 5.43/5.60         ((k3_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 5.43/5.60      inference('sup-', [status(thm)], ['53', '54'])).
% 5.43/5.60  thf(t100_xboole_1, axiom,
% 5.43/5.60    (![A:$i,B:$i]:
% 5.43/5.60     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 5.43/5.60  thf('56', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i]:
% 5.43/5.60         ((k4_xboole_0 @ X0 @ X1)
% 5.43/5.60           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 5.43/5.60      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.43/5.60  thf('57', plain,
% 5.43/5.60      (![X0 : $i]:
% 5.43/5.60         ((k4_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0))
% 5.43/5.60           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 5.43/5.60      inference('sup+', [status(thm)], ['55', '56'])).
% 5.43/5.60  thf(t5_boole, axiom,
% 5.43/5.60    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 5.43/5.60  thf('58', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 5.43/5.60      inference('cnf', [status(esa)], [t5_boole])).
% 5.43/5.60  thf('59', plain,
% 5.43/5.60      (![X0 : $i]:
% 5.43/5.60         ((k4_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 5.43/5.60      inference('demod', [status(thm)], ['57', '58'])).
% 5.43/5.60  thf(t98_xboole_1, axiom,
% 5.43/5.60    (![A:$i,B:$i]:
% 5.43/5.60     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 5.43/5.60  thf('60', plain,
% 5.43/5.60      (![X8 : $i, X9 : $i]:
% 5.43/5.60         ((k2_xboole_0 @ X8 @ X9)
% 5.43/5.60           = (k5_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8)))),
% 5.43/5.60      inference('cnf', [status(esa)], [t98_xboole_1])).
% 5.43/5.60  thf('61', plain,
% 5.43/5.60      (![X0 : $i]:
% 5.43/5.60         ((k2_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0)
% 5.43/5.60           = (k5_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))),
% 5.43/5.60      inference('sup+', [status(thm)], ['59', '60'])).
% 5.43/5.60  thf('62', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 5.43/5.60      inference('cnf', [status(esa)], [t5_boole])).
% 5.43/5.60  thf('63', plain,
% 5.43/5.60      (![X0 : $i]:
% 5.43/5.60         ((k2_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0) = (k1_tarski @ X0))),
% 5.43/5.60      inference('demod', [status(thm)], ['61', '62'])).
% 5.43/5.60  thf('64', plain,
% 5.43/5.60      ((((sk_D_1) = (sk_B)) | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 5.43/5.60      inference('demod', [status(thm)], ['49', '63'])).
% 5.43/5.60  thf('65', plain,
% 5.43/5.60      (![X91 : $i]: ((k2_tarski @ X91 @ X91) = (k1_tarski @ X91))),
% 5.43/5.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 5.43/5.60  thf('66', plain,
% 5.43/5.60      (![X71 : $i, X72 : $i, X73 : $i, X74 : $i]:
% 5.43/5.60         ((k2_enumset1 @ X71 @ X72 @ X73 @ X74)
% 5.43/5.60           = (k2_xboole_0 @ (k2_tarski @ X71 @ X72) @ (k2_tarski @ X73 @ X74)))),
% 5.43/5.60      inference('cnf', [status(esa)], [t45_enumset1])).
% 5.43/5.60  thf('67', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.43/5.60         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0)
% 5.43/5.60           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)))),
% 5.43/5.60      inference('sup+', [status(thm)], ['65', '66'])).
% 5.43/5.60  thf('68', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i]:
% 5.43/5.60         (((k2_enumset1 @ X1 @ X0 @ sk_B @ sk_B)
% 5.43/5.60            = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ k1_xboole_0))
% 5.43/5.60          | ((sk_D_1) = (sk_B)))),
% 5.43/5.60      inference('sup+', [status(thm)], ['64', '67'])).
% 5.43/5.60  thf('69', plain,
% 5.43/5.60      (![X119 : $i, X122 : $i]:
% 5.43/5.60         (r1_tarski @ k1_xboole_0 @ (k2_tarski @ X119 @ X122))),
% 5.43/5.60      inference('simplify', [status(thm)], ['51'])).
% 5.43/5.60  thf('70', plain,
% 5.43/5.60      (![X4 : $i, X5 : $i]:
% 5.43/5.60         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 5.43/5.60      inference('cnf', [status(esa)], [t28_xboole_1])).
% 5.43/5.60  thf('71', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i]:
% 5.43/5.60         ((k3_xboole_0 @ k1_xboole_0 @ (k2_tarski @ X1 @ X0)) = (k1_xboole_0))),
% 5.43/5.60      inference('sup-', [status(thm)], ['69', '70'])).
% 5.43/5.60  thf('72', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i]:
% 5.43/5.60         ((k4_xboole_0 @ X0 @ X1)
% 5.43/5.60           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 5.43/5.60      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.43/5.60  thf('73', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i]:
% 5.43/5.60         ((k4_xboole_0 @ k1_xboole_0 @ (k2_tarski @ X1 @ X0))
% 5.43/5.60           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 5.43/5.60      inference('sup+', [status(thm)], ['71', '72'])).
% 5.43/5.60  thf('74', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 5.43/5.60      inference('cnf', [status(esa)], [t5_boole])).
% 5.43/5.60  thf('75', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i]:
% 5.43/5.60         ((k4_xboole_0 @ k1_xboole_0 @ (k2_tarski @ X1 @ X0)) = (k1_xboole_0))),
% 5.43/5.60      inference('demod', [status(thm)], ['73', '74'])).
% 5.43/5.60  thf('76', plain,
% 5.43/5.60      (![X8 : $i, X9 : $i]:
% 5.43/5.60         ((k2_xboole_0 @ X8 @ X9)
% 5.43/5.60           = (k5_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8)))),
% 5.43/5.60      inference('cnf', [status(esa)], [t98_xboole_1])).
% 5.43/5.60  thf('77', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i]:
% 5.43/5.60         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ k1_xboole_0)
% 5.43/5.60           = (k5_xboole_0 @ (k2_tarski @ X1 @ X0) @ k1_xboole_0))),
% 5.43/5.60      inference('sup+', [status(thm)], ['75', '76'])).
% 5.43/5.60  thf('78', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 5.43/5.60      inference('cnf', [status(esa)], [t5_boole])).
% 5.43/5.60  thf('79', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i]:
% 5.43/5.60         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ k1_xboole_0)
% 5.43/5.60           = (k2_tarski @ X1 @ X0))),
% 5.43/5.60      inference('demod', [status(thm)], ['77', '78'])).
% 5.43/5.60  thf('80', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i]:
% 5.43/5.60         (((k2_enumset1 @ X1 @ X0 @ sk_B @ sk_B) = (k2_tarski @ X1 @ X0))
% 5.43/5.60          | ((sk_D_1) = (sk_B)))),
% 5.43/5.60      inference('demod', [status(thm)], ['68', '79'])).
% 5.43/5.60  thf('81', plain,
% 5.43/5.60      (![X0 : $i]:
% 5.43/5.60         (((k1_enumset1 @ X0 @ sk_B @ sk_B) = (k2_tarski @ X0 @ X0))
% 5.43/5.60          | ((sk_D_1) = (sk_B)))),
% 5.43/5.60      inference('sup+', [status(thm)], ['10', '80'])).
% 5.43/5.60  thf('82', plain,
% 5.43/5.60      (![X119 : $i, X121 : $i, X122 : $i]:
% 5.43/5.60         ((r1_tarski @ X121 @ (k2_tarski @ X119 @ X122))
% 5.43/5.60          | ((X121) != (k1_tarski @ X119)))),
% 5.43/5.60      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 5.43/5.60  thf('83', plain,
% 5.43/5.60      (![X119 : $i, X122 : $i]:
% 5.43/5.60         (r1_tarski @ (k1_tarski @ X119) @ (k2_tarski @ X119 @ X122))),
% 5.43/5.60      inference('simplify', [status(thm)], ['82'])).
% 5.43/5.60  thf('84', plain,
% 5.43/5.60      (![X4 : $i, X5 : $i]:
% 5.43/5.60         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 5.43/5.60      inference('cnf', [status(esa)], [t28_xboole_1])).
% 5.43/5.60  thf('85', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i]:
% 5.43/5.60         ((k3_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 5.43/5.60           = (k1_tarski @ X1))),
% 5.43/5.60      inference('sup-', [status(thm)], ['83', '84'])).
% 5.43/5.60  thf('86', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i]:
% 5.43/5.60         ((k4_xboole_0 @ X0 @ X1)
% 5.43/5.60           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 5.43/5.60      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.43/5.60  thf('87', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i]:
% 5.43/5.60         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1))
% 5.43/5.60           = (k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 5.43/5.60      inference('sup+', [status(thm)], ['85', '86'])).
% 5.43/5.60  thf(t92_xboole_1, axiom,
% 5.43/5.60    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 5.43/5.60  thf('88', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ X7) = (k1_xboole_0))),
% 5.43/5.60      inference('cnf', [status(esa)], [t92_xboole_1])).
% 5.43/5.60  thf('89', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i]:
% 5.43/5.60         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1))
% 5.43/5.60           = (k1_xboole_0))),
% 5.43/5.60      inference('demod', [status(thm)], ['87', '88'])).
% 5.43/5.60  thf('90', plain,
% 5.43/5.60      (![X8 : $i, X9 : $i]:
% 5.43/5.60         ((k2_xboole_0 @ X8 @ X9)
% 5.43/5.60           = (k5_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8)))),
% 5.43/5.60      inference('cnf', [status(esa)], [t98_xboole_1])).
% 5.43/5.60  thf('91', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i]:
% 5.43/5.60         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 5.43/5.60           = (k5_xboole_0 @ (k2_tarski @ X1 @ X0) @ k1_xboole_0))),
% 5.43/5.60      inference('sup+', [status(thm)], ['89', '90'])).
% 5.43/5.60  thf('92', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 5.43/5.60      inference('cnf', [status(esa)], [t5_boole])).
% 5.43/5.60  thf('93', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i]:
% 5.43/5.60         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 5.43/5.60           = (k2_tarski @ X1 @ X0))),
% 5.43/5.60      inference('demod', [status(thm)], ['91', '92'])).
% 5.43/5.60  thf('94', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.43/5.60         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0)
% 5.43/5.60           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)))),
% 5.43/5.60      inference('sup+', [status(thm)], ['65', '66'])).
% 5.43/5.60  thf('95', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i]:
% 5.43/5.60         ((k2_enumset1 @ X1 @ X0 @ X1 @ X1) = (k2_tarski @ X1 @ X0))),
% 5.43/5.60      inference('sup+', [status(thm)], ['93', '94'])).
% 5.43/5.60  thf('96', plain,
% 5.43/5.60      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 5.43/5.60         ((k2_enumset1 @ X40 @ X42 @ X41 @ X43)
% 5.43/5.60           = (k2_enumset1 @ X40 @ X41 @ X42 @ X43))),
% 5.43/5.60      inference('cnf', [status(esa)], [t104_enumset1])).
% 5.43/5.60  thf('97', plain,
% 5.43/5.60      (![X94 : $i, X95 : $i, X96 : $i]:
% 5.43/5.60         ((k2_enumset1 @ X94 @ X94 @ X95 @ X96)
% 5.43/5.60           = (k1_enumset1 @ X94 @ X95 @ X96))),
% 5.43/5.60      inference('cnf', [status(esa)], [t71_enumset1])).
% 5.43/5.60  thf('98', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.43/5.60         ((k2_enumset1 @ X1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 5.43/5.60      inference('sup+', [status(thm)], ['96', '97'])).
% 5.43/5.60  thf('99', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i]:
% 5.43/5.60         ((k1_enumset1 @ X1 @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 5.43/5.60      inference('demod', [status(thm)], ['95', '98'])).
% 5.43/5.60  thf('100', plain,
% 5.43/5.60      (![X119 : $i, X122 : $i]:
% 5.43/5.60         (r1_tarski @ (k1_tarski @ X122) @ (k2_tarski @ X119 @ X122))),
% 5.43/5.60      inference('simplify', [status(thm)], ['44'])).
% 5.43/5.60  thf('101', plain,
% 5.43/5.60      (![X2 : $i, X3 : $i]:
% 5.43/5.60         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 5.43/5.60      inference('cnf', [status(esa)], [t12_xboole_1])).
% 5.43/5.60  thf('102', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i]:
% 5.43/5.60         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))
% 5.43/5.60           = (k2_tarski @ X1 @ X0))),
% 5.43/5.60      inference('sup-', [status(thm)], ['100', '101'])).
% 5.43/5.60  thf('103', plain,
% 5.43/5.60      (![X91 : $i]: ((k2_tarski @ X91 @ X91) = (k1_tarski @ X91))),
% 5.43/5.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 5.43/5.60  thf('104', plain,
% 5.43/5.60      (![X71 : $i, X72 : $i, X73 : $i, X74 : $i]:
% 5.43/5.60         ((k2_enumset1 @ X71 @ X72 @ X73 @ X74)
% 5.43/5.60           = (k2_xboole_0 @ (k2_tarski @ X71 @ X72) @ (k2_tarski @ X73 @ X74)))),
% 5.43/5.60      inference('cnf', [status(esa)], [t45_enumset1])).
% 5.43/5.60  thf('105', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.43/5.60         ((k2_enumset1 @ X0 @ X0 @ X2 @ X1)
% 5.43/5.60           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 5.43/5.60      inference('sup+', [status(thm)], ['103', '104'])).
% 5.43/5.60  thf('106', plain,
% 5.43/5.60      (![X94 : $i, X95 : $i, X96 : $i]:
% 5.43/5.60         ((k2_enumset1 @ X94 @ X94 @ X95 @ X96)
% 5.43/5.60           = (k1_enumset1 @ X94 @ X95 @ X96))),
% 5.43/5.60      inference('cnf', [status(esa)], [t71_enumset1])).
% 5.43/5.60  thf('107', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.43/5.60         ((k1_enumset1 @ X0 @ X2 @ X1)
% 5.43/5.60           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 5.43/5.60      inference('demod', [status(thm)], ['105', '106'])).
% 5.43/5.60  thf('108', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i]:
% 5.43/5.60         ((k1_enumset1 @ X0 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 5.43/5.60      inference('demod', [status(thm)], ['102', '107'])).
% 5.43/5.60  thf('109', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 5.43/5.60      inference('sup+', [status(thm)], ['99', '108'])).
% 5.43/5.60  thf('110', plain,
% 5.43/5.60      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 5.43/5.60         ((k2_enumset1 @ X40 @ X42 @ X41 @ X43)
% 5.43/5.60           = (k2_enumset1 @ X40 @ X41 @ X42 @ X43))),
% 5.43/5.60      inference('cnf', [status(esa)], [t104_enumset1])).
% 5.43/5.60  thf('111', plain,
% 5.43/5.60      (![X119 : $i, X121 : $i, X122 : $i]:
% 5.43/5.60         ((r1_tarski @ X121 @ (k2_tarski @ X119 @ X122))
% 5.43/5.60          | ((X121) != (k2_tarski @ X119 @ X122)))),
% 5.43/5.60      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 5.43/5.60  thf('112', plain,
% 5.43/5.60      (![X119 : $i, X122 : $i]:
% 5.43/5.60         (r1_tarski @ (k2_tarski @ X119 @ X122) @ (k2_tarski @ X119 @ X122))),
% 5.43/5.60      inference('simplify', [status(thm)], ['111'])).
% 5.43/5.60  thf('113', plain,
% 5.43/5.60      (![X2 : $i, X3 : $i]:
% 5.43/5.60         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 5.43/5.60      inference('cnf', [status(esa)], [t12_xboole_1])).
% 5.43/5.60  thf('114', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i]:
% 5.43/5.60         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X1 @ X0))
% 5.43/5.60           = (k2_tarski @ X1 @ X0))),
% 5.43/5.60      inference('sup-', [status(thm)], ['112', '113'])).
% 5.43/5.60  thf('115', plain,
% 5.43/5.60      (![X71 : $i, X72 : $i, X73 : $i, X74 : $i]:
% 5.43/5.60         ((k2_enumset1 @ X71 @ X72 @ X73 @ X74)
% 5.43/5.60           = (k2_xboole_0 @ (k2_tarski @ X71 @ X72) @ (k2_tarski @ X73 @ X74)))),
% 5.43/5.60      inference('cnf', [status(esa)], [t45_enumset1])).
% 5.43/5.60  thf('116', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i]:
% 5.43/5.60         ((k2_enumset1 @ X1 @ X0 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 5.43/5.60      inference('demod', [status(thm)], ['114', '115'])).
% 5.43/5.60  thf('117', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i]:
% 5.43/5.60         ((k2_enumset1 @ X1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 5.43/5.60      inference('sup+', [status(thm)], ['110', '116'])).
% 5.43/5.60  thf('118', plain,
% 5.43/5.60      (![X94 : $i, X95 : $i, X96 : $i]:
% 5.43/5.60         ((k2_enumset1 @ X94 @ X94 @ X95 @ X96)
% 5.43/5.60           = (k1_enumset1 @ X94 @ X95 @ X96))),
% 5.43/5.60      inference('cnf', [status(esa)], [t71_enumset1])).
% 5.43/5.60  thf('119', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i]:
% 5.43/5.60         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 5.43/5.60      inference('demod', [status(thm)], ['117', '118'])).
% 5.43/5.60  thf('120', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i]:
% 5.43/5.60         ((k1_enumset1 @ X0 @ X1 @ X1) = (k2_tarski @ X1 @ X0))),
% 5.43/5.60      inference('sup+', [status(thm)], ['109', '119'])).
% 5.43/5.60  thf('121', plain,
% 5.43/5.60      (![X91 : $i]: ((k2_tarski @ X91 @ X91) = (k1_tarski @ X91))),
% 5.43/5.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 5.43/5.60  thf('122', plain,
% 5.43/5.60      (![X0 : $i]:
% 5.43/5.60         (((k2_tarski @ sk_B @ X0) = (k1_tarski @ X0)) | ((sk_D_1) = (sk_B)))),
% 5.43/5.60      inference('demod', [status(thm)], ['81', '120', '121'])).
% 5.43/5.60  thf('123', plain,
% 5.43/5.60      (![X10 : $i, X13 : $i]: (r2_hidden @ X13 @ (k2_tarski @ X13 @ X10))),
% 5.43/5.60      inference('simplify', [status(thm)], ['35'])).
% 5.43/5.60  thf('124', plain,
% 5.43/5.60      (![X0 : $i]:
% 5.43/5.60         ((r2_hidden @ sk_B @ (k1_tarski @ X0)) | ((sk_D_1) = (sk_B)))),
% 5.43/5.60      inference('sup+', [status(thm)], ['122', '123'])).
% 5.43/5.60  thf('125', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i]:
% 5.43/5.60         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 5.43/5.60      inference('simplify', [status(thm)], ['30'])).
% 5.43/5.60  thf('126', plain, (![X0 : $i]: (((sk_D_1) = (sk_B)) | ((sk_B) = (X0)))),
% 5.43/5.60      inference('sup-', [status(thm)], ['124', '125'])).
% 5.43/5.60  thf('127', plain, (((sk_D_1) = (sk_B))),
% 5.43/5.60      inference('condensation', [status(thm)], ['126'])).
% 5.43/5.60  thf('128', plain,
% 5.43/5.60      (((k2_enumset1 @ sk_A @ sk_C @ sk_D_1 @ sk_D_1)
% 5.43/5.60         = (k2_tarski @ sk_C @ sk_D_1))),
% 5.43/5.60      inference('demod', [status(thm)], ['9', '127'])).
% 5.43/5.60  thf('129', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 5.43/5.60      inference('sup+', [status(thm)], ['34', '36'])).
% 5.43/5.60  thf('130', plain,
% 5.43/5.60      ((((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0))
% 5.43/5.60        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 5.43/5.60        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_D_1))
% 5.43/5.60        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k2_tarski @ sk_C @ sk_D_1)))),
% 5.43/5.60      inference('sup-', [status(thm)], ['11', '12'])).
% 5.43/5.60  thf('131', plain,
% 5.43/5.60      (![X10 : $i, X13 : $i, X14 : $i]:
% 5.43/5.60         (((X14) = (X10))
% 5.43/5.60          | ((X14) = (X13))
% 5.43/5.60          | ~ (r2_hidden @ X14 @ (k2_tarski @ X13 @ X10)))),
% 5.43/5.60      inference('simplify', [status(thm)], ['18'])).
% 5.43/5.60  thf('132', plain,
% 5.43/5.60      (![X0 : $i]:
% 5.43/5.60         (~ (r2_hidden @ X0 @ (k1_enumset1 @ sk_A @ sk_A @ sk_B))
% 5.43/5.60          | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_D_1))
% 5.43/5.60          | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 5.43/5.60          | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0))
% 5.43/5.60          | ((X0) = (sk_C))
% 5.43/5.60          | ((X0) = (sk_D_1)))),
% 5.43/5.60      inference('sup-', [status(thm)], ['130', '131'])).
% 5.43/5.60  thf('133', plain,
% 5.43/5.60      ((((sk_A) = (sk_D_1))
% 5.43/5.60        | ((sk_A) = (sk_C))
% 5.43/5.60        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0))
% 5.43/5.60        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 5.43/5.60        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_D_1)))),
% 5.43/5.60      inference('sup-', [status(thm)], ['129', '132'])).
% 5.43/5.60  thf('134', plain, (((sk_A) != (sk_C))),
% 5.43/5.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.43/5.60  thf('135', plain, (((sk_A) != (sk_D_1))),
% 5.43/5.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.43/5.60  thf('136', plain,
% 5.43/5.60      ((((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0))
% 5.43/5.60        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 5.43/5.60        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_D_1)))),
% 5.43/5.60      inference('simplify_reflect-', [status(thm)], ['133', '134', '135'])).
% 5.43/5.60  thf('137', plain, (((sk_D_1) = (sk_B))),
% 5.43/5.60      inference('condensation', [status(thm)], ['126'])).
% 5.43/5.60  thf('138', plain, (((sk_D_1) = (sk_B))),
% 5.43/5.60      inference('condensation', [status(thm)], ['126'])).
% 5.43/5.60  thf('139', plain, (((sk_D_1) = (sk_B))),
% 5.43/5.60      inference('condensation', [status(thm)], ['126'])).
% 5.43/5.60  thf('140', plain,
% 5.43/5.60      ((((k1_enumset1 @ sk_A @ sk_A @ sk_D_1) = (k1_xboole_0))
% 5.43/5.60        | ((k1_enumset1 @ sk_A @ sk_A @ sk_D_1) = (k1_tarski @ sk_C))
% 5.43/5.60        | ((k1_enumset1 @ sk_A @ sk_A @ sk_D_1) = (k1_tarski @ sk_D_1)))),
% 5.43/5.60      inference('demod', [status(thm)], ['136', '137', '138', '139'])).
% 5.43/5.60  thf('141', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 5.43/5.60      inference('sup+', [status(thm)], ['34', '36'])).
% 5.43/5.60  thf('142', plain,
% 5.43/5.60      (((r2_hidden @ sk_A @ (k1_tarski @ sk_D_1))
% 5.43/5.60        | ((k1_enumset1 @ sk_A @ sk_A @ sk_D_1) = (k1_tarski @ sk_C))
% 5.43/5.60        | ((k1_enumset1 @ sk_A @ sk_A @ sk_D_1) = (k1_xboole_0)))),
% 5.43/5.60      inference('sup+', [status(thm)], ['140', '141'])).
% 5.43/5.60  thf('143', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i]:
% 5.43/5.60         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 5.43/5.60      inference('simplify', [status(thm)], ['30'])).
% 5.43/5.60  thf('144', plain,
% 5.43/5.60      ((((k1_enumset1 @ sk_A @ sk_A @ sk_D_1) = (k1_xboole_0))
% 5.43/5.60        | ((k1_enumset1 @ sk_A @ sk_A @ sk_D_1) = (k1_tarski @ sk_C))
% 5.43/5.60        | ((sk_A) = (sk_D_1)))),
% 5.43/5.60      inference('sup-', [status(thm)], ['142', '143'])).
% 5.43/5.60  thf('145', plain, (((sk_A) != (sk_D_1))),
% 5.43/5.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.43/5.60  thf('146', plain,
% 5.43/5.60      ((((k1_enumset1 @ sk_A @ sk_A @ sk_D_1) = (k1_xboole_0))
% 5.43/5.60        | ((k1_enumset1 @ sk_A @ sk_A @ sk_D_1) = (k1_tarski @ sk_C)))),
% 5.43/5.60      inference('simplify_reflect-', [status(thm)], ['144', '145'])).
% 5.43/5.60  thf('147', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 5.43/5.60      inference('sup+', [status(thm)], ['24', '25'])).
% 5.43/5.60  thf('148', plain,
% 5.43/5.60      (((r2_hidden @ sk_D_1 @ (k1_tarski @ sk_C))
% 5.43/5.60        | ((k1_enumset1 @ sk_A @ sk_A @ sk_D_1) = (k1_xboole_0)))),
% 5.43/5.60      inference('sup+', [status(thm)], ['146', '147'])).
% 5.43/5.60  thf('149', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i]:
% 5.43/5.60         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 5.43/5.60      inference('simplify', [status(thm)], ['30'])).
% 5.43/5.60  thf('150', plain,
% 5.43/5.60      ((((k1_enumset1 @ sk_A @ sk_A @ sk_D_1) = (k1_xboole_0))
% 5.43/5.60        | ((sk_D_1) = (sk_C)))),
% 5.43/5.60      inference('sup-', [status(thm)], ['148', '149'])).
% 5.43/5.60  thf('151', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 5.43/5.60      inference('sup+', [status(thm)], ['24', '25'])).
% 5.43/5.60  thf('152', plain,
% 5.43/5.60      (((r2_hidden @ sk_D_1 @ k1_xboole_0) | ((sk_D_1) = (sk_C)))),
% 5.43/5.60      inference('sup+', [status(thm)], ['150', '151'])).
% 5.43/5.60  thf('153', plain,
% 5.43/5.60      ((((k1_enumset1 @ sk_A @ sk_A @ sk_D_1) = (k1_xboole_0))
% 5.43/5.60        | ((sk_D_1) = (sk_C)))),
% 5.43/5.60      inference('sup-', [status(thm)], ['148', '149'])).
% 5.43/5.60  thf('154', plain,
% 5.43/5.60      (![X92 : $i, X93 : $i]:
% 5.43/5.60         ((k1_enumset1 @ X92 @ X92 @ X93) = (k2_tarski @ X92 @ X93))),
% 5.43/5.60      inference('cnf', [status(esa)], [t70_enumset1])).
% 5.43/5.60  thf('155', plain,
% 5.43/5.60      (![X119 : $i, X122 : $i]:
% 5.43/5.60         (r1_tarski @ (k1_tarski @ X119) @ (k2_tarski @ X119 @ X122))),
% 5.43/5.60      inference('simplify', [status(thm)], ['82'])).
% 5.43/5.60  thf('156', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i]:
% 5.43/5.60         (r1_tarski @ (k1_tarski @ X1) @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 5.43/5.60      inference('sup+', [status(thm)], ['154', '155'])).
% 5.43/5.60  thf('157', plain,
% 5.43/5.60      (((r1_tarski @ (k1_tarski @ sk_A) @ k1_xboole_0) | ((sk_D_1) = (sk_C)))),
% 5.43/5.60      inference('sup+', [status(thm)], ['153', '156'])).
% 5.43/5.60  thf('158', plain,
% 5.43/5.60      (![X2 : $i, X3 : $i]:
% 5.43/5.60         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 5.43/5.60      inference('cnf', [status(esa)], [t12_xboole_1])).
% 5.43/5.60  thf('159', plain,
% 5.43/5.60      ((((sk_D_1) = (sk_C))
% 5.43/5.60        | ((k2_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0) = (k1_xboole_0)))),
% 5.43/5.60      inference('sup-', [status(thm)], ['157', '158'])).
% 5.43/5.60  thf('160', plain,
% 5.43/5.60      (![X0 : $i]:
% 5.43/5.60         ((k2_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0) = (k1_tarski @ X0))),
% 5.43/5.60      inference('demod', [status(thm)], ['61', '62'])).
% 5.43/5.60  thf('161', plain,
% 5.43/5.60      ((((sk_D_1) = (sk_C)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 5.43/5.60      inference('demod', [status(thm)], ['159', '160'])).
% 5.43/5.60  thf('162', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i]:
% 5.43/5.60         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 5.43/5.60      inference('simplify', [status(thm)], ['30'])).
% 5.43/5.60  thf('163', plain,
% 5.43/5.60      (![X0 : $i]:
% 5.43/5.60         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 5.43/5.60          | ((sk_D_1) = (sk_C))
% 5.43/5.60          | ((X0) = (sk_A)))),
% 5.43/5.60      inference('sup-', [status(thm)], ['161', '162'])).
% 5.43/5.60  thf('164', plain,
% 5.43/5.60      ((((sk_D_1) = (sk_C)) | ((sk_D_1) = (sk_A)) | ((sk_D_1) = (sk_C)))),
% 5.43/5.60      inference('sup-', [status(thm)], ['152', '163'])).
% 5.43/5.60  thf('165', plain, ((((sk_D_1) = (sk_A)) | ((sk_D_1) = (sk_C)))),
% 5.43/5.60      inference('simplify', [status(thm)], ['164'])).
% 5.43/5.60  thf('166', plain, (((sk_A) != (sk_D_1))),
% 5.43/5.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.43/5.60  thf('167', plain, (((sk_D_1) = (sk_C))),
% 5.43/5.60      inference('simplify_reflect-', [status(thm)], ['165', '166'])).
% 5.43/5.60  thf('168', plain, (((sk_D_1) = (sk_C))),
% 5.43/5.60      inference('simplify_reflect-', [status(thm)], ['165', '166'])).
% 5.43/5.60  thf('169', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.43/5.60         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0)
% 5.43/5.60           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)))),
% 5.43/5.60      inference('sup+', [status(thm)], ['65', '66'])).
% 5.43/5.60  thf('170', plain,
% 5.43/5.60      (![X119 : $i, X122 : $i]:
% 5.43/5.60         (r1_tarski @ (k1_tarski @ X122) @ (k2_tarski @ X119 @ X122))),
% 5.43/5.60      inference('simplify', [status(thm)], ['44'])).
% 5.43/5.60  thf('171', plain,
% 5.43/5.60      (![X4 : $i, X5 : $i]:
% 5.43/5.60         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 5.43/5.60      inference('cnf', [status(esa)], [t28_xboole_1])).
% 5.43/5.60  thf('172', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i]:
% 5.43/5.60         ((k3_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))
% 5.43/5.60           = (k1_tarski @ X0))),
% 5.43/5.60      inference('sup-', [status(thm)], ['170', '171'])).
% 5.43/5.60  thf('173', plain,
% 5.43/5.60      (![X0 : $i, X1 : $i]:
% 5.43/5.60         ((k4_xboole_0 @ X0 @ X1)
% 5.43/5.61           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 5.43/5.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.43/5.61  thf('174', plain,
% 5.43/5.61      (![X0 : $i, X1 : $i]:
% 5.43/5.61         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))
% 5.43/5.61           = (k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 5.43/5.61      inference('sup+', [status(thm)], ['172', '173'])).
% 5.43/5.61  thf('175', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ X7) = (k1_xboole_0))),
% 5.43/5.61      inference('cnf', [status(esa)], [t92_xboole_1])).
% 5.43/5.61  thf('176', plain,
% 5.43/5.61      (![X0 : $i, X1 : $i]:
% 5.43/5.61         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))
% 5.43/5.61           = (k1_xboole_0))),
% 5.43/5.61      inference('demod', [status(thm)], ['174', '175'])).
% 5.43/5.61  thf('177', plain,
% 5.43/5.61      (![X8 : $i, X9 : $i]:
% 5.43/5.61         ((k2_xboole_0 @ X8 @ X9)
% 5.43/5.61           = (k5_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8)))),
% 5.43/5.61      inference('cnf', [status(esa)], [t98_xboole_1])).
% 5.43/5.61  thf('178', plain,
% 5.43/5.61      (![X0 : $i, X1 : $i]:
% 5.43/5.61         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0))
% 5.43/5.61           = (k5_xboole_0 @ (k2_tarski @ X1 @ X0) @ k1_xboole_0))),
% 5.43/5.61      inference('sup+', [status(thm)], ['176', '177'])).
% 5.43/5.61  thf('179', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 5.43/5.61      inference('cnf', [status(esa)], [t5_boole])).
% 5.43/5.61  thf('180', plain,
% 5.43/5.61      (![X0 : $i, X1 : $i]:
% 5.43/5.61         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0))
% 5.43/5.61           = (k2_tarski @ X1 @ X0))),
% 5.43/5.61      inference('demod', [status(thm)], ['178', '179'])).
% 5.43/5.61  thf('181', plain,
% 5.43/5.61      (![X0 : $i, X1 : $i]:
% 5.43/5.61         ((k2_enumset1 @ X1 @ X0 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 5.43/5.61      inference('sup+', [status(thm)], ['169', '180'])).
% 5.43/5.61  thf('182', plain,
% 5.43/5.61      (![X0 : $i, X1 : $i]:
% 5.43/5.61         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 5.43/5.61      inference('demod', [status(thm)], ['117', '118'])).
% 5.43/5.61  thf('183', plain,
% 5.43/5.61      (![X0 : $i, X1 : $i]:
% 5.43/5.61         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_enumset1 @ X1 @ X0 @ X0 @ X0))),
% 5.43/5.61      inference('sup+', [status(thm)], ['181', '182'])).
% 5.43/5.61  thf('184', plain,
% 5.43/5.61      (![X0 : $i, X1 : $i]:
% 5.43/5.61         ((k1_enumset1 @ X0 @ X1 @ X1) = (k2_tarski @ X1 @ X0))),
% 5.43/5.61      inference('sup+', [status(thm)], ['109', '119'])).
% 5.43/5.61  thf('185', plain,
% 5.43/5.61      (![X0 : $i, X1 : $i]:
% 5.43/5.61         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 5.43/5.61      inference('demod', [status(thm)], ['117', '118'])).
% 5.43/5.61  thf('186', plain,
% 5.43/5.61      (![X0 : $i, X1 : $i]:
% 5.43/5.61         ((k1_enumset1 @ X0 @ X1 @ X1) = (k1_enumset1 @ X1 @ X0 @ X0))),
% 5.43/5.61      inference('sup+', [status(thm)], ['184', '185'])).
% 5.43/5.61  thf('187', plain,
% 5.43/5.61      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 5.43/5.61      inference('sup+', [status(thm)], ['99', '108'])).
% 5.43/5.61  thf('188', plain,
% 5.43/5.61      (![X92 : $i, X93 : $i]:
% 5.43/5.61         ((k1_enumset1 @ X92 @ X92 @ X93) = (k2_tarski @ X92 @ X93))),
% 5.43/5.61      inference('cnf', [status(esa)], [t70_enumset1])).
% 5.43/5.61  thf('189', plain,
% 5.43/5.61      (![X0 : $i, X1 : $i]:
% 5.43/5.61         ((k1_enumset1 @ X0 @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 5.43/5.61      inference('sup+', [status(thm)], ['187', '188'])).
% 5.43/5.61  thf('190', plain,
% 5.43/5.61      (![X0 : $i, X1 : $i]:
% 5.43/5.61         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 5.43/5.61      inference('demod', [status(thm)], ['117', '118'])).
% 5.43/5.61  thf('191', plain,
% 5.43/5.61      (![X0 : $i, X1 : $i]:
% 5.43/5.61         ((k1_enumset1 @ X0 @ X1 @ X1) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 5.43/5.61      inference('sup+', [status(thm)], ['189', '190'])).
% 5.43/5.61  thf('192', plain, (((sk_D_1) = (sk_C))),
% 5.43/5.61      inference('simplify_reflect-', [status(thm)], ['165', '166'])).
% 5.43/5.61  thf('193', plain,
% 5.43/5.61      (![X91 : $i]: ((k2_tarski @ X91 @ X91) = (k1_tarski @ X91))),
% 5.43/5.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 5.43/5.61  thf('194', plain,
% 5.43/5.61      (((k1_enumset1 @ sk_A @ sk_A @ sk_C) = (k1_tarski @ sk_C))),
% 5.43/5.61      inference('demod', [status(thm)],
% 5.43/5.61                ['128', '167', '168', '183', '186', '191', '192', '193'])).
% 5.43/5.61  thf('195', plain,
% 5.43/5.61      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 5.43/5.61      inference('sup+', [status(thm)], ['34', '36'])).
% 5.43/5.61  thf('196', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_C))),
% 5.43/5.61      inference('sup+', [status(thm)], ['194', '195'])).
% 5.43/5.61  thf('197', plain,
% 5.43/5.61      (![X0 : $i, X1 : $i]:
% 5.43/5.61         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 5.43/5.61      inference('simplify', [status(thm)], ['30'])).
% 5.43/5.61  thf('198', plain, (((sk_A) = (sk_C))),
% 5.43/5.61      inference('sup-', [status(thm)], ['196', '197'])).
% 5.43/5.61  thf('199', plain, (((sk_A) != (sk_C))),
% 5.43/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.43/5.61  thf('200', plain, ($false),
% 5.43/5.61      inference('simplify_reflect-', [status(thm)], ['198', '199'])).
% 5.43/5.61  
% 5.43/5.61  % SZS output end Refutation
% 5.43/5.61  
% 5.43/5.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

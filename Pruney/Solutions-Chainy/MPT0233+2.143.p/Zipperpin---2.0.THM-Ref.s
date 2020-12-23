%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pQqfB1u3Bt

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:53 EST 2020

% Result     : Theorem 2.97s
% Output     : Refutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :  230 (4543 expanded)
%              Number of leaves         :   29 (1372 expanded)
%              Depth                    :   40
%              Number of atoms          : 1953 (44599 expanded)
%              Number of equality atoms :  263 (6409 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

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

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('6',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( k2_enumset1 @ X40 @ X41 @ X42 @ X43 )
      = ( k2_xboole_0 @ ( k2_tarski @ X40 @ X41 ) @ ( k2_tarski @ X42 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

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
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( k2_enumset1 @ X44 @ X46 @ X45 @ X47 )
      = ( k2_enumset1 @ X44 @ X45 @ X46 @ X47 ) ) ),
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
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( k2_enumset1 @ X40 @ X41 @ X42 @ X43 )
      = ( k2_xboole_0 @ ( k2_tarski @ X40 @ X41 ) @ ( k2_tarski @ X42 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

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
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( k2_enumset1 @ X44 @ X46 @ X45 @ X47 )
      = ( k2_enumset1 @ X44 @ X45 @ X46 @ X47 ) ) ),
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
    ! [X92: $i,X93: $i] :
      ( ( k1_enumset1 @ X92 @ X92 @ X93 )
      = ( k2_tarski @ X92 @ X93 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('101',plain,(
    ! [X91: $i] :
      ( ( k2_tarski @ X91 @ X91 )
      = ( k1_tarski @ X91 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X119: $i,X122: $i] :
      ( r1_tarski @ ( k1_tarski @ X122 ) @ ( k2_tarski @ X119 @ X122 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_enumset1 @ X0 @ X0 @ X0 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X0 @ X0 @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('108',plain,(
    ! [X94: $i,X95: $i,X96: $i] :
      ( ( k2_enumset1 @ X94 @ X94 @ X95 @ X96 )
      = ( k1_enumset1 @ X94 @ X95 @ X96 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['99','109'])).

thf('111',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( k2_enumset1 @ X44 @ X46 @ X45 @ X47 )
      = ( k2_enumset1 @ X44 @ X45 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t104_enumset1])).

thf('112',plain,(
    ! [X119: $i,X121: $i,X122: $i] :
      ( ( r1_tarski @ X121 @ ( k2_tarski @ X119 @ X122 ) )
      | ( X121
       != ( k2_tarski @ X119 @ X122 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('113',plain,(
    ! [X119: $i,X122: $i] :
      ( r1_tarski @ ( k2_tarski @ X119 @ X122 ) @ ( k2_tarski @ X119 @ X122 ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( k2_enumset1 @ X40 @ X41 @ X42 @ X43 )
      = ( k2_xboole_0 @ ( k2_tarski @ X40 @ X41 ) @ ( k2_tarski @ X42 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['111','117'])).

thf('119',plain,(
    ! [X94: $i,X95: $i,X96: $i] :
      ( ( k2_enumset1 @ X94 @ X94 @ X95 @ X96 )
      = ( k1_enumset1 @ X94 @ X95 @ X96 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['110','120'])).

thf('122',plain,(
    ! [X91: $i] :
      ( ( k2_tarski @ X91 @ X91 )
      = ( k1_tarski @ X91 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ sk_B @ X0 )
        = ( k1_tarski @ X0 ) )
      | ( sk_D_1 = sk_B ) ) ),
    inference(demod,[status(thm)],['81','121','122'])).

thf('124',plain,(
    ! [X10: $i,X13: $i] :
      ( r2_hidden @ X13 @ ( k2_tarski @ X13 @ X10 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ ( k1_tarski @ X0 ) )
      | ( sk_D_1 = sk_B ) ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( sk_D_1 = sk_B )
      | ( sk_B = X0 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    sk_D_1 = sk_B ),
    inference(condensation,[status(thm)],['127'])).

thf('129',plain,
    ( ( k2_enumset1 @ sk_A @ sk_C @ sk_D_1 @ sk_D_1 )
    = ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['9','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','36'])).

thf('131',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D_1 ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k2_tarski @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('132',plain,(
    ! [X10: $i,X13: $i,X14: $i] :
      ( ( X14 = X10 )
      | ( X14 = X13 )
      | ~ ( r2_hidden @ X14 @ ( k2_tarski @ X13 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('133',plain,(
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
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,
    ( ( sk_A = sk_D_1 )
    | ( sk_A = sk_C )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['130','133'])).

thf('135',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    sk_A != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['134','135','136'])).

thf('138',plain,(
    sk_D_1 = sk_B ),
    inference(condensation,[status(thm)],['127'])).

thf('139',plain,(
    sk_D_1 = sk_B ),
    inference(condensation,[status(thm)],['127'])).

thf('140',plain,(
    sk_D_1 = sk_B ),
    inference(condensation,[status(thm)],['127'])).

thf('141',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_D_1 )
      = k1_xboole_0 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_D_1 )
      = ( k1_tarski @ sk_C ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_D_1 )
      = ( k1_tarski @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['137','138','139','140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','36'])).

thf('143',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_D_1 ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_D_1 )
      = ( k1_tarski @ sk_C ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('145',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_D_1 )
      = k1_xboole_0 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_D_1 )
      = ( k1_tarski @ sk_C ) )
    | ( sk_A = sk_D_1 ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    sk_A != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_D_1 )
      = k1_xboole_0 )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_D_1 )
      = ( k1_tarski @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('149',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k1_tarski @ sk_C ) )
    | ( ( k1_enumset1 @ sk_A @ sk_A @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('151',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_D_1 )
      = k1_xboole_0 )
    | ( sk_D_1 = sk_C ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('153',plain,
    ( ( r2_hidden @ sk_D_1 @ k1_xboole_0 )
    | ( sk_D_1 = sk_C ) ),
    inference('sup+',[status(thm)],['151','152'])).

thf('154',plain,
    ( ( ( k1_enumset1 @ sk_A @ sk_A @ sk_D_1 )
      = k1_xboole_0 )
    | ( sk_D_1 = sk_C ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('155',plain,(
    ! [X92: $i,X93: $i] :
      ( ( k1_enumset1 @ X92 @ X92 @ X93 )
      = ( k2_tarski @ X92 @ X93 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('156',plain,(
    ! [X119: $i,X122: $i] :
      ( r1_tarski @ ( k1_tarski @ X119 ) @ ( k2_tarski @ X119 @ X122 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['155','156'])).

thf('158',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
    | ( sk_D_1 = sk_C ) ),
    inference('sup+',[status(thm)],['154','157'])).

thf('159',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('160',plain,
    ( ( sk_D_1 = sk_C )
    | ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('162',plain,
    ( ( sk_D_1 = sk_C )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( sk_D_1 = sk_C )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,
    ( ( sk_D_1 = sk_C )
    | ( sk_D_1 = sk_A )
    | ( sk_D_1 = sk_C ) ),
    inference('sup-',[status(thm)],['153','164'])).

thf('166',plain,
    ( ( sk_D_1 = sk_A )
    | ( sk_D_1 = sk_C ) ),
    inference(simplify,[status(thm)],['165'])).

thf('167',plain,(
    sk_A != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    sk_D_1 = sk_C ),
    inference('simplify_reflect-',[status(thm)],['166','167'])).

thf('169',plain,(
    sk_D_1 = sk_C ),
    inference('simplify_reflect-',[status(thm)],['166','167'])).

thf('170',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('171',plain,(
    ! [X119: $i,X122: $i] :
      ( r1_tarski @ ( k1_tarski @ X122 ) @ ( k2_tarski @ X119 @ X122 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('172',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('175',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['175','176'])).

thf('178',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('179',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k5_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('181',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['179','180'])).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['170','181'])).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('184',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_enumset1 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['182','183'])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['95','98'])).

thf('186',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('187',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X1 )
      = ( k1_enumset1 @ X0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['185','186'])).

thf('188',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['95','98'])).

thf('189',plain,(
    ! [X92: $i,X93: $i] :
      ( ( k1_enumset1 @ X92 @ X92 @ X93 )
      = ( k2_tarski @ X92 @ X93 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('190',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k1_enumset1 @ X0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['188','189'])).

thf('191',plain,(
    sk_D_1 = sk_C ),
    inference('simplify_reflect-',[status(thm)],['166','167'])).

thf('192',plain,(
    ! [X91: $i] :
      ( ( k2_tarski @ X91 @ X91 )
      = ( k1_tarski @ X91 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('193',plain,
    ( ( k1_enumset1 @ sk_A @ sk_A @ sk_C )
    = ( k1_tarski @ sk_C ) ),
    inference(demod,[status(thm)],['129','168','169','184','187','190','191','192'])).

thf('194',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','36'])).

thf('195',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_C ) ),
    inference('sup+',[status(thm)],['193','194'])).

thf('196',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('197',plain,(
    sk_A = sk_C ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['197','198'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pQqfB1u3Bt
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:20:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 2.97/3.18  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.97/3.18  % Solved by: fo/fo7.sh
% 2.97/3.18  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.97/3.18  % done 5530 iterations in 2.686s
% 2.97/3.18  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.97/3.18  % SZS output start Refutation
% 2.97/3.18  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.97/3.18  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 2.97/3.18  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.97/3.18  thf(sk_B_type, type, sk_B: $i).
% 2.97/3.18  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.97/3.18  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.97/3.18  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 2.97/3.18  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.97/3.18  thf(sk_D_1_type, type, sk_D_1: $i).
% 2.97/3.18  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.97/3.18  thf(sk_C_type, type, sk_C: $i).
% 2.97/3.18  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.97/3.18  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 2.97/3.18  thf(sk_A_type, type, sk_A: $i).
% 2.97/3.18  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.97/3.18  thf(t28_zfmisc_1, conjecture,
% 2.97/3.18    (![A:$i,B:$i,C:$i,D:$i]:
% 2.97/3.18     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 2.97/3.18          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 2.97/3.18  thf(zf_stmt_0, negated_conjecture,
% 2.97/3.18    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 2.97/3.18        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 2.97/3.18             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 2.97/3.18    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 2.97/3.18  thf('0', plain,
% 2.97/3.18      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D_1))),
% 2.97/3.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.97/3.18  thf(t70_enumset1, axiom,
% 2.97/3.18    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 2.97/3.18  thf('1', plain,
% 2.97/3.18      (![X92 : $i, X93 : $i]:
% 2.97/3.18         ((k1_enumset1 @ X92 @ X92 @ X93) = (k2_tarski @ X92 @ X93))),
% 2.97/3.18      inference('cnf', [status(esa)], [t70_enumset1])).
% 2.97/3.18  thf('2', plain,
% 2.97/3.18      ((r1_tarski @ (k1_enumset1 @ sk_A @ sk_A @ sk_B) @ 
% 2.97/3.18        (k2_tarski @ sk_C @ sk_D_1))),
% 2.97/3.18      inference('demod', [status(thm)], ['0', '1'])).
% 2.97/3.18  thf(t12_xboole_1, axiom,
% 2.97/3.18    (![A:$i,B:$i]:
% 2.97/3.18     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 2.97/3.18  thf('3', plain,
% 2.97/3.18      (![X2 : $i, X3 : $i]:
% 2.97/3.18         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 2.97/3.18      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.97/3.18  thf('4', plain,
% 2.97/3.18      (((k2_xboole_0 @ (k1_enumset1 @ sk_A @ sk_A @ sk_B) @ 
% 2.97/3.18         (k2_tarski @ sk_C @ sk_D_1)) = (k2_tarski @ sk_C @ sk_D_1))),
% 2.97/3.18      inference('sup-', [status(thm)], ['2', '3'])).
% 2.97/3.18  thf('5', plain,
% 2.97/3.18      (![X92 : $i, X93 : $i]:
% 2.97/3.18         ((k1_enumset1 @ X92 @ X92 @ X93) = (k2_tarski @ X92 @ X93))),
% 2.97/3.18      inference('cnf', [status(esa)], [t70_enumset1])).
% 2.97/3.18  thf(l53_enumset1, axiom,
% 2.97/3.18    (![A:$i,B:$i,C:$i,D:$i]:
% 2.97/3.18     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 2.97/3.18       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 2.97/3.18  thf('6', plain,
% 2.97/3.18      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 2.97/3.18         ((k2_enumset1 @ X40 @ X41 @ X42 @ X43)
% 2.97/3.18           = (k2_xboole_0 @ (k2_tarski @ X40 @ X41) @ (k2_tarski @ X42 @ X43)))),
% 2.97/3.18      inference('cnf', [status(esa)], [l53_enumset1])).
% 2.97/3.18  thf('7', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.97/3.18         ((k2_enumset1 @ X1 @ X0 @ X3 @ X2)
% 2.97/3.18           = (k2_xboole_0 @ (k1_enumset1 @ X1 @ X1 @ X0) @ 
% 2.97/3.18              (k2_tarski @ X3 @ X2)))),
% 2.97/3.18      inference('sup+', [status(thm)], ['5', '6'])).
% 2.97/3.18  thf(t104_enumset1, axiom,
% 2.97/3.18    (![A:$i,B:$i,C:$i,D:$i]:
% 2.97/3.18     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ B @ D ) ))).
% 2.97/3.18  thf('8', plain,
% 2.97/3.18      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 2.97/3.18         ((k2_enumset1 @ X44 @ X46 @ X45 @ X47)
% 2.97/3.18           = (k2_enumset1 @ X44 @ X45 @ X46 @ X47))),
% 2.97/3.18      inference('cnf', [status(esa)], [t104_enumset1])).
% 2.97/3.18  thf('9', plain,
% 2.97/3.18      (((k2_enumset1 @ sk_A @ sk_C @ sk_B @ sk_D_1)
% 2.97/3.18         = (k2_tarski @ sk_C @ sk_D_1))),
% 2.97/3.18      inference('demod', [status(thm)], ['4', '7', '8'])).
% 2.97/3.18  thf(t71_enumset1, axiom,
% 2.97/3.18    (![A:$i,B:$i,C:$i]:
% 2.97/3.18     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 2.97/3.18  thf('10', plain,
% 2.97/3.18      (![X94 : $i, X95 : $i, X96 : $i]:
% 2.97/3.18         ((k2_enumset1 @ X94 @ X94 @ X95 @ X96)
% 2.97/3.18           = (k1_enumset1 @ X94 @ X95 @ X96))),
% 2.97/3.18      inference('cnf', [status(esa)], [t71_enumset1])).
% 2.97/3.18  thf('11', plain,
% 2.97/3.18      ((r1_tarski @ (k1_enumset1 @ sk_A @ sk_A @ sk_B) @ 
% 2.97/3.18        (k2_tarski @ sk_C @ sk_D_1))),
% 2.97/3.18      inference('demod', [status(thm)], ['0', '1'])).
% 2.97/3.18  thf(l45_zfmisc_1, axiom,
% 2.97/3.18    (![A:$i,B:$i,C:$i]:
% 2.97/3.18     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 2.97/3.18       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 2.97/3.18            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 2.97/3.18  thf('12', plain,
% 2.97/3.18      (![X119 : $i, X120 : $i, X121 : $i]:
% 2.97/3.18         (((X121) = (k2_tarski @ X119 @ X120))
% 2.97/3.18          | ((X121) = (k1_tarski @ X120))
% 2.97/3.18          | ((X121) = (k1_tarski @ X119))
% 2.97/3.18          | ((X121) = (k1_xboole_0))
% 2.97/3.18          | ~ (r1_tarski @ X121 @ (k2_tarski @ X119 @ X120)))),
% 2.97/3.18      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 2.97/3.18  thf('13', plain,
% 2.97/3.18      ((((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0))
% 2.97/3.18        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 2.97/3.18        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_D_1))
% 2.97/3.18        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k2_tarski @ sk_C @ sk_D_1)))),
% 2.97/3.18      inference('sup-', [status(thm)], ['11', '12'])).
% 2.97/3.18  thf(d2_tarski, axiom,
% 2.97/3.18    (![A:$i,B:$i,C:$i]:
% 2.97/3.18     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 2.97/3.18       ( ![D:$i]:
% 2.97/3.18         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 2.97/3.18  thf('14', plain,
% 2.97/3.18      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 2.97/3.18         (((X11) != (X10))
% 2.97/3.18          | (r2_hidden @ X11 @ X12)
% 2.97/3.18          | ((X12) != (k2_tarski @ X13 @ X10)))),
% 2.97/3.18      inference('cnf', [status(esa)], [d2_tarski])).
% 2.97/3.18  thf('15', plain,
% 2.97/3.18      (![X10 : $i, X13 : $i]: (r2_hidden @ X10 @ (k2_tarski @ X13 @ X10))),
% 2.97/3.18      inference('simplify', [status(thm)], ['14'])).
% 2.97/3.18  thf('16', plain,
% 2.97/3.18      (((r2_hidden @ sk_D_1 @ (k1_enumset1 @ sk_A @ sk_A @ sk_B))
% 2.97/3.18        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_D_1))
% 2.97/3.18        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 2.97/3.18        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0)))),
% 2.97/3.18      inference('sup+', [status(thm)], ['13', '15'])).
% 2.97/3.18  thf('17', plain,
% 2.97/3.18      (![X92 : $i, X93 : $i]:
% 2.97/3.18         ((k1_enumset1 @ X92 @ X92 @ X93) = (k2_tarski @ X92 @ X93))),
% 2.97/3.18      inference('cnf', [status(esa)], [t70_enumset1])).
% 2.97/3.18  thf('18', plain,
% 2.97/3.18      (![X10 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 2.97/3.18         (~ (r2_hidden @ X14 @ X12)
% 2.97/3.18          | ((X14) = (X13))
% 2.97/3.18          | ((X14) = (X10))
% 2.97/3.18          | ((X12) != (k2_tarski @ X13 @ X10)))),
% 2.97/3.18      inference('cnf', [status(esa)], [d2_tarski])).
% 2.97/3.18  thf('19', plain,
% 2.97/3.18      (![X10 : $i, X13 : $i, X14 : $i]:
% 2.97/3.18         (((X14) = (X10))
% 2.97/3.18          | ((X14) = (X13))
% 2.97/3.18          | ~ (r2_hidden @ X14 @ (k2_tarski @ X13 @ X10)))),
% 2.97/3.18      inference('simplify', [status(thm)], ['18'])).
% 2.97/3.18  thf('20', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.97/3.18         (~ (r2_hidden @ X2 @ (k1_enumset1 @ X1 @ X1 @ X0))
% 2.97/3.18          | ((X2) = (X1))
% 2.97/3.18          | ((X2) = (X0)))),
% 2.97/3.18      inference('sup-', [status(thm)], ['17', '19'])).
% 2.97/3.18  thf('21', plain,
% 2.97/3.18      ((((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0))
% 2.97/3.18        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 2.97/3.18        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_D_1))
% 2.97/3.18        | ((sk_D_1) = (sk_B))
% 2.97/3.18        | ((sk_D_1) = (sk_A)))),
% 2.97/3.18      inference('sup-', [status(thm)], ['16', '20'])).
% 2.97/3.18  thf('22', plain, (((sk_A) != (sk_D_1))),
% 2.97/3.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.97/3.18  thf('23', plain,
% 2.97/3.18      ((((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0))
% 2.97/3.18        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 2.97/3.18        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_D_1))
% 2.97/3.18        | ((sk_D_1) = (sk_B)))),
% 2.97/3.18      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 2.97/3.18  thf('24', plain,
% 2.97/3.18      (![X92 : $i, X93 : $i]:
% 2.97/3.18         ((k1_enumset1 @ X92 @ X92 @ X93) = (k2_tarski @ X92 @ X93))),
% 2.97/3.18      inference('cnf', [status(esa)], [t70_enumset1])).
% 2.97/3.18  thf('25', plain,
% 2.97/3.18      (![X10 : $i, X13 : $i]: (r2_hidden @ X10 @ (k2_tarski @ X13 @ X10))),
% 2.97/3.18      inference('simplify', [status(thm)], ['14'])).
% 2.97/3.18  thf('26', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 2.97/3.18      inference('sup+', [status(thm)], ['24', '25'])).
% 2.97/3.18  thf('27', plain,
% 2.97/3.18      (((r2_hidden @ sk_B @ (k1_tarski @ sk_D_1))
% 2.97/3.18        | ((sk_D_1) = (sk_B))
% 2.97/3.18        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 2.97/3.18        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0)))),
% 2.97/3.18      inference('sup+', [status(thm)], ['23', '26'])).
% 2.97/3.18  thf(t69_enumset1, axiom,
% 2.97/3.18    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 2.97/3.18  thf('28', plain,
% 2.97/3.18      (![X91 : $i]: ((k2_tarski @ X91 @ X91) = (k1_tarski @ X91))),
% 2.97/3.18      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.97/3.18  thf('29', plain,
% 2.97/3.18      (![X10 : $i, X13 : $i, X14 : $i]:
% 2.97/3.18         (((X14) = (X10))
% 2.97/3.18          | ((X14) = (X13))
% 2.97/3.18          | ~ (r2_hidden @ X14 @ (k2_tarski @ X13 @ X10)))),
% 2.97/3.18      inference('simplify', [status(thm)], ['18'])).
% 2.97/3.18  thf('30', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 2.97/3.18      inference('sup-', [status(thm)], ['28', '29'])).
% 2.97/3.18  thf('31', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 2.97/3.18      inference('simplify', [status(thm)], ['30'])).
% 2.97/3.18  thf('32', plain,
% 2.97/3.18      ((((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0))
% 2.97/3.18        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 2.97/3.18        | ((sk_D_1) = (sk_B))
% 2.97/3.18        | ((sk_B) = (sk_D_1)))),
% 2.97/3.18      inference('sup-', [status(thm)], ['27', '31'])).
% 2.97/3.18  thf('33', plain,
% 2.97/3.18      ((((sk_D_1) = (sk_B))
% 2.97/3.18        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 2.97/3.18        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0)))),
% 2.97/3.18      inference('simplify', [status(thm)], ['32'])).
% 2.97/3.18  thf('34', plain,
% 2.97/3.18      (![X92 : $i, X93 : $i]:
% 2.97/3.18         ((k1_enumset1 @ X92 @ X92 @ X93) = (k2_tarski @ X92 @ X93))),
% 2.97/3.18      inference('cnf', [status(esa)], [t70_enumset1])).
% 2.97/3.18  thf('35', plain,
% 2.97/3.18      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 2.97/3.18         (((X11) != (X13))
% 2.97/3.18          | (r2_hidden @ X11 @ X12)
% 2.97/3.18          | ((X12) != (k2_tarski @ X13 @ X10)))),
% 2.97/3.18      inference('cnf', [status(esa)], [d2_tarski])).
% 2.97/3.18  thf('36', plain,
% 2.97/3.18      (![X10 : $i, X13 : $i]: (r2_hidden @ X13 @ (k2_tarski @ X13 @ X10))),
% 2.97/3.18      inference('simplify', [status(thm)], ['35'])).
% 2.97/3.18  thf('37', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 2.97/3.18      inference('sup+', [status(thm)], ['34', '36'])).
% 2.97/3.18  thf('38', plain,
% 2.97/3.18      (((r2_hidden @ sk_A @ (k1_tarski @ sk_C))
% 2.97/3.18        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0))
% 2.97/3.18        | ((sk_D_1) = (sk_B)))),
% 2.97/3.18      inference('sup+', [status(thm)], ['33', '37'])).
% 2.97/3.18  thf('39', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 2.97/3.18      inference('simplify', [status(thm)], ['30'])).
% 2.97/3.18  thf('40', plain,
% 2.97/3.18      ((((sk_D_1) = (sk_B))
% 2.97/3.18        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0))
% 2.97/3.18        | ((sk_A) = (sk_C)))),
% 2.97/3.18      inference('sup-', [status(thm)], ['38', '39'])).
% 2.97/3.18  thf('41', plain, (((sk_A) != (sk_C))),
% 2.97/3.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.97/3.18  thf('42', plain,
% 2.97/3.18      ((((sk_D_1) = (sk_B))
% 2.97/3.18        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0)))),
% 2.97/3.18      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 2.97/3.18  thf('43', plain,
% 2.97/3.18      (![X92 : $i, X93 : $i]:
% 2.97/3.18         ((k1_enumset1 @ X92 @ X92 @ X93) = (k2_tarski @ X92 @ X93))),
% 2.97/3.18      inference('cnf', [status(esa)], [t70_enumset1])).
% 2.97/3.18  thf('44', plain,
% 2.97/3.18      (![X119 : $i, X121 : $i, X122 : $i]:
% 2.97/3.18         ((r1_tarski @ X121 @ (k2_tarski @ X119 @ X122))
% 2.97/3.18          | ((X121) != (k1_tarski @ X122)))),
% 2.97/3.18      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 2.97/3.18  thf('45', plain,
% 2.97/3.18      (![X119 : $i, X122 : $i]:
% 2.97/3.18         (r1_tarski @ (k1_tarski @ X122) @ (k2_tarski @ X119 @ X122))),
% 2.97/3.18      inference('simplify', [status(thm)], ['44'])).
% 2.97/3.18  thf('46', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         (r1_tarski @ (k1_tarski @ X0) @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 2.97/3.18      inference('sup+', [status(thm)], ['43', '45'])).
% 2.97/3.18  thf('47', plain,
% 2.97/3.18      (((r1_tarski @ (k1_tarski @ sk_B) @ k1_xboole_0) | ((sk_D_1) = (sk_B)))),
% 2.97/3.18      inference('sup+', [status(thm)], ['42', '46'])).
% 2.97/3.18  thf('48', plain,
% 2.97/3.18      (![X2 : $i, X3 : $i]:
% 2.97/3.18         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 2.97/3.18      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.97/3.18  thf('49', plain,
% 2.97/3.18      ((((sk_D_1) = (sk_B))
% 2.97/3.18        | ((k2_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0) = (k1_xboole_0)))),
% 2.97/3.18      inference('sup-', [status(thm)], ['47', '48'])).
% 2.97/3.18  thf('50', plain,
% 2.97/3.18      (![X91 : $i]: ((k2_tarski @ X91 @ X91) = (k1_tarski @ X91))),
% 2.97/3.18      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.97/3.18  thf('51', plain,
% 2.97/3.18      (![X119 : $i, X121 : $i, X122 : $i]:
% 2.97/3.18         ((r1_tarski @ X121 @ (k2_tarski @ X119 @ X122))
% 2.97/3.18          | ((X121) != (k1_xboole_0)))),
% 2.97/3.18      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 2.97/3.18  thf('52', plain,
% 2.97/3.18      (![X119 : $i, X122 : $i]:
% 2.97/3.18         (r1_tarski @ k1_xboole_0 @ (k2_tarski @ X119 @ X122))),
% 2.97/3.18      inference('simplify', [status(thm)], ['51'])).
% 2.97/3.18  thf('53', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0))),
% 2.97/3.18      inference('sup+', [status(thm)], ['50', '52'])).
% 2.97/3.18  thf(t28_xboole_1, axiom,
% 2.97/3.18    (![A:$i,B:$i]:
% 2.97/3.18     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.97/3.18  thf('54', plain,
% 2.97/3.18      (![X4 : $i, X5 : $i]:
% 2.97/3.18         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 2.97/3.18      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.97/3.18  thf('55', plain,
% 2.97/3.18      (![X0 : $i]:
% 2.97/3.18         ((k3_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 2.97/3.18      inference('sup-', [status(thm)], ['53', '54'])).
% 2.97/3.18  thf(t100_xboole_1, axiom,
% 2.97/3.18    (![A:$i,B:$i]:
% 2.97/3.18     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.97/3.18  thf('56', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         ((k4_xboole_0 @ X0 @ X1)
% 2.97/3.18           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.97/3.18      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.97/3.18  thf('57', plain,
% 2.97/3.18      (![X0 : $i]:
% 2.97/3.18         ((k4_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0))
% 2.97/3.18           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 2.97/3.18      inference('sup+', [status(thm)], ['55', '56'])).
% 2.97/3.18  thf(t5_boole, axiom,
% 2.97/3.18    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.97/3.18  thf('58', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 2.97/3.18      inference('cnf', [status(esa)], [t5_boole])).
% 2.97/3.18  thf('59', plain,
% 2.97/3.18      (![X0 : $i]:
% 2.97/3.18         ((k4_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 2.97/3.18      inference('demod', [status(thm)], ['57', '58'])).
% 2.97/3.18  thf(t98_xboole_1, axiom,
% 2.97/3.18    (![A:$i,B:$i]:
% 2.97/3.18     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 2.97/3.18  thf('60', plain,
% 2.97/3.18      (![X8 : $i, X9 : $i]:
% 2.97/3.18         ((k2_xboole_0 @ X8 @ X9)
% 2.97/3.18           = (k5_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8)))),
% 2.97/3.18      inference('cnf', [status(esa)], [t98_xboole_1])).
% 2.97/3.18  thf('61', plain,
% 2.97/3.18      (![X0 : $i]:
% 2.97/3.18         ((k2_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0)
% 2.97/3.18           = (k5_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))),
% 2.97/3.18      inference('sup+', [status(thm)], ['59', '60'])).
% 2.97/3.18  thf('62', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 2.97/3.18      inference('cnf', [status(esa)], [t5_boole])).
% 2.97/3.18  thf('63', plain,
% 2.97/3.18      (![X0 : $i]:
% 2.97/3.18         ((k2_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0) = (k1_tarski @ X0))),
% 2.97/3.18      inference('demod', [status(thm)], ['61', '62'])).
% 2.97/3.18  thf('64', plain,
% 2.97/3.18      ((((sk_D_1) = (sk_B)) | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 2.97/3.18      inference('demod', [status(thm)], ['49', '63'])).
% 2.97/3.18  thf('65', plain,
% 2.97/3.18      (![X91 : $i]: ((k2_tarski @ X91 @ X91) = (k1_tarski @ X91))),
% 2.97/3.18      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.97/3.18  thf('66', plain,
% 2.97/3.18      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 2.97/3.18         ((k2_enumset1 @ X40 @ X41 @ X42 @ X43)
% 2.97/3.18           = (k2_xboole_0 @ (k2_tarski @ X40 @ X41) @ (k2_tarski @ X42 @ X43)))),
% 2.97/3.18      inference('cnf', [status(esa)], [l53_enumset1])).
% 2.97/3.18  thf('67', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.97/3.18         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0)
% 2.97/3.18           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)))),
% 2.97/3.18      inference('sup+', [status(thm)], ['65', '66'])).
% 2.97/3.18  thf('68', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         (((k2_enumset1 @ X1 @ X0 @ sk_B @ sk_B)
% 2.97/3.18            = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ k1_xboole_0))
% 2.97/3.18          | ((sk_D_1) = (sk_B)))),
% 2.97/3.18      inference('sup+', [status(thm)], ['64', '67'])).
% 2.97/3.18  thf('69', plain,
% 2.97/3.18      (![X119 : $i, X122 : $i]:
% 2.97/3.18         (r1_tarski @ k1_xboole_0 @ (k2_tarski @ X119 @ X122))),
% 2.97/3.18      inference('simplify', [status(thm)], ['51'])).
% 2.97/3.18  thf('70', plain,
% 2.97/3.18      (![X4 : $i, X5 : $i]:
% 2.97/3.18         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 2.97/3.18      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.97/3.18  thf('71', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         ((k3_xboole_0 @ k1_xboole_0 @ (k2_tarski @ X1 @ X0)) = (k1_xboole_0))),
% 2.97/3.18      inference('sup-', [status(thm)], ['69', '70'])).
% 2.97/3.18  thf('72', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         ((k4_xboole_0 @ X0 @ X1)
% 2.97/3.18           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.97/3.18      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.97/3.18  thf('73', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         ((k4_xboole_0 @ k1_xboole_0 @ (k2_tarski @ X1 @ X0))
% 2.97/3.18           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 2.97/3.18      inference('sup+', [status(thm)], ['71', '72'])).
% 2.97/3.18  thf('74', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 2.97/3.18      inference('cnf', [status(esa)], [t5_boole])).
% 2.97/3.18  thf('75', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         ((k4_xboole_0 @ k1_xboole_0 @ (k2_tarski @ X1 @ X0)) = (k1_xboole_0))),
% 2.97/3.18      inference('demod', [status(thm)], ['73', '74'])).
% 2.97/3.18  thf('76', plain,
% 2.97/3.18      (![X8 : $i, X9 : $i]:
% 2.97/3.18         ((k2_xboole_0 @ X8 @ X9)
% 2.97/3.18           = (k5_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8)))),
% 2.97/3.18      inference('cnf', [status(esa)], [t98_xboole_1])).
% 2.97/3.18  thf('77', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ k1_xboole_0)
% 2.97/3.18           = (k5_xboole_0 @ (k2_tarski @ X1 @ X0) @ k1_xboole_0))),
% 2.97/3.18      inference('sup+', [status(thm)], ['75', '76'])).
% 2.97/3.18  thf('78', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 2.97/3.18      inference('cnf', [status(esa)], [t5_boole])).
% 2.97/3.18  thf('79', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ k1_xboole_0)
% 2.97/3.18           = (k2_tarski @ X1 @ X0))),
% 2.97/3.18      inference('demod', [status(thm)], ['77', '78'])).
% 2.97/3.18  thf('80', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         (((k2_enumset1 @ X1 @ X0 @ sk_B @ sk_B) = (k2_tarski @ X1 @ X0))
% 2.97/3.18          | ((sk_D_1) = (sk_B)))),
% 2.97/3.18      inference('demod', [status(thm)], ['68', '79'])).
% 2.97/3.18  thf('81', plain,
% 2.97/3.18      (![X0 : $i]:
% 2.97/3.18         (((k1_enumset1 @ X0 @ sk_B @ sk_B) = (k2_tarski @ X0 @ X0))
% 2.97/3.18          | ((sk_D_1) = (sk_B)))),
% 2.97/3.18      inference('sup+', [status(thm)], ['10', '80'])).
% 2.97/3.18  thf('82', plain,
% 2.97/3.18      (![X119 : $i, X121 : $i, X122 : $i]:
% 2.97/3.18         ((r1_tarski @ X121 @ (k2_tarski @ X119 @ X122))
% 2.97/3.18          | ((X121) != (k1_tarski @ X119)))),
% 2.97/3.18      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 2.97/3.18  thf('83', plain,
% 2.97/3.18      (![X119 : $i, X122 : $i]:
% 2.97/3.18         (r1_tarski @ (k1_tarski @ X119) @ (k2_tarski @ X119 @ X122))),
% 2.97/3.18      inference('simplify', [status(thm)], ['82'])).
% 2.97/3.18  thf('84', plain,
% 2.97/3.18      (![X4 : $i, X5 : $i]:
% 2.97/3.18         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 2.97/3.18      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.97/3.18  thf('85', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         ((k3_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 2.97/3.18           = (k1_tarski @ X1))),
% 2.97/3.18      inference('sup-', [status(thm)], ['83', '84'])).
% 2.97/3.18  thf('86', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         ((k4_xboole_0 @ X0 @ X1)
% 2.97/3.18           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.97/3.18      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.97/3.18  thf('87', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1))
% 2.97/3.18           = (k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 2.97/3.18      inference('sup+', [status(thm)], ['85', '86'])).
% 2.97/3.18  thf(t92_xboole_1, axiom,
% 2.97/3.18    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 2.97/3.18  thf('88', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ X7) = (k1_xboole_0))),
% 2.97/3.18      inference('cnf', [status(esa)], [t92_xboole_1])).
% 2.97/3.18  thf('89', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1))
% 2.97/3.18           = (k1_xboole_0))),
% 2.97/3.18      inference('demod', [status(thm)], ['87', '88'])).
% 2.97/3.18  thf('90', plain,
% 2.97/3.18      (![X8 : $i, X9 : $i]:
% 2.97/3.18         ((k2_xboole_0 @ X8 @ X9)
% 2.97/3.18           = (k5_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8)))),
% 2.97/3.18      inference('cnf', [status(esa)], [t98_xboole_1])).
% 2.97/3.18  thf('91', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 2.97/3.18           = (k5_xboole_0 @ (k2_tarski @ X1 @ X0) @ k1_xboole_0))),
% 2.97/3.18      inference('sup+', [status(thm)], ['89', '90'])).
% 2.97/3.18  thf('92', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 2.97/3.18      inference('cnf', [status(esa)], [t5_boole])).
% 2.97/3.18  thf('93', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 2.97/3.18           = (k2_tarski @ X1 @ X0))),
% 2.97/3.18      inference('demod', [status(thm)], ['91', '92'])).
% 2.97/3.18  thf('94', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.97/3.18         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0)
% 2.97/3.18           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)))),
% 2.97/3.18      inference('sup+', [status(thm)], ['65', '66'])).
% 2.97/3.18  thf('95', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         ((k2_enumset1 @ X1 @ X0 @ X1 @ X1) = (k2_tarski @ X1 @ X0))),
% 2.97/3.18      inference('sup+', [status(thm)], ['93', '94'])).
% 2.97/3.18  thf('96', plain,
% 2.97/3.18      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 2.97/3.18         ((k2_enumset1 @ X44 @ X46 @ X45 @ X47)
% 2.97/3.18           = (k2_enumset1 @ X44 @ X45 @ X46 @ X47))),
% 2.97/3.18      inference('cnf', [status(esa)], [t104_enumset1])).
% 2.97/3.18  thf('97', plain,
% 2.97/3.18      (![X94 : $i, X95 : $i, X96 : $i]:
% 2.97/3.18         ((k2_enumset1 @ X94 @ X94 @ X95 @ X96)
% 2.97/3.18           = (k1_enumset1 @ X94 @ X95 @ X96))),
% 2.97/3.18      inference('cnf', [status(esa)], [t71_enumset1])).
% 2.97/3.18  thf('98', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.97/3.18         ((k2_enumset1 @ X1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 2.97/3.18      inference('sup+', [status(thm)], ['96', '97'])).
% 2.97/3.18  thf('99', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         ((k1_enumset1 @ X1 @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 2.97/3.18      inference('demod', [status(thm)], ['95', '98'])).
% 2.97/3.18  thf('100', plain,
% 2.97/3.18      (![X92 : $i, X93 : $i]:
% 2.97/3.18         ((k1_enumset1 @ X92 @ X92 @ X93) = (k2_tarski @ X92 @ X93))),
% 2.97/3.18      inference('cnf', [status(esa)], [t70_enumset1])).
% 2.97/3.18  thf('101', plain,
% 2.97/3.18      (![X91 : $i]: ((k2_tarski @ X91 @ X91) = (k1_tarski @ X91))),
% 2.97/3.18      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.97/3.18  thf('102', plain,
% 2.97/3.18      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 2.97/3.18      inference('sup+', [status(thm)], ['100', '101'])).
% 2.97/3.18  thf('103', plain,
% 2.97/3.18      (![X119 : $i, X122 : $i]:
% 2.97/3.18         (r1_tarski @ (k1_tarski @ X122) @ (k2_tarski @ X119 @ X122))),
% 2.97/3.18      inference('simplify', [status(thm)], ['44'])).
% 2.97/3.18  thf('104', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         (r1_tarski @ (k1_enumset1 @ X0 @ X0 @ X0) @ (k2_tarski @ X1 @ X0))),
% 2.97/3.18      inference('sup+', [status(thm)], ['102', '103'])).
% 2.97/3.18  thf('105', plain,
% 2.97/3.18      (![X2 : $i, X3 : $i]:
% 2.97/3.18         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 2.97/3.18      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.97/3.18  thf('106', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         ((k2_xboole_0 @ (k1_enumset1 @ X0 @ X0 @ X0) @ (k2_tarski @ X1 @ X0))
% 2.97/3.18           = (k2_tarski @ X1 @ X0))),
% 2.97/3.18      inference('sup-', [status(thm)], ['104', '105'])).
% 2.97/3.18  thf('107', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.97/3.18         ((k2_enumset1 @ X1 @ X0 @ X3 @ X2)
% 2.97/3.18           = (k2_xboole_0 @ (k1_enumset1 @ X1 @ X1 @ X0) @ 
% 2.97/3.18              (k2_tarski @ X3 @ X2)))),
% 2.97/3.18      inference('sup+', [status(thm)], ['5', '6'])).
% 2.97/3.18  thf('108', plain,
% 2.97/3.18      (![X94 : $i, X95 : $i, X96 : $i]:
% 2.97/3.18         ((k2_enumset1 @ X94 @ X94 @ X95 @ X96)
% 2.97/3.18           = (k1_enumset1 @ X94 @ X95 @ X96))),
% 2.97/3.18      inference('cnf', [status(esa)], [t71_enumset1])).
% 2.97/3.18  thf('109', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         ((k1_enumset1 @ X0 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 2.97/3.18      inference('demod', [status(thm)], ['106', '107', '108'])).
% 2.97/3.18  thf('110', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 2.97/3.18      inference('sup+', [status(thm)], ['99', '109'])).
% 2.97/3.18  thf('111', plain,
% 2.97/3.18      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 2.97/3.18         ((k2_enumset1 @ X44 @ X46 @ X45 @ X47)
% 2.97/3.18           = (k2_enumset1 @ X44 @ X45 @ X46 @ X47))),
% 2.97/3.18      inference('cnf', [status(esa)], [t104_enumset1])).
% 2.97/3.18  thf('112', plain,
% 2.97/3.18      (![X119 : $i, X121 : $i, X122 : $i]:
% 2.97/3.18         ((r1_tarski @ X121 @ (k2_tarski @ X119 @ X122))
% 2.97/3.18          | ((X121) != (k2_tarski @ X119 @ X122)))),
% 2.97/3.18      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 2.97/3.18  thf('113', plain,
% 2.97/3.18      (![X119 : $i, X122 : $i]:
% 2.97/3.18         (r1_tarski @ (k2_tarski @ X119 @ X122) @ (k2_tarski @ X119 @ X122))),
% 2.97/3.18      inference('simplify', [status(thm)], ['112'])).
% 2.97/3.18  thf('114', plain,
% 2.97/3.18      (![X2 : $i, X3 : $i]:
% 2.97/3.18         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 2.97/3.18      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.97/3.18  thf('115', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X1 @ X0))
% 2.97/3.18           = (k2_tarski @ X1 @ X0))),
% 2.97/3.18      inference('sup-', [status(thm)], ['113', '114'])).
% 2.97/3.18  thf('116', plain,
% 2.97/3.18      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 2.97/3.18         ((k2_enumset1 @ X40 @ X41 @ X42 @ X43)
% 2.97/3.18           = (k2_xboole_0 @ (k2_tarski @ X40 @ X41) @ (k2_tarski @ X42 @ X43)))),
% 2.97/3.18      inference('cnf', [status(esa)], [l53_enumset1])).
% 2.97/3.18  thf('117', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         ((k2_enumset1 @ X1 @ X0 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 2.97/3.18      inference('demod', [status(thm)], ['115', '116'])).
% 2.97/3.18  thf('118', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         ((k2_enumset1 @ X1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 2.97/3.18      inference('sup+', [status(thm)], ['111', '117'])).
% 2.97/3.18  thf('119', plain,
% 2.97/3.18      (![X94 : $i, X95 : $i, X96 : $i]:
% 2.97/3.18         ((k2_enumset1 @ X94 @ X94 @ X95 @ X96)
% 2.97/3.18           = (k1_enumset1 @ X94 @ X95 @ X96))),
% 2.97/3.18      inference('cnf', [status(esa)], [t71_enumset1])).
% 2.97/3.18  thf('120', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 2.97/3.18      inference('demod', [status(thm)], ['118', '119'])).
% 2.97/3.18  thf('121', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         ((k1_enumset1 @ X0 @ X1 @ X1) = (k2_tarski @ X1 @ X0))),
% 2.97/3.18      inference('sup+', [status(thm)], ['110', '120'])).
% 2.97/3.18  thf('122', plain,
% 2.97/3.18      (![X91 : $i]: ((k2_tarski @ X91 @ X91) = (k1_tarski @ X91))),
% 2.97/3.18      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.97/3.18  thf('123', plain,
% 2.97/3.18      (![X0 : $i]:
% 2.97/3.18         (((k2_tarski @ sk_B @ X0) = (k1_tarski @ X0)) | ((sk_D_1) = (sk_B)))),
% 2.97/3.18      inference('demod', [status(thm)], ['81', '121', '122'])).
% 2.97/3.18  thf('124', plain,
% 2.97/3.18      (![X10 : $i, X13 : $i]: (r2_hidden @ X13 @ (k2_tarski @ X13 @ X10))),
% 2.97/3.18      inference('simplify', [status(thm)], ['35'])).
% 2.97/3.18  thf('125', plain,
% 2.97/3.18      (![X0 : $i]:
% 2.97/3.18         ((r2_hidden @ sk_B @ (k1_tarski @ X0)) | ((sk_D_1) = (sk_B)))),
% 2.97/3.18      inference('sup+', [status(thm)], ['123', '124'])).
% 2.97/3.18  thf('126', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 2.97/3.18      inference('simplify', [status(thm)], ['30'])).
% 2.97/3.18  thf('127', plain, (![X0 : $i]: (((sk_D_1) = (sk_B)) | ((sk_B) = (X0)))),
% 2.97/3.18      inference('sup-', [status(thm)], ['125', '126'])).
% 2.97/3.18  thf('128', plain, (((sk_D_1) = (sk_B))),
% 2.97/3.18      inference('condensation', [status(thm)], ['127'])).
% 2.97/3.18  thf('129', plain,
% 2.97/3.18      (((k2_enumset1 @ sk_A @ sk_C @ sk_D_1 @ sk_D_1)
% 2.97/3.18         = (k2_tarski @ sk_C @ sk_D_1))),
% 2.97/3.18      inference('demod', [status(thm)], ['9', '128'])).
% 2.97/3.18  thf('130', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 2.97/3.18      inference('sup+', [status(thm)], ['34', '36'])).
% 2.97/3.18  thf('131', plain,
% 2.97/3.18      ((((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0))
% 2.97/3.18        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 2.97/3.18        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_D_1))
% 2.97/3.18        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k2_tarski @ sk_C @ sk_D_1)))),
% 2.97/3.18      inference('sup-', [status(thm)], ['11', '12'])).
% 2.97/3.18  thf('132', plain,
% 2.97/3.18      (![X10 : $i, X13 : $i, X14 : $i]:
% 2.97/3.18         (((X14) = (X10))
% 2.97/3.18          | ((X14) = (X13))
% 2.97/3.18          | ~ (r2_hidden @ X14 @ (k2_tarski @ X13 @ X10)))),
% 2.97/3.18      inference('simplify', [status(thm)], ['18'])).
% 2.97/3.18  thf('133', plain,
% 2.97/3.18      (![X0 : $i]:
% 2.97/3.18         (~ (r2_hidden @ X0 @ (k1_enumset1 @ sk_A @ sk_A @ sk_B))
% 2.97/3.18          | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_D_1))
% 2.97/3.18          | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 2.97/3.18          | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0))
% 2.97/3.18          | ((X0) = (sk_C))
% 2.97/3.18          | ((X0) = (sk_D_1)))),
% 2.97/3.18      inference('sup-', [status(thm)], ['131', '132'])).
% 2.97/3.18  thf('134', plain,
% 2.97/3.18      ((((sk_A) = (sk_D_1))
% 2.97/3.18        | ((sk_A) = (sk_C))
% 2.97/3.18        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0))
% 2.97/3.18        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 2.97/3.18        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_D_1)))),
% 2.97/3.18      inference('sup-', [status(thm)], ['130', '133'])).
% 2.97/3.18  thf('135', plain, (((sk_A) != (sk_C))),
% 2.97/3.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.97/3.18  thf('136', plain, (((sk_A) != (sk_D_1))),
% 2.97/3.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.97/3.18  thf('137', plain,
% 2.97/3.18      ((((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_xboole_0))
% 2.97/3.18        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 2.97/3.18        | ((k1_enumset1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_D_1)))),
% 2.97/3.18      inference('simplify_reflect-', [status(thm)], ['134', '135', '136'])).
% 2.97/3.18  thf('138', plain, (((sk_D_1) = (sk_B))),
% 2.97/3.18      inference('condensation', [status(thm)], ['127'])).
% 2.97/3.18  thf('139', plain, (((sk_D_1) = (sk_B))),
% 2.97/3.18      inference('condensation', [status(thm)], ['127'])).
% 2.97/3.18  thf('140', plain, (((sk_D_1) = (sk_B))),
% 2.97/3.18      inference('condensation', [status(thm)], ['127'])).
% 2.97/3.18  thf('141', plain,
% 2.97/3.18      ((((k1_enumset1 @ sk_A @ sk_A @ sk_D_1) = (k1_xboole_0))
% 2.97/3.18        | ((k1_enumset1 @ sk_A @ sk_A @ sk_D_1) = (k1_tarski @ sk_C))
% 2.97/3.18        | ((k1_enumset1 @ sk_A @ sk_A @ sk_D_1) = (k1_tarski @ sk_D_1)))),
% 2.97/3.18      inference('demod', [status(thm)], ['137', '138', '139', '140'])).
% 2.97/3.18  thf('142', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 2.97/3.18      inference('sup+', [status(thm)], ['34', '36'])).
% 2.97/3.18  thf('143', plain,
% 2.97/3.18      (((r2_hidden @ sk_A @ (k1_tarski @ sk_D_1))
% 2.97/3.18        | ((k1_enumset1 @ sk_A @ sk_A @ sk_D_1) = (k1_tarski @ sk_C))
% 2.97/3.18        | ((k1_enumset1 @ sk_A @ sk_A @ sk_D_1) = (k1_xboole_0)))),
% 2.97/3.18      inference('sup+', [status(thm)], ['141', '142'])).
% 2.97/3.18  thf('144', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 2.97/3.18      inference('simplify', [status(thm)], ['30'])).
% 2.97/3.18  thf('145', plain,
% 2.97/3.18      ((((k1_enumset1 @ sk_A @ sk_A @ sk_D_1) = (k1_xboole_0))
% 2.97/3.18        | ((k1_enumset1 @ sk_A @ sk_A @ sk_D_1) = (k1_tarski @ sk_C))
% 2.97/3.18        | ((sk_A) = (sk_D_1)))),
% 2.97/3.18      inference('sup-', [status(thm)], ['143', '144'])).
% 2.97/3.18  thf('146', plain, (((sk_A) != (sk_D_1))),
% 2.97/3.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.97/3.18  thf('147', plain,
% 2.97/3.18      ((((k1_enumset1 @ sk_A @ sk_A @ sk_D_1) = (k1_xboole_0))
% 2.97/3.18        | ((k1_enumset1 @ sk_A @ sk_A @ sk_D_1) = (k1_tarski @ sk_C)))),
% 2.97/3.18      inference('simplify_reflect-', [status(thm)], ['145', '146'])).
% 2.97/3.18  thf('148', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 2.97/3.18      inference('sup+', [status(thm)], ['24', '25'])).
% 2.97/3.18  thf('149', plain,
% 2.97/3.18      (((r2_hidden @ sk_D_1 @ (k1_tarski @ sk_C))
% 2.97/3.18        | ((k1_enumset1 @ sk_A @ sk_A @ sk_D_1) = (k1_xboole_0)))),
% 2.97/3.18      inference('sup+', [status(thm)], ['147', '148'])).
% 2.97/3.18  thf('150', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 2.97/3.18      inference('simplify', [status(thm)], ['30'])).
% 2.97/3.18  thf('151', plain,
% 2.97/3.18      ((((k1_enumset1 @ sk_A @ sk_A @ sk_D_1) = (k1_xboole_0))
% 2.97/3.18        | ((sk_D_1) = (sk_C)))),
% 2.97/3.18      inference('sup-', [status(thm)], ['149', '150'])).
% 2.97/3.18  thf('152', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 2.97/3.18      inference('sup+', [status(thm)], ['24', '25'])).
% 2.97/3.18  thf('153', plain,
% 2.97/3.18      (((r2_hidden @ sk_D_1 @ k1_xboole_0) | ((sk_D_1) = (sk_C)))),
% 2.97/3.18      inference('sup+', [status(thm)], ['151', '152'])).
% 2.97/3.18  thf('154', plain,
% 2.97/3.18      ((((k1_enumset1 @ sk_A @ sk_A @ sk_D_1) = (k1_xboole_0))
% 2.97/3.18        | ((sk_D_1) = (sk_C)))),
% 2.97/3.18      inference('sup-', [status(thm)], ['149', '150'])).
% 2.97/3.18  thf('155', plain,
% 2.97/3.18      (![X92 : $i, X93 : $i]:
% 2.97/3.18         ((k1_enumset1 @ X92 @ X92 @ X93) = (k2_tarski @ X92 @ X93))),
% 2.97/3.18      inference('cnf', [status(esa)], [t70_enumset1])).
% 2.97/3.18  thf('156', plain,
% 2.97/3.18      (![X119 : $i, X122 : $i]:
% 2.97/3.18         (r1_tarski @ (k1_tarski @ X119) @ (k2_tarski @ X119 @ X122))),
% 2.97/3.18      inference('simplify', [status(thm)], ['82'])).
% 2.97/3.18  thf('157', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         (r1_tarski @ (k1_tarski @ X1) @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 2.97/3.18      inference('sup+', [status(thm)], ['155', '156'])).
% 2.97/3.18  thf('158', plain,
% 2.97/3.18      (((r1_tarski @ (k1_tarski @ sk_A) @ k1_xboole_0) | ((sk_D_1) = (sk_C)))),
% 2.97/3.18      inference('sup+', [status(thm)], ['154', '157'])).
% 2.97/3.18  thf('159', plain,
% 2.97/3.18      (![X2 : $i, X3 : $i]:
% 2.97/3.18         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 2.97/3.18      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.97/3.18  thf('160', plain,
% 2.97/3.18      ((((sk_D_1) = (sk_C))
% 2.97/3.18        | ((k2_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0) = (k1_xboole_0)))),
% 2.97/3.18      inference('sup-', [status(thm)], ['158', '159'])).
% 2.97/3.18  thf('161', plain,
% 2.97/3.18      (![X0 : $i]:
% 2.97/3.18         ((k2_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0) = (k1_tarski @ X0))),
% 2.97/3.18      inference('demod', [status(thm)], ['61', '62'])).
% 2.97/3.18  thf('162', plain,
% 2.97/3.18      ((((sk_D_1) = (sk_C)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 2.97/3.18      inference('demod', [status(thm)], ['160', '161'])).
% 2.97/3.18  thf('163', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 2.97/3.18      inference('simplify', [status(thm)], ['30'])).
% 2.97/3.18  thf('164', plain,
% 2.97/3.18      (![X0 : $i]:
% 2.97/3.18         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 2.97/3.18          | ((sk_D_1) = (sk_C))
% 2.97/3.18          | ((X0) = (sk_A)))),
% 2.97/3.18      inference('sup-', [status(thm)], ['162', '163'])).
% 2.97/3.18  thf('165', plain,
% 2.97/3.18      ((((sk_D_1) = (sk_C)) | ((sk_D_1) = (sk_A)) | ((sk_D_1) = (sk_C)))),
% 2.97/3.18      inference('sup-', [status(thm)], ['153', '164'])).
% 2.97/3.18  thf('166', plain, ((((sk_D_1) = (sk_A)) | ((sk_D_1) = (sk_C)))),
% 2.97/3.18      inference('simplify', [status(thm)], ['165'])).
% 2.97/3.18  thf('167', plain, (((sk_A) != (sk_D_1))),
% 2.97/3.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.97/3.18  thf('168', plain, (((sk_D_1) = (sk_C))),
% 2.97/3.18      inference('simplify_reflect-', [status(thm)], ['166', '167'])).
% 2.97/3.18  thf('169', plain, (((sk_D_1) = (sk_C))),
% 2.97/3.18      inference('simplify_reflect-', [status(thm)], ['166', '167'])).
% 2.97/3.18  thf('170', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.97/3.18         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0)
% 2.97/3.18           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)))),
% 2.97/3.18      inference('sup+', [status(thm)], ['65', '66'])).
% 2.97/3.18  thf('171', plain,
% 2.97/3.18      (![X119 : $i, X122 : $i]:
% 2.97/3.18         (r1_tarski @ (k1_tarski @ X122) @ (k2_tarski @ X119 @ X122))),
% 2.97/3.18      inference('simplify', [status(thm)], ['44'])).
% 2.97/3.18  thf('172', plain,
% 2.97/3.18      (![X4 : $i, X5 : $i]:
% 2.97/3.18         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 2.97/3.18      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.97/3.18  thf('173', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         ((k3_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))
% 2.97/3.18           = (k1_tarski @ X0))),
% 2.97/3.18      inference('sup-', [status(thm)], ['171', '172'])).
% 2.97/3.18  thf('174', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         ((k4_xboole_0 @ X0 @ X1)
% 2.97/3.18           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.97/3.18      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.97/3.18  thf('175', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))
% 2.97/3.18           = (k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 2.97/3.18      inference('sup+', [status(thm)], ['173', '174'])).
% 2.97/3.18  thf('176', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ X7) = (k1_xboole_0))),
% 2.97/3.18      inference('cnf', [status(esa)], [t92_xboole_1])).
% 2.97/3.18  thf('177', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))
% 2.97/3.18           = (k1_xboole_0))),
% 2.97/3.18      inference('demod', [status(thm)], ['175', '176'])).
% 2.97/3.18  thf('178', plain,
% 2.97/3.18      (![X8 : $i, X9 : $i]:
% 2.97/3.18         ((k2_xboole_0 @ X8 @ X9)
% 2.97/3.18           = (k5_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8)))),
% 2.97/3.18      inference('cnf', [status(esa)], [t98_xboole_1])).
% 2.97/3.18  thf('179', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0))
% 2.97/3.18           = (k5_xboole_0 @ (k2_tarski @ X1 @ X0) @ k1_xboole_0))),
% 2.97/3.18      inference('sup+', [status(thm)], ['177', '178'])).
% 2.97/3.18  thf('180', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 2.97/3.18      inference('cnf', [status(esa)], [t5_boole])).
% 2.97/3.18  thf('181', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0))
% 2.97/3.18           = (k2_tarski @ X1 @ X0))),
% 2.97/3.18      inference('demod', [status(thm)], ['179', '180'])).
% 2.97/3.18  thf('182', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         ((k2_enumset1 @ X1 @ X0 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 2.97/3.18      inference('sup+', [status(thm)], ['170', '181'])).
% 2.97/3.18  thf('183', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 2.97/3.18      inference('demod', [status(thm)], ['118', '119'])).
% 2.97/3.18  thf('184', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_enumset1 @ X1 @ X0 @ X0 @ X0))),
% 2.97/3.18      inference('sup+', [status(thm)], ['182', '183'])).
% 2.97/3.18  thf('185', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         ((k1_enumset1 @ X1 @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 2.97/3.18      inference('demod', [status(thm)], ['95', '98'])).
% 2.97/3.18  thf('186', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 2.97/3.18      inference('demod', [status(thm)], ['118', '119'])).
% 2.97/3.18  thf('187', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         ((k1_enumset1 @ X0 @ X1 @ X1) = (k1_enumset1 @ X0 @ X1 @ X0))),
% 2.97/3.18      inference('sup+', [status(thm)], ['185', '186'])).
% 2.97/3.18  thf('188', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         ((k1_enumset1 @ X1 @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 2.97/3.18      inference('demod', [status(thm)], ['95', '98'])).
% 2.97/3.18  thf('189', plain,
% 2.97/3.18      (![X92 : $i, X93 : $i]:
% 2.97/3.18         ((k1_enumset1 @ X92 @ X92 @ X93) = (k2_tarski @ X92 @ X93))),
% 2.97/3.18      inference('cnf', [status(esa)], [t70_enumset1])).
% 2.97/3.18  thf('190', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         ((k1_enumset1 @ X0 @ X0 @ X1) = (k1_enumset1 @ X0 @ X1 @ X0))),
% 2.97/3.18      inference('sup+', [status(thm)], ['188', '189'])).
% 2.97/3.18  thf('191', plain, (((sk_D_1) = (sk_C))),
% 2.97/3.18      inference('simplify_reflect-', [status(thm)], ['166', '167'])).
% 2.97/3.18  thf('192', plain,
% 2.97/3.18      (![X91 : $i]: ((k2_tarski @ X91 @ X91) = (k1_tarski @ X91))),
% 2.97/3.18      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.97/3.18  thf('193', plain,
% 2.97/3.18      (((k1_enumset1 @ sk_A @ sk_A @ sk_C) = (k1_tarski @ sk_C))),
% 2.97/3.18      inference('demod', [status(thm)],
% 2.97/3.18                ['129', '168', '169', '184', '187', '190', '191', '192'])).
% 2.97/3.18  thf('194', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k1_enumset1 @ X1 @ X1 @ X0))),
% 2.97/3.18      inference('sup+', [status(thm)], ['34', '36'])).
% 2.97/3.18  thf('195', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_C))),
% 2.97/3.18      inference('sup+', [status(thm)], ['193', '194'])).
% 2.97/3.18  thf('196', plain,
% 2.97/3.18      (![X0 : $i, X1 : $i]:
% 2.97/3.18         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 2.97/3.18      inference('simplify', [status(thm)], ['30'])).
% 2.97/3.18  thf('197', plain, (((sk_A) = (sk_C))),
% 2.97/3.18      inference('sup-', [status(thm)], ['195', '196'])).
% 2.97/3.18  thf('198', plain, (((sk_A) != (sk_C))),
% 2.97/3.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.97/3.18  thf('199', plain, ($false),
% 2.97/3.18      inference('simplify_reflect-', [status(thm)], ['197', '198'])).
% 2.97/3.18  
% 2.97/3.18  % SZS output end Refutation
% 2.97/3.18  
% 2.97/3.19  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

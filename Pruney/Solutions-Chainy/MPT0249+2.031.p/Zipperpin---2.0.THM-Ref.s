%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KryMeNlO2Z

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:42 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 721 expanded)
%              Number of leaves         :   30 ( 229 expanded)
%              Depth                    :   22
%              Number of atoms          :  672 (5741 expanded)
%              Number of equality atoms :   95 ( 920 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X46 @ X47 ) )
      = ( k2_xboole_0 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('2',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('3',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('4',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('6',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X46 @ X47 ) )
      = ( k2_xboole_0 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('7',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k3_tarski @ ( k2_tarski @ X21 @ X22 ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['4','7'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('10',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X20: $i] :
      ( ( k3_xboole_0 @ X20 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('14',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ k1_xboole_0 )
      = X25 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( sk_B_1
    = ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('17',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('18',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','19'])).

thf('21',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['20','21'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('23',plain,(
    ! [X28: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X31 @ X30 )
      | ( X31 = X28 )
      | ( X30
       != ( k1_tarski @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('24',plain,(
    ! [X28: $i,X31: $i] :
      ( ( X31 = X28 )
      | ~ ( r2_hidden @ X31 @ ( k1_tarski @ X28 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( sk_B @ sk_B_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('27',plain,(
    ! [X43: $i,X45: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X43 ) @ X45 )
      | ~ ( r2_hidden @ X43 @ X45 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X13: $i,X15: $i] :
      ( ( X13 = X15 )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    | ( sk_B_1
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('33',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ X26 @ ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('34',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X46 @ X47 ) )
      = ( k2_xboole_0 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('35',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ X26 @ ( k3_tarski @ ( k2_tarski @ X26 @ X27 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf('37',plain,
    ( ( sk_B @ sk_B_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['22','24'])).

thf('38',plain,
    ( ( sk_B_1
      = ( k1_tarski @ sk_A ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','36','37'])).

thf('39',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['38','39'])).

thf('41',plain,
    ( sk_B_1
    = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['2','40'])).

thf('42',plain,
    ( sk_B_1
    = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['2','40'])).

thf('43',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X46 @ X47 ) )
      = ( k2_xboole_0 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k3_tarski @ ( k2_tarski @ X3 @ X1 ) ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['43','47'])).

thf('49',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C_1 ) @ sk_B_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','48'])).

thf('50',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    r2_hidden @ ( sk_B @ sk_C_1 ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['49','50'])).

thf('52',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['38','39'])).

thf('53',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['38','39'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('54',plain,(
    ! [X33: $i] :
      ( ( k2_tarski @ X33 @ X33 )
      = ( k1_tarski @ X33 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('55',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ( X13 != X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('56',plain,(
    ! [X14: $i] :
      ( r1_tarski @ X14 @ X14 ) ),
    inference(simplify,[status(thm)],['55'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('57',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_xboole_0 @ X19 @ X18 )
        = X18 )
      | ~ ( r1_tarski @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('58',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X46 @ X47 ) )
      = ( k2_xboole_0 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('59',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_tarski @ ( k2_tarski @ X19 @ X18 ) )
        = X18 )
      | ~ ( r1_tarski @ X19 @ X18 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['54','60'])).

thf('62',plain,
    ( ( k3_tarski @ sk_B_1 )
    = sk_A ),
    inference('sup+',[status(thm)],['53','61'])).

thf('63',plain,
    ( sk_B_1
    = ( k1_tarski @ ( k3_tarski @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['52','62'])).

thf('64',plain,(
    ! [X28: $i,X31: $i] :
      ( ( X31 = X28 )
      | ~ ( r2_hidden @ X31 @ ( k1_tarski @ X28 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( X0
        = ( k3_tarski @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( sk_B @ sk_C_1 )
    = ( k3_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['51','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('68',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_tarski @ ( k2_tarski @ X19 @ X18 ) )
        = X18 )
      | ~ ( r1_tarski @ X19 @ X18 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ ( k3_tarski @ sk_B_1 ) ) @ sk_C_1 ) )
      = sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['66','69'])).

thf('71',plain,
    ( sk_B_1
    = ( k1_tarski @ ( k3_tarski @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['52','62'])).

thf('72',plain,
    ( ( ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
      = sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
    = sk_C_1 ),
    inference('simplify_reflect-',[status(thm)],['72','73'])).

thf('75',plain,(
    sk_B_1 = sk_C_1 ),
    inference('sup+',[status(thm)],['41','74'])).

thf('76',plain,(
    sk_B_1 != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['75','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KryMeNlO2Z
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:06:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.47/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.66  % Solved by: fo/fo7.sh
% 0.47/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.66  % done 444 iterations in 0.201s
% 0.47/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.66  % SZS output start Refutation
% 0.47/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.47/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.66  thf(sk_B_type, type, sk_B: $i > $i).
% 0.47/0.66  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.47/0.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.47/0.66  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.47/0.66  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.47/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.66  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.47/0.66  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.47/0.66  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.47/0.66  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.47/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.66  thf(t44_zfmisc_1, conjecture,
% 0.47/0.66    (![A:$i,B:$i,C:$i]:
% 0.47/0.66     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.47/0.66          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.47/0.66          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.47/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.66    (~( ![A:$i,B:$i,C:$i]:
% 0.47/0.66        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.47/0.66             ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.47/0.66             ( ( C ) != ( k1_xboole_0 ) ) ) ) )),
% 0.47/0.66    inference('cnf.neg', [status(esa)], [t44_zfmisc_1])).
% 0.47/0.66  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(l51_zfmisc_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.47/0.66  thf('1', plain,
% 0.47/0.66      (![X46 : $i, X47 : $i]:
% 0.47/0.66         ((k3_tarski @ (k2_tarski @ X46 @ X47)) = (k2_xboole_0 @ X46 @ X47))),
% 0.47/0.66      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.47/0.66  thf('2', plain,
% 0.47/0.66      (((k1_tarski @ sk_A) = (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_1)))),
% 0.47/0.66      inference('demod', [status(thm)], ['0', '1'])).
% 0.47/0.66  thf(t7_xboole_0, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.47/0.66          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.47/0.66  thf('3', plain,
% 0.47/0.66      (![X12 : $i]:
% 0.47/0.66         (((X12) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 0.47/0.66      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.47/0.66  thf('4', plain,
% 0.47/0.66      (((k1_tarski @ sk_A) = (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_1)))),
% 0.47/0.66      inference('demod', [status(thm)], ['0', '1'])).
% 0.47/0.66  thf(t46_xboole_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.47/0.66  thf('5', plain,
% 0.47/0.66      (![X21 : $i, X22 : $i]:
% 0.47/0.66         ((k4_xboole_0 @ X21 @ (k2_xboole_0 @ X21 @ X22)) = (k1_xboole_0))),
% 0.47/0.66      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.47/0.66  thf('6', plain,
% 0.47/0.66      (![X46 : $i, X47 : $i]:
% 0.47/0.66         ((k3_tarski @ (k2_tarski @ X46 @ X47)) = (k2_xboole_0 @ X46 @ X47))),
% 0.47/0.66      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.47/0.66  thf('7', plain,
% 0.47/0.66      (![X21 : $i, X22 : $i]:
% 0.47/0.66         ((k4_xboole_0 @ X21 @ (k3_tarski @ (k2_tarski @ X21 @ X22)))
% 0.47/0.66           = (k1_xboole_0))),
% 0.47/0.66      inference('demod', [status(thm)], ['5', '6'])).
% 0.47/0.66  thf('8', plain,
% 0.47/0.66      (((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.47/0.66      inference('sup+', [status(thm)], ['4', '7'])).
% 0.47/0.66  thf(t48_xboole_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.47/0.66  thf('9', plain,
% 0.47/0.66      (![X23 : $i, X24 : $i]:
% 0.47/0.66         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 0.47/0.66           = (k3_xboole_0 @ X23 @ X24))),
% 0.47/0.66      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.47/0.66  thf('10', plain,
% 0.47/0.66      (((k4_xboole_0 @ sk_B_1 @ k1_xboole_0)
% 0.47/0.66         = (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.47/0.66      inference('sup+', [status(thm)], ['8', '9'])).
% 0.47/0.66  thf(t2_boole, axiom,
% 0.47/0.66    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.47/0.66  thf('11', plain,
% 0.47/0.66      (![X20 : $i]: ((k3_xboole_0 @ X20 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.66      inference('cnf', [status(esa)], [t2_boole])).
% 0.47/0.66  thf(t100_xboole_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.47/0.66  thf('12', plain,
% 0.47/0.66      (![X16 : $i, X17 : $i]:
% 0.47/0.66         ((k4_xboole_0 @ X16 @ X17)
% 0.47/0.66           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 0.47/0.66      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.47/0.66  thf('13', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.47/0.66      inference('sup+', [status(thm)], ['11', '12'])).
% 0.47/0.66  thf(t5_boole, axiom,
% 0.47/0.66    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.47/0.66  thf('14', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ k1_xboole_0) = (X25))),
% 0.47/0.66      inference('cnf', [status(esa)], [t5_boole])).
% 0.47/0.66  thf('15', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.47/0.66      inference('demod', [status(thm)], ['13', '14'])).
% 0.47/0.66  thf('16', plain, (((sk_B_1) = (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.47/0.66      inference('demod', [status(thm)], ['10', '15'])).
% 0.47/0.66  thf(d4_xboole_0, axiom,
% 0.47/0.66    (![A:$i,B:$i,C:$i]:
% 0.47/0.66     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.47/0.66       ( ![D:$i]:
% 0.47/0.66         ( ( r2_hidden @ D @ C ) <=>
% 0.47/0.66           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.47/0.66  thf('17', plain,
% 0.47/0.66      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.47/0.66         (~ (r2_hidden @ X10 @ X9)
% 0.47/0.66          | (r2_hidden @ X10 @ X8)
% 0.47/0.66          | ((X9) != (k3_xboole_0 @ X7 @ X8)))),
% 0.47/0.66      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.47/0.66  thf('18', plain,
% 0.47/0.66      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.47/0.66         ((r2_hidden @ X10 @ X8)
% 0.47/0.66          | ~ (r2_hidden @ X10 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.47/0.66      inference('simplify', [status(thm)], ['17'])).
% 0.47/0.66  thf('19', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (r2_hidden @ X0 @ sk_B_1) | (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['16', '18'])).
% 0.47/0.66  thf('20', plain,
% 0.47/0.66      ((((sk_B_1) = (k1_xboole_0))
% 0.47/0.66        | (r2_hidden @ (sk_B @ sk_B_1) @ (k1_tarski @ sk_A)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['3', '19'])).
% 0.47/0.66  thf('21', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('22', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (k1_tarski @ sk_A))),
% 0.47/0.66      inference('simplify_reflect-', [status(thm)], ['20', '21'])).
% 0.47/0.66  thf(d1_tarski, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.47/0.66       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.47/0.66  thf('23', plain,
% 0.47/0.66      (![X28 : $i, X30 : $i, X31 : $i]:
% 0.47/0.66         (~ (r2_hidden @ X31 @ X30)
% 0.47/0.66          | ((X31) = (X28))
% 0.47/0.66          | ((X30) != (k1_tarski @ X28)))),
% 0.47/0.66      inference('cnf', [status(esa)], [d1_tarski])).
% 0.47/0.66  thf('24', plain,
% 0.47/0.66      (![X28 : $i, X31 : $i]:
% 0.47/0.66         (((X31) = (X28)) | ~ (r2_hidden @ X31 @ (k1_tarski @ X28)))),
% 0.47/0.66      inference('simplify', [status(thm)], ['23'])).
% 0.47/0.66  thf('25', plain, (((sk_B @ sk_B_1) = (sk_A))),
% 0.47/0.66      inference('sup-', [status(thm)], ['22', '24'])).
% 0.47/0.66  thf('26', plain,
% 0.47/0.66      (![X12 : $i]:
% 0.47/0.66         (((X12) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 0.47/0.66      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.47/0.66  thf(l1_zfmisc_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.47/0.66  thf('27', plain,
% 0.47/0.66      (![X43 : $i, X45 : $i]:
% 0.47/0.66         ((r1_tarski @ (k1_tarski @ X43) @ X45) | ~ (r2_hidden @ X43 @ X45))),
% 0.47/0.66      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.47/0.66  thf('28', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (((X0) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['26', '27'])).
% 0.47/0.66  thf(d10_xboole_0, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.47/0.66  thf('29', plain,
% 0.47/0.66      (![X13 : $i, X15 : $i]:
% 0.47/0.66         (((X13) = (X15))
% 0.47/0.66          | ~ (r1_tarski @ X15 @ X13)
% 0.47/0.66          | ~ (r1_tarski @ X13 @ X15))),
% 0.47/0.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.66  thf('30', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (((X0) = (k1_xboole_0))
% 0.47/0.66          | ~ (r1_tarski @ X0 @ (k1_tarski @ (sk_B @ X0)))
% 0.47/0.66          | ((X0) = (k1_tarski @ (sk_B @ X0))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['28', '29'])).
% 0.47/0.66  thf('31', plain,
% 0.47/0.66      ((~ (r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.47/0.66        | ((sk_B_1) = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.47/0.66        | ((sk_B_1) = (k1_xboole_0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['25', '30'])).
% 0.47/0.66  thf('32', plain,
% 0.47/0.66      (((k1_tarski @ sk_A) = (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_1)))),
% 0.47/0.66      inference('demod', [status(thm)], ['0', '1'])).
% 0.47/0.66  thf(t7_xboole_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.47/0.66  thf('33', plain,
% 0.47/0.66      (![X26 : $i, X27 : $i]: (r1_tarski @ X26 @ (k2_xboole_0 @ X26 @ X27))),
% 0.47/0.66      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.47/0.66  thf('34', plain,
% 0.47/0.66      (![X46 : $i, X47 : $i]:
% 0.47/0.66         ((k3_tarski @ (k2_tarski @ X46 @ X47)) = (k2_xboole_0 @ X46 @ X47))),
% 0.47/0.66      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.47/0.66  thf('35', plain,
% 0.47/0.66      (![X26 : $i, X27 : $i]:
% 0.47/0.66         (r1_tarski @ X26 @ (k3_tarski @ (k2_tarski @ X26 @ X27)))),
% 0.47/0.66      inference('demod', [status(thm)], ['33', '34'])).
% 0.47/0.66  thf('36', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.47/0.66      inference('sup+', [status(thm)], ['32', '35'])).
% 0.47/0.66  thf('37', plain, (((sk_B @ sk_B_1) = (sk_A))),
% 0.47/0.66      inference('sup-', [status(thm)], ['22', '24'])).
% 0.47/0.66  thf('38', plain,
% 0.47/0.66      ((((sk_B_1) = (k1_tarski @ sk_A)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.47/0.66      inference('demod', [status(thm)], ['31', '36', '37'])).
% 0.47/0.66  thf('39', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('40', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 0.47/0.66      inference('simplify_reflect-', [status(thm)], ['38', '39'])).
% 0.47/0.66  thf('41', plain, (((sk_B_1) = (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_1)))),
% 0.47/0.66      inference('demod', [status(thm)], ['2', '40'])).
% 0.47/0.66  thf('42', plain, (((sk_B_1) = (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_1)))),
% 0.47/0.66      inference('demod', [status(thm)], ['2', '40'])).
% 0.47/0.66  thf('43', plain,
% 0.47/0.66      (![X12 : $i]:
% 0.47/0.66         (((X12) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 0.47/0.66      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.47/0.66  thf(d3_xboole_0, axiom,
% 0.47/0.66    (![A:$i,B:$i,C:$i]:
% 0.47/0.66     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.47/0.66       ( ![D:$i]:
% 0.47/0.66         ( ( r2_hidden @ D @ C ) <=>
% 0.47/0.66           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.47/0.66  thf('44', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.47/0.66         (~ (r2_hidden @ X0 @ X1)
% 0.47/0.66          | (r2_hidden @ X0 @ X2)
% 0.47/0.66          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.47/0.66      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.47/0.66  thf('45', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.47/0.66         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 0.47/0.66      inference('simplify', [status(thm)], ['44'])).
% 0.47/0.66  thf('46', plain,
% 0.47/0.66      (![X46 : $i, X47 : $i]:
% 0.47/0.66         ((k3_tarski @ (k2_tarski @ X46 @ X47)) = (k2_xboole_0 @ X46 @ X47))),
% 0.47/0.66      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.47/0.66  thf('47', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.47/0.66         ((r2_hidden @ X0 @ (k3_tarski @ (k2_tarski @ X3 @ X1)))
% 0.47/0.66          | ~ (r2_hidden @ X0 @ X1))),
% 0.47/0.66      inference('demod', [status(thm)], ['45', '46'])).
% 0.47/0.66  thf('48', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (((X0) = (k1_xboole_0))
% 0.47/0.66          | (r2_hidden @ (sk_B @ X0) @ (k3_tarski @ (k2_tarski @ X1 @ X0))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['43', '47'])).
% 0.47/0.66  thf('49', plain,
% 0.47/0.66      (((r2_hidden @ (sk_B @ sk_C_1) @ sk_B_1) | ((sk_C_1) = (k1_xboole_0)))),
% 0.47/0.66      inference('sup+', [status(thm)], ['42', '48'])).
% 0.47/0.66  thf('50', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('51', plain, ((r2_hidden @ (sk_B @ sk_C_1) @ sk_B_1)),
% 0.47/0.66      inference('simplify_reflect-', [status(thm)], ['49', '50'])).
% 0.47/0.66  thf('52', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 0.47/0.66      inference('simplify_reflect-', [status(thm)], ['38', '39'])).
% 0.47/0.66  thf('53', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 0.47/0.66      inference('simplify_reflect-', [status(thm)], ['38', '39'])).
% 0.47/0.66  thf(t69_enumset1, axiom,
% 0.47/0.66    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.47/0.66  thf('54', plain,
% 0.47/0.66      (![X33 : $i]: ((k2_tarski @ X33 @ X33) = (k1_tarski @ X33))),
% 0.47/0.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.47/0.66  thf('55', plain,
% 0.47/0.66      (![X13 : $i, X14 : $i]: ((r1_tarski @ X13 @ X14) | ((X13) != (X14)))),
% 0.47/0.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.66  thf('56', plain, (![X14 : $i]: (r1_tarski @ X14 @ X14)),
% 0.47/0.66      inference('simplify', [status(thm)], ['55'])).
% 0.47/0.66  thf(t12_xboole_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.47/0.66  thf('57', plain,
% 0.47/0.66      (![X18 : $i, X19 : $i]:
% 0.47/0.66         (((k2_xboole_0 @ X19 @ X18) = (X18)) | ~ (r1_tarski @ X19 @ X18))),
% 0.47/0.66      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.47/0.66  thf('58', plain,
% 0.47/0.66      (![X46 : $i, X47 : $i]:
% 0.47/0.66         ((k3_tarski @ (k2_tarski @ X46 @ X47)) = (k2_xboole_0 @ X46 @ X47))),
% 0.47/0.66      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.47/0.66  thf('59', plain,
% 0.47/0.66      (![X18 : $i, X19 : $i]:
% 0.47/0.66         (((k3_tarski @ (k2_tarski @ X19 @ X18)) = (X18))
% 0.47/0.66          | ~ (r1_tarski @ X19 @ X18))),
% 0.47/0.66      inference('demod', [status(thm)], ['57', '58'])).
% 0.47/0.66  thf('60', plain, (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['56', '59'])).
% 0.47/0.66  thf('61', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.47/0.66      inference('sup+', [status(thm)], ['54', '60'])).
% 0.47/0.66  thf('62', plain, (((k3_tarski @ sk_B_1) = (sk_A))),
% 0.47/0.66      inference('sup+', [status(thm)], ['53', '61'])).
% 0.47/0.66  thf('63', plain, (((sk_B_1) = (k1_tarski @ (k3_tarski @ sk_B_1)))),
% 0.47/0.66      inference('demod', [status(thm)], ['52', '62'])).
% 0.47/0.66  thf('64', plain,
% 0.47/0.66      (![X28 : $i, X31 : $i]:
% 0.47/0.66         (((X31) = (X28)) | ~ (r2_hidden @ X31 @ (k1_tarski @ X28)))),
% 0.47/0.66      inference('simplify', [status(thm)], ['23'])).
% 0.47/0.66  thf('65', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (r2_hidden @ X0 @ sk_B_1) | ((X0) = (k3_tarski @ sk_B_1)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['63', '64'])).
% 0.47/0.66  thf('66', plain, (((sk_B @ sk_C_1) = (k3_tarski @ sk_B_1))),
% 0.47/0.66      inference('sup-', [status(thm)], ['51', '65'])).
% 0.47/0.66  thf('67', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (((X0) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['26', '27'])).
% 0.47/0.66  thf('68', plain,
% 0.47/0.66      (![X18 : $i, X19 : $i]:
% 0.47/0.66         (((k3_tarski @ (k2_tarski @ X19 @ X18)) = (X18))
% 0.47/0.66          | ~ (r1_tarski @ X19 @ X18))),
% 0.47/0.66      inference('demod', [status(thm)], ['57', '58'])).
% 0.47/0.66  thf('69', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (((X0) = (k1_xboole_0))
% 0.47/0.66          | ((k3_tarski @ (k2_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0)) = (X0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['67', '68'])).
% 0.47/0.66  thf('70', plain,
% 0.47/0.66      ((((k3_tarski @ (k2_tarski @ (k1_tarski @ (k3_tarski @ sk_B_1)) @ sk_C_1))
% 0.47/0.66          = (sk_C_1))
% 0.47/0.66        | ((sk_C_1) = (k1_xboole_0)))),
% 0.47/0.66      inference('sup+', [status(thm)], ['66', '69'])).
% 0.47/0.66  thf('71', plain, (((sk_B_1) = (k1_tarski @ (k3_tarski @ sk_B_1)))),
% 0.47/0.66      inference('demod', [status(thm)], ['52', '62'])).
% 0.47/0.66  thf('72', plain,
% 0.47/0.66      ((((k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_1)) = (sk_C_1))
% 0.47/0.66        | ((sk_C_1) = (k1_xboole_0)))),
% 0.47/0.66      inference('demod', [status(thm)], ['70', '71'])).
% 0.47/0.66  thf('73', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('74', plain, (((k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_1)) = (sk_C_1))),
% 0.47/0.66      inference('simplify_reflect-', [status(thm)], ['72', '73'])).
% 0.47/0.66  thf('75', plain, (((sk_B_1) = (sk_C_1))),
% 0.47/0.66      inference('sup+', [status(thm)], ['41', '74'])).
% 0.47/0.66  thf('76', plain, (((sk_B_1) != (sk_C_1))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('77', plain, ($false),
% 0.47/0.66      inference('simplify_reflect-', [status(thm)], ['75', '76'])).
% 0.47/0.66  
% 0.47/0.66  % SZS output end Refutation
% 0.47/0.66  
% 0.47/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

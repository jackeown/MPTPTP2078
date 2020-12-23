%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EfQQf3k20W

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:40 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  113 (1086 expanded)
%              Number of leaves         :   30 ( 341 expanded)
%              Depth                    :   22
%              Number of atoms          :  687 (8735 expanded)
%              Number of equality atoms :   93 (1399 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

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

thf('1',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('3',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('5',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('11',plain,(
    ! [X24: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X27 @ X26 )
      | ( X27 = X24 )
      | ( X26
       != ( k1_tarski @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('12',plain,(
    ! [X24: $i,X27: $i] :
      ( ( X27 = X24 )
      | ~ ( r2_hidden @ X27 @ ( k1_tarski @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( sk_B @ sk_B_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('15',plain,(
    ! [X57: $i,X59: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X57 ) @ X59 )
      | ~ ( r2_hidden @ X57 @ X59 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('17',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k2_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','18'])).

thf('20',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X9: $i,X11: $i] :
      ( ( X9 = X11 )
      | ~ ( r1_tarski @ X11 @ X9 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    | ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('27',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

thf('28',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['1','28'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('30',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('31',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('32',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_2 )
    = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ sk_C_2 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('35',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_2 )
    = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('36',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('37',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('39',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('40',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('42',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('43',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','46'])).

thf('48',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_2 )
    = sk_C_2 ),
    inference(demod,[status(thm)],['35','47'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('49',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('50',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_2 )
      | ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_C_2 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','52'])).

thf('54',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    r2_hidden @ ( sk_B @ sk_C_2 ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['53','54'])).

thf('56',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('57',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('58',plain,(
    ! [X29: $i] :
      ( ( k2_tarski @ X29 @ X29 )
      = ( k1_tarski @ X29 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('59',plain,(
    ! [X60: $i,X61: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X60 @ X61 ) )
      = ( k2_xboole_0 @ X60 @ X61 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k3_tarski @ sk_B_1 )
    = sk_A ),
    inference('sup+',[status(thm)],['57','62'])).

thf('64',plain,
    ( sk_B_1
    = ( k1_tarski @ ( k3_tarski @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['56','63'])).

thf('65',plain,(
    ! [X24: $i,X27: $i] :
      ( ( X27 = X24 )
      | ~ ( r2_hidden @ X27 @ ( k1_tarski @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( X0
        = ( k3_tarski @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( sk_B @ sk_C_2 )
    = ( k3_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['55','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('69',plain,(
    ! [X9: $i,X11: $i] :
      ( ( X9 = X11 )
      | ~ ( r1_tarski @ X11 @ X9 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ~ ( r1_tarski @ sk_C_2 @ ( k1_tarski @ ( k3_tarski @ sk_B_1 ) ) )
    | ( sk_C_2
      = ( k1_tarski @ ( sk_B @ sk_C_2 ) ) )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,
    ( sk_B_1
    = ( k1_tarski @ ( k3_tarski @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['56','63'])).

thf('73',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_2 )
    = sk_C_2 ),
    inference(demod,[status(thm)],['35','47'])).

thf('74',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('75',plain,(
    r1_tarski @ sk_C_2 @ sk_B_1 ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( sk_B @ sk_C_2 )
    = ( k3_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['55','66'])).

thf('77',plain,
    ( sk_B_1
    = ( k1_tarski @ ( k3_tarski @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['56','63'])).

thf('78',plain,
    ( ( sk_C_2 = sk_B_1 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','72','75','76','77'])).

thf('79',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    sk_B_1 != sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['78','79','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EfQQf3k20W
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:24:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.53  % Solved by: fo/fo7.sh
% 0.35/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.53  % done 191 iterations in 0.082s
% 0.35/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.53  % SZS output start Refutation
% 0.35/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.35/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.53  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.35/0.53  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.35/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.35/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.35/0.53  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.35/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.35/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.35/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.53  thf(t7_xboole_0, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.35/0.53          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.35/0.53  thf('0', plain,
% 0.35/0.53      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.35/0.53      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.35/0.53  thf(t44_zfmisc_1, conjecture,
% 0.35/0.53    (![A:$i,B:$i,C:$i]:
% 0.35/0.53     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.35/0.53          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.35/0.53          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.35/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.35/0.53        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.35/0.53             ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.35/0.53             ( ( C ) != ( k1_xboole_0 ) ) ) ) )),
% 0.35/0.53    inference('cnf.neg', [status(esa)], [t44_zfmisc_1])).
% 0.35/0.53  thf('1', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('2', plain,
% 0.35/0.53      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.35/0.53      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.35/0.53  thf('3', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(t7_xboole_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.35/0.53  thf('4', plain,
% 0.35/0.53      (![X16 : $i, X17 : $i]: (r1_tarski @ X16 @ (k2_xboole_0 @ X16 @ X17))),
% 0.35/0.53      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.35/0.53  thf('5', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.35/0.53      inference('sup+', [status(thm)], ['3', '4'])).
% 0.35/0.53  thf(d3_tarski, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( r1_tarski @ A @ B ) <=>
% 0.35/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.35/0.53  thf('6', plain,
% 0.35/0.53      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.35/0.53         (~ (r2_hidden @ X2 @ X3)
% 0.35/0.53          | (r2_hidden @ X2 @ X4)
% 0.35/0.53          | ~ (r1_tarski @ X3 @ X4))),
% 0.35/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.35/0.53  thf('7', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((r2_hidden @ X0 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.35/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.35/0.53  thf('8', plain,
% 0.35/0.53      ((((sk_B_1) = (k1_xboole_0))
% 0.35/0.53        | (r2_hidden @ (sk_B @ sk_B_1) @ (k1_tarski @ sk_A)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['2', '7'])).
% 0.35/0.53  thf('9', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('10', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (k1_tarski @ sk_A))),
% 0.35/0.53      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.35/0.53  thf(d1_tarski, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.35/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.35/0.53  thf('11', plain,
% 0.35/0.53      (![X24 : $i, X26 : $i, X27 : $i]:
% 0.35/0.53         (~ (r2_hidden @ X27 @ X26)
% 0.35/0.53          | ((X27) = (X24))
% 0.35/0.53          | ((X26) != (k1_tarski @ X24)))),
% 0.35/0.53      inference('cnf', [status(esa)], [d1_tarski])).
% 0.35/0.53  thf('12', plain,
% 0.35/0.53      (![X24 : $i, X27 : $i]:
% 0.35/0.53         (((X27) = (X24)) | ~ (r2_hidden @ X27 @ (k1_tarski @ X24)))),
% 0.35/0.53      inference('simplify', [status(thm)], ['11'])).
% 0.35/0.53  thf('13', plain, (((sk_B @ sk_B_1) = (sk_A))),
% 0.35/0.53      inference('sup-', [status(thm)], ['10', '12'])).
% 0.35/0.53  thf('14', plain,
% 0.35/0.53      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.35/0.53      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.35/0.53  thf(l1_zfmisc_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.35/0.53  thf('15', plain,
% 0.35/0.53      (![X57 : $i, X59 : $i]:
% 0.35/0.53         ((r1_tarski @ (k1_tarski @ X57) @ X59) | ~ (r2_hidden @ X57 @ X59))),
% 0.35/0.53      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.35/0.53  thf('16', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (((X0) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.35/0.53      inference('sup-', [status(thm)], ['14', '15'])).
% 0.35/0.53  thf(t12_xboole_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.35/0.53  thf('17', plain,
% 0.35/0.53      (![X12 : $i, X13 : $i]:
% 0.35/0.53         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 0.35/0.53      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.35/0.53  thf('18', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (((X0) = (k1_xboole_0))
% 0.35/0.53          | ((k2_xboole_0 @ (k1_tarski @ (sk_B @ X0)) @ X0) = (X0)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.35/0.53  thf('19', plain,
% 0.35/0.53      ((((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (sk_B_1))
% 0.35/0.53        | ((sk_B_1) = (k1_xboole_0)))),
% 0.35/0.53      inference('sup+', [status(thm)], ['13', '18'])).
% 0.35/0.53  thf('20', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('21', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (sk_B_1))),
% 0.35/0.53      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.35/0.53  thf('22', plain,
% 0.35/0.53      (![X16 : $i, X17 : $i]: (r1_tarski @ X16 @ (k2_xboole_0 @ X16 @ X17))),
% 0.35/0.53      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.35/0.53  thf(d10_xboole_0, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.35/0.53  thf('23', plain,
% 0.35/0.53      (![X9 : $i, X11 : $i]:
% 0.35/0.53         (((X9) = (X11)) | ~ (r1_tarski @ X11 @ X9) | ~ (r1_tarski @ X9 @ X11))),
% 0.35/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.35/0.53  thf('24', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.35/0.53          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['22', '23'])).
% 0.35/0.53  thf('25', plain,
% 0.35/0.53      ((~ (r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.35/0.53        | ((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['21', '24'])).
% 0.35/0.53  thf('26', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.35/0.53      inference('sup+', [status(thm)], ['3', '4'])).
% 0.35/0.53  thf('27', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (sk_B_1))),
% 0.35/0.53      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.35/0.53  thf('28', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 0.35/0.53      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.35/0.53  thf('29', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.35/0.53      inference('demod', [status(thm)], ['1', '28'])).
% 0.35/0.53  thf(t95_xboole_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( k3_xboole_0 @ A @ B ) =
% 0.35/0.53       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.35/0.53  thf('30', plain,
% 0.35/0.53      (![X22 : $i, X23 : $i]:
% 0.35/0.53         ((k3_xboole_0 @ X22 @ X23)
% 0.35/0.53           = (k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ 
% 0.35/0.53              (k2_xboole_0 @ X22 @ X23)))),
% 0.35/0.53      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.35/0.53  thf(t91_xboole_1, axiom,
% 0.35/0.53    (![A:$i,B:$i,C:$i]:
% 0.35/0.53     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.35/0.53       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.35/0.53  thf('31', plain,
% 0.35/0.53      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.35/0.53         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 0.35/0.53           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 0.35/0.53      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.35/0.53  thf('32', plain,
% 0.35/0.53      (![X22 : $i, X23 : $i]:
% 0.35/0.53         ((k3_xboole_0 @ X22 @ X23)
% 0.35/0.53           = (k5_xboole_0 @ X22 @ 
% 0.35/0.53              (k5_xboole_0 @ X23 @ (k2_xboole_0 @ X22 @ X23))))),
% 0.35/0.53      inference('demod', [status(thm)], ['30', '31'])).
% 0.35/0.53  thf('33', plain,
% 0.35/0.53      (((k3_xboole_0 @ sk_B_1 @ sk_C_2)
% 0.35/0.53         = (k5_xboole_0 @ sk_B_1 @ (k5_xboole_0 @ sk_C_2 @ sk_B_1)))),
% 0.35/0.53      inference('sup+', [status(thm)], ['29', '32'])).
% 0.35/0.53  thf(commutativity_k5_xboole_0, axiom,
% 0.35/0.53    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.35/0.53  thf('34', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.35/0.53      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.35/0.53  thf('35', plain,
% 0.35/0.53      (((k3_xboole_0 @ sk_B_1 @ sk_C_2)
% 0.35/0.53         = (k5_xboole_0 @ sk_B_1 @ (k5_xboole_0 @ sk_B_1 @ sk_C_2)))),
% 0.35/0.53      inference('demod', [status(thm)], ['33', '34'])).
% 0.35/0.53  thf(t92_xboole_1, axiom,
% 0.35/0.53    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.35/0.53  thf('36', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ X21) = (k1_xboole_0))),
% 0.35/0.53      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.35/0.53  thf('37', plain,
% 0.35/0.53      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.35/0.53         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 0.35/0.53           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 0.35/0.53      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.35/0.53  thf('38', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.35/0.53           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.35/0.53      inference('sup+', [status(thm)], ['36', '37'])).
% 0.35/0.53  thf(idempotence_k2_xboole_0, axiom,
% 0.35/0.53    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.35/0.53  thf('39', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ X6) = (X6))),
% 0.35/0.53      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.37/0.54  thf('40', plain,
% 0.37/0.54      (![X22 : $i, X23 : $i]:
% 0.37/0.54         ((k3_xboole_0 @ X22 @ X23)
% 0.37/0.54           = (k5_xboole_0 @ X22 @ 
% 0.37/0.54              (k5_xboole_0 @ X23 @ (k2_xboole_0 @ X22 @ X23))))),
% 0.37/0.54      inference('demod', [status(thm)], ['30', '31'])).
% 0.37/0.54  thf('41', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         ((k3_xboole_0 @ X0 @ X0)
% 0.37/0.54           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.37/0.54      inference('sup+', [status(thm)], ['39', '40'])).
% 0.37/0.54  thf(idempotence_k3_xboole_0, axiom,
% 0.37/0.54    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.37/0.54  thf('42', plain, (![X7 : $i]: ((k3_xboole_0 @ X7 @ X7) = (X7))),
% 0.37/0.54      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.37/0.54  thf('43', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ X21) = (k1_xboole_0))),
% 0.37/0.54      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.37/0.54  thf('44', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.54      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.37/0.54  thf('45', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.37/0.54      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.37/0.54  thf('46', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.37/0.54      inference('sup+', [status(thm)], ['44', '45'])).
% 0.37/0.54  thf('47', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.37/0.54      inference('demod', [status(thm)], ['38', '46'])).
% 0.37/0.54  thf('48', plain, (((k3_xboole_0 @ sk_B_1 @ sk_C_2) = (sk_C_2))),
% 0.37/0.54      inference('demod', [status(thm)], ['35', '47'])).
% 0.37/0.54  thf(t17_xboole_1, axiom,
% 0.37/0.54    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.37/0.54  thf('49', plain,
% 0.37/0.54      (![X14 : $i, X15 : $i]: (r1_tarski @ (k3_xboole_0 @ X14 @ X15) @ X14)),
% 0.37/0.54      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.37/0.54  thf('50', plain,
% 0.37/0.54      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.37/0.54         (~ (r2_hidden @ X2 @ X3)
% 0.37/0.54          | (r2_hidden @ X2 @ X4)
% 0.37/0.54          | ~ (r1_tarski @ X3 @ X4))),
% 0.37/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.54  thf('51', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.54         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['49', '50'])).
% 0.37/0.54  thf('52', plain,
% 0.37/0.54      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_C_2) | (r2_hidden @ X0 @ sk_B_1))),
% 0.37/0.54      inference('sup-', [status(thm)], ['48', '51'])).
% 0.37/0.54  thf('53', plain,
% 0.37/0.54      ((((sk_C_2) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ sk_C_2) @ sk_B_1))),
% 0.37/0.54      inference('sup-', [status(thm)], ['0', '52'])).
% 0.37/0.54  thf('54', plain, (((sk_C_2) != (k1_xboole_0))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('55', plain, ((r2_hidden @ (sk_B @ sk_C_2) @ sk_B_1)),
% 0.37/0.54      inference('simplify_reflect-', [status(thm)], ['53', '54'])).
% 0.37/0.54  thf('56', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 0.37/0.54      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.37/0.54  thf('57', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 0.37/0.54      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.37/0.54  thf(t69_enumset1, axiom,
% 0.37/0.54    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.37/0.54  thf('58', plain,
% 0.37/0.54      (![X29 : $i]: ((k2_tarski @ X29 @ X29) = (k1_tarski @ X29))),
% 0.37/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.54  thf(l51_zfmisc_1, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.37/0.54  thf('59', plain,
% 0.37/0.54      (![X60 : $i, X61 : $i]:
% 0.37/0.54         ((k3_tarski @ (k2_tarski @ X60 @ X61)) = (k2_xboole_0 @ X60 @ X61))),
% 0.37/0.54      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.37/0.54  thf('60', plain,
% 0.37/0.54      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.37/0.54      inference('sup+', [status(thm)], ['58', '59'])).
% 0.37/0.54  thf('61', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ X6) = (X6))),
% 0.37/0.54      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.37/0.54  thf('62', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.37/0.54      inference('demod', [status(thm)], ['60', '61'])).
% 0.37/0.54  thf('63', plain, (((k3_tarski @ sk_B_1) = (sk_A))),
% 0.37/0.54      inference('sup+', [status(thm)], ['57', '62'])).
% 0.37/0.54  thf('64', plain, (((sk_B_1) = (k1_tarski @ (k3_tarski @ sk_B_1)))),
% 0.37/0.54      inference('demod', [status(thm)], ['56', '63'])).
% 0.37/0.54  thf('65', plain,
% 0.37/0.54      (![X24 : $i, X27 : $i]:
% 0.37/0.54         (((X27) = (X24)) | ~ (r2_hidden @ X27 @ (k1_tarski @ X24)))),
% 0.37/0.54      inference('simplify', [status(thm)], ['11'])).
% 0.37/0.54  thf('66', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (~ (r2_hidden @ X0 @ sk_B_1) | ((X0) = (k3_tarski @ sk_B_1)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['64', '65'])).
% 0.37/0.54  thf('67', plain, (((sk_B @ sk_C_2) = (k3_tarski @ sk_B_1))),
% 0.37/0.54      inference('sup-', [status(thm)], ['55', '66'])).
% 0.37/0.54  thf('68', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (((X0) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['14', '15'])).
% 0.37/0.54  thf('69', plain,
% 0.37/0.54      (![X9 : $i, X11 : $i]:
% 0.37/0.54         (((X9) = (X11)) | ~ (r1_tarski @ X11 @ X9) | ~ (r1_tarski @ X9 @ X11))),
% 0.37/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.54  thf('70', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (((X0) = (k1_xboole_0))
% 0.37/0.54          | ~ (r1_tarski @ X0 @ (k1_tarski @ (sk_B @ X0)))
% 0.37/0.54          | ((X0) = (k1_tarski @ (sk_B @ X0))))),
% 0.37/0.54      inference('sup-', [status(thm)], ['68', '69'])).
% 0.37/0.54  thf('71', plain,
% 0.37/0.54      ((~ (r1_tarski @ sk_C_2 @ (k1_tarski @ (k3_tarski @ sk_B_1)))
% 0.37/0.54        | ((sk_C_2) = (k1_tarski @ (sk_B @ sk_C_2)))
% 0.37/0.54        | ((sk_C_2) = (k1_xboole_0)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['67', '70'])).
% 0.37/0.54  thf('72', plain, (((sk_B_1) = (k1_tarski @ (k3_tarski @ sk_B_1)))),
% 0.37/0.54      inference('demod', [status(thm)], ['56', '63'])).
% 0.37/0.54  thf('73', plain, (((k3_xboole_0 @ sk_B_1 @ sk_C_2) = (sk_C_2))),
% 0.37/0.54      inference('demod', [status(thm)], ['35', '47'])).
% 0.37/0.54  thf('74', plain,
% 0.37/0.54      (![X14 : $i, X15 : $i]: (r1_tarski @ (k3_xboole_0 @ X14 @ X15) @ X14)),
% 0.37/0.54      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.37/0.54  thf('75', plain, ((r1_tarski @ sk_C_2 @ sk_B_1)),
% 0.37/0.54      inference('sup+', [status(thm)], ['73', '74'])).
% 0.37/0.54  thf('76', plain, (((sk_B @ sk_C_2) = (k3_tarski @ sk_B_1))),
% 0.37/0.54      inference('sup-', [status(thm)], ['55', '66'])).
% 0.37/0.54  thf('77', plain, (((sk_B_1) = (k1_tarski @ (k3_tarski @ sk_B_1)))),
% 0.37/0.54      inference('demod', [status(thm)], ['56', '63'])).
% 0.37/0.54  thf('78', plain, ((((sk_C_2) = (sk_B_1)) | ((sk_C_2) = (k1_xboole_0)))),
% 0.37/0.54      inference('demod', [status(thm)], ['71', '72', '75', '76', '77'])).
% 0.37/0.54  thf('79', plain, (((sk_C_2) != (k1_xboole_0))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('80', plain, (((sk_B_1) != (sk_C_2))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('81', plain, ($false),
% 0.37/0.54      inference('simplify_reflect-', [status(thm)], ['78', '79', '80'])).
% 0.37/0.54  
% 0.37/0.54  % SZS output end Refutation
% 0.37/0.54  
% 0.37/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

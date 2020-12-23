%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kmeGlSSUYp

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:38 EST 2020

% Result     : Theorem 3.21s
% Output     : Refutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :  159 (1107 expanded)
%              Number of leaves         :   23 ( 334 expanded)
%              Depth                    :   32
%              Number of atoms          : 1181 (10875 expanded)
%              Number of equality atoms :  129 (1585 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('1',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t134_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = ( k2_zfmisc_1 @ C @ D ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( ( A = C )
          & ( B = D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( k2_zfmisc_1 @ A @ B )
          = ( k2_zfmisc_1 @ C @ D ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( ( A = C )
            & ( B = D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t134_zfmisc_1])).

thf('9',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('10',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X40 @ X42 ) @ ( k3_xboole_0 @ X41 @ X43 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X40 @ X41 ) @ ( k2_zfmisc_1 @ X42 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X1 ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D_1 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X40 @ X42 ) @ ( k3_xboole_0 @ X41 @ X43 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X40 @ X41 ) @ ( k2_zfmisc_1 @ X42 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X1 ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ X1 ) @ ( k3_xboole_0 @ sk_D_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ ( k4_xboole_0 @ X1 @ sk_A ) ) @ ( k3_xboole_0 @ sk_D_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('15',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k2_zfmisc_1 @ X32 @ X33 )
        = k1_xboole_0 )
      | ( X32 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('16',plain,(
    ! [X33: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X33 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ ( k4_xboole_0 @ X1 @ sk_A ) ) @ ( k3_xboole_0 @ sk_D_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_D_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','17'])).

thf('19',plain,
    ( k1_xboole_0
    = ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_C @ sk_A ) @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['0','18'])).

thf('20',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k2_zfmisc_1 @ X32 @ X33 )
        = k1_xboole_0 )
      | ( X33 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('21',plain,(
    ! [X32: $i] :
      ( ( k2_zfmisc_1 @ X32 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t117_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) )
          | ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) )
        & ~ ( r1_tarski @ B @ C ) ) )).

thf('22',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( X34 = k1_xboole_0 )
      | ( r1_tarski @ X35 @ X36 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X34 @ X35 ) @ ( k2_zfmisc_1 @ X34 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ X1 ) @ k1_xboole_0 )
      | ( r1_tarski @ X1 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_C @ sk_A )
      = k1_xboole_0 )
    | ( r1_tarski @ sk_D_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','23'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('25',plain,(
    ! [X21: $i] :
      ( ( k3_xboole_0 @ X21 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('26',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k4_xboole_0 @ sk_C @ sk_A )
      = k1_xboole_0 )
    | ( r1_tarski @ sk_D_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','27'])).

thf(t118_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )).

thf('29',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( r1_tarski @ X37 @ X38 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X39 @ X37 ) @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_C @ sk_A )
        = k1_xboole_0 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_D_1 ) @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X32: $i] :
      ( ( k2_zfmisc_1 @ X32 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_C @ sk_A )
        = k1_xboole_0 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_D_1 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ X1 ) @ k1_xboole_0 )
      | ( r1_tarski @ X1 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('35',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D_1 ) @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D_1 ) @ k1_xboole_0 )
    | ( r1_tarski @ sk_B @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['35','36'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('38',plain,(
    ! [X28: $i] :
      ( ( k5_xboole_0 @ X28 @ X28 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('39',plain,(
    ! [X28: $i] :
      ( ( k5_xboole_0 @ X28 @ X28 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('40',plain,(
    ! [X32: $i] :
      ( ( k2_zfmisc_1 @ X32 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( X34 = k1_xboole_0 )
      | ( r1_tarski @ X35 @ X36 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X34 @ X35 ) @ ( k2_zfmisc_1 @ X34 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_C @ sk_D_1 ) )
      | ( r1_tarski @ X0 @ sk_B )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_C @ sk_D_1 ) )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D_1 ) )
      | ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('49',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ sk_B ) ),
    inference(demod,[status(thm)],['47','48'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('50',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( sk_B
        = ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X28: $i] :
      ( ( k5_xboole_0 @ X28 @ X28 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('53',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( sk_B
     != ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ sk_B @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['51','54'])).

thf('56',plain,(
    ~ ( r1_tarski @ sk_B @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','55'])).

thf('57',plain,(
    ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D_1 ) @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['37','56'])).

thf('58',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['32','57'])).

thf('59',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( ( k4_xboole_0 @ X7 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('60',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( r1_tarski @ X37 @ X38 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X37 @ X39 ) @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( X34 = k1_xboole_0 )
      | ( r1_tarski @ X35 @ X36 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X34 @ X35 ) @ ( k2_zfmisc_1 @ X34 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['66','67'])).

thf('69',plain,(
    r1_tarski @ sk_B @ sk_D_1 ),
    inference('sup-',[status(thm)],['63','68'])).

thf('70',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('71',plain,
    ( ~ ( r1_tarski @ sk_D_1 @ sk_B )
    | ( sk_D_1 = sk_B ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('73',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_C @ sk_D_1 ) )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).

thf('75',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('76',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('78',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( r1_tarski @ X37 @ X38 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X37 @ X39 ) @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) @ ( k2_zfmisc_1 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['76','79'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('81',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D_1 ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X40 @ X42 ) @ ( k3_xboole_0 @ X41 @ X43 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X40 @ X41 ) @ ( k2_zfmisc_1 @ X42 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_D_1 ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    r1_tarski @ sk_B @ sk_D_1 ),
    inference('sup-',[status(thm)],['63','68'])).

thf('86',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('87',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_D_1 )
    = sk_B ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_C ) @ sk_B )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['84','87'])).

thf('89',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ sk_B )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['75','88'])).

thf('90',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('91',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ sk_B )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( X34 = k1_xboole_0 )
      | ( r1_tarski @ X35 @ X36 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X35 @ X34 ) @ ( k2_zfmisc_1 @ X36 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) )
      | ( r1_tarski @ sk_A @ X0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D_1 ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_C @ sk_D_1 ) )
    | ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['93','98'])).

thf('100',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('101',plain,(
    r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('103',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['101','104'])).

thf('106',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('107',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('110',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( ( k4_xboole_0 @ X7 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('111',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['108','111'])).

thf('113',plain,(
    ! [X21: $i] :
      ( ( k3_xboole_0 @ X21 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ~ ( r1_tarski @ sk_C @ sk_A )
    | ( sk_C
      = ( k3_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['105','117'])).

thf('119',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(simplify,[status(thm)],['60'])).

thf('120',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['101','104'])).

thf('121',plain,(
    sk_C = sk_A ),
    inference(demod,[status(thm)],['118','119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ X0 ) @ ( k2_zfmisc_1 @ sk_C @ sk_D_1 ) )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['74','121'])).

thf('123',plain,(
    r1_tarski @ sk_D_1 @ sk_B ),
    inference('sup-',[status(thm)],['73','122'])).

thf('124',plain,(
    sk_D_1 = sk_B ),
    inference(demod,[status(thm)],['71','123'])).

thf('125',plain,
    ( ( sk_A != sk_C )
    | ( sk_B != sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( sk_B != sk_D_1 )
   <= ( sk_B != sk_D_1 ) ),
    inference(split,[status(esa)],['125'])).

thf('127',plain,(
    sk_C = sk_A ),
    inference(demod,[status(thm)],['118','119','120'])).

thf('128',plain,
    ( ( sk_A != sk_C )
   <= ( sk_A != sk_C ) ),
    inference(split,[status(esa)],['125'])).

thf('129',plain,
    ( ( sk_C != sk_C )
   <= ( sk_A != sk_C ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    sk_A = sk_C ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,
    ( ( sk_B != sk_D_1 )
    | ( sk_A != sk_C ) ),
    inference(split,[status(esa)],['125'])).

thf('132',plain,(
    sk_B != sk_D_1 ),
    inference('sat_resolution*',[status(thm)],['130','131'])).

thf('133',plain,(
    sk_B != sk_D_1 ),
    inference(simpl_trail,[status(thm)],['126','132'])).

thf('134',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['124','133'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kmeGlSSUYp
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:08:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.21/3.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.21/3.48  % Solved by: fo/fo7.sh
% 3.21/3.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.21/3.48  % done 6767 iterations in 3.027s
% 3.21/3.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.21/3.48  % SZS output start Refutation
% 3.21/3.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.21/3.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.21/3.48  thf(sk_D_1_type, type, sk_D_1: $i).
% 3.21/3.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.21/3.48  thf(sk_B_type, type, sk_B: $i).
% 3.21/3.48  thf(sk_C_type, type, sk_C: $i).
% 3.21/3.48  thf(sk_A_type, type, sk_A: $i).
% 3.21/3.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.21/3.48  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 3.21/3.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.21/3.48  thf(idempotence_k3_xboole_0, axiom,
% 3.21/3.48    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 3.21/3.48  thf('0', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 3.21/3.48      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 3.21/3.48  thf('1', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 3.21/3.48      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 3.21/3.48  thf(t49_xboole_1, axiom,
% 3.21/3.48    (![A:$i,B:$i,C:$i]:
% 3.21/3.48     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 3.21/3.48       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 3.21/3.48  thf('2', plain,
% 3.21/3.48      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.21/3.48         ((k3_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X24))
% 3.21/3.48           = (k4_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ X24))),
% 3.21/3.48      inference('cnf', [status(esa)], [t49_xboole_1])).
% 3.21/3.48  thf('3', plain,
% 3.21/3.48      (![X0 : $i, X1 : $i]:
% 3.21/3.48         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 3.21/3.48           = (k4_xboole_0 @ X0 @ X1))),
% 3.21/3.48      inference('sup+', [status(thm)], ['1', '2'])).
% 3.21/3.48  thf(t17_xboole_1, axiom,
% 3.21/3.48    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 3.21/3.48  thf('4', plain,
% 3.21/3.48      (![X12 : $i, X13 : $i]: (r1_tarski @ (k3_xboole_0 @ X12 @ X13) @ X12)),
% 3.21/3.48      inference('cnf', [status(esa)], [t17_xboole_1])).
% 3.21/3.48  thf(l32_xboole_1, axiom,
% 3.21/3.48    (![A:$i,B:$i]:
% 3.21/3.48     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.21/3.48  thf('5', plain,
% 3.21/3.48      (![X7 : $i, X9 : $i]:
% 3.21/3.48         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 3.21/3.48      inference('cnf', [status(esa)], [l32_xboole_1])).
% 3.21/3.48  thf('6', plain,
% 3.21/3.48      (![X0 : $i, X1 : $i]:
% 3.21/3.48         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 3.21/3.48      inference('sup-', [status(thm)], ['4', '5'])).
% 3.21/3.48  thf('7', plain,
% 3.21/3.48      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.21/3.48         ((k3_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X24))
% 3.21/3.48           = (k4_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ X24))),
% 3.21/3.48      inference('cnf', [status(esa)], [t49_xboole_1])).
% 3.21/3.48  thf('8', plain,
% 3.21/3.48      (![X0 : $i, X1 : $i]:
% 3.21/3.48         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 3.21/3.48      inference('demod', [status(thm)], ['6', '7'])).
% 3.21/3.48  thf(t134_zfmisc_1, conjecture,
% 3.21/3.48    (![A:$i,B:$i,C:$i,D:$i]:
% 3.21/3.48     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 3.21/3.48       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 3.21/3.48         ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ))).
% 3.21/3.48  thf(zf_stmt_0, negated_conjecture,
% 3.21/3.48    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 3.21/3.48        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 3.21/3.48          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 3.21/3.48            ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) )),
% 3.21/3.48    inference('cnf.neg', [status(esa)], [t134_zfmisc_1])).
% 3.21/3.48  thf('9', plain,
% 3.21/3.48      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D_1))),
% 3.21/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.48  thf(t123_zfmisc_1, axiom,
% 3.21/3.48    (![A:$i,B:$i,C:$i,D:$i]:
% 3.21/3.48     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 3.21/3.48       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 3.21/3.48  thf('10', plain,
% 3.21/3.48      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 3.21/3.48         ((k2_zfmisc_1 @ (k3_xboole_0 @ X40 @ X42) @ (k3_xboole_0 @ X41 @ X43))
% 3.21/3.48           = (k3_xboole_0 @ (k2_zfmisc_1 @ X40 @ X41) @ 
% 3.21/3.48              (k2_zfmisc_1 @ X42 @ X43)))),
% 3.21/3.48      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 3.21/3.48  thf('11', plain,
% 3.21/3.48      (![X0 : $i, X1 : $i]:
% 3.21/3.48         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X1) @ (k3_xboole_0 @ sk_B @ X0))
% 3.21/3.48           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D_1) @ 
% 3.21/3.48              (k2_zfmisc_1 @ X1 @ X0)))),
% 3.21/3.48      inference('sup+', [status(thm)], ['9', '10'])).
% 3.21/3.48  thf('12', plain,
% 3.21/3.48      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 3.21/3.48         ((k2_zfmisc_1 @ (k3_xboole_0 @ X40 @ X42) @ (k3_xboole_0 @ X41 @ X43))
% 3.21/3.48           = (k3_xboole_0 @ (k2_zfmisc_1 @ X40 @ X41) @ 
% 3.21/3.48              (k2_zfmisc_1 @ X42 @ X43)))),
% 3.21/3.48      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 3.21/3.48  thf('13', plain,
% 3.21/3.48      (![X0 : $i, X1 : $i]:
% 3.21/3.48         ((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X1) @ (k3_xboole_0 @ sk_B @ X0))
% 3.21/3.48           = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ X1) @ 
% 3.21/3.48              (k3_xboole_0 @ sk_D_1 @ X0)))),
% 3.21/3.48      inference('demod', [status(thm)], ['11', '12'])).
% 3.21/3.48  thf('14', plain,
% 3.21/3.48      (![X0 : $i, X1 : $i]:
% 3.21/3.48         ((k2_zfmisc_1 @ k1_xboole_0 @ (k3_xboole_0 @ sk_B @ X0))
% 3.21/3.48           = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ (k4_xboole_0 @ X1 @ sk_A)) @ 
% 3.21/3.48              (k3_xboole_0 @ sk_D_1 @ X0)))),
% 3.21/3.48      inference('sup+', [status(thm)], ['8', '13'])).
% 3.21/3.48  thf(t113_zfmisc_1, axiom,
% 3.21/3.48    (![A:$i,B:$i]:
% 3.21/3.48     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.21/3.48       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.21/3.48  thf('15', plain,
% 3.21/3.48      (![X32 : $i, X33 : $i]:
% 3.21/3.48         (((k2_zfmisc_1 @ X32 @ X33) = (k1_xboole_0))
% 3.21/3.48          | ((X32) != (k1_xboole_0)))),
% 3.21/3.48      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.21/3.48  thf('16', plain,
% 3.21/3.48      (![X33 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X33) = (k1_xboole_0))),
% 3.21/3.48      inference('simplify', [status(thm)], ['15'])).
% 3.21/3.48  thf('17', plain,
% 3.21/3.48      (![X0 : $i, X1 : $i]:
% 3.21/3.48         ((k1_xboole_0)
% 3.21/3.48           = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ (k4_xboole_0 @ X1 @ sk_A)) @ 
% 3.21/3.48              (k3_xboole_0 @ sk_D_1 @ X0)))),
% 3.21/3.48      inference('demod', [status(thm)], ['14', '16'])).
% 3.21/3.48  thf('18', plain,
% 3.21/3.48      (![X0 : $i]:
% 3.21/3.48         ((k1_xboole_0)
% 3.21/3.48           = (k2_zfmisc_1 @ (k4_xboole_0 @ sk_C @ sk_A) @ 
% 3.21/3.48              (k3_xboole_0 @ sk_D_1 @ X0)))),
% 3.21/3.48      inference('sup+', [status(thm)], ['3', '17'])).
% 3.21/3.48  thf('19', plain,
% 3.21/3.48      (((k1_xboole_0) = (k2_zfmisc_1 @ (k4_xboole_0 @ sk_C @ sk_A) @ sk_D_1))),
% 3.21/3.48      inference('sup+', [status(thm)], ['0', '18'])).
% 3.21/3.48  thf('20', plain,
% 3.21/3.48      (![X32 : $i, X33 : $i]:
% 3.21/3.48         (((k2_zfmisc_1 @ X32 @ X33) = (k1_xboole_0))
% 3.21/3.48          | ((X33) != (k1_xboole_0)))),
% 3.21/3.48      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.21/3.48  thf('21', plain,
% 3.21/3.48      (![X32 : $i]: ((k2_zfmisc_1 @ X32 @ k1_xboole_0) = (k1_xboole_0))),
% 3.21/3.48      inference('simplify', [status(thm)], ['20'])).
% 3.21/3.48  thf(t117_zfmisc_1, axiom,
% 3.21/3.48    (![A:$i,B:$i,C:$i]:
% 3.21/3.48     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 3.21/3.48          ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) ) | 
% 3.21/3.48            ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 3.21/3.48          ( ~( r1_tarski @ B @ C ) ) ) ))).
% 3.21/3.48  thf('22', plain,
% 3.21/3.48      (![X34 : $i, X35 : $i, X36 : $i]:
% 3.21/3.48         (((X34) = (k1_xboole_0))
% 3.21/3.48          | (r1_tarski @ X35 @ X36)
% 3.21/3.48          | ~ (r1_tarski @ (k2_zfmisc_1 @ X34 @ X35) @ 
% 3.21/3.48               (k2_zfmisc_1 @ X34 @ X36)))),
% 3.21/3.48      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 3.21/3.48  thf('23', plain,
% 3.21/3.48      (![X0 : $i, X1 : $i]:
% 3.21/3.48         (~ (r1_tarski @ (k2_zfmisc_1 @ X0 @ X1) @ k1_xboole_0)
% 3.21/3.48          | (r1_tarski @ X1 @ k1_xboole_0)
% 3.21/3.48          | ((X0) = (k1_xboole_0)))),
% 3.21/3.48      inference('sup-', [status(thm)], ['21', '22'])).
% 3.21/3.48  thf('24', plain,
% 3.21/3.48      ((~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0)
% 3.21/3.48        | ((k4_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))
% 3.21/3.48        | (r1_tarski @ sk_D_1 @ k1_xboole_0))),
% 3.21/3.48      inference('sup-', [status(thm)], ['19', '23'])).
% 3.21/3.48  thf(t2_boole, axiom,
% 3.21/3.48    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 3.21/3.48  thf('25', plain,
% 3.21/3.48      (![X21 : $i]: ((k3_xboole_0 @ X21 @ k1_xboole_0) = (k1_xboole_0))),
% 3.21/3.48      inference('cnf', [status(esa)], [t2_boole])).
% 3.21/3.48  thf('26', plain,
% 3.21/3.48      (![X12 : $i, X13 : $i]: (r1_tarski @ (k3_xboole_0 @ X12 @ X13) @ X12)),
% 3.21/3.48      inference('cnf', [status(esa)], [t17_xboole_1])).
% 3.21/3.48  thf('27', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 3.21/3.48      inference('sup+', [status(thm)], ['25', '26'])).
% 3.21/3.48  thf('28', plain,
% 3.21/3.48      ((((k4_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))
% 3.21/3.48        | (r1_tarski @ sk_D_1 @ k1_xboole_0))),
% 3.21/3.48      inference('demod', [status(thm)], ['24', '27'])).
% 3.21/3.48  thf(t118_zfmisc_1, axiom,
% 3.21/3.48    (![A:$i,B:$i,C:$i]:
% 3.21/3.48     ( ( r1_tarski @ A @ B ) =>
% 3.21/3.48       ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 3.21/3.48         ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ))).
% 3.21/3.48  thf('29', plain,
% 3.21/3.48      (![X37 : $i, X38 : $i, X39 : $i]:
% 3.21/3.48         (~ (r1_tarski @ X37 @ X38)
% 3.21/3.48          | (r1_tarski @ (k2_zfmisc_1 @ X39 @ X37) @ (k2_zfmisc_1 @ X39 @ X38)))),
% 3.21/3.48      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 3.21/3.48  thf('30', plain,
% 3.21/3.48      (![X0 : $i]:
% 3.21/3.48         (((k4_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))
% 3.21/3.48          | (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_D_1) @ 
% 3.21/3.48             (k2_zfmisc_1 @ X0 @ k1_xboole_0)))),
% 3.21/3.48      inference('sup-', [status(thm)], ['28', '29'])).
% 3.21/3.48  thf('31', plain,
% 3.21/3.48      (![X32 : $i]: ((k2_zfmisc_1 @ X32 @ k1_xboole_0) = (k1_xboole_0))),
% 3.21/3.48      inference('simplify', [status(thm)], ['20'])).
% 3.21/3.48  thf('32', plain,
% 3.21/3.48      (![X0 : $i]:
% 3.21/3.48         (((k4_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))
% 3.21/3.48          | (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_D_1) @ k1_xboole_0))),
% 3.21/3.48      inference('demod', [status(thm)], ['30', '31'])).
% 3.21/3.48  thf('33', plain,
% 3.21/3.48      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D_1))),
% 3.21/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.48  thf('34', plain,
% 3.21/3.48      (![X0 : $i, X1 : $i]:
% 3.21/3.48         (~ (r1_tarski @ (k2_zfmisc_1 @ X0 @ X1) @ k1_xboole_0)
% 3.21/3.48          | (r1_tarski @ X1 @ k1_xboole_0)
% 3.21/3.48          | ((X0) = (k1_xboole_0)))),
% 3.21/3.48      inference('sup-', [status(thm)], ['21', '22'])).
% 3.21/3.48  thf('35', plain,
% 3.21/3.48      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D_1) @ k1_xboole_0)
% 3.21/3.48        | ((sk_A) = (k1_xboole_0))
% 3.21/3.48        | (r1_tarski @ sk_B @ k1_xboole_0))),
% 3.21/3.48      inference('sup-', [status(thm)], ['33', '34'])).
% 3.21/3.48  thf('36', plain, (((sk_A) != (k1_xboole_0))),
% 3.21/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.48  thf('37', plain,
% 3.21/3.48      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D_1) @ k1_xboole_0)
% 3.21/3.48        | (r1_tarski @ sk_B @ k1_xboole_0))),
% 3.21/3.48      inference('simplify_reflect-', [status(thm)], ['35', '36'])).
% 3.21/3.48  thf(t92_xboole_1, axiom,
% 3.21/3.48    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 3.21/3.48  thf('38', plain, (![X28 : $i]: ((k5_xboole_0 @ X28 @ X28) = (k1_xboole_0))),
% 3.21/3.48      inference('cnf', [status(esa)], [t92_xboole_1])).
% 3.21/3.48  thf('39', plain, (![X28 : $i]: ((k5_xboole_0 @ X28 @ X28) = (k1_xboole_0))),
% 3.21/3.48      inference('cnf', [status(esa)], [t92_xboole_1])).
% 3.21/3.48  thf('40', plain,
% 3.21/3.48      (![X32 : $i]: ((k2_zfmisc_1 @ X32 @ k1_xboole_0) = (k1_xboole_0))),
% 3.21/3.48      inference('simplify', [status(thm)], ['20'])).
% 3.21/3.48  thf('41', plain,
% 3.21/3.48      (![X0 : $i, X1 : $i]:
% 3.21/3.48         ((k2_zfmisc_1 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 3.21/3.48      inference('sup+', [status(thm)], ['39', '40'])).
% 3.21/3.48  thf('42', plain,
% 3.21/3.48      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D_1))),
% 3.21/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.48  thf('43', plain,
% 3.21/3.48      (![X34 : $i, X35 : $i, X36 : $i]:
% 3.21/3.48         (((X34) = (k1_xboole_0))
% 3.21/3.48          | (r1_tarski @ X35 @ X36)
% 3.21/3.48          | ~ (r1_tarski @ (k2_zfmisc_1 @ X34 @ X35) @ 
% 3.21/3.48               (k2_zfmisc_1 @ X34 @ X36)))),
% 3.21/3.48      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 3.21/3.48  thf('44', plain,
% 3.21/3.48      (![X0 : $i]:
% 3.21/3.48         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ X0) @ 
% 3.21/3.48             (k2_zfmisc_1 @ sk_C @ sk_D_1))
% 3.21/3.48          | (r1_tarski @ X0 @ sk_B)
% 3.21/3.48          | ((sk_A) = (k1_xboole_0)))),
% 3.21/3.48      inference('sup-', [status(thm)], ['42', '43'])).
% 3.21/3.48  thf('45', plain, (((sk_A) != (k1_xboole_0))),
% 3.21/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.48  thf('46', plain,
% 3.21/3.48      (![X0 : $i]:
% 3.21/3.48         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ X0) @ 
% 3.21/3.48             (k2_zfmisc_1 @ sk_C @ sk_D_1))
% 3.21/3.48          | (r1_tarski @ X0 @ sk_B))),
% 3.21/3.48      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 3.21/3.48  thf('47', plain,
% 3.21/3.48      (![X0 : $i]:
% 3.21/3.48         (~ (r1_tarski @ k1_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D_1))
% 3.21/3.48          | (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ sk_B))),
% 3.21/3.48      inference('sup-', [status(thm)], ['41', '46'])).
% 3.21/3.48  thf('48', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 3.21/3.48      inference('sup+', [status(thm)], ['25', '26'])).
% 3.21/3.48  thf('49', plain, (![X0 : $i]: (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ sk_B)),
% 3.21/3.48      inference('demod', [status(thm)], ['47', '48'])).
% 3.21/3.48  thf(d10_xboole_0, axiom,
% 3.21/3.48    (![A:$i,B:$i]:
% 3.21/3.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.21/3.48  thf('50', plain,
% 3.21/3.48      (![X4 : $i, X6 : $i]:
% 3.21/3.48         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 3.21/3.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.21/3.48  thf('51', plain,
% 3.21/3.48      (![X0 : $i]:
% 3.21/3.48         (~ (r1_tarski @ sk_B @ (k5_xboole_0 @ X0 @ X0))
% 3.21/3.48          | ((sk_B) = (k5_xboole_0 @ X0 @ X0)))),
% 3.21/3.48      inference('sup-', [status(thm)], ['49', '50'])).
% 3.21/3.48  thf('52', plain, (![X28 : $i]: ((k5_xboole_0 @ X28 @ X28) = (k1_xboole_0))),
% 3.21/3.48      inference('cnf', [status(esa)], [t92_xboole_1])).
% 3.21/3.48  thf('53', plain, (((sk_B) != (k1_xboole_0))),
% 3.21/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.48  thf('54', plain, (![X0 : $i]: ((sk_B) != (k5_xboole_0 @ X0 @ X0))),
% 3.21/3.48      inference('sup-', [status(thm)], ['52', '53'])).
% 3.21/3.48  thf('55', plain,
% 3.21/3.48      (![X0 : $i]: ~ (r1_tarski @ sk_B @ (k5_xboole_0 @ X0 @ X0))),
% 3.21/3.48      inference('clc', [status(thm)], ['51', '54'])).
% 3.21/3.48  thf('56', plain, (~ (r1_tarski @ sk_B @ k1_xboole_0)),
% 3.21/3.48      inference('sup-', [status(thm)], ['38', '55'])).
% 3.21/3.48  thf('57', plain,
% 3.21/3.48      (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D_1) @ k1_xboole_0)),
% 3.21/3.48      inference('clc', [status(thm)], ['37', '56'])).
% 3.21/3.48  thf('58', plain, (((k4_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 3.21/3.48      inference('sup-', [status(thm)], ['32', '57'])).
% 3.21/3.48  thf('59', plain,
% 3.21/3.48      (![X7 : $i, X8 : $i]:
% 3.21/3.48         ((r1_tarski @ X7 @ X8) | ((k4_xboole_0 @ X7 @ X8) != (k1_xboole_0)))),
% 3.21/3.48      inference('cnf', [status(esa)], [l32_xboole_1])).
% 3.21/3.48  thf('60', plain,
% 3.21/3.48      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_C @ sk_A))),
% 3.21/3.48      inference('sup-', [status(thm)], ['58', '59'])).
% 3.21/3.48  thf('61', plain, ((r1_tarski @ sk_C @ sk_A)),
% 3.21/3.48      inference('simplify', [status(thm)], ['60'])).
% 3.21/3.48  thf('62', plain,
% 3.21/3.48      (![X37 : $i, X38 : $i, X39 : $i]:
% 3.21/3.48         (~ (r1_tarski @ X37 @ X38)
% 3.21/3.48          | (r1_tarski @ (k2_zfmisc_1 @ X37 @ X39) @ (k2_zfmisc_1 @ X38 @ X39)))),
% 3.21/3.48      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 3.21/3.48  thf('63', plain,
% 3.21/3.48      (![X0 : $i]:
% 3.21/3.48         (r1_tarski @ (k2_zfmisc_1 @ sk_C @ X0) @ (k2_zfmisc_1 @ sk_A @ X0))),
% 3.21/3.48      inference('sup-', [status(thm)], ['61', '62'])).
% 3.21/3.48  thf('64', plain,
% 3.21/3.48      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D_1))),
% 3.21/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.48  thf('65', plain,
% 3.21/3.48      (![X34 : $i, X35 : $i, X36 : $i]:
% 3.21/3.48         (((X34) = (k1_xboole_0))
% 3.21/3.48          | (r1_tarski @ X35 @ X36)
% 3.21/3.48          | ~ (r1_tarski @ (k2_zfmisc_1 @ X34 @ X35) @ 
% 3.21/3.48               (k2_zfmisc_1 @ X34 @ X36)))),
% 3.21/3.48      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 3.21/3.48  thf('66', plain,
% 3.21/3.48      (![X0 : $i]:
% 3.21/3.48         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D_1) @ 
% 3.21/3.48             (k2_zfmisc_1 @ sk_A @ X0))
% 3.21/3.48          | (r1_tarski @ sk_B @ X0)
% 3.21/3.48          | ((sk_A) = (k1_xboole_0)))),
% 3.21/3.48      inference('sup-', [status(thm)], ['64', '65'])).
% 3.21/3.48  thf('67', plain, (((sk_A) != (k1_xboole_0))),
% 3.21/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.48  thf('68', plain,
% 3.21/3.48      (![X0 : $i]:
% 3.21/3.48         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D_1) @ 
% 3.21/3.48             (k2_zfmisc_1 @ sk_A @ X0))
% 3.21/3.48          | (r1_tarski @ sk_B @ X0))),
% 3.21/3.48      inference('simplify_reflect-', [status(thm)], ['66', '67'])).
% 3.21/3.48  thf('69', plain, ((r1_tarski @ sk_B @ sk_D_1)),
% 3.21/3.48      inference('sup-', [status(thm)], ['63', '68'])).
% 3.21/3.48  thf('70', plain,
% 3.21/3.48      (![X4 : $i, X6 : $i]:
% 3.21/3.48         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 3.21/3.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.21/3.48  thf('71', plain, ((~ (r1_tarski @ sk_D_1 @ sk_B) | ((sk_D_1) = (sk_B)))),
% 3.21/3.48      inference('sup-', [status(thm)], ['69', '70'])).
% 3.21/3.48  thf('72', plain,
% 3.21/3.48      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 3.21/3.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.21/3.48  thf('73', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 3.21/3.48      inference('simplify', [status(thm)], ['72'])).
% 3.21/3.48  thf('74', plain,
% 3.21/3.48      (![X0 : $i]:
% 3.21/3.48         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ X0) @ 
% 3.21/3.48             (k2_zfmisc_1 @ sk_C @ sk_D_1))
% 3.21/3.48          | (r1_tarski @ X0 @ sk_B))),
% 3.21/3.48      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 3.21/3.48  thf('75', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 3.21/3.48      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 3.21/3.48  thf('76', plain,
% 3.21/3.48      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D_1))),
% 3.21/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.48  thf('77', plain,
% 3.21/3.48      (![X12 : $i, X13 : $i]: (r1_tarski @ (k3_xboole_0 @ X12 @ X13) @ X12)),
% 3.21/3.48      inference('cnf', [status(esa)], [t17_xboole_1])).
% 3.21/3.48  thf('78', plain,
% 3.21/3.48      (![X37 : $i, X38 : $i, X39 : $i]:
% 3.21/3.48         (~ (r1_tarski @ X37 @ X38)
% 3.21/3.48          | (r1_tarski @ (k2_zfmisc_1 @ X37 @ X39) @ (k2_zfmisc_1 @ X38 @ X39)))),
% 3.21/3.48      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 3.21/3.48  thf('79', plain,
% 3.21/3.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.21/3.48         (r1_tarski @ (k2_zfmisc_1 @ (k3_xboole_0 @ X0 @ X1) @ X2) @ 
% 3.21/3.48          (k2_zfmisc_1 @ X0 @ X2))),
% 3.21/3.48      inference('sup-', [status(thm)], ['77', '78'])).
% 3.21/3.48  thf('80', plain,
% 3.21/3.48      (![X0 : $i]:
% 3.21/3.48         (r1_tarski @ (k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B) @ 
% 3.21/3.48          (k2_zfmisc_1 @ sk_C @ sk_D_1))),
% 3.21/3.48      inference('sup+', [status(thm)], ['76', '79'])).
% 3.21/3.48  thf(t28_xboole_1, axiom,
% 3.21/3.48    (![A:$i,B:$i]:
% 3.21/3.48     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 3.21/3.48  thf('81', plain,
% 3.21/3.48      (![X19 : $i, X20 : $i]:
% 3.21/3.48         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 3.21/3.48      inference('cnf', [status(esa)], [t28_xboole_1])).
% 3.21/3.48  thf('82', plain,
% 3.21/3.48      (![X0 : $i]:
% 3.21/3.48         ((k3_xboole_0 @ (k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B) @ 
% 3.21/3.48           (k2_zfmisc_1 @ sk_C @ sk_D_1))
% 3.21/3.48           = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B))),
% 3.21/3.48      inference('sup-', [status(thm)], ['80', '81'])).
% 3.21/3.48  thf('83', plain,
% 3.21/3.48      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 3.21/3.48         ((k2_zfmisc_1 @ (k3_xboole_0 @ X40 @ X42) @ (k3_xboole_0 @ X41 @ X43))
% 3.21/3.48           = (k3_xboole_0 @ (k2_zfmisc_1 @ X40 @ X41) @ 
% 3.21/3.48              (k2_zfmisc_1 @ X42 @ X43)))),
% 3.21/3.48      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 3.21/3.48  thf('84', plain,
% 3.21/3.48      (![X0 : $i]:
% 3.21/3.48         ((k2_zfmisc_1 @ (k3_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ sk_C) @ 
% 3.21/3.48           (k3_xboole_0 @ sk_B @ sk_D_1))
% 3.21/3.48           = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B))),
% 3.21/3.48      inference('demod', [status(thm)], ['82', '83'])).
% 3.21/3.48  thf('85', plain, ((r1_tarski @ sk_B @ sk_D_1)),
% 3.21/3.48      inference('sup-', [status(thm)], ['63', '68'])).
% 3.21/3.48  thf('86', plain,
% 3.21/3.48      (![X19 : $i, X20 : $i]:
% 3.21/3.48         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 3.21/3.48      inference('cnf', [status(esa)], [t28_xboole_1])).
% 3.21/3.48  thf('87', plain, (((k3_xboole_0 @ sk_B @ sk_D_1) = (sk_B))),
% 3.21/3.48      inference('sup-', [status(thm)], ['85', '86'])).
% 3.21/3.48  thf('88', plain,
% 3.21/3.48      (![X0 : $i]:
% 3.21/3.48         ((k2_zfmisc_1 @ (k3_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ sk_C) @ 
% 3.21/3.48           sk_B) = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B))),
% 3.21/3.48      inference('demod', [status(thm)], ['84', '87'])).
% 3.21/3.48  thf('89', plain,
% 3.21/3.48      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C) @ sk_B)
% 3.21/3.48         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_A) @ sk_B))),
% 3.21/3.48      inference('sup+', [status(thm)], ['75', '88'])).
% 3.21/3.48  thf('90', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 3.21/3.48      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 3.21/3.48  thf('91', plain,
% 3.21/3.48      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C) @ sk_B)
% 3.21/3.48         = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 3.21/3.48      inference('demod', [status(thm)], ['89', '90'])).
% 3.21/3.48  thf('92', plain,
% 3.21/3.48      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D_1))),
% 3.21/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.48  thf('93', plain,
% 3.21/3.48      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C) @ sk_B)
% 3.21/3.48         = (k2_zfmisc_1 @ sk_C @ sk_D_1))),
% 3.21/3.48      inference('demod', [status(thm)], ['91', '92'])).
% 3.21/3.48  thf('94', plain,
% 3.21/3.48      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D_1))),
% 3.21/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.48  thf('95', plain,
% 3.21/3.48      (![X34 : $i, X35 : $i, X36 : $i]:
% 3.21/3.48         (((X34) = (k1_xboole_0))
% 3.21/3.48          | (r1_tarski @ X35 @ X36)
% 3.21/3.48          | ~ (r1_tarski @ (k2_zfmisc_1 @ X35 @ X34) @ 
% 3.21/3.48               (k2_zfmisc_1 @ X36 @ X34)))),
% 3.21/3.48      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 3.21/3.48  thf('96', plain,
% 3.21/3.48      (![X0 : $i]:
% 3.21/3.48         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D_1) @ 
% 3.21/3.48             (k2_zfmisc_1 @ X0 @ sk_B))
% 3.21/3.48          | (r1_tarski @ sk_A @ X0)
% 3.21/3.48          | ((sk_B) = (k1_xboole_0)))),
% 3.21/3.48      inference('sup-', [status(thm)], ['94', '95'])).
% 3.21/3.48  thf('97', plain, (((sk_B) != (k1_xboole_0))),
% 3.21/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.48  thf('98', plain,
% 3.21/3.48      (![X0 : $i]:
% 3.21/3.48         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D_1) @ 
% 3.21/3.48             (k2_zfmisc_1 @ X0 @ sk_B))
% 3.21/3.48          | (r1_tarski @ sk_A @ X0))),
% 3.21/3.48      inference('simplify_reflect-', [status(thm)], ['96', '97'])).
% 3.21/3.48  thf('99', plain,
% 3.21/3.48      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D_1) @ 
% 3.21/3.48           (k2_zfmisc_1 @ sk_C @ sk_D_1))
% 3.21/3.48        | (r1_tarski @ sk_A @ (k3_xboole_0 @ sk_A @ sk_C)))),
% 3.21/3.48      inference('sup-', [status(thm)], ['93', '98'])).
% 3.21/3.48  thf('100', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 3.21/3.48      inference('simplify', [status(thm)], ['72'])).
% 3.21/3.48  thf('101', plain, ((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_A @ sk_C))),
% 3.21/3.48      inference('demod', [status(thm)], ['99', '100'])).
% 3.21/3.48  thf('102', plain,
% 3.21/3.48      (![X12 : $i, X13 : $i]: (r1_tarski @ (k3_xboole_0 @ X12 @ X13) @ X12)),
% 3.21/3.48      inference('cnf', [status(esa)], [t17_xboole_1])).
% 3.21/3.48  thf('103', plain,
% 3.21/3.48      (![X4 : $i, X6 : $i]:
% 3.21/3.48         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 3.21/3.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.21/3.48  thf('104', plain,
% 3.21/3.48      (![X0 : $i, X1 : $i]:
% 3.21/3.48         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 3.21/3.48          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 3.21/3.48      inference('sup-', [status(thm)], ['102', '103'])).
% 3.21/3.48  thf('105', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ sk_C))),
% 3.21/3.48      inference('sup-', [status(thm)], ['101', '104'])).
% 3.21/3.48  thf('106', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 3.21/3.48      inference('simplify', [status(thm)], ['72'])).
% 3.21/3.48  thf('107', plain,
% 3.21/3.48      (![X7 : $i, X9 : $i]:
% 3.21/3.48         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 3.21/3.48      inference('cnf', [status(esa)], [l32_xboole_1])).
% 3.21/3.48  thf('108', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.21/3.48      inference('sup-', [status(thm)], ['106', '107'])).
% 3.21/3.48  thf('109', plain,
% 3.21/3.48      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.21/3.48         ((k3_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X24))
% 3.21/3.48           = (k4_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ X24))),
% 3.21/3.48      inference('cnf', [status(esa)], [t49_xboole_1])).
% 3.21/3.48  thf('110', plain,
% 3.21/3.48      (![X7 : $i, X8 : $i]:
% 3.21/3.48         ((r1_tarski @ X7 @ X8) | ((k4_xboole_0 @ X7 @ X8) != (k1_xboole_0)))),
% 3.21/3.48      inference('cnf', [status(esa)], [l32_xboole_1])).
% 3.21/3.48  thf('111', plain,
% 3.21/3.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.21/3.48         (((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 3.21/3.48          | (r1_tarski @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 3.21/3.48      inference('sup-', [status(thm)], ['109', '110'])).
% 3.21/3.48  thf('112', plain,
% 3.21/3.48      (![X0 : $i, X1 : $i]:
% 3.21/3.48         (((k3_xboole_0 @ X1 @ k1_xboole_0) != (k1_xboole_0))
% 3.21/3.48          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 3.21/3.48      inference('sup-', [status(thm)], ['108', '111'])).
% 3.21/3.48  thf('113', plain,
% 3.21/3.48      (![X21 : $i]: ((k3_xboole_0 @ X21 @ k1_xboole_0) = (k1_xboole_0))),
% 3.21/3.48      inference('cnf', [status(esa)], [t2_boole])).
% 3.21/3.48  thf('114', plain,
% 3.21/3.48      (![X0 : $i, X1 : $i]:
% 3.21/3.48         (((k1_xboole_0) != (k1_xboole_0))
% 3.21/3.48          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 3.21/3.48      inference('demod', [status(thm)], ['112', '113'])).
% 3.21/3.48  thf('115', plain,
% 3.21/3.48      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 3.21/3.48      inference('simplify', [status(thm)], ['114'])).
% 3.21/3.48  thf('116', plain,
% 3.21/3.48      (![X4 : $i, X6 : $i]:
% 3.21/3.48         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 3.21/3.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.21/3.48  thf('117', plain,
% 3.21/3.48      (![X0 : $i, X1 : $i]:
% 3.21/3.48         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 3.21/3.48          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 3.21/3.48      inference('sup-', [status(thm)], ['115', '116'])).
% 3.21/3.48  thf('118', plain,
% 3.21/3.48      ((~ (r1_tarski @ sk_C @ sk_A) | ((sk_C) = (k3_xboole_0 @ sk_A @ sk_C)))),
% 3.21/3.48      inference('sup-', [status(thm)], ['105', '117'])).
% 3.21/3.48  thf('119', plain, ((r1_tarski @ sk_C @ sk_A)),
% 3.21/3.48      inference('simplify', [status(thm)], ['60'])).
% 3.21/3.48  thf('120', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ sk_C))),
% 3.21/3.48      inference('sup-', [status(thm)], ['101', '104'])).
% 3.21/3.48  thf('121', plain, (((sk_C) = (sk_A))),
% 3.21/3.48      inference('demod', [status(thm)], ['118', '119', '120'])).
% 3.21/3.48  thf('122', plain,
% 3.21/3.48      (![X0 : $i]:
% 3.21/3.48         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ X0) @ 
% 3.21/3.48             (k2_zfmisc_1 @ sk_C @ sk_D_1))
% 3.21/3.48          | (r1_tarski @ X0 @ sk_B))),
% 3.21/3.48      inference('demod', [status(thm)], ['74', '121'])).
% 3.21/3.48  thf('123', plain, ((r1_tarski @ sk_D_1 @ sk_B)),
% 3.21/3.48      inference('sup-', [status(thm)], ['73', '122'])).
% 3.21/3.48  thf('124', plain, (((sk_D_1) = (sk_B))),
% 3.21/3.48      inference('demod', [status(thm)], ['71', '123'])).
% 3.21/3.48  thf('125', plain, ((((sk_A) != (sk_C)) | ((sk_B) != (sk_D_1)))),
% 3.21/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.48  thf('126', plain, ((((sk_B) != (sk_D_1))) <= (~ (((sk_B) = (sk_D_1))))),
% 3.21/3.48      inference('split', [status(esa)], ['125'])).
% 3.21/3.48  thf('127', plain, (((sk_C) = (sk_A))),
% 3.21/3.48      inference('demod', [status(thm)], ['118', '119', '120'])).
% 3.21/3.48  thf('128', plain, ((((sk_A) != (sk_C))) <= (~ (((sk_A) = (sk_C))))),
% 3.21/3.48      inference('split', [status(esa)], ['125'])).
% 3.21/3.48  thf('129', plain, ((((sk_C) != (sk_C))) <= (~ (((sk_A) = (sk_C))))),
% 3.21/3.48      inference('sup-', [status(thm)], ['127', '128'])).
% 3.21/3.48  thf('130', plain, ((((sk_A) = (sk_C)))),
% 3.21/3.48      inference('simplify', [status(thm)], ['129'])).
% 3.21/3.48  thf('131', plain, (~ (((sk_B) = (sk_D_1))) | ~ (((sk_A) = (sk_C)))),
% 3.21/3.48      inference('split', [status(esa)], ['125'])).
% 3.21/3.48  thf('132', plain, (~ (((sk_B) = (sk_D_1)))),
% 3.21/3.48      inference('sat_resolution*', [status(thm)], ['130', '131'])).
% 3.21/3.48  thf('133', plain, (((sk_B) != (sk_D_1))),
% 3.21/3.48      inference('simpl_trail', [status(thm)], ['126', '132'])).
% 3.21/3.48  thf('134', plain, ($false),
% 3.21/3.48      inference('simplify_reflect-', [status(thm)], ['124', '133'])).
% 3.21/3.48  
% 3.21/3.48  % SZS output end Refutation
% 3.21/3.48  
% 3.31/3.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.O0OkaslhQ8

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:42 EST 2020

% Result     : Theorem 0.78s
% Output     : Refutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :  172 (1356 expanded)
%              Number of leaves         :   31 ( 435 expanded)
%              Depth                    :   29
%              Number of atoms          : 1192 (11611 expanded)
%              Number of equality atoms :  135 (1620 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('3',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_2 )
    = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ sk_C_2 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['0','3'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('6',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k5_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ sk_C_2 @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_B_1 @ ( k3_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('10',plain,
    ( ( k5_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ sk_C_2 @ ( k1_tarski @ sk_A ) ) )
    = ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('14',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('15',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,
    ( ( k5_xboole_0 @ sk_C_2 @ ( k1_tarski @ sk_A ) )
    = ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['10','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k1_tarski @ sk_A )
    = ( k5_xboole_0 @ sk_C_2 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X11: $i,X13: $i] :
      ( ( X11 = X13 )
      | ~ ( r1_tarski @ X13 @ X11 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    | ( ( k2_xboole_0 @ sk_B_1 @ sk_C_2 )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('29',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('30',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('32',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['35','36'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('38',plain,(
    ! [X26: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X29 @ X28 )
      | ( X29 = X26 )
      | ( X28
       != ( k1_tarski @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('39',plain,(
    ! [X26: $i,X29: $i] :
      ( ( X29 = X26 )
      | ~ ( r2_hidden @ X29 @ ( k1_tarski @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( sk_B @ sk_B_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('42',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('46',plain,(
    ! [X26: $i,X29: $i] :
      ( ( X29 = X26 )
      | ~ ( r2_hidden @ X29 @ ( k1_tarski @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['44','50'])).

thf('52',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['28','51'])).

thf('53',plain,
    ( sk_B_1
    = ( k5_xboole_0 @ sk_C_2 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['21','52'])).

thf('54',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('55',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['28','51'])).

thf('60',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['28','51'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('61',plain,(
    ! [X31: $i] :
      ( ( k2_tarski @ X31 @ X31 )
      = ( k1_tarski @ X31 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('62',plain,(
    ! [X59: $i,X60: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X59 @ X60 ) )
      = ( k2_xboole_0 @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k3_tarski @ sk_B_1 )
    = sk_A ),
    inference('sup+',[status(thm)],['60','65'])).

thf('67',plain,
    ( ( k1_tarski @ ( k3_tarski @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['59','66'])).

thf('68',plain,(
    ! [X26: $i,X29: $i] :
      ( ( X29 = X26 )
      | ~ ( r2_hidden @ X29 @ ( k1_tarski @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( X0
        = ( k3_tarski @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B_1 @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k4_xboole_0 @ sk_B_1 @ X0 ) )
        = ( k3_tarski @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['58','69'])).

thf('71',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('72',plain,
    ( ( k5_xboole_0 @ sk_C_2 @ ( k1_tarski @ sk_A ) )
    = ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['10','16'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('73',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['28','51'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_2 )
      | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( ( k4_xboole_0 @ sk_B_1 @ sk_C_2 )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['71','78'])).

thf('80',plain,
    ( ~ ( r2_hidden @ ( k3_tarski @ sk_B_1 ) @ sk_C_2 )
    | ( ( k4_xboole_0 @ sk_B_1 @ sk_C_2 )
      = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_B_1 @ sk_C_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','79'])).

thf('81',plain,
    ( sk_B_1
    = ( k5_xboole_0 @ sk_C_2 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['21','52'])).

thf('82',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('83',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ( r2_hidden @ X6 @ ( k5_xboole_0 @ X7 @ X9 ) )
      | ( r2_hidden @ X6 @ X9 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C_2 ) @ sk_B_1 )
    | ( r2_hidden @ ( sk_B @ sk_C_2 ) @ ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['81','84'])).

thf('86',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C_2 ) @ sk_B_1 )
    | ( r2_hidden @ ( sk_B @ sk_C_2 ) @ ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_2 )
    = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ sk_C_2 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['0','3'])).

thf('89',plain,
    ( ( k5_xboole_0 @ sk_C_2 @ ( k1_tarski @ sk_A ) )
    = ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['10','16'])).

thf('90',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_2 )
    = ( k5_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k5_xboole_0 @ sk_C_2 @ ( k1_tarski @ sk_A ) )
    = ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['10','16'])).

thf('92',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['28','51'])).

thf('93',plain,
    ( ( k5_xboole_0 @ sk_C_2 @ sk_B_1 )
    = ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('95',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k5_xboole_0 @ sk_C_2 @ ( k5_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['93','96'])).

thf('98',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_2 )
    = ( k5_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('99',plain,
    ( ( k5_xboole_0 @ sk_C_2 @ ( k3_xboole_0 @ sk_B_1 @ sk_C_2 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('101',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_2 )
    = ( k5_xboole_0 @ sk_C_2 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('103',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('108',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('112',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['106','112'])).

thf('114',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_2 )
    = sk_C_2 ),
    inference(demod,[status(thm)],['101','113'])).

thf('115',plain,
    ( sk_C_2
    = ( k5_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['90','114'])).

thf('116',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('117',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k5_xboole_0 @ X1 @ X0 ) ) @ X0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k5_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ~ ( r2_hidden @ ( sk_B @ sk_C_2 ) @ ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) )
    | ~ ( r2_hidden @ ( sk_B @ ( k5_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ) @ sk_B_1 )
    | ( ( k5_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['115','118'])).

thf('120',plain,
    ( sk_C_2
    = ( k5_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['90','114'])).

thf('121',plain,
    ( sk_C_2
    = ( k5_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['90','114'])).

thf('122',plain,
    ( ~ ( r2_hidden @ ( sk_B @ sk_C_2 ) @ ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) )
    | ~ ( r2_hidden @ ( sk_B @ sk_C_2 ) @ sk_B_1 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['119','120','121'])).

thf('123',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ~ ( r2_hidden @ ( sk_B @ sk_C_2 ) @ ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) )
    | ~ ( r2_hidden @ ( sk_B @ sk_C_2 ) @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('126',plain,(
    ~ ( r2_hidden @ ( sk_B @ sk_C_2 ) @ ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('127',plain,(
    r2_hidden @ ( sk_B @ sk_C_2 ) @ sk_B_1 ),
    inference(clc,[status(thm)],['87','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( X0
        = ( k3_tarski @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('129',plain,
    ( ( sk_B @ sk_C_2 )
    = ( k3_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('131',plain,
    ( ( r2_hidden @ ( k3_tarski @ sk_B_1 ) @ sk_C_2 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    r2_hidden @ ( k3_tarski @ sk_B_1 ) @ sk_C_2 ),
    inference('simplify_reflect-',[status(thm)],['131','132'])).

thf('134',plain,
    ( ( ( k4_xboole_0 @ sk_B_1 @ sk_C_2 )
      = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_B_1 @ sk_C_2 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','133'])).

thf('135',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_C_2 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['106','112'])).

thf('137',plain,(
    sk_B_1 = sk_C_2 ),
    inference(demod,[status(thm)],['53','135','136'])).

thf('138',plain,(
    sk_B_1 != sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['137','138'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.O0OkaslhQ8
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:09:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 0.78/0.98  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.78/0.98  % Solved by: fo/fo7.sh
% 0.78/0.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.78/0.98  % done 1178 iterations in 0.502s
% 0.78/0.98  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.78/0.98  % SZS output start Refutation
% 0.78/0.98  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.78/0.98  thf(sk_A_type, type, sk_A: $i).
% 0.78/0.98  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.78/0.98  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.78/0.98  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.78/0.98  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.78/0.98  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.78/0.98  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.78/0.98  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.78/0.98  thf(sk_B_type, type, sk_B: $i > $i).
% 0.78/0.98  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.78/0.98  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.78/0.98  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.78/0.98  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.78/0.98  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.78/0.98  thf(t44_zfmisc_1, conjecture,
% 0.78/0.98    (![A:$i,B:$i,C:$i]:
% 0.78/0.98     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.78/0.98          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.78/0.98          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.78/0.98  thf(zf_stmt_0, negated_conjecture,
% 0.78/0.98    (~( ![A:$i,B:$i,C:$i]:
% 0.78/0.98        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.78/0.98             ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.78/0.98             ( ( C ) != ( k1_xboole_0 ) ) ) ) )),
% 0.78/0.98    inference('cnf.neg', [status(esa)], [t44_zfmisc_1])).
% 0.78/0.98  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.78/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.98  thf(t95_xboole_1, axiom,
% 0.78/0.98    (![A:$i,B:$i]:
% 0.78/0.98     ( ( k3_xboole_0 @ A @ B ) =
% 0.78/0.98       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.78/0.98  thf('1', plain,
% 0.78/0.98      (![X24 : $i, X25 : $i]:
% 0.78/0.98         ((k3_xboole_0 @ X24 @ X25)
% 0.78/0.98           = (k5_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ 
% 0.78/0.98              (k2_xboole_0 @ X24 @ X25)))),
% 0.78/0.98      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.78/0.98  thf(t91_xboole_1, axiom,
% 0.78/0.98    (![A:$i,B:$i,C:$i]:
% 0.78/0.98     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.78/0.98       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.78/0.98  thf('2', plain,
% 0.78/0.98      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.78/0.98         ((k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ X22)
% 0.78/0.98           = (k5_xboole_0 @ X20 @ (k5_xboole_0 @ X21 @ X22)))),
% 0.78/0.98      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.78/0.98  thf('3', plain,
% 0.78/0.98      (![X24 : $i, X25 : $i]:
% 0.78/0.98         ((k3_xboole_0 @ X24 @ X25)
% 0.78/0.98           = (k5_xboole_0 @ X24 @ 
% 0.78/0.98              (k5_xboole_0 @ X25 @ (k2_xboole_0 @ X24 @ X25))))),
% 0.78/0.98      inference('demod', [status(thm)], ['1', '2'])).
% 0.78/0.98  thf('4', plain,
% 0.78/0.98      (((k3_xboole_0 @ sk_B_1 @ sk_C_2)
% 0.78/0.98         = (k5_xboole_0 @ sk_B_1 @ (k5_xboole_0 @ sk_C_2 @ (k1_tarski @ sk_A))))),
% 0.78/0.98      inference('sup+', [status(thm)], ['0', '3'])).
% 0.78/0.98  thf(t92_xboole_1, axiom,
% 0.78/0.98    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.78/0.98  thf('5', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 0.78/0.98      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.78/0.98  thf('6', plain,
% 0.78/0.98      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.78/0.98         ((k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ X22)
% 0.78/0.98           = (k5_xboole_0 @ X20 @ (k5_xboole_0 @ X21 @ X22)))),
% 0.78/0.98      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.78/0.98  thf('7', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i]:
% 0.78/0.98         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.78/0.98           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.78/0.98      inference('sup+', [status(thm)], ['5', '6'])).
% 0.78/0.98  thf('8', plain,
% 0.78/0.98      (((k5_xboole_0 @ k1_xboole_0 @ 
% 0.78/0.98         (k5_xboole_0 @ sk_C_2 @ (k1_tarski @ sk_A)))
% 0.78/0.98         = (k5_xboole_0 @ sk_B_1 @ (k3_xboole_0 @ sk_B_1 @ sk_C_2)))),
% 0.78/0.98      inference('sup+', [status(thm)], ['4', '7'])).
% 0.78/0.98  thf(t100_xboole_1, axiom,
% 0.78/0.98    (![A:$i,B:$i]:
% 0.78/0.98     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.78/0.98  thf('9', plain,
% 0.78/0.98      (![X14 : $i, X15 : $i]:
% 0.78/0.98         ((k4_xboole_0 @ X14 @ X15)
% 0.78/0.98           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.78/0.98      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.78/0.98  thf('10', plain,
% 0.78/0.98      (((k5_xboole_0 @ k1_xboole_0 @ 
% 0.78/0.98         (k5_xboole_0 @ sk_C_2 @ (k1_tarski @ sk_A)))
% 0.78/0.98         = (k4_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.78/0.98      inference('demod', [status(thm)], ['8', '9'])).
% 0.78/0.98  thf('11', plain,
% 0.78/0.98      (![X24 : $i, X25 : $i]:
% 0.78/0.98         ((k3_xboole_0 @ X24 @ X25)
% 0.78/0.98           = (k5_xboole_0 @ X24 @ 
% 0.78/0.98              (k5_xboole_0 @ X25 @ (k2_xboole_0 @ X24 @ X25))))),
% 0.78/0.98      inference('demod', [status(thm)], ['1', '2'])).
% 0.78/0.98  thf('12', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i]:
% 0.78/0.98         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.78/0.98           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.78/0.98      inference('sup+', [status(thm)], ['5', '6'])).
% 0.78/0.98  thf('13', plain,
% 0.78/0.98      (![X0 : $i]:
% 0.78/0.98         ((k5_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X0))
% 0.78/0.98           = (k3_xboole_0 @ X0 @ X0))),
% 0.78/0.98      inference('sup+', [status(thm)], ['11', '12'])).
% 0.78/0.98  thf(idempotence_k2_xboole_0, axiom,
% 0.78/0.98    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.78/0.98  thf('14', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ X4) = (X4))),
% 0.78/0.98      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.78/0.98  thf(idempotence_k3_xboole_0, axiom,
% 0.78/0.98    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.78/0.98  thf('15', plain, (![X5 : $i]: ((k3_xboole_0 @ X5 @ X5) = (X5))),
% 0.78/0.98      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.78/0.98  thf('16', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.78/0.98      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.78/0.98  thf('17', plain,
% 0.78/0.98      (((k5_xboole_0 @ sk_C_2 @ (k1_tarski @ sk_A))
% 0.78/0.98         = (k4_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.78/0.98      inference('demod', [status(thm)], ['10', '16'])).
% 0.78/0.98  thf('18', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i]:
% 0.78/0.98         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.78/0.98           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.78/0.98      inference('sup+', [status(thm)], ['5', '6'])).
% 0.78/0.98  thf('19', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.78/0.98      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.78/0.98  thf('20', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i]:
% 0.78/0.98         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.78/0.98      inference('demod', [status(thm)], ['18', '19'])).
% 0.78/0.98  thf('21', plain,
% 0.78/0.98      (((k1_tarski @ sk_A)
% 0.78/0.98         = (k5_xboole_0 @ sk_C_2 @ (k4_xboole_0 @ sk_B_1 @ sk_C_2)))),
% 0.78/0.98      inference('sup+', [status(thm)], ['17', '20'])).
% 0.78/0.98  thf('22', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.78/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.98  thf(t7_xboole_1, axiom,
% 0.78/0.98    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.78/0.98  thf('23', plain,
% 0.78/0.98      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 0.78/0.98      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.78/0.98  thf(d10_xboole_0, axiom,
% 0.78/0.98    (![A:$i,B:$i]:
% 0.78/0.98     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.78/0.98  thf('24', plain,
% 0.78/0.98      (![X11 : $i, X13 : $i]:
% 0.78/0.98         (((X11) = (X13))
% 0.78/0.98          | ~ (r1_tarski @ X13 @ X11)
% 0.78/0.98          | ~ (r1_tarski @ X11 @ X13))),
% 0.78/0.98      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.78/0.98  thf('25', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i]:
% 0.78/0.98         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.78/0.98          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 0.78/0.98      inference('sup-', [status(thm)], ['23', '24'])).
% 0.78/0.98  thf('26', plain,
% 0.78/0.98      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.78/0.98        | ((k2_xboole_0 @ sk_B_1 @ sk_C_2) = (sk_B_1)))),
% 0.78/0.98      inference('sup-', [status(thm)], ['22', '25'])).
% 0.78/0.98  thf('27', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.78/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.98  thf('28', plain,
% 0.78/0.98      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.78/0.98        | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 0.78/0.98      inference('demod', [status(thm)], ['26', '27'])).
% 0.78/0.98  thf(t7_xboole_0, axiom,
% 0.78/0.98    (![A:$i]:
% 0.78/0.98     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.78/0.98          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.78/0.98  thf('29', plain,
% 0.78/0.98      (![X10 : $i]:
% 0.78/0.98         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.78/0.98      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.78/0.98  thf('30', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.78/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.98  thf('31', plain,
% 0.78/0.98      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 0.78/0.98      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.78/0.98  thf('32', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.78/0.98      inference('sup+', [status(thm)], ['30', '31'])).
% 0.78/0.98  thf(d3_tarski, axiom,
% 0.78/0.98    (![A:$i,B:$i]:
% 0.78/0.98     ( ( r1_tarski @ A @ B ) <=>
% 0.78/0.98       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.78/0.98  thf('33', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/0.98         (~ (r2_hidden @ X0 @ X1)
% 0.78/0.98          | (r2_hidden @ X0 @ X2)
% 0.78/0.98          | ~ (r1_tarski @ X1 @ X2))),
% 0.78/0.98      inference('cnf', [status(esa)], [d3_tarski])).
% 0.78/0.98  thf('34', plain,
% 0.78/0.98      (![X0 : $i]:
% 0.78/0.98         ((r2_hidden @ X0 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.78/0.98      inference('sup-', [status(thm)], ['32', '33'])).
% 0.78/0.98  thf('35', plain,
% 0.78/0.98      ((((sk_B_1) = (k1_xboole_0))
% 0.78/0.98        | (r2_hidden @ (sk_B @ sk_B_1) @ (k1_tarski @ sk_A)))),
% 0.78/0.98      inference('sup-', [status(thm)], ['29', '34'])).
% 0.78/0.98  thf('36', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.78/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.98  thf('37', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (k1_tarski @ sk_A))),
% 0.78/0.98      inference('simplify_reflect-', [status(thm)], ['35', '36'])).
% 0.78/0.98  thf(d1_tarski, axiom,
% 0.78/0.98    (![A:$i,B:$i]:
% 0.78/0.98     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.78/0.98       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.78/0.98  thf('38', plain,
% 0.78/0.98      (![X26 : $i, X28 : $i, X29 : $i]:
% 0.78/0.98         (~ (r2_hidden @ X29 @ X28)
% 0.78/0.98          | ((X29) = (X26))
% 0.78/0.98          | ((X28) != (k1_tarski @ X26)))),
% 0.78/0.98      inference('cnf', [status(esa)], [d1_tarski])).
% 0.78/0.98  thf('39', plain,
% 0.78/0.98      (![X26 : $i, X29 : $i]:
% 0.78/0.98         (((X29) = (X26)) | ~ (r2_hidden @ X29 @ (k1_tarski @ X26)))),
% 0.78/0.98      inference('simplify', [status(thm)], ['38'])).
% 0.78/0.98  thf('40', plain, (((sk_B @ sk_B_1) = (sk_A))),
% 0.78/0.98      inference('sup-', [status(thm)], ['37', '39'])).
% 0.78/0.98  thf('41', plain,
% 0.78/0.98      (![X10 : $i]:
% 0.78/0.98         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.78/0.98      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.78/0.98  thf('42', plain,
% 0.78/0.98      (((r2_hidden @ sk_A @ sk_B_1) | ((sk_B_1) = (k1_xboole_0)))),
% 0.78/0.98      inference('sup+', [status(thm)], ['40', '41'])).
% 0.78/0.98  thf('43', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.78/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.98  thf('44', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.78/0.98      inference('simplify_reflect-', [status(thm)], ['42', '43'])).
% 0.78/0.98  thf('45', plain,
% 0.78/0.98      (![X1 : $i, X3 : $i]:
% 0.78/0.98         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.78/0.98      inference('cnf', [status(esa)], [d3_tarski])).
% 0.78/0.98  thf('46', plain,
% 0.78/0.98      (![X26 : $i, X29 : $i]:
% 0.78/0.98         (((X29) = (X26)) | ~ (r2_hidden @ X29 @ (k1_tarski @ X26)))),
% 0.78/0.98      inference('simplify', [status(thm)], ['38'])).
% 0.78/0.98  thf('47', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i]:
% 0.78/0.98         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.78/0.98          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.78/0.98      inference('sup-', [status(thm)], ['45', '46'])).
% 0.78/0.98  thf('48', plain,
% 0.78/0.98      (![X1 : $i, X3 : $i]:
% 0.78/0.98         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.78/0.98      inference('cnf', [status(esa)], [d3_tarski])).
% 0.78/0.98  thf('49', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i]:
% 0.78/0.98         (~ (r2_hidden @ X0 @ X1)
% 0.78/0.98          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.78/0.98          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.78/0.98      inference('sup-', [status(thm)], ['47', '48'])).
% 0.78/0.98  thf('50', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i]:
% 0.78/0.98         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.78/0.98      inference('simplify', [status(thm)], ['49'])).
% 0.78/0.98  thf('51', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.78/0.98      inference('sup-', [status(thm)], ['44', '50'])).
% 0.78/0.98  thf('52', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.78/0.98      inference('demod', [status(thm)], ['28', '51'])).
% 0.78/0.98  thf('53', plain,
% 0.78/0.98      (((sk_B_1) = (k5_xboole_0 @ sk_C_2 @ (k4_xboole_0 @ sk_B_1 @ sk_C_2)))),
% 0.78/0.98      inference('demod', [status(thm)], ['21', '52'])).
% 0.78/0.98  thf('54', plain,
% 0.78/0.98      (![X10 : $i]:
% 0.78/0.98         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.78/0.98      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.78/0.98  thf(t36_xboole_1, axiom,
% 0.78/0.98    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.78/0.98  thf('55', plain,
% 0.78/0.98      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 0.78/0.98      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.78/0.98  thf('56', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/0.98         (~ (r2_hidden @ X0 @ X1)
% 0.78/0.98          | (r2_hidden @ X0 @ X2)
% 0.78/0.98          | ~ (r1_tarski @ X1 @ X2))),
% 0.78/0.98      inference('cnf', [status(esa)], [d3_tarski])).
% 0.78/0.98  thf('57', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/0.98         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.78/0.98      inference('sup-', [status(thm)], ['55', '56'])).
% 0.78/0.98  thf('58', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i]:
% 0.78/0.98         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.78/0.98          | (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.78/0.98      inference('sup-', [status(thm)], ['54', '57'])).
% 0.78/0.98  thf('59', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.78/0.98      inference('demod', [status(thm)], ['28', '51'])).
% 0.78/0.98  thf('60', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.78/0.98      inference('demod', [status(thm)], ['28', '51'])).
% 0.78/0.98  thf(t69_enumset1, axiom,
% 0.78/0.98    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.78/0.98  thf('61', plain,
% 0.78/0.98      (![X31 : $i]: ((k2_tarski @ X31 @ X31) = (k1_tarski @ X31))),
% 0.78/0.98      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.78/0.98  thf(l51_zfmisc_1, axiom,
% 0.78/0.98    (![A:$i,B:$i]:
% 0.78/0.98     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.78/0.98  thf('62', plain,
% 0.78/0.98      (![X59 : $i, X60 : $i]:
% 0.78/0.98         ((k3_tarski @ (k2_tarski @ X59 @ X60)) = (k2_xboole_0 @ X59 @ X60))),
% 0.78/0.98      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.78/0.98  thf('63', plain,
% 0.78/0.98      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.78/0.98      inference('sup+', [status(thm)], ['61', '62'])).
% 0.78/0.98  thf('64', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ X4) = (X4))),
% 0.78/0.98      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.78/0.98  thf('65', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.78/0.98      inference('demod', [status(thm)], ['63', '64'])).
% 0.78/0.98  thf('66', plain, (((k3_tarski @ sk_B_1) = (sk_A))),
% 0.78/0.98      inference('sup+', [status(thm)], ['60', '65'])).
% 0.78/0.98  thf('67', plain, (((k1_tarski @ (k3_tarski @ sk_B_1)) = (sk_B_1))),
% 0.78/0.98      inference('demod', [status(thm)], ['59', '66'])).
% 0.78/0.98  thf('68', plain,
% 0.78/0.98      (![X26 : $i, X29 : $i]:
% 0.78/0.98         (((X29) = (X26)) | ~ (r2_hidden @ X29 @ (k1_tarski @ X26)))),
% 0.78/0.98      inference('simplify', [status(thm)], ['38'])).
% 0.78/0.98  thf('69', plain,
% 0.78/0.98      (![X0 : $i]:
% 0.78/0.98         (~ (r2_hidden @ X0 @ sk_B_1) | ((X0) = (k3_tarski @ sk_B_1)))),
% 0.78/0.98      inference('sup-', [status(thm)], ['67', '68'])).
% 0.78/0.98  thf('70', plain,
% 0.78/0.98      (![X0 : $i]:
% 0.78/0.98         (((k4_xboole_0 @ sk_B_1 @ X0) = (k1_xboole_0))
% 0.78/0.98          | ((sk_B @ (k4_xboole_0 @ sk_B_1 @ X0)) = (k3_tarski @ sk_B_1)))),
% 0.78/0.98      inference('sup-', [status(thm)], ['58', '69'])).
% 0.78/0.98  thf('71', plain,
% 0.78/0.98      (![X10 : $i]:
% 0.78/0.98         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.78/0.98      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.78/0.98  thf('72', plain,
% 0.78/0.98      (((k5_xboole_0 @ sk_C_2 @ (k1_tarski @ sk_A))
% 0.78/0.98         = (k4_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.78/0.98      inference('demod', [status(thm)], ['10', '16'])).
% 0.78/0.98  thf(t1_xboole_0, axiom,
% 0.78/0.98    (![A:$i,B:$i,C:$i]:
% 0.78/0.98     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.78/0.98       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.78/0.98  thf('73', plain,
% 0.78/0.98      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.78/0.98         (~ (r2_hidden @ X6 @ X7)
% 0.78/0.98          | ~ (r2_hidden @ X6 @ X8)
% 0.78/0.98          | ~ (r2_hidden @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.78/0.98      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.78/0.98  thf('74', plain,
% 0.78/0.98      (![X0 : $i]:
% 0.78/0.98         (~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_B_1 @ sk_C_2))
% 0.78/0.98          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.78/0.98          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 0.78/0.98      inference('sup-', [status(thm)], ['72', '73'])).
% 0.78/0.98  thf('75', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.78/0.98      inference('demod', [status(thm)], ['28', '51'])).
% 0.78/0.98  thf('76', plain,
% 0.78/0.98      (![X0 : $i]:
% 0.78/0.98         (~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_B_1 @ sk_C_2))
% 0.78/0.98          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.78/0.98          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 0.78/0.98      inference('demod', [status(thm)], ['74', '75'])).
% 0.78/0.98  thf('77', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/0.98         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.78/0.98      inference('sup-', [status(thm)], ['55', '56'])).
% 0.78/0.98  thf('78', plain,
% 0.78/0.98      (![X0 : $i]:
% 0.78/0.98         (~ (r2_hidden @ X0 @ sk_C_2)
% 0.78/0.98          | ~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_B_1 @ sk_C_2)))),
% 0.78/0.98      inference('clc', [status(thm)], ['76', '77'])).
% 0.78/0.98  thf('79', plain,
% 0.78/0.98      ((((k4_xboole_0 @ sk_B_1 @ sk_C_2) = (k1_xboole_0))
% 0.78/0.98        | ~ (r2_hidden @ (sk_B @ (k4_xboole_0 @ sk_B_1 @ sk_C_2)) @ sk_C_2))),
% 0.78/0.98      inference('sup-', [status(thm)], ['71', '78'])).
% 0.78/0.98  thf('80', plain,
% 0.78/0.98      ((~ (r2_hidden @ (k3_tarski @ sk_B_1) @ sk_C_2)
% 0.78/0.98        | ((k4_xboole_0 @ sk_B_1 @ sk_C_2) = (k1_xboole_0))
% 0.78/0.98        | ((k4_xboole_0 @ sk_B_1 @ sk_C_2) = (k1_xboole_0)))),
% 0.78/0.98      inference('sup-', [status(thm)], ['70', '79'])).
% 0.78/0.98  thf('81', plain,
% 0.78/0.98      (((sk_B_1) = (k5_xboole_0 @ sk_C_2 @ (k4_xboole_0 @ sk_B_1 @ sk_C_2)))),
% 0.78/0.98      inference('demod', [status(thm)], ['21', '52'])).
% 0.78/0.98  thf('82', plain,
% 0.78/0.98      (![X10 : $i]:
% 0.78/0.98         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.78/0.98      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.78/0.98  thf('83', plain,
% 0.78/0.98      (![X6 : $i, X7 : $i, X9 : $i]:
% 0.78/0.98         ((r2_hidden @ X6 @ (k5_xboole_0 @ X7 @ X9))
% 0.78/0.98          | (r2_hidden @ X6 @ X9)
% 0.78/0.98          | ~ (r2_hidden @ X6 @ X7))),
% 0.78/0.98      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.78/0.98  thf('84', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i]:
% 0.78/0.98         (((X0) = (k1_xboole_0))
% 0.78/0.98          | (r2_hidden @ (sk_B @ X0) @ X1)
% 0.78/0.98          | (r2_hidden @ (sk_B @ X0) @ (k5_xboole_0 @ X0 @ X1)))),
% 0.78/0.98      inference('sup-', [status(thm)], ['82', '83'])).
% 0.78/0.98  thf('85', plain,
% 0.78/0.98      (((r2_hidden @ (sk_B @ sk_C_2) @ sk_B_1)
% 0.78/0.98        | (r2_hidden @ (sk_B @ sk_C_2) @ (k4_xboole_0 @ sk_B_1 @ sk_C_2))
% 0.78/0.98        | ((sk_C_2) = (k1_xboole_0)))),
% 0.78/0.98      inference('sup+', [status(thm)], ['81', '84'])).
% 0.78/0.98  thf('86', plain, (((sk_C_2) != (k1_xboole_0))),
% 0.78/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.98  thf('87', plain,
% 0.78/0.98      (((r2_hidden @ (sk_B @ sk_C_2) @ sk_B_1)
% 0.78/0.98        | (r2_hidden @ (sk_B @ sk_C_2) @ (k4_xboole_0 @ sk_B_1 @ sk_C_2)))),
% 0.78/0.98      inference('simplify_reflect-', [status(thm)], ['85', '86'])).
% 0.78/0.98  thf('88', plain,
% 0.78/0.98      (((k3_xboole_0 @ sk_B_1 @ sk_C_2)
% 0.78/0.98         = (k5_xboole_0 @ sk_B_1 @ (k5_xboole_0 @ sk_C_2 @ (k1_tarski @ sk_A))))),
% 0.78/0.98      inference('sup+', [status(thm)], ['0', '3'])).
% 0.78/0.98  thf('89', plain,
% 0.78/0.98      (((k5_xboole_0 @ sk_C_2 @ (k1_tarski @ sk_A))
% 0.78/0.98         = (k4_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.78/0.98      inference('demod', [status(thm)], ['10', '16'])).
% 0.78/0.98  thf('90', plain,
% 0.78/0.98      (((k3_xboole_0 @ sk_B_1 @ sk_C_2)
% 0.78/0.98         = (k5_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ sk_B_1 @ sk_C_2)))),
% 0.78/0.98      inference('demod', [status(thm)], ['88', '89'])).
% 0.78/0.98  thf('91', plain,
% 0.78/0.98      (((k5_xboole_0 @ sk_C_2 @ (k1_tarski @ sk_A))
% 0.78/0.98         = (k4_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.78/0.98      inference('demod', [status(thm)], ['10', '16'])).
% 0.78/0.98  thf('92', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.78/0.98      inference('demod', [status(thm)], ['28', '51'])).
% 0.78/0.98  thf('93', plain,
% 0.78/0.98      (((k5_xboole_0 @ sk_C_2 @ sk_B_1) = (k4_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.78/0.98      inference('demod', [status(thm)], ['91', '92'])).
% 0.78/0.98  thf('94', plain,
% 0.78/0.98      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.78/0.98         ((k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ X22)
% 0.78/0.98           = (k5_xboole_0 @ X20 @ (k5_xboole_0 @ X21 @ X22)))),
% 0.78/0.98      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.78/0.98  thf('95', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 0.78/0.98      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.78/0.98  thf('96', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i]:
% 0.78/0.98         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 0.78/0.98           = (k1_xboole_0))),
% 0.78/0.98      inference('sup+', [status(thm)], ['94', '95'])).
% 0.78/0.98  thf('97', plain,
% 0.78/0.98      (((k5_xboole_0 @ sk_C_2 @ 
% 0.78/0.98         (k5_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ sk_B_1 @ sk_C_2)))
% 0.78/0.98         = (k1_xboole_0))),
% 0.78/0.98      inference('sup+', [status(thm)], ['93', '96'])).
% 0.78/0.98  thf('98', plain,
% 0.78/0.98      (((k3_xboole_0 @ sk_B_1 @ sk_C_2)
% 0.78/0.98         = (k5_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ sk_B_1 @ sk_C_2)))),
% 0.78/0.98      inference('demod', [status(thm)], ['88', '89'])).
% 0.78/0.98  thf('99', plain,
% 0.78/0.98      (((k5_xboole_0 @ sk_C_2 @ (k3_xboole_0 @ sk_B_1 @ sk_C_2))
% 0.78/0.98         = (k1_xboole_0))),
% 0.78/0.98      inference('demod', [status(thm)], ['97', '98'])).
% 0.78/0.98  thf('100', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i]:
% 0.78/0.98         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.78/0.98      inference('demod', [status(thm)], ['18', '19'])).
% 0.78/0.98  thf('101', plain,
% 0.78/0.98      (((k3_xboole_0 @ sk_B_1 @ sk_C_2) = (k5_xboole_0 @ sk_C_2 @ k1_xboole_0))),
% 0.78/0.98      inference('sup+', [status(thm)], ['99', '100'])).
% 0.78/0.98  thf('102', plain, (![X5 : $i]: ((k3_xboole_0 @ X5 @ X5) = (X5))),
% 0.78/0.98      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.78/0.98  thf('103', plain,
% 0.78/0.98      (![X14 : $i, X15 : $i]:
% 0.78/0.98         ((k4_xboole_0 @ X14 @ X15)
% 0.78/0.98           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.78/0.98      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.78/0.98  thf('104', plain,
% 0.78/0.98      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.78/0.98      inference('sup+', [status(thm)], ['102', '103'])).
% 0.78/0.98  thf('105', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 0.78/0.98      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.78/0.98  thf('106', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.78/0.98      inference('sup+', [status(thm)], ['104', '105'])).
% 0.78/0.98  thf('107', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ X4) = (X4))),
% 0.78/0.98      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.78/0.98  thf('108', plain,
% 0.78/0.98      (![X24 : $i, X25 : $i]:
% 0.78/0.98         ((k3_xboole_0 @ X24 @ X25)
% 0.78/0.98           = (k5_xboole_0 @ X24 @ 
% 0.78/0.98              (k5_xboole_0 @ X25 @ (k2_xboole_0 @ X24 @ X25))))),
% 0.78/0.98      inference('demod', [status(thm)], ['1', '2'])).
% 0.78/0.98  thf('109', plain,
% 0.78/0.98      (![X0 : $i]:
% 0.78/0.98         ((k3_xboole_0 @ X0 @ X0)
% 0.78/0.98           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.78/0.98      inference('sup+', [status(thm)], ['107', '108'])).
% 0.78/0.98  thf('110', plain, (![X5 : $i]: ((k3_xboole_0 @ X5 @ X5) = (X5))),
% 0.78/0.98      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.78/0.98  thf('111', plain,
% 0.78/0.98      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.78/0.98      inference('sup+', [status(thm)], ['102', '103'])).
% 0.78/0.98  thf('112', plain,
% 0.78/0.98      (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.78/0.98      inference('demod', [status(thm)], ['109', '110', '111'])).
% 0.78/0.98  thf('113', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.78/0.98      inference('sup+', [status(thm)], ['106', '112'])).
% 0.78/0.98  thf('114', plain, (((k3_xboole_0 @ sk_B_1 @ sk_C_2) = (sk_C_2))),
% 0.78/0.98      inference('demod', [status(thm)], ['101', '113'])).
% 0.78/0.98  thf('115', plain,
% 0.78/0.98      (((sk_C_2) = (k5_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ sk_B_1 @ sk_C_2)))),
% 0.78/0.98      inference('demod', [status(thm)], ['90', '114'])).
% 0.78/0.98  thf('116', plain,
% 0.78/0.98      (![X10 : $i]:
% 0.78/0.98         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.78/0.98      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.78/0.98  thf('117', plain,
% 0.78/0.98      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.78/0.98         (~ (r2_hidden @ X6 @ X7)
% 0.78/0.98          | ~ (r2_hidden @ X6 @ X8)
% 0.78/0.98          | ~ (r2_hidden @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.78/0.98      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.78/0.98  thf('118', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i]:
% 0.78/0.98         (((k5_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.78/0.98          | ~ (r2_hidden @ (sk_B @ (k5_xboole_0 @ X1 @ X0)) @ X0)
% 0.78/0.98          | ~ (r2_hidden @ (sk_B @ (k5_xboole_0 @ X1 @ X0)) @ X1))),
% 0.78/0.98      inference('sup-', [status(thm)], ['116', '117'])).
% 0.78/0.98  thf('119', plain,
% 0.78/0.98      ((~ (r2_hidden @ (sk_B @ sk_C_2) @ (k4_xboole_0 @ sk_B_1 @ sk_C_2))
% 0.78/0.98        | ~ (r2_hidden @ 
% 0.78/0.98             (sk_B @ (k5_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ sk_B_1 @ sk_C_2))) @ 
% 0.78/0.98             sk_B_1)
% 0.78/0.98        | ((k5_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ sk_B_1 @ sk_C_2))
% 0.78/0.98            = (k1_xboole_0)))),
% 0.78/0.98      inference('sup-', [status(thm)], ['115', '118'])).
% 0.78/0.98  thf('120', plain,
% 0.78/0.98      (((sk_C_2) = (k5_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ sk_B_1 @ sk_C_2)))),
% 0.78/0.98      inference('demod', [status(thm)], ['90', '114'])).
% 0.78/0.98  thf('121', plain,
% 0.78/0.98      (((sk_C_2) = (k5_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ sk_B_1 @ sk_C_2)))),
% 0.78/0.98      inference('demod', [status(thm)], ['90', '114'])).
% 0.78/0.98  thf('122', plain,
% 0.78/0.98      ((~ (r2_hidden @ (sk_B @ sk_C_2) @ (k4_xboole_0 @ sk_B_1 @ sk_C_2))
% 0.78/0.98        | ~ (r2_hidden @ (sk_B @ sk_C_2) @ sk_B_1)
% 0.78/0.98        | ((sk_C_2) = (k1_xboole_0)))),
% 0.78/0.98      inference('demod', [status(thm)], ['119', '120', '121'])).
% 0.78/0.98  thf('123', plain, (((sk_C_2) != (k1_xboole_0))),
% 0.78/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.98  thf('124', plain,
% 0.78/0.98      ((~ (r2_hidden @ (sk_B @ sk_C_2) @ (k4_xboole_0 @ sk_B_1 @ sk_C_2))
% 0.78/0.98        | ~ (r2_hidden @ (sk_B @ sk_C_2) @ sk_B_1))),
% 0.78/0.98      inference('simplify_reflect-', [status(thm)], ['122', '123'])).
% 0.78/0.98  thf('125', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/0.98         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.78/0.98      inference('sup-', [status(thm)], ['55', '56'])).
% 0.78/0.98  thf('126', plain,
% 0.78/0.98      (~ (r2_hidden @ (sk_B @ sk_C_2) @ (k4_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.78/0.98      inference('clc', [status(thm)], ['124', '125'])).
% 0.78/0.98  thf('127', plain, ((r2_hidden @ (sk_B @ sk_C_2) @ sk_B_1)),
% 0.78/0.98      inference('clc', [status(thm)], ['87', '126'])).
% 0.78/0.98  thf('128', plain,
% 0.78/0.98      (![X0 : $i]:
% 0.78/0.98         (~ (r2_hidden @ X0 @ sk_B_1) | ((X0) = (k3_tarski @ sk_B_1)))),
% 0.78/0.98      inference('sup-', [status(thm)], ['67', '68'])).
% 0.78/0.98  thf('129', plain, (((sk_B @ sk_C_2) = (k3_tarski @ sk_B_1))),
% 0.78/0.98      inference('sup-', [status(thm)], ['127', '128'])).
% 0.78/0.98  thf('130', plain,
% 0.78/0.98      (![X10 : $i]:
% 0.78/0.98         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.78/0.98      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.78/0.98  thf('131', plain,
% 0.78/0.98      (((r2_hidden @ (k3_tarski @ sk_B_1) @ sk_C_2)
% 0.78/0.98        | ((sk_C_2) = (k1_xboole_0)))),
% 0.78/0.98      inference('sup+', [status(thm)], ['129', '130'])).
% 0.78/0.98  thf('132', plain, (((sk_C_2) != (k1_xboole_0))),
% 0.78/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.98  thf('133', plain, ((r2_hidden @ (k3_tarski @ sk_B_1) @ sk_C_2)),
% 0.78/0.98      inference('simplify_reflect-', [status(thm)], ['131', '132'])).
% 0.78/0.98  thf('134', plain,
% 0.78/0.98      ((((k4_xboole_0 @ sk_B_1 @ sk_C_2) = (k1_xboole_0))
% 0.78/0.98        | ((k4_xboole_0 @ sk_B_1 @ sk_C_2) = (k1_xboole_0)))),
% 0.78/0.98      inference('demod', [status(thm)], ['80', '133'])).
% 0.78/0.98  thf('135', plain, (((k4_xboole_0 @ sk_B_1 @ sk_C_2) = (k1_xboole_0))),
% 0.78/0.98      inference('simplify', [status(thm)], ['134'])).
% 0.78/0.98  thf('136', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.78/0.98      inference('sup+', [status(thm)], ['106', '112'])).
% 0.78/0.98  thf('137', plain, (((sk_B_1) = (sk_C_2))),
% 0.78/0.98      inference('demod', [status(thm)], ['53', '135', '136'])).
% 0.78/0.98  thf('138', plain, (((sk_B_1) != (sk_C_2))),
% 0.78/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.98  thf('139', plain, ($false),
% 0.78/0.98      inference('simplify_reflect-', [status(thm)], ['137', '138'])).
% 0.78/0.98  
% 0.78/0.98  % SZS output end Refutation
% 0.78/0.98  
% 0.78/0.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

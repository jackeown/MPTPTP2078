%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LSv8wiUVoK

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:06 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 324 expanded)
%              Number of leaves         :   28 ( 112 expanded)
%              Depth                    :   16
%              Number of atoms          :  818 (2433 expanded)
%              Number of equality atoms :   82 ( 252 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t13_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t13_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k2_xboole_0 @ X28 @ X29 )
      = ( k5_xboole_0 @ X28 @ ( k4_xboole_0 @ X29 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('2',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('5',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X23 @ X24 ) @ X24 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('6',plain,(
    ! [X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X15 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('7',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k3_xboole_0 @ X11 @ X14 ) )
      | ~ ( r1_xboole_0 @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('12',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X20 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','17'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X25 @ X26 ) @ X27 )
      = ( k5_xboole_0 @ X25 @ ( k5_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('22',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','24'])).

thf('26',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['0','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','17'])).

thf('28',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C @ X12 @ X11 ) @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('30',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('31',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('33',plain,(
    ! [X42: $i,X44: $i,X45: $i] :
      ( ~ ( r2_hidden @ X45 @ X44 )
      | ( X45 = X42 )
      | ( X44
       != ( k1_tarski @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('34',plain,(
    ! [X42: $i,X45: $i] :
      ( ( X45 = X42 )
      | ~ ( r2_hidden @ X45 @ ( k1_tarski @ X42 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C @ X12 @ X11 ) @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('37',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('38',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ sk_B_1 ) )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['28','47'])).

thf('49',plain,(
    ! [X42: $i,X45: $i] :
      ( ( X45 = X42 )
      | ~ ( r2_hidden @ X45 @ ( k1_tarski @ X42 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('50',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ sk_B_1 ) )
    | ( sk_A = sk_B_1 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( X43 != X42 )
      | ( r2_hidden @ X43 @ X44 )
      | ( X44
       != ( k1_tarski @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('54',plain,(
    ! [X42: $i] :
      ( r2_hidden @ X42 @ ( k1_tarski @ X42 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('56',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k3_xboole_0 @ X11 @ X14 ) )
      | ~ ( r1_xboole_0 @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','58'])).

thf('60',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['50','51'])).

thf('61',plain,(
    ! [X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X15 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('62',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k2_xboole_0 @ X28 @ X29 )
      = ( k5_xboole_0 @ X28 @ ( k4_xboole_0 @ X29 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X23 @ X24 ) @ X24 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('78',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k3_xboole_0 @ X11 @ X14 ) )
      | ~ ( r1_xboole_0 @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('82',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C @ X12 @ X11 ) @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('84',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k3_xboole_0 @ X11 @ X14 ) )
      | ~ ( r1_xboole_0 @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','86'])).

thf('88',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('91',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X23 @ X24 ) @ X24 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('93',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    $false ),
    inference(demod,[status(thm)],['59','60','93'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LSv8wiUVoK
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:36:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.37/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.60  % Solved by: fo/fo7.sh
% 0.37/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.60  % done 517 iterations in 0.156s
% 0.37/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.60  % SZS output start Refutation
% 0.37/0.60  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.37/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.60  thf(sk_B_type, type, sk_B: $i > $i).
% 0.37/0.60  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.60  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.37/0.60  thf(t13_zfmisc_1, conjecture,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.37/0.60         ( k1_tarski @ A ) ) =>
% 0.37/0.60       ( ( A ) = ( B ) ) ))).
% 0.37/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.60    (~( ![A:$i,B:$i]:
% 0.37/0.60        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.37/0.60            ( k1_tarski @ A ) ) =>
% 0.37/0.60          ( ( A ) = ( B ) ) ) )),
% 0.37/0.60    inference('cnf.neg', [status(esa)], [t13_zfmisc_1])).
% 0.37/0.60  thf('0', plain,
% 0.37/0.60      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.37/0.60         = (k1_tarski @ sk_A))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf(t98_xboole_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.37/0.60  thf('1', plain,
% 0.37/0.60      (![X28 : $i, X29 : $i]:
% 0.37/0.60         ((k2_xboole_0 @ X28 @ X29)
% 0.37/0.60           = (k5_xboole_0 @ X28 @ (k4_xboole_0 @ X29 @ X28)))),
% 0.37/0.60      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.37/0.60  thf(idempotence_k3_xboole_0, axiom,
% 0.37/0.60    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.37/0.60  thf('2', plain, (![X10 : $i]: ((k3_xboole_0 @ X10 @ X10) = (X10))),
% 0.37/0.60      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.37/0.60  thf(t100_xboole_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.60  thf('3', plain,
% 0.37/0.60      (![X16 : $i, X17 : $i]:
% 0.37/0.60         ((k4_xboole_0 @ X16 @ X17)
% 0.37/0.60           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 0.37/0.60      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.60  thf('4', plain,
% 0.37/0.60      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.60      inference('sup+', [status(thm)], ['2', '3'])).
% 0.37/0.60  thf(t79_xboole_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.37/0.60  thf('5', plain,
% 0.37/0.60      (![X23 : $i, X24 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X23 @ X24) @ X24)),
% 0.37/0.60      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.37/0.60  thf(t7_xboole_0, axiom,
% 0.37/0.60    (![A:$i]:
% 0.37/0.60     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.37/0.60          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.37/0.60  thf('6', plain,
% 0.37/0.60      (![X15 : $i]:
% 0.37/0.60         (((X15) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X15) @ X15))),
% 0.37/0.60      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.37/0.60  thf(t4_xboole_0, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.37/0.60            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.37/0.60       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.37/0.60            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.37/0.60  thf('7', plain,
% 0.37/0.60      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.37/0.60         (~ (r2_hidden @ X13 @ (k3_xboole_0 @ X11 @ X14))
% 0.37/0.60          | ~ (r1_xboole_0 @ X11 @ X14))),
% 0.37/0.60      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.37/0.60  thf('8', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.37/0.60      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.60  thf('9', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.37/0.60      inference('sup-', [status(thm)], ['5', '8'])).
% 0.37/0.60  thf(commutativity_k3_xboole_0, axiom,
% 0.37/0.60    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.37/0.60  thf('10', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.60  thf('11', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.37/0.60      inference('demod', [status(thm)], ['9', '10'])).
% 0.37/0.60  thf(t36_xboole_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.37/0.60  thf('12', plain,
% 0.37/0.60      (![X20 : $i, X21 : $i]: (r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X20)),
% 0.37/0.60      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.37/0.60  thf(t28_xboole_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.37/0.60  thf('13', plain,
% 0.37/0.60      (![X18 : $i, X19 : $i]:
% 0.37/0.60         (((k3_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_tarski @ X18 @ X19))),
% 0.37/0.60      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.60  thf('14', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.37/0.60           = (k4_xboole_0 @ X0 @ X1))),
% 0.37/0.60      inference('sup-', [status(thm)], ['12', '13'])).
% 0.37/0.60  thf('15', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.60  thf('16', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.37/0.60           = (k4_xboole_0 @ X0 @ X1))),
% 0.37/0.60      inference('demod', [status(thm)], ['14', '15'])).
% 0.37/0.60  thf('17', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.37/0.60      inference('sup+', [status(thm)], ['11', '16'])).
% 0.37/0.60  thf('18', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.60      inference('demod', [status(thm)], ['4', '17'])).
% 0.37/0.60  thf(t91_xboole_1, axiom,
% 0.37/0.60    (![A:$i,B:$i,C:$i]:
% 0.37/0.60     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.37/0.60       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.37/0.60  thf('19', plain,
% 0.37/0.60      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.37/0.60         ((k5_xboole_0 @ (k5_xboole_0 @ X25 @ X26) @ X27)
% 0.37/0.60           = (k5_xboole_0 @ X25 @ (k5_xboole_0 @ X26 @ X27)))),
% 0.37/0.60      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.37/0.60  thf('20', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.37/0.60           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.37/0.60      inference('sup+', [status(thm)], ['18', '19'])).
% 0.37/0.60  thf(commutativity_k5_xboole_0, axiom,
% 0.37/0.60    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.37/0.60  thf('21', plain,
% 0.37/0.60      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.37/0.60      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.37/0.60  thf(t5_boole, axiom,
% 0.37/0.60    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.37/0.60  thf('22', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.37/0.60      inference('cnf', [status(esa)], [t5_boole])).
% 0.37/0.60  thf('23', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.37/0.60      inference('sup+', [status(thm)], ['21', '22'])).
% 0.37/0.60  thf('24', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.37/0.60      inference('demod', [status(thm)], ['20', '23'])).
% 0.37/0.60  thf('25', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         ((k4_xboole_0 @ X0 @ X1)
% 0.37/0.60           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.37/0.60      inference('sup+', [status(thm)], ['1', '24'])).
% 0.37/0.60  thf('26', plain,
% 0.37/0.60      (((k4_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A))
% 0.37/0.60         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.37/0.60      inference('sup+', [status(thm)], ['0', '25'])).
% 0.37/0.60  thf('27', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.60      inference('demod', [status(thm)], ['4', '17'])).
% 0.37/0.60  thf('28', plain,
% 0.37/0.60      (((k4_xboole_0 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_A))
% 0.37/0.60         = (k1_xboole_0))),
% 0.37/0.60      inference('demod', [status(thm)], ['26', '27'])).
% 0.37/0.60  thf('29', plain,
% 0.37/0.60      (![X11 : $i, X12 : $i]:
% 0.37/0.60         ((r1_xboole_0 @ X11 @ X12)
% 0.37/0.60          | (r2_hidden @ (sk_C @ X12 @ X11) @ (k3_xboole_0 @ X11 @ X12)))),
% 0.37/0.60      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.37/0.60  thf(d4_xboole_0, axiom,
% 0.37/0.60    (![A:$i,B:$i,C:$i]:
% 0.37/0.60     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.37/0.60       ( ![D:$i]:
% 0.37/0.60         ( ( r2_hidden @ D @ C ) <=>
% 0.37/0.60           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.37/0.60  thf('30', plain,
% 0.37/0.60      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.37/0.60         (~ (r2_hidden @ X8 @ X7)
% 0.37/0.60          | (r2_hidden @ X8 @ X6)
% 0.37/0.60          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 0.37/0.60      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.37/0.60  thf('31', plain,
% 0.37/0.60      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.37/0.60         ((r2_hidden @ X8 @ X6) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.37/0.60      inference('simplify', [status(thm)], ['30'])).
% 0.37/0.60  thf('32', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C @ X0 @ X1) @ X0))),
% 0.37/0.60      inference('sup-', [status(thm)], ['29', '31'])).
% 0.37/0.60  thf(d1_tarski, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.37/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.37/0.60  thf('33', plain,
% 0.37/0.60      (![X42 : $i, X44 : $i, X45 : $i]:
% 0.37/0.60         (~ (r2_hidden @ X45 @ X44)
% 0.37/0.60          | ((X45) = (X42))
% 0.37/0.60          | ((X44) != (k1_tarski @ X42)))),
% 0.37/0.60      inference('cnf', [status(esa)], [d1_tarski])).
% 0.37/0.60  thf('34', plain,
% 0.37/0.60      (![X42 : $i, X45 : $i]:
% 0.37/0.60         (((X45) = (X42)) | ~ (r2_hidden @ X45 @ (k1_tarski @ X42)))),
% 0.37/0.60      inference('simplify', [status(thm)], ['33'])).
% 0.37/0.60  thf('35', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.37/0.60          | ((sk_C @ (k1_tarski @ X0) @ X1) = (X0)))),
% 0.37/0.60      inference('sup-', [status(thm)], ['32', '34'])).
% 0.37/0.60  thf('36', plain,
% 0.37/0.60      (![X11 : $i, X12 : $i]:
% 0.37/0.60         ((r1_xboole_0 @ X11 @ X12)
% 0.37/0.60          | (r2_hidden @ (sk_C @ X12 @ X11) @ (k3_xboole_0 @ X11 @ X12)))),
% 0.37/0.60      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.37/0.60  thf('37', plain,
% 0.37/0.60      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.37/0.60         (~ (r2_hidden @ X8 @ X7)
% 0.37/0.60          | (r2_hidden @ X8 @ X5)
% 0.37/0.60          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 0.37/0.60      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.37/0.60  thf('38', plain,
% 0.37/0.60      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.37/0.60         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.37/0.60      inference('simplify', [status(thm)], ['37'])).
% 0.37/0.60  thf('39', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 0.37/0.60      inference('sup-', [status(thm)], ['36', '38'])).
% 0.37/0.60  thf('40', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         ((r2_hidden @ X0 @ X1)
% 0.37/0.60          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.37/0.60          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.37/0.60      inference('sup+', [status(thm)], ['35', '39'])).
% 0.37/0.60  thf('41', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0)) | (r2_hidden @ X0 @ X1))),
% 0.37/0.60      inference('simplify', [status(thm)], ['40'])).
% 0.37/0.60  thf('42', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.37/0.60      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.60  thf('43', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         ((r2_hidden @ X0 @ X1)
% 0.37/0.60          | ((k3_xboole_0 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0)))),
% 0.37/0.60      inference('sup-', [status(thm)], ['41', '42'])).
% 0.37/0.60  thf('44', plain,
% 0.37/0.60      (![X16 : $i, X17 : $i]:
% 0.37/0.60         ((k4_xboole_0 @ X16 @ X17)
% 0.37/0.60           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 0.37/0.60      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.60  thf('45', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.37/0.60            = (k5_xboole_0 @ X1 @ k1_xboole_0))
% 0.37/0.60          | (r2_hidden @ X0 @ X1))),
% 0.37/0.60      inference('sup+', [status(thm)], ['43', '44'])).
% 0.37/0.60  thf('46', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.37/0.60      inference('cnf', [status(esa)], [t5_boole])).
% 0.37/0.60  thf('47', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1))
% 0.37/0.60          | (r2_hidden @ X0 @ X1))),
% 0.37/0.60      inference('demod', [status(thm)], ['45', '46'])).
% 0.37/0.60  thf('48', plain,
% 0.37/0.60      ((((k1_xboole_0) = (k1_tarski @ sk_B_1))
% 0.37/0.60        | (r2_hidden @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.37/0.60      inference('sup+', [status(thm)], ['28', '47'])).
% 0.37/0.60  thf('49', plain,
% 0.37/0.60      (![X42 : $i, X45 : $i]:
% 0.37/0.60         (((X45) = (X42)) | ~ (r2_hidden @ X45 @ (k1_tarski @ X42)))),
% 0.37/0.60      inference('simplify', [status(thm)], ['33'])).
% 0.37/0.60  thf('50', plain,
% 0.37/0.60      ((((k1_xboole_0) = (k1_tarski @ sk_B_1)) | ((sk_A) = (sk_B_1)))),
% 0.37/0.60      inference('sup-', [status(thm)], ['48', '49'])).
% 0.37/0.60  thf('51', plain, (((sk_A) != (sk_B_1))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('52', plain, (((k1_xboole_0) = (k1_tarski @ sk_B_1))),
% 0.37/0.60      inference('simplify_reflect-', [status(thm)], ['50', '51'])).
% 0.37/0.60  thf('53', plain,
% 0.37/0.60      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.37/0.60         (((X43) != (X42))
% 0.37/0.60          | (r2_hidden @ X43 @ X44)
% 0.37/0.60          | ((X44) != (k1_tarski @ X42)))),
% 0.37/0.60      inference('cnf', [status(esa)], [d1_tarski])).
% 0.37/0.60  thf('54', plain, (![X42 : $i]: (r2_hidden @ X42 @ (k1_tarski @ X42))),
% 0.37/0.60      inference('simplify', [status(thm)], ['53'])).
% 0.37/0.60  thf('55', plain, (![X10 : $i]: ((k3_xboole_0 @ X10 @ X10) = (X10))),
% 0.37/0.60      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.37/0.60  thf('56', plain,
% 0.37/0.60      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.37/0.60         (~ (r2_hidden @ X13 @ (k3_xboole_0 @ X11 @ X14))
% 0.37/0.60          | ~ (r1_xboole_0 @ X11 @ X14))),
% 0.37/0.60      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.37/0.60  thf('57', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.37/0.60      inference('sup-', [status(thm)], ['55', '56'])).
% 0.37/0.60  thf('58', plain,
% 0.37/0.60      (![X0 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.37/0.60      inference('sup-', [status(thm)], ['54', '57'])).
% 0.37/0.60  thf('59', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_B_1) @ k1_xboole_0)),
% 0.37/0.61      inference('sup-', [status(thm)], ['52', '58'])).
% 0.37/0.61  thf('60', plain, (((k1_xboole_0) = (k1_tarski @ sk_B_1))),
% 0.37/0.61      inference('simplify_reflect-', [status(thm)], ['50', '51'])).
% 0.37/0.61  thf('61', plain,
% 0.37/0.61      (![X15 : $i]:
% 0.37/0.61         (((X15) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X15) @ X15))),
% 0.37/0.61      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.37/0.61  thf('62', plain,
% 0.37/0.61      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.37/0.61         ((r2_hidden @ X8 @ X6) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.37/0.61      inference('simplify', [status(thm)], ['30'])).
% 0.37/0.61  thf('63', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.37/0.61          | (r2_hidden @ (sk_B @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['61', '62'])).
% 0.37/0.61  thf('64', plain,
% 0.37/0.61      (![X28 : $i, X29 : $i]:
% 0.37/0.61         ((k2_xboole_0 @ X28 @ X29)
% 0.37/0.61           = (k5_xboole_0 @ X28 @ (k4_xboole_0 @ X29 @ X28)))),
% 0.37/0.61      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.37/0.61  thf('65', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['21', '22'])).
% 0.37/0.61  thf('66', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['64', '65'])).
% 0.37/0.61  thf('67', plain,
% 0.37/0.61      (![X23 : $i, X24 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X23 @ X24) @ X24)),
% 0.37/0.61      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.37/0.61  thf('68', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (r1_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0)),
% 0.37/0.61      inference('sup+', [status(thm)], ['66', '67'])).
% 0.37/0.61  thf('69', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.61  thf('70', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((k3_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.37/0.61           = (k1_xboole_0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['68', '69'])).
% 0.37/0.61  thf('71', plain,
% 0.37/0.61      (![X16 : $i, X17 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ X16 @ X17)
% 0.37/0.61           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 0.37/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.61  thf('72', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['21', '22'])).
% 0.37/0.61  thf('73', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['71', '72'])).
% 0.37/0.61  thf('74', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.61  thf('75', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['73', '74'])).
% 0.37/0.61  thf('76', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0))
% 0.37/0.61           = (k1_xboole_0))),
% 0.37/0.61      inference('demod', [status(thm)], ['70', '75'])).
% 0.37/0.61  thf('77', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['71', '72'])).
% 0.37/0.61  thf('78', plain,
% 0.37/0.61      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.37/0.61         (~ (r2_hidden @ X13 @ (k3_xboole_0 @ X11 @ X14))
% 0.37/0.61          | ~ (r1_xboole_0 @ X11 @ X14))),
% 0.37/0.61      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.37/0.61  thf('79', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))
% 0.37/0.61          | ~ (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['77', '78'])).
% 0.37/0.61  thf('80', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 0.37/0.61          | ~ (r1_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['76', '79'])).
% 0.37/0.61  thf('81', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (r1_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0)),
% 0.37/0.61      inference('sup+', [status(thm)], ['66', '67'])).
% 0.37/0.61  thf('82', plain,
% 0.37/0.61      (![X11 : $i, X12 : $i]:
% 0.37/0.61         ((r1_xboole_0 @ X11 @ X12)
% 0.37/0.61          | (r2_hidden @ (sk_C @ X12 @ X11) @ (k3_xboole_0 @ X11 @ X12)))),
% 0.37/0.61      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.37/0.61  thf('83', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.61  thf('84', plain,
% 0.37/0.61      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.37/0.61         (~ (r2_hidden @ X13 @ (k3_xboole_0 @ X11 @ X14))
% 0.37/0.61          | ~ (r1_xboole_0 @ X11 @ X14))),
% 0.37/0.61      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.37/0.61  thf('85', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.61         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.37/0.61          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.37/0.61      inference('sup-', [status(thm)], ['83', '84'])).
% 0.37/0.61  thf('86', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]:
% 0.37/0.61         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.37/0.61      inference('sup-', [status(thm)], ['82', '85'])).
% 0.37/0.61  thf('87', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         (r1_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['81', '86'])).
% 0.37/0.61  thf('88', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.37/0.61      inference('demod', [status(thm)], ['80', '87'])).
% 0.37/0.61  thf('89', plain,
% 0.37/0.61      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['63', '88'])).
% 0.37/0.61  thf('90', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['73', '74'])).
% 0.37/0.61  thf('91', plain,
% 0.37/0.61      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['89', '90'])).
% 0.37/0.61  thf('92', plain,
% 0.37/0.61      (![X23 : $i, X24 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X23 @ X24) @ X24)),
% 0.37/0.61      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.37/0.61  thf('93', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.37/0.61      inference('sup+', [status(thm)], ['91', '92'])).
% 0.37/0.61  thf('94', plain, ($false),
% 0.37/0.61      inference('demod', [status(thm)], ['59', '60', '93'])).
% 0.37/0.61  
% 0.37/0.61  % SZS output end Refutation
% 0.37/0.61  
% 0.37/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.g0Ag70rFSG

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:25 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 370 expanded)
%              Number of leaves         :   22 ( 114 expanded)
%              Depth                    :   18
%              Number of atoms          :  888 (3731 expanded)
%              Number of equality atoms :  164 ( 750 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t43_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B = k1_xboole_0 )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B = k1_xboole_0 )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('4',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('8',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('9',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('18',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('19',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','22'])).

thf('24',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('25',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('26',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('27',plain,(
    ! [X47: $i,X48: $i] :
      ( ( X48
        = ( k1_tarski @ X47 ) )
      | ( X48 = k1_xboole_0 )
      | ~ ( r1_tarski @ X48 @ ( k1_tarski @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('28',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','14'])).

thf('31',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_B )
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k4_xboole_0 @ sk_C @ sk_B )
      = ( k5_xboole_0 @ sk_B @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('37',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('44',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['35','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('51',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf('55',plain,
    ( ( ( k4_xboole_0 @ sk_C @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','53','54'])).

thf('56',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( ( k4_xboole_0 @ X4 @ X5 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('57',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('60',plain,(
    ! [X47: $i,X48: $i] :
      ( ( X48
        = ( k1_tarski @ X47 ) )
      | ( X48 = k1_xboole_0 )
      | ~ ( r1_tarski @ X48 @ ( k1_tarski @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( sk_B = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C
      = ( k1_tarski @ sk_A ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_C
      = ( k1_tarski @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['64'])).

thf('66',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['64'])).

thf('67',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['67'])).

thf('69',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('70',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['70'])).

thf('72',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','71'])).

thf('73',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['64'])).

thf('75',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['66','68','76'])).

thf('78',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['65','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf('81',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['70'])).

thf('82',plain,
    ( ! [X0: $i] :
        ( sk_C
       != ( k4_xboole_0 @ X0 @ X0 ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['79','82'])).

thf('84',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('87',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('90',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['88','91'])).

thf('93',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ sk_B @ X0 )
        = X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['85','94'])).

thf('96',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['84','95'])).

thf('97',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['65','77'])).

thf('98',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( sk_C != k1_xboole_0 )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['70'])).

thf('100',plain,(
    sk_C != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['98','99'])).

thf('101',plain,(
    sk_C != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['83','100'])).

thf('102',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['63','78','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['23','102'])).

thf('104',plain,
    ( ( k1_tarski @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['0','103'])).

thf('105',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['65','77'])).

thf('106',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['104','105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.g0Ag70rFSG
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:48:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.46/0.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.70  % Solved by: fo/fo7.sh
% 0.46/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.70  % done 678 iterations in 0.248s
% 0.46/0.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.70  % SZS output start Refutation
% 0.46/0.70  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.46/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.70  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.70  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.70  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.70  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.70  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.70  thf(t43_zfmisc_1, conjecture,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.46/0.70          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.46/0.70          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.46/0.70          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.46/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.70    (~( ![A:$i,B:$i,C:$i]:
% 0.46/0.70        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.46/0.70             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.46/0.70             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.46/0.70             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.46/0.70    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.46/0.70  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(commutativity_k3_xboole_0, axiom,
% 0.46/0.70    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.46/0.70  thf('1', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.70      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.70  thf(t94_xboole_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( k2_xboole_0 @ A @ B ) =
% 0.46/0.70       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.46/0.70  thf('2', plain,
% 0.46/0.70      (![X17 : $i, X18 : $i]:
% 0.46/0.70         ((k2_xboole_0 @ X17 @ X18)
% 0.46/0.70           = (k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ 
% 0.46/0.70              (k3_xboole_0 @ X17 @ X18)))),
% 0.46/0.70      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.46/0.70  thf(t91_xboole_1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.46/0.70       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.46/0.70  thf('3', plain,
% 0.46/0.70      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.70         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.46/0.70           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.46/0.70      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.70  thf('4', plain,
% 0.46/0.70      (![X17 : $i, X18 : $i]:
% 0.46/0.70         ((k2_xboole_0 @ X17 @ X18)
% 0.46/0.70           = (k5_xboole_0 @ X17 @ 
% 0.46/0.70              (k5_xboole_0 @ X18 @ (k3_xboole_0 @ X17 @ X18))))),
% 0.46/0.70      inference('demod', [status(thm)], ['2', '3'])).
% 0.46/0.70  thf('5', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         ((k2_xboole_0 @ X0 @ X1)
% 0.46/0.70           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.46/0.70      inference('sup+', [status(thm)], ['1', '4'])).
% 0.46/0.70  thf(t100_xboole_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.46/0.70  thf('6', plain,
% 0.46/0.70      (![X7 : $i, X8 : $i]:
% 0.46/0.70         ((k4_xboole_0 @ X7 @ X8)
% 0.46/0.70           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.46/0.70      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.70  thf('7', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         ((k2_xboole_0 @ X0 @ X1)
% 0.46/0.70           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.46/0.70      inference('demod', [status(thm)], ['5', '6'])).
% 0.46/0.70  thf(t92_xboole_1, axiom,
% 0.46/0.70    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.46/0.70  thf('8', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.46/0.70      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.46/0.70  thf('9', plain,
% 0.46/0.70      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.70         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.46/0.70           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.46/0.70      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.70  thf('10', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.70           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.46/0.70      inference('sup+', [status(thm)], ['8', '9'])).
% 0.46/0.70  thf(commutativity_k5_xboole_0, axiom,
% 0.46/0.70    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.46/0.70  thf('11', plain,
% 0.46/0.70      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.46/0.70      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.46/0.70  thf(t5_boole, axiom,
% 0.46/0.70    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.70  thf('12', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.46/0.70      inference('cnf', [status(esa)], [t5_boole])).
% 0.46/0.70  thf('13', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.70      inference('sup+', [status(thm)], ['11', '12'])).
% 0.46/0.70  thf('14', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.46/0.70      inference('demod', [status(thm)], ['10', '13'])).
% 0.46/0.70  thf('15', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         ((k4_xboole_0 @ X0 @ X1)
% 0.46/0.70           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.46/0.70      inference('sup+', [status(thm)], ['7', '14'])).
% 0.46/0.70  thf('16', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.70      inference('sup+', [status(thm)], ['11', '12'])).
% 0.46/0.70  thf('17', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.46/0.70      inference('sup+', [status(thm)], ['15', '16'])).
% 0.46/0.70  thf(t2_boole, axiom,
% 0.46/0.70    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.46/0.70  thf('18', plain,
% 0.46/0.70      (![X9 : $i]: ((k3_xboole_0 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.70      inference('cnf', [status(esa)], [t2_boole])).
% 0.46/0.70  thf('19', plain,
% 0.46/0.70      (![X7 : $i, X8 : $i]:
% 0.46/0.70         ((k4_xboole_0 @ X7 @ X8)
% 0.46/0.70           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.46/0.70      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.70  thf('20', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.70      inference('sup+', [status(thm)], ['18', '19'])).
% 0.46/0.70  thf('21', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.46/0.70      inference('cnf', [status(esa)], [t5_boole])).
% 0.46/0.70  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.46/0.70      inference('sup+', [status(thm)], ['20', '21'])).
% 0.46/0.70  thf('23', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.46/0.70      inference('demod', [status(thm)], ['17', '22'])).
% 0.46/0.70  thf('24', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(t7_xboole_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.46/0.70  thf('25', plain,
% 0.46/0.70      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 0.46/0.70      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.46/0.70  thf('26', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 0.46/0.70      inference('sup+', [status(thm)], ['24', '25'])).
% 0.46/0.70  thf(l3_zfmisc_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.46/0.70       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.46/0.70  thf('27', plain,
% 0.46/0.70      (![X47 : $i, X48 : $i]:
% 0.46/0.70         (((X48) = (k1_tarski @ X47))
% 0.46/0.70          | ((X48) = (k1_xboole_0))
% 0.46/0.70          | ~ (r1_tarski @ X48 @ (k1_tarski @ X47)))),
% 0.46/0.70      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.46/0.70  thf('28', plain,
% 0.46/0.70      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['26', '27'])).
% 0.46/0.70  thf('29', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('30', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         ((k4_xboole_0 @ X0 @ X1)
% 0.46/0.70           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.46/0.70      inference('sup+', [status(thm)], ['7', '14'])).
% 0.46/0.70  thf('31', plain,
% 0.46/0.70      (((k4_xboole_0 @ sk_C @ sk_B) = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.46/0.70      inference('sup+', [status(thm)], ['29', '30'])).
% 0.46/0.70  thf('32', plain,
% 0.46/0.70      ((((k4_xboole_0 @ sk_C @ sk_B) = (k5_xboole_0 @ sk_B @ sk_B))
% 0.46/0.70        | ((sk_B) = (k1_xboole_0)))),
% 0.46/0.70      inference('sup+', [status(thm)], ['28', '31'])).
% 0.46/0.70  thf('33', plain,
% 0.46/0.70      (![X7 : $i, X8 : $i]:
% 0.46/0.70         ((k4_xboole_0 @ X7 @ X8)
% 0.46/0.70           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.46/0.70      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.70  thf('34', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.46/0.70      inference('demod', [status(thm)], ['10', '13'])).
% 0.46/0.70  thf('35', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         ((k3_xboole_0 @ X1 @ X0)
% 0.46/0.70           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.46/0.70      inference('sup+', [status(thm)], ['33', '34'])).
% 0.46/0.70  thf('36', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.70      inference('sup+', [status(thm)], ['11', '12'])).
% 0.46/0.70  thf('37', plain,
% 0.46/0.70      (![X17 : $i, X18 : $i]:
% 0.46/0.70         ((k2_xboole_0 @ X17 @ X18)
% 0.46/0.70           = (k5_xboole_0 @ X17 @ 
% 0.46/0.70              (k5_xboole_0 @ X18 @ (k3_xboole_0 @ X17 @ X18))))),
% 0.46/0.70      inference('demod', [status(thm)], ['2', '3'])).
% 0.46/0.70  thf('38', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((k2_xboole_0 @ X0 @ k1_xboole_0)
% 0.46/0.70           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.46/0.70      inference('sup+', [status(thm)], ['36', '37'])).
% 0.46/0.70  thf('39', plain,
% 0.46/0.70      (![X9 : $i]: ((k3_xboole_0 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.70      inference('cnf', [status(esa)], [t2_boole])).
% 0.46/0.70  thf('40', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.70      inference('demod', [status(thm)], ['38', '39'])).
% 0.46/0.70  thf('41', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.46/0.70      inference('cnf', [status(esa)], [t5_boole])).
% 0.46/0.70  thf('42', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.46/0.70      inference('sup+', [status(thm)], ['40', '41'])).
% 0.46/0.70  thf('43', plain,
% 0.46/0.70      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 0.46/0.70      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.46/0.70  thf(l32_xboole_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.70  thf('44', plain,
% 0.46/0.70      (![X4 : $i, X6 : $i]:
% 0.46/0.70         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.46/0.70      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.46/0.70  thf('45', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['43', '44'])).
% 0.46/0.70  thf('46', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.70      inference('sup+', [status(thm)], ['42', '45'])).
% 0.46/0.70  thf('47', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.46/0.70      inference('cnf', [status(esa)], [t5_boole])).
% 0.46/0.70  thf('48', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 0.46/0.70      inference('sup+', [status(thm)], ['46', '47'])).
% 0.46/0.70  thf('49', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.46/0.70      inference('sup+', [status(thm)], ['35', '48'])).
% 0.46/0.70  thf('50', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.70      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.70  thf('51', plain,
% 0.46/0.70      (![X7 : $i, X8 : $i]:
% 0.46/0.70         ((k4_xboole_0 @ X7 @ X8)
% 0.46/0.70           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.46/0.70      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.70  thf('52', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         ((k4_xboole_0 @ X0 @ X1)
% 0.46/0.70           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.46/0.70      inference('sup+', [status(thm)], ['50', '51'])).
% 0.46/0.70  thf('53', plain,
% 0.46/0.70      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.46/0.70      inference('sup+', [status(thm)], ['49', '52'])).
% 0.46/0.70  thf('54', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.70      inference('sup+', [status(thm)], ['42', '45'])).
% 0.46/0.70  thf('55', plain,
% 0.46/0.70      ((((k4_xboole_0 @ sk_C @ sk_B) = (k1_xboole_0))
% 0.46/0.70        | ((sk_B) = (k1_xboole_0)))),
% 0.46/0.70      inference('demod', [status(thm)], ['32', '53', '54'])).
% 0.46/0.70  thf('56', plain,
% 0.46/0.70      (![X4 : $i, X5 : $i]:
% 0.46/0.70         ((r1_tarski @ X4 @ X5) | ((k4_xboole_0 @ X4 @ X5) != (k1_xboole_0)))),
% 0.46/0.70      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.46/0.70  thf('57', plain,
% 0.46/0.70      ((((k1_xboole_0) != (k1_xboole_0))
% 0.46/0.70        | ((sk_B) = (k1_xboole_0))
% 0.46/0.70        | (r1_tarski @ sk_C @ sk_B))),
% 0.46/0.70      inference('sup-', [status(thm)], ['55', '56'])).
% 0.46/0.70  thf('58', plain, (((r1_tarski @ sk_C @ sk_B) | ((sk_B) = (k1_xboole_0)))),
% 0.46/0.70      inference('simplify', [status(thm)], ['57'])).
% 0.46/0.70  thf('59', plain,
% 0.46/0.70      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['26', '27'])).
% 0.46/0.70  thf('60', plain,
% 0.46/0.70      (![X47 : $i, X48 : $i]:
% 0.46/0.70         (((X48) = (k1_tarski @ X47))
% 0.46/0.70          | ((X48) = (k1_xboole_0))
% 0.46/0.70          | ~ (r1_tarski @ X48 @ (k1_tarski @ X47)))),
% 0.46/0.70      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.46/0.70  thf('61', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (r1_tarski @ X0 @ sk_B)
% 0.46/0.70          | ((sk_B) = (k1_xboole_0))
% 0.46/0.70          | ((X0) = (k1_xboole_0))
% 0.46/0.70          | ((X0) = (k1_tarski @ sk_A)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['59', '60'])).
% 0.46/0.70  thf('62', plain,
% 0.46/0.70      ((((sk_B) = (k1_xboole_0))
% 0.46/0.70        | ((sk_C) = (k1_tarski @ sk_A))
% 0.46/0.70        | ((sk_C) = (k1_xboole_0))
% 0.46/0.70        | ((sk_B) = (k1_xboole_0)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['58', '61'])).
% 0.46/0.70  thf('63', plain,
% 0.46/0.70      ((((sk_C) = (k1_xboole_0))
% 0.46/0.70        | ((sk_C) = (k1_tarski @ sk_A))
% 0.46/0.70        | ((sk_B) = (k1_xboole_0)))),
% 0.46/0.70      inference('simplify', [status(thm)], ['62'])).
% 0.46/0.70  thf('64', plain,
% 0.46/0.70      ((((sk_B) != (k1_xboole_0)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('65', plain,
% 0.46/0.70      ((((sk_C) != (k1_tarski @ sk_A))) <= (~ (((sk_C) = (k1_tarski @ sk_A))))),
% 0.46/0.70      inference('split', [status(esa)], ['64'])).
% 0.46/0.70  thf('66', plain,
% 0.46/0.70      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_xboole_0)))),
% 0.46/0.70      inference('split', [status(esa)], ['64'])).
% 0.46/0.70  thf('67', plain,
% 0.46/0.70      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('68', plain,
% 0.46/0.70      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.46/0.70      inference('split', [status(esa)], ['67'])).
% 0.46/0.70  thf('69', plain,
% 0.46/0.70      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['26', '27'])).
% 0.46/0.70  thf('70', plain,
% 0.46/0.70      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_xboole_0)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('71', plain,
% 0.46/0.70      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.46/0.70      inference('split', [status(esa)], ['70'])).
% 0.46/0.70  thf('72', plain,
% 0.46/0.70      (((((sk_B) != (sk_B)) | ((sk_B) = (k1_xboole_0))))
% 0.46/0.70         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['69', '71'])).
% 0.46/0.70  thf('73', plain,
% 0.46/0.70      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.46/0.70      inference('simplify', [status(thm)], ['72'])).
% 0.46/0.70  thf('74', plain,
% 0.46/0.70      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.46/0.70      inference('split', [status(esa)], ['64'])).
% 0.46/0.70  thf('75', plain,
% 0.46/0.70      ((((sk_B) != (sk_B)))
% 0.46/0.70         <= (~ (((sk_B) = (k1_xboole_0))) & ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['73', '74'])).
% 0.46/0.70  thf('76', plain,
% 0.46/0.70      ((((sk_B) = (k1_xboole_0))) | (((sk_B) = (k1_tarski @ sk_A)))),
% 0.46/0.70      inference('simplify', [status(thm)], ['75'])).
% 0.46/0.70  thf('77', plain, (~ (((sk_C) = (k1_tarski @ sk_A)))),
% 0.46/0.70      inference('sat_resolution*', [status(thm)], ['66', '68', '76'])).
% 0.46/0.70  thf('78', plain, (((sk_C) != (k1_tarski @ sk_A))),
% 0.46/0.70      inference('simpl_trail', [status(thm)], ['65', '77'])).
% 0.46/0.70  thf('79', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.46/0.70      inference('sup+', [status(thm)], ['20', '21'])).
% 0.46/0.70  thf('80', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.70      inference('sup+', [status(thm)], ['42', '45'])).
% 0.46/0.70  thf('81', plain,
% 0.46/0.70      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.46/0.70      inference('split', [status(esa)], ['70'])).
% 0.46/0.70  thf('82', plain,
% 0.46/0.70      ((![X0 : $i]: ((sk_C) != (k4_xboole_0 @ X0 @ X0)))
% 0.46/0.70         <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['80', '81'])).
% 0.46/0.70  thf('83', plain,
% 0.46/0.70      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['79', '82'])).
% 0.46/0.70  thf('84', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('85', plain,
% 0.46/0.70      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.46/0.70      inference('simplify', [status(thm)], ['72'])).
% 0.46/0.70  thf('86', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.70      inference('sup+', [status(thm)], ['11', '12'])).
% 0.46/0.70  thf('87', plain,
% 0.46/0.70      (![X17 : $i, X18 : $i]:
% 0.46/0.70         ((k2_xboole_0 @ X17 @ X18)
% 0.46/0.70           = (k5_xboole_0 @ X17 @ 
% 0.46/0.70              (k5_xboole_0 @ X18 @ (k3_xboole_0 @ X17 @ X18))))),
% 0.46/0.70      inference('demod', [status(thm)], ['2', '3'])).
% 0.46/0.70  thf('88', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.70           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.46/0.70      inference('sup+', [status(thm)], ['86', '87'])).
% 0.46/0.70  thf('89', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.70      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.70  thf('90', plain,
% 0.46/0.70      (![X9 : $i]: ((k3_xboole_0 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.70      inference('cnf', [status(esa)], [t2_boole])).
% 0.46/0.70  thf('91', plain,
% 0.46/0.70      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.46/0.70      inference('sup+', [status(thm)], ['89', '90'])).
% 0.46/0.70  thf('92', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.70      inference('demod', [status(thm)], ['88', '91'])).
% 0.46/0.70  thf('93', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.46/0.70      inference('cnf', [status(esa)], [t5_boole])).
% 0.46/0.70  thf('94', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.70      inference('sup+', [status(thm)], ['92', '93'])).
% 0.46/0.70  thf('95', plain,
% 0.46/0.70      ((![X0 : $i]: ((k2_xboole_0 @ sk_B @ X0) = (X0)))
% 0.46/0.70         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.46/0.70      inference('sup+', [status(thm)], ['85', '94'])).
% 0.46/0.70  thf('96', plain,
% 0.46/0.70      ((((k1_tarski @ sk_A) = (sk_C))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.46/0.70      inference('sup+', [status(thm)], ['84', '95'])).
% 0.46/0.70  thf('97', plain, (((sk_C) != (k1_tarski @ sk_A))),
% 0.46/0.70      inference('simpl_trail', [status(thm)], ['65', '77'])).
% 0.46/0.70  thf('98', plain, ((((sk_B) = (k1_tarski @ sk_A)))),
% 0.46/0.70      inference('simplify_reflect-', [status(thm)], ['96', '97'])).
% 0.46/0.70  thf('99', plain,
% 0.46/0.70      (~ (((sk_C) = (k1_xboole_0))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.46/0.70      inference('split', [status(esa)], ['70'])).
% 0.46/0.70  thf('100', plain, (~ (((sk_C) = (k1_xboole_0)))),
% 0.46/0.70      inference('sat_resolution*', [status(thm)], ['98', '99'])).
% 0.46/0.70  thf('101', plain, (((sk_C) != (k1_xboole_0))),
% 0.46/0.70      inference('simpl_trail', [status(thm)], ['83', '100'])).
% 0.46/0.70  thf('102', plain, (((sk_B) = (k1_xboole_0))),
% 0.46/0.70      inference('simplify_reflect-', [status(thm)], ['63', '78', '101'])).
% 0.46/0.70  thf('103', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ sk_B @ X0))),
% 0.46/0.70      inference('demod', [status(thm)], ['23', '102'])).
% 0.46/0.70  thf('104', plain, (((k1_tarski @ sk_A) = (sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['0', '103'])).
% 0.46/0.70  thf('105', plain, (((sk_C) != (k1_tarski @ sk_A))),
% 0.46/0.70      inference('simpl_trail', [status(thm)], ['65', '77'])).
% 0.46/0.70  thf('106', plain, ($false),
% 0.46/0.70      inference('simplify_reflect-', [status(thm)], ['104', '105'])).
% 0.46/0.70  
% 0.46/0.70  % SZS output end Refutation
% 0.46/0.70  
% 0.53/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
